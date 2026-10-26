import V185TrunkScan20Chunk096

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_588942 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_588942 : Nat := 118140960795 + 588942 * 2 ^ 59
def prefixEnd_588942 : Nat := 4983230072969 + 3 ^ 40 * 588942 * 2
def baseEnd_588942 : Nat := 268809176551413329259121

theorem tailTrace_588942 : CollatzResearch.WordTrace tailWord_588942 prefixEnd_588942 268809176551413329259121 := by
  unfold tailWord_588942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2685059929046399016358135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14320319621580794753910053 2685059929046399016358135)
  ·
    refine ⟨4027589893569598524537203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2685059929046399016358135 4027589893569598524537203)
    ·
      refine ⟨6041384840354397786805805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4027589893569598524537203 6041384840354397786805805)
      ·
        refine ⟨2265519315132899170052177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6041384840354397786805805 2265519315132899170052177)
        ·
          refine ⟨1699139486349674377539133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2265519315132899170052177 1699139486349674377539133)
          ·
            refine ⟨637177307381127891577175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1699139486349674377539133 637177307381127891577175)
            ·
              refine ⟨955765961071691837365763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637177307381127891577175 955765961071691837365763)
              ·
                refine ⟨1433648941607537756048645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955765961071691837365763 1433648941607537756048645)
                ·
                  refine ⟨268809176551413329259121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1433648941607537756048645 268809176551413329259121)
                  ·
                    rfl

theorem cell20_588942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_588942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588942 prefixEnd_588942 := by exact prefixLift 588942
  have htrace : WordTrace (prefixWord ++ tailWord_588942) baseStart_588942 baseEnd_588942 := by
    simpa [prefixWord, tailWord_588942, baseEnd_588942] using wordTrace_append hprefix tailTrace_588942
  have hstable : (prefixWord ++ tailWord_588942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588942).length < 2 ^ (prefixWord ++ tailWord_588942).sum := by decide
  have hdescent : baseEnd_588942 < baseStart_588942 := by decide
  rcases family_descends (prefixWord ++ tailWord_588942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_588956 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_588956 : Nat := 118140960795 + 588956 * 2 ^ 59
def prefixEnd_588956 : Nat := 4983230072969 + 3 ^ 40 * 588956 * 2
def baseEnd_588956 : Nat := 268815566532891502792397

theorem tailTrace_588956 : CollatzResearch.WordTrace tailWord_588956 prefixEnd_588956 268815566532891502792397 := by
  unfold tailWord_588956
  simp only [CollatzResearch.WordTrace]
  refine ⟨10740495027160236260937361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14320660036213648347916481 10740495027160236260937361)
  ·
    refine ⟨8055371270370177195703021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10740495027160236260937361 8055371270370177195703021)
    ·
      refine ⟨3020764226388816448388633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8055371270370177195703021 3020764226388816448388633)
      ·
        refine ⟨2265573169791612336291475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3020764226388816448388633 2265573169791612336291475)
        ·
          refine ⟨3398359754687418504437213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265573169791612336291475 3398359754687418504437213)
          ·
            refine ⟨1274384908007781939163955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3398359754687418504437213 1274384908007781939163955)
            ·
              refine ⟨1911577362011672908745933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274384908007781939163955 1911577362011672908745933)
              ·
                refine ⟨716841510754377340779725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911577362011672908745933 716841510754377340779725)
                ·
                  refine ⟨268815566532891502792397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716841510754377340779725 268815566532891502792397)
                  ·
                    rfl

theorem cell20_588956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_588956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_588956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_588956 prefixEnd_588956 := by exact prefixLift 588956
  have htrace : WordTrace (prefixWord ++ tailWord_588956) baseStart_588956 baseEnd_588956 := by
    simpa [prefixWord, tailWord_588956, baseEnd_588956] using wordTrace_append hprefix tailTrace_588956
  have hstable : (prefixWord ++ tailWord_588956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_588956).length < 2 ^ (prefixWord ++ tailWord_588956).sum := by decide
  have hdescent : baseEnd_588956 < baseStart_588956 := by decide
  rcases family_descends (prefixWord ++ tailWord_588956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589015 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 3]
def baseStart_589015 : Nat := 118140960795 + 589015 * 2 ^ 59
def prefixEnd_589015 : Nat := 4983230072969 + 3 ^ 40 * 589015 * 2
def baseEnd_589015 : Nat := 268842495740549519825489

theorem tailTrace_589015 : CollatzResearch.WordTrace tailWord_589015 prefixEnd_589015 268842495740549519825489 := by
  unfold tailWord_589015
  simp only [CollatzResearch.WordTrace]
  refine ⟨21483141961106725598272499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14322094640737817065514999 21483141961106725598272499)
  ·
    refine ⟨32224712941660088397408749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21483141961106725598272499 32224712941660088397408749)
    ·
      refine ⟨12084267353122533149028281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32224712941660088397408749 12084267353122533149028281)
      ·
        refine ⟨9063200514841899861771211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12084267353122533149028281 9063200514841899861771211)
        ·
          refine ⟨13594800772262849792656817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9063200514841899861771211 13594800772262849792656817)
          ·
            refine ⟨10196100579197137344492613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13594800772262849792656817 10196100579197137344492613)
            ·
              refine ⟨1911768858599463252092365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10196100579197137344492613 1911768858599463252092365)
              ·
                refine ⟨716913321974798719534637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911768858599463252092365 716913321974798719534637)
                ·
                  refine ⟨268842495740549519825489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716913321974798719534637 268842495740549519825489)
                  ·
                    rfl

theorem cell20_589015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_589015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589015 prefixEnd_589015 := by exact prefixLift 589015
  have htrace : WordTrace (prefixWord ++ tailWord_589015) baseStart_589015 baseEnd_589015 := by
    simpa [prefixWord, tailWord_589015, baseEnd_589015] using wordTrace_append hprefix tailTrace_589015
  have hstable : (prefixWord ++ tailWord_589015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589015).length < 2 ^ (prefixWord ++ tailWord_589015).sum := by decide
  have hdescent : baseEnd_589015 < baseStart_589015 := by decide
  rcases family_descends (prefixWord ++ tailWord_589015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589084 : List Nat := [2, 2, 3, 1, 1, 1, 6, 4]
def baseStart_589084 : Nat := 118140960795 + 589084 * 2 ^ 59
def prefixEnd_589084 : Nat := 4983230072969 + 3 ^ 40 * 589084 * 2
def baseEnd_589084 : Nat := 89624663073563982175069

theorem tailTrace_589084 : CollatzResearch.WordTrace tailWord_589084 prefixEnd_589084 89624663073563982175069 := by
  unfold tailWord_589084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742829298928375191267153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14323772398571166921689537 10742829298928375191267153)
  ·
    refine ⟨8057121974196281393450365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10742829298928375191267153 8057121974196281393450365)
    ·
      refine ⟨3021420740323605522543887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8057121974196281393450365 3021420740323605522543887)
      ·
        refine ⟨4532131110485408283815831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021420740323605522543887 4532131110485408283815831)
        ·
          refine ⟨6798196665728112425723747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532131110485408283815831 6798196665728112425723747)
          ·
            refine ⟨10197294998592168638585621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6798196665728112425723747 10197294998592168638585621)
            ·
              refine ⟨477998203059007904933701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10197294998592168638585621 477998203059007904933701)
              ·
                refine ⟨89624663073563982175069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 477998203059007904933701 89624663073563982175069)
                ·
                  rfl

theorem cell20_589084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_589084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589084 prefixEnd_589084 := by exact prefixLift 589084
  have htrace : WordTrace (prefixWord ++ tailWord_589084) baseStart_589084 baseEnd_589084 := by
    simpa [prefixWord, tailWord_589084, baseEnd_589084] using wordTrace_append hprefix tailTrace_589084
  have hstable : (prefixWord ++ tailWord_589084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589084).length < 2 ^ (prefixWord ++ tailWord_589084).sum := by decide
  have hdescent : baseEnd_589084 < baseStart_589084 := by decide
  rcases family_descends (prefixWord ++ tailWord_589084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589090 : List Nat := [3, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_589090 : Nat := 118140960795 + 589090 * 2 ^ 59
def prefixEnd_589090 : Nat := 4983230072969 + 3 ^ 40 * 589090 * 2
def baseEnd_589090 : Nat := 268876727784182592325183

theorem tailTrace_589090 : CollatzResearch.WordTrace tailWord_589090 prefixEnd_589090 268876727784182592325183 := by
  unfold tailWord_589090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371469358958753351813181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14323918290556675604835149 5371469358958753351813181)
  ·
    refine ⟨2014301009609532506929943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5371469358958753351813181 2014301009609532506929943)
    ·
      refine ⟨3021451514414298760394915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014301009609532506929943 3021451514414298760394915)
      ·
        refine ⟨4532177271621448140592373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021451514414298760394915 4532177271621448140592373)
        ·
          refine ⟨424891619214510763180535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4532177271621448140592373 424891619214510763180535)
          ·
            refine ⟨637337428821766144770803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424891619214510763180535 637337428821766144770803)
            ·
              refine ⟨956006143232649217156205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637337428821766144770803 956006143232649217156205)
              ·
                refine ⟨358502303712243456433577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 956006143232649217156205 358502303712243456433577)
                ·
                  refine ⟨268876727784182592325183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358502303712243456433577 268876727784182592325183)
                  ·
                    rfl

theorem cell20_589090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_589090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589090 prefixEnd_589090 := by exact prefixLift 589090
  have htrace : WordTrace (prefixWord ++ tailWord_589090) baseStart_589090 baseEnd_589090 := by
    simpa [prefixWord, tailWord_589090, baseEnd_589090] using wordTrace_append hprefix tailTrace_589090
  have hstable : (prefixWord ++ tailWord_589090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589090).length < 2 ^ (prefixWord ++ tailWord_589090).sum := by decide
  have hdescent : baseEnd_589090 < baseStart_589090 := by decide
  rcases family_descends (prefixWord ++ tailWord_589090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589101 : List Nat := [1, 5, 3, 1, 1, 3, 6]
def baseStart_589101 : Nat := 118140960795 + 589101 * 2 ^ 59
def prefixEnd_589101 : Nat := 4983230072969 + 3 ^ 40 * 589101 * 2
def baseEnd_589101 : Nat := 29875749831546160328719

theorem tailTrace_589101 : CollatzResearch.WordTrace tailWord_589101 prefixEnd_589101 29875749831546160328719 := by
  unfold tailWord_589101
  simp only [CollatzResearch.WordTrace]
  refine ⟨21486278638795162285903157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14324185759196774857268771 21486278638795162285903157)
  ·
    refine ⟨2014338622387046464303421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21486278638795162285903157 2014338622387046464303421)
    ·
      refine ⟨755376983395142424113783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2014338622387046464303421 755376983395142424113783)
      ·
        refine ⟨1133065475092713636170675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755376983395142424113783 1133065475092713636170675)
        ·
          refine ⟨1699598212639070454256013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133065475092713636170675 1699598212639070454256013)
          ·
            refine ⟨637349329739651420346005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1699598212639070454256013 637349329739651420346005)
            ·
              refine ⟨29875749831546160328719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 637349329739651420346005 29875749831546160328719)
              ·
                rfl

theorem cell20_589101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 6].length) (baseStart_589101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589101 prefixEnd_589101 := by exact prefixLift 589101
  have htrace : WordTrace (prefixWord ++ tailWord_589101) baseStart_589101 baseEnd_589101 := by
    simpa [prefixWord, tailWord_589101, baseEnd_589101] using wordTrace_append hprefix tailTrace_589101
  have hstable : (prefixWord ++ tailWord_589101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589101).length < 2 ^ (prefixWord ++ tailWord_589101).sum := by decide
  have hdescent : baseEnd_589101 < baseStart_589101 := by decide
  rcases family_descends (prefixWord ++ tailWord_589101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589105 : List Nat := [1, 2, 2, 3, 3, 1, 8]
def baseStart_589105 : Nat := 118140960795 + 589105 * 2 ^ 59
def prefixEnd_589105 : Nat := 4983230072969 + 3 ^ 40 * 589105 * 2
def baseEnd_589105 : Nat := 29875952688101022980569

theorem tailTrace_589105 : CollatzResearch.WordTrace tailWord_589105 prefixEnd_589105 29875952688101022980569 := by
  unfold tailWord_589105
  simp only [CollatzResearch.WordTrace]
  refine ⟨21486424530780670969048769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14324283020520447312699179 21486424530780670969048769)
  ·
    refine ⟨16114818398085503226786577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21486424530780670969048769 16114818398085503226786577)
    ·
      refine ⟨12086113798564127420089933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16114818398085503226786577 12086113798564127420089933)
      ·
        refine ⟨4532292674461547782533725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12086113798564127420089933 4532292674461547782533725)
        ·
          refine ⟨1699609752923080418450147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4532292674461547782533725 1699609752923080418450147)
          ·
            refine ⟨2549414629384620627675221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699609752923080418450147 2549414629384620627675221)
            ·
              refine ⟨29875952688101022980569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2549414629384620627675221 29875952688101022980569)
              ·
                rfl

theorem cell20_589105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_589105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589105 prefixEnd_589105 := by exact prefixLift 589105
  have htrace : WordTrace (prefixWord ++ tailWord_589105) baseStart_589105 baseEnd_589105 := by
    simpa [prefixWord, tailWord_589105, baseEnd_589105] using wordTrace_append hprefix tailTrace_589105
  have hstable : (prefixWord ++ tailWord_589105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589105).length < 2 ^ (prefixWord ++ tailWord_589105).sum := by decide
  have hdescent : baseEnd_589105 < baseStart_589105 := by decide
  rcases family_descends (prefixWord ++ tailWord_589105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589108 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_589108 : Nat := 118140960795 + 589108 * 2 ^ 59
def prefixEnd_589108 : Nat := 4983230072969 + 3 ^ 40 * 589108 * 2
def baseEnd_589108 : Nat := 268884943474654529725109

theorem tailTrace_589108 : CollatzResearch.WordTrace tailWord_589108 prefixEnd_589108 268884943474654529725109 := by
  unfold tailWord_589108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10743266974884901240703989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14324355966513201654271985 10743266974884901240703989)
  ·
    refine ⟨1007181278895459491315999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10743266974884901240703989 1007181278895459491315999)
    ·
      refine ⟨1510771918343189236973999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1007181278895459491315999 1510771918343189236973999)
      ·
        refine ⟨2266157877514783855460999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1510771918343189236973999 2266157877514783855460999)
        ·
          refine ⟨3399236816272175783191499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266157877514783855460999 3399236816272175783191499)
          ·
            refine ⟨5098855224408263674787249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399236816272175783191499 5098855224408263674787249)
            ·
              refine ⟨3824141418306197756090437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098855224408263674787249 3824141418306197756090437)
              ·
                refine ⟨717026515932412079266957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3824141418306197756090437 717026515932412079266957)
                ·
                  refine ⟨268884943474654529725109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717026515932412079266957 268884943474654529725109)
                  ·
                    rfl

theorem cell20_589108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_589108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589108 prefixEnd_589108 := by exact prefixLift 589108
  have htrace : WordTrace (prefixWord ++ tailWord_589108) baseStart_589108 baseEnd_589108 := by
    simpa [prefixWord, tailWord_589108, baseEnd_589108] using wordTrace_append hprefix tailTrace_589108
  have hstable : (prefixWord ++ tailWord_589108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589108).length < 2 ^ (prefixWord ++ tailWord_589108).sum := by decide
  have hdescent : baseEnd_589108 < baseStart_589108 := by decide
  rcases family_descends (prefixWord ++ tailWord_589108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589143 : List Nat := [1, 1, 3, 2, 3, 2, 2, 6]
def baseStart_589143 : Nat := 118140960795 + 589143 * 2 ^ 59
def prefixEnd_589143 : Nat := 4983230072969 + 3 ^ 40 * 589143 * 2
def baseEnd_589143 : Nat := 89633639476116654519433

theorem tailTrace_589143 : CollatzResearch.WordTrace tailWord_589143 prefixEnd_589143 89633639476116654519433 := by
  unfold tailWord_589143
  simp only [CollatzResearch.WordTrace]
  refine ⟨21487810504643003458932083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14325207003095335639288055 21487810504643003458932083)
  ·
    refine ⟨32231715756964505188398125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21487810504643003458932083 32231715756964505188398125)
    ·
      refine ⟨12086893408861689445649297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32231715756964505188398125 12086893408861689445649297)
      ·
        refine ⟨9065170056646267084236973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12086893408861689445649297 9065170056646267084236973)
        ·
          refine ⟨3399438771242350156588865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9065170056646267084236973 3399438771242350156588865)
          ·
            refine ⟨2549579078431762617441649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3399438771242350156588865 2549579078431762617441649)
            ·
              refine ⟨1912184308823821963081237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549579078431762617441649 1912184308823821963081237)
              ·
                refine ⟨89633639476116654519433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1912184308823821963081237 89633639476116654519433)
                ·
                  rfl

theorem cell20_589143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_589143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589143 prefixEnd_589143 := by exact prefixLift 589143
  have htrace : WordTrace (prefixWord ++ tailWord_589143) baseStart_589143 baseEnd_589143 := by
    simpa [prefixWord, tailWord_589143, baseEnd_589143] using wordTrace_append hprefix tailTrace_589143
  have hstable : (prefixWord ++ tailWord_589143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589143).length < 2 ^ (prefixWord ++ tailWord_589143).sum := by decide
  have hdescent : baseEnd_589143 < baseStart_589143 := by decide
  rcases family_descends (prefixWord ++ tailWord_589143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589160 : List Nat := [2, 1, 4, 2, 4, 7]
def baseStart_589160 : Nat := 118140960795 + 589160 * 2 ^ 59
def prefixEnd_589160 : Nat := 4983230072969 + 3 ^ 40 * 589160 * 2
def baseEnd_589160 : Nat := 9959580655243461481169

theorem tailTrace_589160 : CollatzResearch.WordTrace tailWord_589160 prefixEnd_589160 9959580655243461481169 := by
  unfold tailWord_589160
  simp only [CollatzResearch.WordTrace]
  refine ⟨10744215272790707681150467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14325620363720943574867289 10744215272790707681150467)
  ·
    refine ⟨16116322909186061521725701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10744215272790707681150467 16116322909186061521725701)
    ·
      refine ⟨3021810545472386535323569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16116322909186061521725701 3021810545472386535323569)
      ·
        refine ⟨2266357909104289901492677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3021810545472386535323569 2266357909104289901492677)
        ·
          refine ⟨424942107957054356529877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2266357909104289901492677 424942107957054356529877)
          ·
            refine ⟨9959580655243461481169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 424942107957054356529877 9959580655243461481169)
            ·
              rfl

theorem cell20_589160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 7].length) (baseStart_589160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589160 prefixEnd_589160 := by exact prefixLift 589160
  have htrace : WordTrace (prefixWord ++ tailWord_589160) baseStart_589160 baseEnd_589160 := by
    simpa [prefixWord, tailWord_589160, baseEnd_589160] using wordTrace_append hprefix tailTrace_589160
  have hstable : (prefixWord ++ tailWord_589160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589160).length < 2 ^ (prefixWord ++ tailWord_589160).sum := by decide
  have hdescent : baseEnd_589160 < baseStart_589160 := by decide
  rcases family_descends (prefixWord ++ tailWord_589160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589167 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 3]
def baseStart_589167 : Nat := 118140960795 + 589167 * 2 ^ 59
def prefixEnd_589167 : Nat := 4983230072969 + 3 ^ 40 * 589167 * 2
def baseEnd_589167 : Nat := 268911872682312546758201

theorem tailTrace_589167 : CollatzResearch.WordTrace tailWord_589167 prefixEnd_589167 268911872682312546758201 := by
  unfold tailWord_589167
  simp only [CollatzResearch.WordTrace]
  refine ⟨21488685856556055557805755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14325790571037370371870503 21488685856556055557805755)
  ·
    refine ⟨32233028784834083336708633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21488685856556055557805755 32233028784834083336708633)
    ·
      refine ⟨24174771588625562502531475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32233028784834083336708633 24174771588625562502531475)
      ·
        refine ⟨36262157382938343753797213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24174771588625562502531475 36262157382938343753797213)
        ·
          refine ⟨13598309018601878907673955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36262157382938343753797213 13598309018601878907673955)
          ·
            refine ⟨20397463527902818361510933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13598309018601878907673955 20397463527902818361510933)
            ·
              refine ⟨956131102870444610695825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20397463527902818361510933 956131102870444610695825)
              ·
                refine ⟨717098327152833458021869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956131102870444610695825 717098327152833458021869)
                ·
                  refine ⟨268911872682312546758201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717098327152833458021869 268911872682312546758201)
                  ·
                    rfl

theorem cell20_589167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_589167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589167 prefixEnd_589167 := by exact prefixLift 589167
  have htrace : WordTrace (prefixWord ++ tailWord_589167) baseStart_589167 baseEnd_589167 := by
    simpa [prefixWord, tailWord_589167, baseEnd_589167] using wordTrace_append hprefix tailTrace_589167
  have hstable : (prefixWord ++ tailWord_589167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589167).length < 2 ^ (prefixWord ++ tailWord_589167).sum := by decide
  have hdescent : baseEnd_589167 < baseStart_589167 := by decide
  rcases family_descends (prefixWord ++ tailWord_589167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589229 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_589229 : Nat := 118140960795 + 589229 * 2 ^ 59
def prefixEnd_589229 : Nat := 4983230072969 + 3 ^ 40 * 589229 * 2
def baseEnd_589229 : Nat := 268940171171715886691281

theorem tailTrace_589229 : CollatzResearch.WordTrace tailWord_589229 prefixEnd_589229 268940171171715886691281 := by
  unfold tailWord_589229
  simp only [CollatzResearch.WordTrace]
  refine ⟨21490947182331440146562741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14327298121554293431041827 21490947182331440146562741)
  ·
    refine ⟨2014776298343572513740257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21490947182331440146562741 2014776298343572513740257)
    ·
      refine ⟨1511082223757679385305193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2014776298343572513740257 1511082223757679385305193)
      ·
        refine ⟨1133311667818259538978895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1511082223757679385305193 1133311667818259538978895)
        ·
          refine ⟨1699967501727389308468343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133311667818259538978895 1699967501727389308468343)
          ·
            refine ⟨2549951252591083962702515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699967501727389308468343 2549951252591083962702515)
            ·
              refine ⟨3824926878886625944053773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549951252591083962702515 3824926878886625944053773)
              ·
                refine ⟨1434347579582484729020165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3824926878886625944053773 1434347579582484729020165)
                ·
                  refine ⟨268940171171715886691281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434347579582484729020165 268940171171715886691281)
                  ·
                    rfl

theorem cell20_589229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_589229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589229 prefixEnd_589229 := by exact prefixLift 589229
  have htrace : WordTrace (prefixWord ++ tailWord_589229) baseStart_589229 baseEnd_589229 := by
    simpa [prefixWord, tailWord_589229, baseEnd_589229] using wordTrace_append hprefix tailTrace_589229
  have hstable : (prefixWord ++ tailWord_589229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589229).length < 2 ^ (prefixWord ++ tailWord_589229).sum := by decide
  have hdescent : baseEnd_589229 < baseStart_589229 := by decide
  rcases family_descends (prefixWord ++ tailWord_589229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589271 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_589271 : Nat := 118140960795 + 589271 * 2 ^ 59
def prefixEnd_589271 : Nat := 4983230072969 + 3 ^ 40 * 589271 * 2
def baseEnd_589271 : Nat := 268959341116150407291109

theorem tailTrace_589271 : CollatzResearch.WordTrace tailWord_589271 prefixEnd_589271 268959341116150407291109 := by
  unfold tailWord_589271
  simp only [CollatzResearch.WordTrace]
  refine ⟨21492479048179281319591667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14328319365452854213061111 21492479048179281319591667)
  ·
    refine ⟨32238718572268921979387501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21492479048179281319591667 32238718572268921979387501)
    ·
      refine ⟨12089519464600845742270313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32238718572268921979387501 12089519464600845742270313)
      ·
        refine ⟨9067139598450634306702735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12089519464600845742270313 9067139598450634306702735)
        ·
          refine ⟨13600709397675951460054103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9067139598450634306702735 13600709397675951460054103)
          ·
            refine ⟨20401064096513927190081155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13600709397675951460054103 20401064096513927190081155)
            ·
              refine ⟨30601596144770890785121733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20401064096513927190081155 30601596144770890785121733)
              ·
                refine ⟨5737799277144542022210325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30601596144770890785121733 5737799277144542022210325)
                ·
                  refine ⟨268959341116150407291109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5737799277144542022210325 268959341116150407291109)
                  ·
                    rfl

theorem cell20_589271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_589271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589271 prefixEnd_589271 := by exact prefixLift 589271
  have htrace : WordTrace (prefixWord ++ tailWord_589271) baseStart_589271 baseEnd_589271 := by
    simpa [prefixWord, tailWord_589271, baseEnd_589271] using wordTrace_append hprefix tailTrace_589271
  have hstable : (prefixWord ++ tailWord_589271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589271).length < 2 ^ (prefixWord ++ tailWord_589271).sum := by decide
  have hdescent : baseEnd_589271 < baseStart_589271 := by decide
  rcases family_descends (prefixWord ++ tailWord_589271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589298 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_589298 : Nat := 118140960795 + 589298 * 2 ^ 59
def prefixEnd_589298 : Nat := 4983230072969 + 3 ^ 40 * 589298 * 2
def baseEnd_589298 : Nat := 268971664651858313390999

theorem tailTrace_589298 : CollatzResearch.WordTrace tailWord_589298 prefixEnd_589298 268971664651858313390999 := by
  unfold tailWord_589298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5373365954770366232706137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14328975879387643287216365 5373365954770366232706137)
  ·
    refine ⟨4030024466077774674529603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5373365954770366232706137 4030024466077774674529603)
    ·
      refine ⟨6045036699116662011794405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030024466077774674529603 6045036699116662011794405)
      ·
        refine ⟨1133444381084374127211451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6045036699116662011794405 1133444381084374127211451)
        ·
          refine ⟨1700166571626561190817177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133444381084374127211451 1700166571626561190817177)
          ·
            refine ⟨1275124928719920893112883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1700166571626561190817177 1275124928719920893112883)
            ·
              refine ⟨1912687393079881339669325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275124928719920893112883 1912687393079881339669325)
              ·
                refine ⟨717257772404955502375997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1912687393079881339669325 717257772404955502375997)
                ·
                  refine ⟨268971664651858313390999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717257772404955502375997 268971664651858313390999)
                  ·
                    rfl

theorem cell20_589298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_589298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589298 prefixEnd_589298 := by exact prefixLift 589298
  have htrace : WordTrace (prefixWord ++ tailWord_589298) baseStart_589298 baseEnd_589298 := by
    simpa [prefixWord, tailWord_589298, baseEnd_589298] using wordTrace_append hprefix tailTrace_589298
  have hstable : (prefixWord ++ tailWord_589298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589298).length < 2 ^ (prefixWord ++ tailWord_589298).sum := by decide
  have hdescent : baseEnd_589298 < baseStart_589298 := by decide
  rcases family_descends (prefixWord ++ tailWord_589298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589336 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_589336 : Nat := 118140960795 + 589336 * 2 ^ 59
def prefixEnd_589336 : Nat := 4983230072969 + 3 ^ 40 * 589336 * 2
def baseEnd_589336 : Nat := 268989008887299070124177

theorem tailTrace_589336 : CollatzResearch.WordTrace tailWord_589336 prefixEnd_589336 268989008887299070124177 := by
  unfold tailWord_589336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10747424896471898710353931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14329899861962531613805241 10747424896471898710353931)
  ·
    refine ⟨16121137344707848065530897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10747424896471898710353931 16121137344707848065530897)
    ·
      refine ⟨12090853008530886049148173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16121137344707848065530897 12090853008530886049148173)
      ·
        refine ⟨4534069878199082268430565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12090853008530886049148173 4534069878199082268430565)
        ·
          refine ⟨850138102162327925330731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4534069878199082268430565 850138102162327925330731)
          ·
            refine ⟨1275207153243491887996097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850138102162327925330731 1275207153243491887996097)
            ·
              refine ⟨956405364932618915997073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275207153243491887996097 956405364932618915997073)
              ·
                refine ⟨717304023699464186997805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956405364932618915997073 717304023699464186997805)
                ·
                  refine ⟨268989008887299070124177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717304023699464186997805 268989008887299070124177)
                  ·
                    rfl

theorem cell20_589336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_589336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589336 prefixEnd_589336 := by exact prefixLift 589336
  have htrace : WordTrace (prefixWord ++ tailWord_589336) baseStart_589336 baseEnd_589336 := by
    simpa [prefixWord, tailWord_589336, baseEnd_589336] using wordTrace_append hprefix tailTrace_589336
  have hstable : (prefixWord ++ tailWord_589336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589336).length < 2 ^ (prefixWord ++ tailWord_589336).sum := by decide
  have hdescent : baseEnd_589336 < baseStart_589336 := by decide
  rcases family_descends (prefixWord ++ tailWord_589336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589342 : List Nat := [4, 3, 3, 1, 2, 1, 1, 5]
def baseStart_589342 : Nat := 118140960795 + 589342 * 2 ^ 59
def prefixEnd_589342 : Nat := 4983230072969 + 3 ^ 40 * 589342 * 2
def baseEnd_589342 : Nat := 89663915816929905308051

theorem tailTrace_589342 : CollatzResearch.WordTrace tailWord_589342 prefixEnd_589342 89663915816929905308051 := by
  unfold tailWord_589342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686883578865257555678285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14330045753948040296950853 2686883578865257555678285)
  ·
    refine ⟨1007581342074471583379357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2686883578865257555678285 1007581342074471583379357)
    ·
      refine ⟨377843003277926843767259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1007581342074471583379357 377843003277926843767259)
      ·
        refine ⟨566764504916890265650889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377843003277926843767259 566764504916890265650889)
        ·
          refine ⟨425073378687667699238167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566764504916890265650889 425073378687667699238167)
          ·
            refine ⟨637610068031501548857251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425073378687667699238167 637610068031501548857251)
            ·
              refine ⟨956415102047252323285877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637610068031501548857251 956415102047252323285877)
              ·
                refine ⟨89663915816929905308051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 956415102047252323285877 89663915816929905308051)
                ·
                  rfl

theorem cell20_589342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_589342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589342 prefixEnd_589342 := by exact prefixLift 589342
  have htrace : WordTrace (prefixWord ++ tailWord_589342) baseStart_589342 baseEnd_589342 := by
    simpa [prefixWord, tailWord_589342, baseEnd_589342] using wordTrace_append hprefix tailTrace_589342
  have hstable : (prefixWord ++ tailWord_589342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589342).length < 2 ^ (prefixWord ++ tailWord_589342).sum := by decide
  have hdescent : baseEnd_589342 < baseStart_589342 := by decide
  rcases family_descends (prefixWord ++ tailWord_589342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589381 : List Nat := [1, 3, 1, 1, 1, 4, 4, 3, 2]
def baseStart_589381 : Nat := 118140960795 + 589381 * 2 ^ 59
def prefixEnd_589381 : Nat := 4983230072969 + 3 ^ 40 * 589381 * 2
def baseEnd_589381 : Nat := 269009548113478913623993

theorem tailTrace_589381 : CollatzResearch.WordTrace tailWord_589381 prefixEnd_589381 269009548113478913623993 := by
  unfold tailWord_589381
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496491077780770106095997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14330994051853846737397331 21496491077780770106095997)
  ·
    refine ⟨8061184154167788789785999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21496491077780770106095997 8061184154167788789785999)
    ·
      refine ⟨12091776231251683184678999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8061184154167788789785999 12091776231251683184678999)
      ·
        refine ⟨18137664346877524777018499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12091776231251683184678999 18137664346877524777018499)
        ·
          refine ⟨27206496520316287165527749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18137664346877524777018499 27206496520316287165527749)
          ·
            refine ⟨5101218097559303843536453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27206496520316287165527749 5101218097559303843536453)
            ·
              refine ⟨956478393292369470663085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5101218097559303843536453 956478393292369470663085)
              ·
                refine ⟨358679397484638551498657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 956478393292369470663085 358679397484638551498657)
                ·
                  refine ⟨269009548113478913623993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358679397484638551498657 269009548113478913623993)
                  ·
                    rfl

theorem cell20_589381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_589381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589381 prefixEnd_589381 := by exact prefixLift 589381
  have htrace : WordTrace (prefixWord ++ tailWord_589381) baseStart_589381 baseEnd_589381 := by
    simpa [prefixWord, tailWord_589381, baseEnd_589381] using wordTrace_append hprefix tailTrace_589381
  have hstable : (prefixWord ++ tailWord_589381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589381).length < 2 ^ (prefixWord ++ tailWord_589381).sum := by decide
  have hdescent : baseEnd_589381 < baseStart_589381 := by decide
  rcases family_descends (prefixWord ++ tailWord_589381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589392 : List Nat := [2, 1, 1, 1, 1, 3, 11]
def baseStart_589392 : Nat := 118140960795 + 589392 * 2 ^ 59
def prefixEnd_589392 : Nat := 4983230072969 + 3 ^ 40 * 589392 * 2
def baseEnd_589392 : Nat := 29890507645912418250809

theorem tailTrace_589392 : CollatzResearch.WordTrace tailWord_589392 prefixEnd_589392 29890507645912418250809 := by
  unfold tailWord_589392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10748446140370459492373215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14331261520493945989830953 10748446140370459492373215)
  ·
    refine ⟨16122669210555689238559823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10748446140370459492373215 16122669210555689238559823)
    ·
      refine ⟨24184003815833533857839735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16122669210555689238559823 24184003815833533857839735)
      ·
        refine ⟨36276005723750300786759603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24184003815833533857839735 36276005723750300786759603)
        ·
          refine ⟨54414008585625451180139405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36276005723750300786759603 54414008585625451180139405)
          ·
            refine ⟨20405253219609544192552277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54414008585625451180139405 20405253219609544192552277)
            ·
              refine ⟨29890507645912418250809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20405253219609544192552277 29890507645912418250809)
              ·
                rfl

theorem cell20_589392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 11].length) (baseStart_589392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589392 prefixEnd_589392 := by exact prefixLift 589392
  have htrace : WordTrace (prefixWord ++ tailWord_589392) baseStart_589392 baseEnd_589392 := by
    simpa [prefixWord, tailWord_589392, baseEnd_589392] using wordTrace_append hprefix tailTrace_589392
  have hstable : (prefixWord ++ tailWord_589392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589392).length < 2 ^ (prefixWord ++ tailWord_589392).sum := by decide
  have hdescent : baseEnd_589392 < baseStart_589392 := by decide
  rcases family_descends (prefixWord ++ tailWord_589392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589412 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_589412 : Nat := 118140960795 + 589412 * 2 ^ 59
def prefixEnd_589412 : Nat := 4983230072969 + 3 ^ 40 * 589412 * 2
def baseEnd_589412 : Nat := 269023697358180583590533

theorem tailTrace_589412 : CollatzResearch.WordTrace tailWord_589412 prefixEnd_589412 269023697358180583590533 := by
  unfold tailWord_589412
  simp only [CollatzResearch.WordTrace]
  refine ⟨10748810870334231200237245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14331747827112308266982993 10748810870334231200237245)
  ·
    refine ⟨4030804076375336700088967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10748810870334231200237245 4030804076375336700088967)
    ·
      refine ⟨6046206114563005050133451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030804076375336700088967 6046206114563005050133451)
      ·
        refine ⟨9069309171844507575200177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046206114563005050133451 9069309171844507575200177)
        ·
          refine ⟨6801981878883380681400133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9069309171844507575200177 6801981878883380681400133)
          ·
            refine ⟨1275371602290633877762525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6801981878883380681400133 1275371602290633877762525)
            ·
              refine ⟨478264350858987704160947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275371602290633877762525 478264350858987704160947)
              ·
                refine ⟨717396526288481556241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478264350858987704160947 717396526288481556241421)
                ·
                  refine ⟨269023697358180583590533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717396526288481556241421 269023697358180583590533)
                  ·
                    rfl

theorem cell20_589412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_589412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589412 prefixEnd_589412 := by exact prefixLift 589412
  have htrace : WordTrace (prefixWord ++ tailWord_589412) baseStart_589412 baseEnd_589412 := by
    simpa [prefixWord, tailWord_589412, baseEnd_589412] using wordTrace_append hprefix tailTrace_589412
  have hstable : (prefixWord ++ tailWord_589412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589412).length < 2 ^ (prefixWord ++ tailWord_589412).sum := by decide
  have hdescent : baseEnd_589412 < baseStart_589412 := by decide
  rcases family_descends (prefixWord ++ tailWord_589412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589422 : List Nat := [4, 1, 2, 2, 4, 1, 2, 4]
def baseStart_589422 : Nat := 118140960795 + 589422 * 2 ^ 59
def prefixEnd_589422 : Nat := 4983230072969 + 3 ^ 40 * 589422 * 2
def baseEnd_589422 : Nat := 89676087210221664419053

theorem tailTrace_589422 : CollatzResearch.WordTrace tailWord_589422 prefixEnd_589422 89676087210221664419053 := by
  unfold tailWord_589422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687248308829029263542315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14331990980421489405559013 2687248308829029263542315)
  ·
    refine ⟨4030872463243543895313473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2687248308829029263542315 4030872463243543895313473)
    ·
      refine ⟨3023154347432657921485105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4030872463243543895313473 3023154347432657921485105)
      ·
        refine ⟨2267365760574493441113829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3023154347432657921485105 2267365760574493441113829)
        ·
          refine ⟨425131080107717520208843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2267365760574493441113829 425131080107717520208843)
          ·
            refine ⟨637696620161576280313265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425131080107717520208843 637696620161576280313265)
            ·
              refine ⟨478272465121182210234949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637696620161576280313265 478272465121182210234949)
              ·
                refine ⟨89676087210221664419053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478272465121182210234949 89676087210221664419053)
                ·
                  rfl

theorem cell20_589422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_589422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589422 prefixEnd_589422 := by exact prefixLift 589422
  have htrace : WordTrace (prefixWord ++ tailWord_589422) baseStart_589422 baseEnd_589422 := by
    simpa [prefixWord, tailWord_589422, baseEnd_589422] using wordTrace_append hprefix tailTrace_589422
  have hstable : (prefixWord ++ tailWord_589422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589422).length < 2 ^ (prefixWord ++ tailWord_589422).sum := by decide
  have hdescent : baseEnd_589422 < baseStart_589422 := by decide
  rcases family_descends (prefixWord ++ tailWord_589422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589426 : List Nat := [3, 2, 1, 2, 3, 1, 4, 4]
def baseStart_589426 : Nat := 118140960795 + 589426 * 2 ^ 59
def prefixEnd_589426 : Nat := 4983230072969 + 3 ^ 40 * 589426 * 2
def baseEnd_589426 : Nat := 89676695779886252374603

theorem tailTrace_589426 : CollatzResearch.WordTrace tailWord_589426 prefixEnd_589426 89676695779886252374603 := by
  unfold tailWord_589426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374533090654435697871033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14332088241745161860989421 5374533090654435697871033)
  ·
    refine ⟨4030899817990826773403275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5374533090654435697871033 4030899817990826773403275)
    ·
      refine ⟨6046349726986240160104913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030899817990826773403275 6046349726986240160104913)
      ·
        refine ⟨4534762295239680120078685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6046349726986240160104913 4534762295239680120078685)
        ·
          refine ⟨1700535860714880045029507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4534762295239680120078685 1700535860714880045029507)
          ·
            refine ⟨2550803791072320067544261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700535860714880045029507 2550803791072320067544261)
            ·
              refine ⟨478275710826060012664549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2550803791072320067544261 478275710826060012664549)
              ·
                refine ⟨89676695779886252374603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478275710826060012664549 89676695779886252374603)
                ·
                  rfl

theorem cell20_589426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_589426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589426 prefixEnd_589426 := by exact prefixLift 589426
  have htrace : WordTrace (prefixWord ++ tailWord_589426) baseStart_589426 baseEnd_589426 := by
    simpa [prefixWord, tailWord_589426, baseEnd_589426] using wordTrace_append hprefix tailTrace_589426
  have hstable : (prefixWord ++ tailWord_589426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589426).length < 2 ^ (prefixWord ++ tailWord_589426).sum := by decide
  have hdescent : baseEnd_589426 < baseStart_589426 := by decide
  rcases family_descends (prefixWord ++ tailWord_589426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589447 : List Nat := [1, 1, 4, 2, 1, 5, 6]
def baseStart_589447 : Nat := 118140960795 + 589447 * 2 ^ 59
def prefixEnd_589447 : Nat := 4983230072969 + 3 ^ 40 * 589447 * 2
def baseEnd_589447 : Nat := 29893296923541779713747

theorem tailTrace_589447 : CollatzResearch.WordTrace tailWord_589447 prefixEnd_589447 29893296923541779713747 := by
  unfold tailWord_589447
  simp only [CollatzResearch.WordTrace]
  refine ⟨21498898295541663377998595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14332598863694442251999063 21498898295541663377998595)
  ·
    refine ⟨32248347443312495066997893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21498898295541663377998595 32248347443312495066997893)
    ·
      refine ⟨6046565145621092825062105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32248347443312495066997893 6046565145621092825062105)
      ·
        refine ⟨4534923859215819618796579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6046565145621092825062105 4534923859215819618796579)
        ·
          refine ⟨6802385788823729428194869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534923859215819618796579 6802385788823729428194869)
          ·
            refine ⟨637723667702224633893269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6802385788823729428194869 637723667702224633893269)
            ·
              refine ⟨29893296923541779713747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 637723667702224633893269 29893296923541779713747)
              ·
                rfl

theorem cell20_589447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 6].length) (baseStart_589447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589447 prefixEnd_589447 := by exact prefixLift 589447
  have htrace : WordTrace (prefixWord ++ tailWord_589447) baseStart_589447 baseEnd_589447 := by
    simpa [prefixWord, tailWord_589447, baseEnd_589447] using wordTrace_append hprefix tailTrace_589447
  have hstable : (prefixWord ++ tailWord_589447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589447).length < 2 ^ (prefixWord ++ tailWord_589447).sum := by decide
  have hdescent : baseEnd_589447 < baseStart_589447 := by decide
  rcases family_descends (prefixWord ++ tailWord_589447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589485 : List Nat := [1, 5, 2, 1, 1, 1, 1, 8]
def baseStart_589485 : Nat := 118140960795 + 589485 * 2 ^ 59
def prefixEnd_589485 : Nat := 4983230072969 + 3 ^ 40 * 589485 * 2
def baseEnd_589485 : Nat := 89685672182438924718967

theorem tailTrace_589485 : CollatzResearch.WordTrace tailWord_589485 prefixEnd_589485 89685672182438924718967 := by
  unfold tailWord_589485
  simp only [CollatzResearch.WordTrace]
  refine ⟨21500284269403995867881909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14333522846269330578587939 21500284269403995867881909)
  ·
    refine ⟨2015651650256624612613929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21500284269403995867881909 2015651650256624612613929)
    ·
      refine ⟨1511738737692468459460447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2015651650256624612613929 1511738737692468459460447)
      ·
        refine ⟨2267608106538702689190671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511738737692468459460447 2267608106538702689190671)
        ·
          refine ⟨3401412159808054033786007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267608106538702689190671 3401412159808054033786007)
          ·
            refine ⟨5102118239712081050679011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401412159808054033786007 5102118239712081050679011)
            ·
              refine ⟨7653177359568121576018517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102118239712081050679011 7653177359568121576018517)
              ·
                refine ⟨89685672182438924718967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7653177359568121576018517 89685672182438924718967)
                ·
                  rfl

theorem cell20_589485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_589485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589485 prefixEnd_589485 := by exact prefixLift 589485
  have htrace : WordTrace (prefixWord ++ tailWord_589485) baseStart_589485 baseEnd_589485 := by
    simpa [prefixWord, tailWord_589485, baseEnd_589485] using wordTrace_append hprefix tailTrace_589485
  have hstable : (prefixWord ++ tailWord_589485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589485).length < 2 ^ (prefixWord ++ tailWord_589485).sum := by decide
  have hdescent : baseEnd_589485 < baseStart_589485 := by decide
  rcases family_descends (prefixWord ++ tailWord_589485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589626 : List Nat := [3, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_589626 : Nat := 118140960795 + 589626 * 2 ^ 59
def prefixEnd_589626 : Nat := 4983230072969 + 3 ^ 40 * 589626 * 2
def baseEnd_589626 : Nat := 269121372789346950456325

theorem tailTrace_589626 : CollatzResearch.WordTrace tailWord_589626 prefixEnd_589626 269121372789346950456325 := by
  unfold tailWord_589626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5376356740473294237191183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14336951307928784632509821 5376356740473294237191183)
  ·
    refine ⟨8064535110709941355786775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5376356740473294237191183 8064535110709941355786775)
    ·
      refine ⟨12096802666064912033680163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8064535110709941355786775 12096802666064912033680163)
      ·
        refine ⟨18145203999097368050520245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12096802666064912033680163 18145203999097368050520245)
        ·
          refine ⟨1701112874915378254736273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18145203999097368050520245 1701112874915378254736273)
          ·
            refine ⟨1275834656186533691052205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701112874915378254736273 1275834656186533691052205)
            ·
              refine ⟨478437996069950134144577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275834656186533691052205 478437996069950134144577)
              ·
                refine ⟨358828497052462600608433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 478437996069950134144577 358828497052462600608433)
                ·
                  refine ⟨269121372789346950456325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358828497052462600608433 269121372789346950456325)
                  ·
                    rfl

theorem cell20_589626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_589626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589626 prefixEnd_589626 := by exact prefixLift 589626
  have htrace : WordTrace (prefixWord ++ tailWord_589626) baseStart_589626 baseEnd_589626 := by
    simpa [prefixWord, tailWord_589626, baseEnd_589626] using wordTrace_append hprefix tailTrace_589626
  have hstable : (prefixWord ++ tailWord_589626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589626).length < 2 ^ (prefixWord ++ tailWord_589626).sum := by decide
  have hdescent : baseEnd_589626 < baseStart_589626 := by decide
  rcases family_descends (prefixWord ++ tailWord_589626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589640 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_589640 : Nat := 118140960795 + 589640 * 2 ^ 59
def prefixEnd_589640 : Nat := 4983230072969 + 3 ^ 40 * 589640 * 2
def baseEnd_589640 : Nat := 269127762770825123989601

theorem tailTrace_589640 : CollatzResearch.WordTrace tailWord_589640 prefixEnd_589640 269127762770825123989601 := by
  unfold tailWord_589640
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752968791921228669887187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14337291722561638226516249 10752968791921228669887187)
  ·
    refine ⟨16129453187881843004830781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10752968791921228669887187 16129453187881843004830781)
    ·
      refine ⟨6048544945455691126811543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16129453187881843004830781 6048544945455691126811543)
      ·
        refine ⟨9072817418183536690217315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6048544945455691126811543 9072817418183536690217315)
        ·
          refine ⟨13609226127275305035325973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9072817418183536690217315 13609226127275305035325973)
          ·
            refine ⟨637932474716029923530905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13609226127275305035325973 637932474716029923530905)
            ·
              refine ⟨478449356037022442648179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637932474716029923530905 478449356037022442648179)
              ·
                refine ⟨717674034055533663972269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478449356037022442648179 717674034055533663972269)
                ·
                  refine ⟨269127762770825123989601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717674034055533663972269 269127762770825123989601)
                  ·
                    rfl

theorem cell20_589640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_589640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589640 prefixEnd_589640 := by exact prefixLift 589640
  have htrace : WordTrace (prefixWord ++ tailWord_589640) baseStart_589640 baseEnd_589640 := by
    simpa [prefixWord, tailWord_589640, baseEnd_589640] using wordTrace_append hprefix tailTrace_589640
  have hstable : (prefixWord ++ tailWord_589640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589640).length < 2 ^ (prefixWord ++ tailWord_589640).sum := by decide
  have hdescent : baseEnd_589640 < baseStart_589640 := by decide
  rcases family_descends (prefixWord ++ tailWord_589640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589658 : List Nat := [3, 1, 1, 2, 1, 3, 1, 8]
def baseStart_589658 : Nat := 118140960795 + 589658 * 2 ^ 59
def prefixEnd_589658 : Nat := 4983230072969 + 3 ^ 40 * 589658 * 2
def baseEnd_589658 : Nat := 89711992820432353796509

theorem tailTrace_589658 : CollatzResearch.WordTrace tailWord_589658 prefixEnd_589658 89711992820432353796509 := by
  unfold tailWord_589658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5376648524444311603482407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14337729398518164275953085 5376648524444311603482407)
  ·
    refine ⟨8064972786666467405223611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5376648524444311603482407 8064972786666467405223611)
    ·
      refine ⟨12097459179999701107835417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8064972786666467405223611 12097459179999701107835417)
      ·
        refine ⟨9073094384999775830876563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12097459179999701107835417 9073094384999775830876563)
        ·
          refine ⟨13609641577499663746314845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9073094384999775830876563 13609641577499663746314845)
          ·
            refine ⟨5103615591562373904868067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13609641577499663746314845 5103615591562373904868067)
            ·
              refine ⟨7655423387343560857302101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103615591562373904868067 7655423387343560857302101)
              ·
                refine ⟨89711992820432353796509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7655423387343560857302101 89711992820432353796509)
                ·
                  rfl

theorem cell20_589658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_589658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589658 prefixEnd_589658 := by exact prefixLift 589658
  have htrace : WordTrace (prefixWord ++ tailWord_589658) baseStart_589658 baseEnd_589658 := by
    simpa [prefixWord, tailWord_589658, baseEnd_589658] using wordTrace_append hprefix tailTrace_589658
  have hstable : (prefixWord ++ tailWord_589658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589658).length < 2 ^ (prefixWord ++ tailWord_589658).sum := by decide
  have hdescent : baseEnd_589658 < baseStart_589658 := by decide
  rcases family_descends (prefixWord ++ tailWord_589658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589678 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_589678 : Nat := 118140960795 + 589678 * 2 ^ 59
def prefixEnd_589678 : Nat := 4983230072969 + 3 ^ 40 * 589678 * 2
def baseEnd_589678 : Nat := 269145107006265880722779

theorem tailTrace_589678 : CollatzResearch.WordTrace tailWord_589678 prefixEnd_589678 269145107006265880722779 := by
  unfold tailWord_589678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688415444713098728707211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14338215705136526553105125 2688415444713098728707211)
  ·
    refine ⟨4032623167069648093060817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2688415444713098728707211 4032623167069648093060817)
    ·
      refine ⟨3024467375302236069795613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4032623167069648093060817 3024467375302236069795613)
      ·
        refine ⟨1134175265738338526173355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3024467375302236069795613 1134175265738338526173355)
        ·
          refine ⟨1701262898607507789260033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134175265738338526173355 1701262898607507789260033)
          ·
            refine ⟨1275947173955630841945025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701262898607507789260033 1275947173955630841945025)
            ·
              refine ⟨956960380466723131458769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275947173955630841945025 956960380466723131458769)
              ·
                refine ⟨717720285350042348594077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956960380466723131458769 717720285350042348594077)
                ·
                  refine ⟨269145107006265880722779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717720285350042348594077 269145107006265880722779)
                  ·
                    rfl

theorem cell20_589678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_589678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589678 prefixEnd_589678 := by exact prefixLift 589678
  have htrace : WordTrace (prefixWord ++ tailWord_589678) baseStart_589678 baseEnd_589678 := by
    simpa [prefixWord, tailWord_589678, baseEnd_589678] using wordTrace_append hprefix tailTrace_589678
  have hstable : (prefixWord ++ tailWord_589678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589678).length < 2 ^ (prefixWord ++ tailWord_589678).sum := by decide
  have hdescent : baseEnd_589678 < baseStart_589678 := by decide
  rcases family_descends (prefixWord ++ tailWord_589678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589685 : List Nat := [1, 3, 4, 1, 1, 1, 3, 4, 2]
def baseStart_589685 : Nat := 118140960795 + 589685 * 2 ^ 59
def prefixEnd_589685 : Nat := 4983230072969 + 3 ^ 40 * 589685 * 2
def baseEnd_589685 : Nat := 269148301997004967489417

theorem tailTrace_589685 : CollatzResearch.WordTrace tailWord_589685 prefixEnd_589685 269148301997004967489417 := by
  unfold tailWord_589685
  simp only [CollatzResearch.WordTrace]
  refine ⟨21507578868679430025162509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14338385912452953350108339 21507578868679430025162509)
  ·
    refine ⟨8065342075754786259435941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21507578868679430025162509 8065342075754786259435941)
    ·
      refine ⟨1512251639204022423644239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8065342075754786259435941 1512251639204022423644239)
      ·
        refine ⟨2268377458806033635466359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512251639204022423644239 2268377458806033635466359)
        ·
          refine ⟨3402566188209050453199539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2268377458806033635466359 3402566188209050453199539)
          ·
            refine ⟨5103849282313575679799309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3402566188209050453199539 5103849282313575679799309)
            ·
              refine ⟨1913943480867590879924741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5103849282313575679799309 1913943480867590879924741)
              ·
                refine ⟨358864402662673289985889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1913943480867590879924741 358864402662673289985889)
                ·
                  refine ⟨269148301997004967489417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358864402662673289985889 269148301997004967489417)
                  ·
                    rfl

theorem cell20_589685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_589685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589685 prefixEnd_589685 := by exact prefixLift 589685
  have htrace : WordTrace (prefixWord ++ tailWord_589685) baseStart_589685 baseEnd_589685 := by
    simpa [prefixWord, tailWord_589685, baseEnd_589685] using wordTrace_append hprefix tailTrace_589685
  have hstable : (prefixWord ++ tailWord_589685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589685).length < 2 ^ (prefixWord ++ tailWord_589685).sum := by decide
  have hdescent : baseEnd_589685 < baseStart_589685 := by decide
  rcases family_descends (prefixWord ++ tailWord_589685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589689 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_589689 : Nat := 118140960795 + 589689 * 2 ^ 59
def prefixEnd_589689 : Nat := 4983230072969 + 3 ^ 40 * 589689 * 2
def baseEnd_589689 : Nat := 269150127705998731356067

theorem tailTrace_589689 : CollatzResearch.WordTrace tailWord_589689 prefixEnd_589689 269150127705998731356067 := by
  unfold tailWord_589689
  simp only [CollatzResearch.WordTrace]
  refine ⟨21507724760664938708308121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14338483173776625805538747 21507724760664938708308121)
  ·
    refine ⟨16130793570498704031231091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21507724760664938708308121 16130793570498704031231091)
    ·
      refine ⟨24196190355748056046846637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16130793570498704031231091 24196190355748056046846637)
      ·
        refine ⟨9073571383405521017567489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24196190355748056046846637 9073571383405521017567489)
        ·
          refine ⟨6805178537554140763175617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9073571383405521017567489 6805178537554140763175617)
          ·
            refine ⟨5103883903165605572381713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6805178537554140763175617 5103883903165605572381713)
            ·
              refine ⟨3827912927374204179286285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5103883903165605572381713 3827912927374204179286285)
              ·
                refine ⟨1435467347765326567232357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3827912927374204179286285 1435467347765326567232357)
                ·
                  refine ⟨269150127705998731356067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435467347765326567232357 269150127705998731356067)
                  ·
                    rfl

theorem cell20_589689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_589689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589689 prefixEnd_589689 := by exact prefixLift 589689
  have htrace : WordTrace (prefixWord ++ tailWord_589689) baseStart_589689 baseEnd_589689 := by
    simpa [prefixWord, tailWord_589689, baseEnd_589689] using wordTrace_append hprefix tailTrace_589689
  have hstable : (prefixWord ++ tailWord_589689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589689).length < 2 ^ (prefixWord ++ tailWord_589689).sum := by decide
  have hdescent : baseEnd_589689 < baseStart_589689 := by decide
  rcases family_descends (prefixWord ++ tailWord_589689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589768 : List Nat := [2, 1, 3, 1, 4, 3, 2, 4]
def baseStart_589768 : Nat := 118140960795 + 589768 * 2 ^ 59
def prefixEnd_589768 : Nat := 4983230072969 + 3 ^ 40 * 589768 * 2
def baseEnd_589768 : Nat := 89728728486208522574137

theorem tailTrace_589768 : CollatzResearch.WordTrace tailWord_589768 prefixEnd_589768 89728728486208522574137 := by
  unfold tailWord_589768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10755303063689367600216979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14340404084919156800289305 10755303063689367600216979)
  ·
    refine ⟨16132954595534051400325469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10755303063689367600216979 16132954595534051400325469)
    ·
      refine ⟨6049857973325269275122051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16132954595534051400325469 6049857973325269275122051)
      ·
        refine ⟨9074786959987903912683077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049857973325269275122051 9074786959987903912683077)
        ·
          refine ⟨1701522554997731983628077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9074786959987903912683077 1701522554997731983628077)
          ·
            refine ⟨638070958124149493860529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1701522554997731983628077 638070958124149493860529)
            ·
              refine ⟨478553218593112120395397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638070958124149493860529 478553218593112120395397)
              ·
                refine ⟨89728728486208522574137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478553218593112120395397 89728728486208522574137)
                ·
                  rfl

theorem cell20_589768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_589768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589768 prefixEnd_589768 := by exact prefixLift 589768
  have htrace : WordTrace (prefixWord ++ tailWord_589768) baseStart_589768 baseEnd_589768 := by
    simpa [prefixWord, tailWord_589768, baseEnd_589768] using wordTrace_append hprefix tailTrace_589768
  have hstable : (prefixWord ++ tailWord_589768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589768).length < 2 ^ (prefixWord ++ tailWord_589768).sum := by decide
  have hdescent : baseEnd_589768 < baseStart_589768 := by decide
  rcases family_descends (prefixWord ++ tailWord_589768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589796 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_589796 : Nat := 118140960795 + 589796 * 2 ^ 59
def prefixEnd_589796 : Nat := 4983230072969 + 3 ^ 40 * 589796 * 2
def baseEnd_589796 : Nat := 269198965421581914788963

theorem tailTrace_589796 : CollatzResearch.WordTrace tailWord_589796 prefixEnd_589796 269198965421581914788963 := by
  unfold tailWord_589796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10755813685638647991226621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14341084914184863988302161 10755813685638647991226621)
  ·
    refine ⟨4033430132114492996709983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10755813685638647991226621 4033430132114492996709983)
    ·
      refine ⟨6050145198171739495064975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033430132114492996709983 6050145198171739495064975)
      ·
        refine ⟨9075217797257609242597463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050145198171739495064975 9075217797257609242597463)
        ·
          refine ⟨13612826695886413863896195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075217797257609242597463 13612826695886413863896195)
          ·
            refine ⟨20419240043829620795844293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13612826695886413863896195 20419240043829620795844293)
            ·
              refine ⟨3828607508218053899220805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20419240043829620795844293 3828607508218053899220805)
              ·
                refine ⟨717863907790885106103901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3828607508218053899220805 717863907790885106103901)
                ·
                  refine ⟨269198965421581914788963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717863907790885106103901 269198965421581914788963)
                  ·
                    rfl

theorem cell20_589796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_589796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589796 prefixEnd_589796 := by exact prefixLift 589796
  have htrace : WordTrace (prefixWord ++ tailWord_589796) baseStart_589796 baseEnd_589796 := by
    simpa [prefixWord, tailWord_589796, baseEnd_589796] using wordTrace_append hprefix tailTrace_589796
  have hstable : (prefixWord ++ tailWord_589796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589796).length < 2 ^ (prefixWord ++ tailWord_589796).sum := by decide
  have hdescent : baseEnd_589796 < baseStart_589796 := by decide
  rcases family_descends (prefixWord ++ tailWord_589796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589799 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 4]
def baseStart_589799 : Nat := 118140960795 + 589799 * 2 ^ 59
def prefixEnd_589799 : Nat := 4983230072969 + 3 ^ 40 * 589799 * 2
def baseEnd_589799 : Nat := 269200334703327237688951

theorem tailTrace_589799 : CollatzResearch.WordTrace tailWord_589799 prefixEnd_589799 269200334703327237688951 := by
  unfold tailWord_589799
  simp only [CollatzResearch.WordTrace]
  refine ⟨21511736790266427494812451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14341157860177618329874967 21511736790266427494812451)
  ·
    refine ⟨32267605185399641242218677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21511736790266427494812451 32267605185399641242218677)
    ·
      refine ⟨3025087986131216366458001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32267605185399641242218677 3025087986131216366458001)
      ·
        refine ⟨2268815989598412274843501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3025087986131216366458001 2268815989598412274843501)
        ·
          refine ⟨850805996099404603066313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2268815989598412274843501 850805996099404603066313)
          ·
            refine ⟨638104497074553452299735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850805996099404603066313 638104497074553452299735)
            ·
              refine ⟨957156745611830178449603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638104497074553452299735 957156745611830178449603)
              ·
                refine ⟨1435735118417745267674405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957156745611830178449603 1435735118417745267674405)
                ·
                  refine ⟨269200334703327237688951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435735118417745267674405 269200334703327237688951)
                  ·
                    rfl

theorem cell20_589799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_589799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589799 prefixEnd_589799 := by exact prefixLift 589799
  have htrace : WordTrace (prefixWord ++ tailWord_589799) baseStart_589799 baseEnd_589799 := by
    simpa [prefixWord, tailWord_589799, baseEnd_589799] using wordTrace_append hprefix tailTrace_589799
  have hstable : (prefixWord ++ tailWord_589799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589799).length < 2 ^ (prefixWord ++ tailWord_589799).sum := by decide
  have hdescent : baseEnd_589799 < baseStart_589799 := by decide
  rcases family_descends (prefixWord ++ tailWord_589799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589809 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 3]
def baseStart_589809 : Nat := 118140960795 + 589809 * 2 ^ 59
def prefixEnd_589809 : Nat := 4983230072969 + 3 ^ 40 * 589809 * 2
def baseEnd_589809 : Nat := 269204898975811647355577

theorem tailTrace_589809 : CollatzResearch.WordTrace tailWord_589809 prefixEnd_589809 269204898975811647355577 := by
  unfold tailWord_589809
  simp only [CollatzResearch.WordTrace]
  refine ⟨21512101520230199202676481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14341401013486799468450987 21512101520230199202676481)
  ·
    refine ⟨16134076140172649402007361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21512101520230199202676481 16134076140172649402007361)
    ·
      refine ⟨12100557105129487051505521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16134076140172649402007361 12100557105129487051505521)
      ·
        refine ⟨9075417828847115288629141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12100557105129487051505521 9075417828847115288629141)
        ·
          refine ⟨425410210727208529154491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9075417828847115288629141 425410210727208529154491)
          ·
            refine ⟨638115316090812793731737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425410210727208529154491 638115316090812793731737)
            ·
              refine ⟨478586487068109595298803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638115316090812793731737 478586487068109595298803)
              ·
                refine ⟨717879730602164392948205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478586487068109595298803 717879730602164392948205)
                ·
                  refine ⟨269204898975811647355577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717879730602164392948205 269204898975811647355577)
                  ·
                    rfl

theorem cell20_589809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_589809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589809 prefixEnd_589809 := by exact prefixLift 589809
  have htrace : WordTrace (prefixWord ++ tailWord_589809) baseStart_589809 baseEnd_589809 := by
    simpa [prefixWord, tailWord_589809, baseEnd_589809] using wordTrace_append hprefix tailTrace_589809
  have hstable : (prefixWord ++ tailWord_589809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589809).length < 2 ^ (prefixWord ++ tailWord_589809).sum := by decide
  have hdescent : baseEnd_589809 < baseStart_589809 := by decide
  rcases family_descends (prefixWord ++ tailWord_589809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589844 : List Nat := [2, 4, 3, 2, 1, 8]
def baseStart_589844 : Nat := 118140960795 + 589844 * 2 ^ 59
def prefixEnd_589844 : Nat := 4983230072969 + 3 ^ 40 * 589844 * 2
def baseEnd_589844 : Nat := 9971143478870632636621

theorem tailTrace_589844 : CollatzResearch.WordTrace tailWord_589844 prefixEnd_589844 9971143478870632636621 := by
  unfold tailWord_589844
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756689037551700090100293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14342252050068933453467057 10756689037551700090100293)
  ·
    refine ⟨2016879194540943766893805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10756689037551700090100293 2016879194540943766893805)
    ·
      refine ⟨756329697952853912585177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2016879194540943766893805 756329697952853912585177)
      ·
        refine ⟨567247273464640434438883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756329697952853912585177 567247273464640434438883)
        ·
          refine ⟨850870910196960651658325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567247273464640434438883 850870910196960651658325)
          ·
            refine ⟨9971143478870632636621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 850870910196960651658325 9971143478870632636621)
            ·
              rfl

theorem cell20_589844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 8].length) (baseStart_589844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589844 prefixEnd_589844 := by exact prefixLift 589844
  have htrace : WordTrace (prefixWord ++ tailWord_589844) baseStart_589844 baseEnd_589844 := by
    simpa [prefixWord, tailWord_589844, baseEnd_589844] using wordTrace_append hprefix tailTrace_589844
  have hstable : (prefixWord ++ tailWord_589844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589844).length < 2 ^ (prefixWord ++ tailWord_589844).sum := by decide
  have hdescent : baseEnd_589844 < baseStart_589844 := by decide
  rcases family_descends (prefixWord ++ tailWord_589844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589872 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_589872 : Nat := 118140960795 + 589872 * 2 ^ 59
def prefixEnd_589872 : Nat := 4983230072969 + 3 ^ 40 * 589872 * 2
def baseEnd_589872 : Nat := 269233653892463428255319

theorem tailTrace_589872 : CollatzResearch.WordTrace tailWord_589872 prefixEnd_589872 269233653892463428255319 := by
  unfold tailWord_589872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757199659500980481109935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14342932879334640641479913 10757199659500980481109935)
  ·
    refine ⟨16135799489251470721664903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10757199659500980481109935 16135799489251470721664903)
    ·
      refine ⟨24203699233877206082497355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16135799489251470721664903 24203699233877206082497355)
      ·
        refine ⟨36305548850815809123746033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24203699233877206082497355 36305548850815809123746033)
        ·
          refine ⟨27229161638111856842809525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36305548850815809123746033 27229161638111856842809525)
          ·
            refine ⟨2552733903572986579013393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27229161638111856842809525 2552733903572986579013393)
            ·
              refine ⟨1914550427679739934260045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552733903572986579013393 1914550427679739934260045)
              ·
                refine ⟨717956410379902475347517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914550427679739934260045 717956410379902475347517)
                ·
                  refine ⟨269233653892463428255319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717956410379902475347517 269233653892463428255319)
                  ·
                    rfl

theorem cell20_589872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_589872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589872 prefixEnd_589872 := by exact prefixLift 589872
  have htrace : WordTrace (prefixWord ++ tailWord_589872) baseStart_589872 baseEnd_589872 := by
    simpa [prefixWord, tailWord_589872, baseEnd_589872] using wordTrace_append hprefix tailTrace_589872
  have hstable : (prefixWord ++ tailWord_589872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589872).length < 2 ^ (prefixWord ++ tailWord_589872).sum := by decide
  have hdescent : baseEnd_589872 < baseStart_589872 := by decide
  rcases family_descends (prefixWord ++ tailWord_589872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589893 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_589893 : Nat := 118140960795 + 589893 * 2 ^ 59
def prefixEnd_589893 : Nat := 4983230072969 + 3 ^ 40 * 589893 * 2
def baseEnd_589893 : Nat := 269243238864680688555233

theorem tailTrace_589893 : CollatzResearch.WordTrace tailWord_589893 prefixEnd_589893 269243238864680688555233 := by
  unfold tailWord_589893
  simp only [CollatzResearch.WordTrace]
  refine ⟨21515165251925881548734333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14343443501283921032489555 21515165251925881548734333)
  ·
    refine ⟨8068186969472205580775375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21515165251925881548734333 8068186969472205580775375)
    ·
      refine ⟨12102280454208308371163063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068186969472205580775375 12102280454208308371163063)
      ·
        refine ⟨18153420681312462556744595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12102280454208308371163063 18153420681312462556744595)
        ·
          refine ⟨27230131021968693835116893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18153420681312462556744595 27230131021968693835116893)
          ·
            refine ⟨10211299133238260188168835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27230131021968693835116893 10211299133238260188168835)
            ·
              refine ⟨15316948699857390282253253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10211299133238260188168835 15316948699857390282253253)
              ·
                refine ⟨2871927881223260677922485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15316948699857390282253253 2871927881223260677922485)
                ·
                  refine ⟨269243238864680688555233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2871927881223260677922485 269243238864680688555233)
                  ·
                    rfl

theorem cell20_589893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_589893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589893 prefixEnd_589893 := by exact prefixLift 589893
  have htrace : WordTrace (prefixWord ++ tailWord_589893) baseStart_589893 baseEnd_589893 := by
    simpa [prefixWord, tailWord_589893, baseEnd_589893] using wordTrace_append hprefix tailTrace_589893
  have hstable : (prefixWord ++ tailWord_589893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589893).length < 2 ^ (prefixWord ++ tailWord_589893).sum := by decide
  have hdescent : baseEnd_589893 < baseStart_589893 := by decide
  rcases family_descends (prefixWord ++ tailWord_589893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589906 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_589906 : Nat := 118140960795 + 589906 * 2 ^ 59
def prefixEnd_589906 : Nat := 4983230072969 + 3 ^ 40 * 589906 * 2
def baseEnd_589906 : Nat := 269249172418910421121847

theorem tailTrace_589906 : CollatzResearch.WordTrace tailWord_589906 prefixEnd_589906 269249172418910421121847 := by
  unfold tailWord_589906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378909850219696192239393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14343759600585856512638381 5378909850219696192239393)
  ·
    refine ⟨4034182387664772144179545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5378909850219696192239393 4034182387664772144179545)
    ·
      refine ⟨3025636790748579108134659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4034182387664772144179545 3025636790748579108134659)
      ·
        refine ⟨4538455186122868662201989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3025636790748579108134659 4538455186122868662201989)
        ·
          refine ⟨850960347398037874162873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4538455186122868662201989 850960347398037874162873)
          ·
            refine ⟨638220260548528405622155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850960347398037874162873 638220260548528405622155)
            ·
              refine ⟨957330390822792608433233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638220260548528405622155 957330390822792608433233)
              ·
                refine ⟨717997793117094456324925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957330390822792608433233 717997793117094456324925)
                ·
                  refine ⟨269249172418910421121847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717997793117094456324925 269249172418910421121847)
                  ·
                    rfl

theorem cell20_589906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_589906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589906 prefixEnd_589906 := by exact prefixLift 589906
  have htrace : WordTrace (prefixWord ++ tailWord_589906) baseStart_589906 baseEnd_589906 := by
    simpa [prefixWord, tailWord_589906, baseEnd_589906] using wordTrace_append hprefix tailTrace_589906
  have hstable : (prefixWord ++ tailWord_589906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589906).length < 2 ^ (prefixWord ++ tailWord_589906).sum := by decide
  have hdescent : baseEnd_589906 < baseStart_589906 := by decide
  rcases family_descends (prefixWord ++ tailWord_589906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589927 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 3]
def baseStart_589927 : Nat := 118140960795 + 589927 * 2 ^ 59
def prefixEnd_589927 : Nat := 4983230072969 + 3 ^ 40 * 589927 * 2
def baseEnd_589927 : Nat := 269258757391127681421761

theorem tailTrace_589927 : CollatzResearch.WordTrace tailWord_589927 prefixEnd_589927 269258757391127681421761 := by
  unfold tailWord_589927
  simp only [CollatzResearch.WordTrace]
  refine ⟨21516405333802705355472035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14344270222535136903648023 21516405333802705355472035)
  ·
    refine ⟨32274608000704058033208053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21516405333802705355472035 32274608000704058033208053)
    ·
      refine ⟨3025744500066005440613255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32274608000704058033208053 3025744500066005440613255)
      ·
        refine ⟨4538616750099008160919883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3025744500066005440613255 4538616750099008160919883)
        ·
          refine ⟨6807925125148512241379825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538616750099008160919883 6807925125148512241379825)
          ·
            refine ⟨5105943843861384181034869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6807925125148512241379825 5105943843861384181034869)
            ·
              refine ⟨478682235362004766972019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5105943843861384181034869 478682235362004766972019)
              ·
                refine ⟨718023353043007150458029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478682235362004766972019 718023353043007150458029)
                ·
                  refine ⟨269258757391127681421761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718023353043007150458029 269258757391127681421761)
                  ·
                    rfl

theorem cell20_589927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 3].length) (baseStart_589927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589927 prefixEnd_589927 := by exact prefixLift 589927
  have htrace : WordTrace (prefixWord ++ tailWord_589927) baseStart_589927 baseEnd_589927 := by
    simpa [prefixWord, tailWord_589927, baseEnd_589927] using wordTrace_append hprefix tailTrace_589927
  have hstable : (prefixWord ++ tailWord_589927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589927).length < 2 ^ (prefixWord ++ tailWord_589927).sum := by decide
  have hdescent : baseEnd_589927 < baseStart_589927 := by decide
  rcases family_descends (prefixWord ++ tailWord_589927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589962 : List Nat := [3, 1, 2, 3, 1, 2, 8]
def baseStart_589962 : Nat := 118140960795 + 589962 * 2 ^ 59
def prefixEnd_589962 : Nat := 4983230072969 + 3 ^ 40 * 589962 * 2
def baseEnd_589962 : Nat := 29919414704980346139439

theorem tailTrace_589962 : CollatzResearch.WordTrace tailWord_589962 prefixEnd_589962 29919414704980346139439 := by
  unfold tailWord_589962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379420472168976583249035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14345121259117270888664093 5379420472168976583249035)
  ·
    refine ⟨8069130708253464874873553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5379420472168976583249035 8069130708253464874873553)
    ·
      refine ⟨6051848031190098656155165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8069130708253464874873553 6051848031190098656155165)
      ·
        refine ⟨2269443011696286996058187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6051848031190098656155165 2269443011696286996058187)
        ·
          refine ⟨3404164517544430494087281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269443011696286996058187 3404164517544430494087281)
          ·
            refine ⟨2553123388158322870565461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3404164517544430494087281 2553123388158322870565461)
            ·
              refine ⟨29919414704980346139439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2553123388158322870565461 29919414704980346139439)
              ·
                rfl

theorem cell20_589962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 8].length) (baseStart_589962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589962 prefixEnd_589962 := by exact prefixLift 589962
  have htrace : WordTrace (prefixWord ++ tailWord_589962) baseStart_589962 baseEnd_589962 := by
    simpa [prefixWord, tailWord_589962, baseEnd_589962] using wordTrace_append hprefix tailTrace_589962
  have hstable : (prefixWord ++ tailWord_589962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589962).length < 2 ^ (prefixWord ++ tailWord_589962).sum := by decide
  have hdescent : baseEnd_589962 < baseStart_589962 := by decide
  rcases family_descends (prefixWord ++ tailWord_589962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589974 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_589974 : Nat := 118140960795 + 589974 * 2 ^ 59
def prefixEnd_589974 : Nat := 4983230072969 + 3 ^ 40 * 589974 * 2
def baseEnd_589974 : Nat := 269280209471804406854903

theorem tailTrace_589974 : CollatzResearch.WordTrace tailWord_589974 prefixEnd_589974 269280209471804406854903 := by
  unfold tailWord_589974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344882472789527023902061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14345413043088288254955317 1344882472789527023902061)
  ·
    refine ⟨504330927296072633963273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1344882472789527023902061 504330927296072633963273)
    ·
      refine ⟨378248195472054475472455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 504330927296072633963273 378248195472054475472455)
      ·
        refine ⟨567372293208081713208683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378248195472054475472455 567372293208081713208683)
        ·
          refine ⟨851058439812122569813025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567372293208081713208683 851058439812122569813025)
          ·
            refine ⟨638293829859091927359769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 851058439812122569813025 638293829859091927359769)
            ·
              refine ⟨478720372394318945519827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638293829859091927359769 478720372394318945519827)
              ·
                refine ⟨718080558591478418279741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478720372394318945519827 718080558591478418279741)
                ·
                  refine ⟨269280209471804406854903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718080558591478418279741 269280209471804406854903)
                  ·
                    rfl

theorem cell20_589974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_589974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589974 prefixEnd_589974 := by exact prefixLift 589974
  have htrace : WordTrace (prefixWord ++ tailWord_589974) baseStart_589974 baseEnd_589974 := by
    simpa [prefixWord, tailWord_589974, baseEnd_589974] using wordTrace_append hprefix tailTrace_589974
  have hstable : (prefixWord ++ tailWord_589974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589974).length < 2 ^ (prefixWord ++ tailWord_589974).sum := by decide
  have hdescent : baseEnd_589974 < baseStart_589974 := by decide
  rcases family_descends (prefixWord ++ tailWord_589974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_589982 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_589982 : Nat := 118140960795 + 589982 * 2 ^ 59
def prefixEnd_589982 : Nat := 4983230072969 + 3 ^ 40 * 589982 * 2
def baseEnd_589982 : Nat := 269283860889791934588203

theorem tailTrace_589982 : CollatzResearch.WordTrace tailWord_589982 prefixEnd_589982 269283860889791934588203 := by
  unfold tailWord_589982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689801418575431218590525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14345607565735633165816133 2689801418575431218590525)
  ·
    refine ⟨1008675531965786706971447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2689801418575431218590525 1008675531965786706971447)
    ·
      refine ⟨1513013297948680060457171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1008675531965786706971447 1513013297948680060457171)
      ·
        refine ⟨2269519946923020090685757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513013297948680060457171 2269519946923020090685757)
        ·
          refine ⟨851069980096132534007159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2269519946923020090685757 851069980096132534007159)
          ·
            refine ⟨1276604970144198801010739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851069980096132534007159 1276604970144198801010739)
            ·
              refine ⟨1914907455216298201516109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276604970144198801010739 1914907455216298201516109)
              ·
                refine ⟨718090295706111825568541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914907455216298201516109 718090295706111825568541)
                ·
                  refine ⟨269283860889791934588203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718090295706111825568541 269283860889791934588203)
                  ·
                    rfl

theorem cell20_589982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_589982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_589982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_589982 prefixEnd_589982 := by exact prefixLift 589982
  have htrace : WordTrace (prefixWord ++ tailWord_589982) baseStart_589982 baseEnd_589982 := by
    simpa [prefixWord, tailWord_589982, baseEnd_589982] using wordTrace_append hprefix tailTrace_589982
  have hstable : (prefixWord ++ tailWord_589982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_589982).length < 2 ^ (prefixWord ++ tailWord_589982).sum := by decide
  have hdescent : baseEnd_589982 < baseStart_589982 := by decide
  rcases family_descends (prefixWord ++ tailWord_589982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590017 : List Nat := [1, 2, 6, 1, 2, 8]
def baseStart_590017 : Nat := 118140960795 + 590017 * 2 ^ 59
def prefixEnd_590017 : Nat := 4983230072969 + 3 ^ 40 * 590017 * 2
def baseEnd_590017 : Nat := 9974067994203235867459

theorem tailTrace_590017 : CollatzResearch.WordTrace tailWord_590017 prefixEnd_590017 9974067994203235867459 := by
  unfold tailWord_590017
  simp only [CollatzResearch.WordTrace]
  refine ⟨21519687903476650726248305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14346458602317767150832203 21519687903476650726248305)
  ·
    refine ⟨16139765927607488044686229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21519687903476650726248305 16139765927607488044686229)
    ·
      refine ⟨756551527856601002094667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16139765927607488044686229 756551527856601002094667)
      ·
        refine ⟨1134827291784901503142001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756551527856601002094667 1134827291784901503142001)
        ·
          refine ⟨851120468838676127356501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1134827291784901503142001 851120468838676127356501)
          ·
            refine ⟨9974067994203235867459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 851120468838676127356501 9974067994203235867459)
            ·
              rfl

theorem cell20_590017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 8].length) (baseStart_590017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590017 prefixEnd_590017 := by exact prefixLift 590017
  have htrace : WordTrace (prefixWord ++ tailWord_590017) baseStart_590017 baseEnd_590017 := by
    simpa [prefixWord, tailWord_590017, baseEnd_590017] using wordTrace_append hprefix tailTrace_590017
  have hstable : (prefixWord ++ tailWord_590017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590017).length < 2 ^ (prefixWord ++ tailWord_590017).sum := by decide
  have hdescent : baseEnd_590017 < baseStart_590017 := by decide
  rcases family_descends (prefixWord ++ tailWord_590017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590076 : List Nat := [2, 2, 2, 1, 4, 2, 7]
def baseStart_590076 : Nat := 118140960795 + 590076 * 2 ^ 59
def prefixEnd_590076 : Nat := 4983230072969 + 3 ^ 40 * 590076 * 2
def baseEnd_590076 : Nat := 29925196116793931717165

theorem tailTrace_590076 : CollatzResearch.WordTrace tailWord_590076 prefixEnd_590076 29925196116793931717165 := by
  unfold tailWord_590076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10760919905131451901323041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14347893206841935868430721 10760919905131451901323041)
  ·
    refine ⟨8070689928848588925992281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10760919905131451901323041 8070689928848588925992281)
    ·
      refine ⟨6053017446636441694494211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8070689928848588925992281 6053017446636441694494211)
      ·
        refine ⟨9079526169954662541741317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6053017446636441694494211 9079526169954662541741317)
        ·
          refine ⟨1702411156866499226576497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9079526169954662541741317 1702411156866499226576497)
          ·
            refine ⟨1276808367649874419932373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702411156866499226576497 1276808367649874419932373)
            ·
              refine ⟨29925196116793931717165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1276808367649874419932373 29925196116793931717165)
              ·
                rfl

theorem cell20_590076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 7].length) (baseStart_590076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590076 prefixEnd_590076 := by exact prefixLift 590076
  have htrace : WordTrace (prefixWord ++ tailWord_590076) baseStart_590076 baseEnd_590076 := by
    simpa [prefixWord, tailWord_590076, baseEnd_590076] using wordTrace_append hprefix tailTrace_590076
  have hstable : (prefixWord ++ tailWord_590076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590076).length < 2 ^ (prefixWord ++ tailWord_590076).sum := by decide
  have hdescent : baseEnd_590076 < baseStart_590076 := by decide
  rcases family_descends (prefixWord ++ tailWord_590076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590083 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_590083 : Nat := 118140960795 + 590083 * 2 ^ 59
def prefixEnd_590083 : Nat := 4983230072969 + 3 ^ 40 * 590083 * 2
def baseEnd_590083 : Nat := 269329960041884472221123

theorem tailTrace_590083 : CollatzResearch.WordTrace tailWord_590083 prefixEnd_590083 269329960041884472221123 := by
  unfold tailWord_590083
  simp only [CollatzResearch.WordTrace]
  refine ⟨21522095121237543998150903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14348063414158362665433935 21522095121237543998150903)
  ·
    refine ⟨32283142681856315997226355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21522095121237543998150903 32283142681856315997226355)
    ·
      refine ⟨48424714022784473995839533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32283142681856315997226355 48424714022784473995839533)
      ·
        refine ⟨18159267758544177748439825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48424714022784473995839533 18159267758544177748439825)
        ·
          refine ⟨13619450818908133311329869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18159267758544177748439825 13619450818908133311329869)
          ·
            refine ⟨5107294057090549991748701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13619450818908133311329869 5107294057090549991748701)
            ·
              refine ⟨1915235271408956246905763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5107294057090549991748701 1915235271408956246905763)
              ·
                refine ⟨2872852907113434370358645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915235271408956246905763 2872852907113434370358645)
                ·
                  refine ⟨269329960041884472221123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2872852907113434370358645 269329960041884472221123)
                  ·
                    rfl

theorem cell20_590083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_590083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590083 prefixEnd_590083 := by exact prefixLift 590083
  have htrace : WordTrace (prefixWord ++ tailWord_590083) baseStart_590083 baseEnd_590083 := by
    simpa [prefixWord, tailWord_590083, baseEnd_590083] using wordTrace_append hprefix tailTrace_590083
  have hstable : (prefixWord ++ tailWord_590083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590083).length < 2 ^ (prefixWord ++ tailWord_590083).sum := by decide
  have hdescent : baseEnd_590083 < baseStart_590083 := by decide
  rcases family_descends (prefixWord ++ tailWord_590083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590110 : List Nat := [4, 3, 2, 1, 1, 2, 1, 6]
def baseStart_590110 : Nat := 118140960795 + 590110 * 2 ^ 59
def prefixEnd_590110 : Nat := 4983230072969 + 3 ^ 40 * 590110 * 2
def baseEnd_590110 : Nat := 89780761192530792773671

theorem tailTrace_590110 : CollatzResearch.WordTrace tailWord_590110 prefixEnd_590110 89780761192530792773671 := by
  unfold tailWord_590110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690384986517465951172973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14348719928093151739589189 2690384986517465951172973)
  ·
    refine ⟨1008894369944049731689865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2690384986517465951172973 1008894369944049731689865)
    ·
      refine ⟨756670777458037298767399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1008894369944049731689865 756670777458037298767399)
      ·
        refine ⟨1135006166187055948151099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756670777458037298767399 1135006166187055948151099)
        ·
          refine ⟨1702509249280583922226649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135006166187055948151099 1702509249280583922226649)
          ·
            refine ⟨1276881936960437941669987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702509249280583922226649 1276881936960437941669987)
            ·
              refine ⟨1915322905440656912504981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276881936960437941669987 1915322905440656912504981)
              ·
                refine ⟨89780761192530792773671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1915322905440656912504981 89780761192530792773671)
                ·
                  rfl

theorem cell20_590110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_590110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590110 prefixEnd_590110 := by exact prefixLift 590110
  have htrace : WordTrace (prefixWord ++ tailWord_590110) baseStart_590110 baseEnd_590110 := by
    simpa [prefixWord, tailWord_590110, baseEnd_590110] using wordTrace_append hprefix tailTrace_590110
  have hstable : (prefixWord ++ tailWord_590110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590110).length < 2 ^ (prefixWord ++ tailWord_590110).sum := by decide
  have hdescent : baseEnd_590110 < baseStart_590110 := by decide
  rcases family_descends (prefixWord ++ tailWord_590110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590120 : List Nat := [2, 1, 5, 1, 3, 2, 1, 3, 2]
def baseStart_590120 : Nat := 118140960795 + 590120 * 2 ^ 59
def prefixEnd_590120 : Nat := 4983230072969 + 3 ^ 40 * 590120 * 2
def baseEnd_590120 : Nat := 269346847850076787987639

theorem tailTrace_590120 : CollatzResearch.WordTrace tailWord_590120 prefixEnd_590120 269346847850076787987639 := by
  unfold tailWord_590120
  simp only [CollatzResearch.WordTrace]
  refine ⟨10761722311051749658623907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14348963081402332878165209 10761722311051749658623907)
  ·
    refine ⟨16142583466577624487935861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10761722311051749658623907 16142583466577624487935861)
    ·
      refine ⟨1513367199991652295743987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16142583466577624487935861 1513367199991652295743987)
      ·
        refine ⟨2270050799987478443615981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513367199991652295743987 2270050799987478443615981)
        ·
          refine ⟨851269049995304416355993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2270050799987478443615981 851269049995304416355993)
          ·
            refine ⟨638451787496478312266995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 851269049995304416355993 638451787496478312266995)
            ·
              refine ⟨957677681244717468400493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638451787496478312266995 957677681244717468400493)
              ·
                refine ⟨359129130466769050650185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957677681244717468400493 359129130466769050650185)
                ·
                  refine ⟨269346847850076787987639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359129130466769050650185 269346847850076787987639)
                  ·
                    rfl

theorem cell20_590120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_590120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590120 prefixEnd_590120 := by exact prefixLift 590120
  have htrace : WordTrace (prefixWord ++ tailWord_590120) baseStart_590120 baseEnd_590120 := by
    simpa [prefixWord, tailWord_590120, baseEnd_590120] using wordTrace_append hprefix tailTrace_590120
  have hstable : (prefixWord ++ tailWord_590120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590120).length < 2 ^ (prefixWord ++ tailWord_590120).sum := by decide
  have hdescent : baseEnd_590120 < baseStart_590120 := by decide
  rcases family_descends (prefixWord ++ tailWord_590120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590124 : List Nat := [2, 2, 1, 1, 1, 3, 5, 3, 2]
def baseStart_590124 : Nat := 118140960795 + 590124 * 2 ^ 59
def prefixEnd_590124 : Nat := 4983230072969 + 3 ^ 40 * 590124 * 2
def baseEnd_590124 : Nat := 269348673559070551854289

theorem tailTrace_590124 : CollatzResearch.WordTrace tailWord_590124 prefixEnd_590124 269348673559070551854289 := by
  unfold tailWord_590124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10761795257044504000196713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14349060342726005333595617 10761795257044504000196713)
  ·
    refine ⟨8071346442783378000147535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10761795257044504000196713 8071346442783378000147535)
    ·
      refine ⟨12107019664175067000221303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8071346442783378000147535 12107019664175067000221303)
      ·
        refine ⟨18160529496262600500331955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12107019664175067000221303 18160529496262600500331955)
        ·
          refine ⟨27240794244393900750497933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18160529496262600500331955 27240794244393900750497933)
          ·
            refine ⟨10215297841647712781436725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27240794244393900750497933 10215297841647712781436725)
            ·
              refine ⟨957684172654473073259693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10215297841647712781436725 957684172654473073259693)
              ·
                refine ⟨359131564745427402472385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957684172654473073259693 359131564745427402472385)
                ·
                  refine ⟨269348673559070551854289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359131564745427402472385 269348673559070551854289)
                  ·
                    rfl

theorem cell20_590124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_590124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590124 prefixEnd_590124 := by exact prefixLift 590124
  have htrace : WordTrace (prefixWord ++ tailWord_590124) baseStart_590124 baseEnd_590124 := by
    simpa [prefixWord, tailWord_590124, baseEnd_590124] using wordTrace_append hprefix tailTrace_590124
  have hstable : (prefixWord ++ tailWord_590124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590124).length < 2 ^ (prefixWord ++ tailWord_590124).sum := by decide
  have hdescent : baseEnd_590124 < baseStart_590124 := by decide
  rcases family_descends (prefixWord ++ tailWord_590124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590148 : List Nat := [2, 3, 4, 1, 2, 1, 2, 5]
def baseStart_590148 : Nat := 118140960795 + 590148 * 2 ^ 59
def prefixEnd_590148 : Nat := 4983230072969 + 3 ^ 40 * 590148 * 2
def baseEnd_590148 : Nat := 89786542604344378351397

theorem tailTrace_590148 : CollatzResearch.WordTrace tailWord_590148 prefixEnd_590148 89786542604344378351397 := by
  unfold tailWord_590148
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762232933001030049633549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14349643910668040066178065 10762232933001030049633549)
  ·
    refine ⟨4035837349875386268612581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10762232933001030049633549 4035837349875386268612581)
    ·
      refine ⟨756719503101634925364859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4035837349875386268612581 756719503101634925364859)
      ·
        refine ⟨1135079254652452388047289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756719503101634925364859 1135079254652452388047289)
        ·
          refine ⟨851309440989339291035467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135079254652452388047289 851309440989339291035467)
          ·
            refine ⟨1276964161484008936553201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851309440989339291035467 1276964161484008936553201)
            ·
              refine ⟨957723121113006702414901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276964161484008936553201 957723121113006702414901)
              ·
                refine ⟨89786542604344378351397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 957723121113006702414901 89786542604344378351397)
                ·
                  rfl

theorem cell20_590148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_590148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590148 prefixEnd_590148 := by exact prefixLift 590148
  have htrace : WordTrace (prefixWord ++ tailWord_590148) baseStart_590148 baseEnd_590148 := by
    simpa [prefixWord, tailWord_590148, baseEnd_590148] using wordTrace_append hprefix tailTrace_590148
  have hstable : (prefixWord ++ tailWord_590148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590148).length < 2 ^ (prefixWord ++ tailWord_590148).sum := by decide
  have hdescent : baseEnd_590148 < baseStart_590148 := by decide
  rcases family_descends (prefixWord ++ tailWord_590148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590230 : List Nat := [5, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_590230 : Nat := 118140960795 + 590230 * 2 ^ 59
def prefixEnd_590230 : Nat := 4983230072969 + 3 ^ 40 * 590230 * 2
def baseEnd_590230 : Nat := 269397054847405294320523

theorem tailTrace_590230 : CollatzResearch.WordTrace tailWord_590230 prefixEnd_590230 269397054847405294320523 := by
  unfold tailWord_590230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345466040731561756484509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14351637767803325402501429 1345466040731561756484509)
  ·
    refine ⟨504549765274335658681691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1345466040731561756484509 504549765274335658681691)
    ·
      refine ⟨756824647911503488022537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504549765274335658681691 756824647911503488022537)
      ·
        refine ⟨567618485933627616016903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756824647911503488022537 567618485933627616016903)
        ·
          refine ⟨851427728900441424025355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567618485933627616016903 851427728900441424025355)
          ·
            refine ⟨1277141593350662136038033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851427728900441424025355 1277141593350662136038033)
            ·
              refine ⟨957856195012996602028525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277141593350662136038033 957856195012996602028525)
              ·
                refine ⟨359196073129873725760697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957856195012996602028525 359196073129873725760697)
                ·
                  refine ⟨269397054847405294320523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359196073129873725760697 269397054847405294320523)
                  ·
                    rfl

theorem cell20_590230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_590230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590230 prefixEnd_590230 := by exact prefixLift 590230
  have htrace : WordTrace (prefixWord ++ tailWord_590230) baseStart_590230 baseEnd_590230 := by
    simpa [prefixWord, tailWord_590230, baseEnd_590230] using wordTrace_append hprefix tailTrace_590230
  have hstable : (prefixWord ++ tailWord_590230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590230).length < 2 ^ (prefixWord ++ tailWord_590230).sum := by decide
  have hdescent : baseEnd_590230 < baseStart_590230 := by decide
  rcases family_descends (prefixWord ++ tailWord_590230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590248 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_590248 : Nat := 118140960795 + 590248 * 2 ^ 59
def prefixEnd_590248 : Nat := 4983230072969 + 3 ^ 40 * 590248 * 2
def baseEnd_590248 : Nat := 269405270537877231720449

theorem tailTrace_590248 : CollatzResearch.WordTrace tailWord_590248 prefixEnd_590248 269405270537877231720449 := by
  unfold tailWord_590248
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764056582819888588953699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14352075443759851451938265 10764056582819888588953699)
  ·
    refine ⟨16146084874229832883430549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10764056582819888588953699 16146084874229832883430549)
    ·
      refine ⟨756847728479523416410807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16146084874229832883430549 756847728479523416410807)
      ·
        refine ⟨1135271592719285124616211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756847728479523416410807 1135271592719285124616211)
        ·
          refine ⟨1702907389078927686924317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135271592719285124616211 1702907389078927686924317)
          ·
            refine ⟨638590270904597882596619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1702907389078927686924317 638590270904597882596619)
            ·
              refine ⟨957885406356896823894929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638590270904597882596619 957885406356896823894929)
              ·
                refine ⟨718414054767672617921197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 957885406356896823894929 718414054767672617921197)
                ·
                  refine ⟨269405270537877231720449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718414054767672617921197 269405270537877231720449)
                  ·
                    rfl

theorem cell20_590248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_590248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590248 prefixEnd_590248 := by exact prefixLift 590248
  have htrace : WordTrace (prefixWord ++ tailWord_590248) baseStart_590248 baseEnd_590248 := by
    simpa [prefixWord, tailWord_590248, baseEnd_590248] using wordTrace_append hprefix tailTrace_590248
  have hstable : (prefixWord ++ tailWord_590248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590248).length < 2 ^ (prefixWord ++ tailWord_590248).sum := by decide
  have hdescent : baseEnd_590248 < baseStart_590248 := by decide
  rcases family_descends (prefixWord ++ tailWord_590248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590269 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 3]
def baseStart_590269 : Nat := 118140960795 + 590269 * 2 ^ 59
def prefixEnd_590269 : Nat := 4983230072969 + 3 ^ 40 * 590269 * 2
def baseEnd_590269 : Nat := 269414855510094492020363

theorem tailTrace_590269 : CollatzResearch.WordTrace tailWord_590269 prefixEnd_590269 269414855510094492020363 := by
  unfold tailWord_590269
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528879098563697764421861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14352586065709131842947907 21528879098563697764421861)
  ·
    refine ⟨4036664830980693330829099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21528879098563697764421861 4036664830980693330829099)
    ·
      refine ⟨6054997246471039996243649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4036664830980693330829099 6054997246471039996243649)
      ·
        refine ⟨4541247934853279997182737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6054997246471039996243649 4541247934853279997182737)
        ·
          refine ⟨3405935951139959997887053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4541247934853279997182737 3405935951139959997887053)
          ·
            refine ⟨1277225981677484999207645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3405935951139959997887053 1277225981677484999207645)
            ·
              refine ⟨478959743129056874702867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1277225981677484999207645 478959743129056874702867)
              ·
                refine ⟨718439614693585312054301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478959743129056874702867 718439614693585312054301)
                ·
                  refine ⟨269414855510094492020363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718439614693585312054301 269414855510094492020363)
                  ·
                    rfl

theorem cell20_590269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_590269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590269 prefixEnd_590269 := by exact prefixLift 590269
  have htrace : WordTrace (prefixWord ++ tailWord_590269) baseStart_590269 baseEnd_590269 := by
    simpa [prefixWord, tailWord_590269, baseEnd_590269] using wordTrace_append hprefix tailTrace_590269
  have hstable : (prefixWord ++ tailWord_590269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590269).length < 2 ^ (prefixWord ++ tailWord_590269).sum := by decide
  have hdescent : baseEnd_590269 < baseStart_590269 := by decide
  rcases family_descends (prefixWord ++ tailWord_590269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590293 : List Nat := [1, 3, 2, 3, 1, 4, 1, 3, 2]
def baseStart_590293 : Nat := 118140960795 + 590293 * 2 ^ 59
def prefixEnd_590293 : Nat := 4983230072969 + 3 ^ 40 * 590293 * 2
def baseEnd_590293 : Nat := 269425809764057075220265

theorem tailTrace_590293 : CollatzResearch.WordTrace tailWord_590293 prefixEnd_590293 269425809764057075220265 := by
  unfold tailWord_590293
  simp only [CollatzResearch.WordTrace]
  refine ⟨21529754450476749863295533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14353169633651166575530355 21529754450476749863295533)
  ·
    refine ⟨8073657918928781198735825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21529754450476749863295533 8073657918928781198735825)
    ·
      refine ⟨6055243439196585899051869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8073657918928781198735825 6055243439196585899051869)
      ·
        refine ⟨2270716289698719712144451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6055243439196585899051869 2270716289698719712144451)
        ·
          refine ⟨3406074434548079568216677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270716289698719712144451 3406074434548079568216677)
          ·
            refine ⟨638638956477764919040627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3406074434548079568216677 638638956477764919040627)
            ·
              refine ⟨957958434716647378560941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638638956477764919040627 957958434716647378560941)
              ·
                refine ⟨359234413018742766960353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957958434716647378560941 359234413018742766960353)
                ·
                  refine ⟨269425809764057075220265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359234413018742766960353 269425809764057075220265)
                  ·
                    rfl

theorem cell20_590293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_590293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590293 prefixEnd_590293 := by exact prefixLift 590293
  have htrace : WordTrace (prefixWord ++ tailWord_590293) baseStart_590293 baseEnd_590293 := by
    simpa [prefixWord, tailWord_590293, baseEnd_590293] using wordTrace_append hprefix tailTrace_590293
  have hstable : (prefixWord ++ tailWord_590293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590293).length < 2 ^ (prefixWord ++ tailWord_590293).sum := by decide
  have hdescent : baseEnd_590293 < baseStart_590293 := by decide
  rcases family_descends (prefixWord ++ tailWord_590293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590311 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_590311 : Nat := 118140960795 + 590311 * 2 ^ 59
def prefixEnd_590311 : Nat := 4983230072969 + 3 ^ 40 * 590311 * 2
def baseEnd_590311 : Nat := 269434025454529012620191

theorem tailTrace_590311 : CollatzResearch.WordTrace tailWord_590311 prefixEnd_590311 269434025454529012620191 := by
  unfold tailWord_590311
  simp only [CollatzResearch.WordTrace]
  refine ⟨21530410964411538937450787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14353607309607692624967191 21530410964411538937450787)
  ·
    refine ⟨32295616446617308406176181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21530410964411538937450787 32295616446617308406176181)
    ·
      refine ⟨3027714041870372663079017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32295616446617308406176181 3027714041870372663079017)
      ·
        refine ⟨2270785531402779497309263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027714041870372663079017 2270785531402779497309263)
        ·
          refine ⟨3406178297104169245963895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270785531402779497309263 3406178297104169245963895)
          ·
            refine ⟨5109267445656253868945843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406178297104169245963895 5109267445656253868945843)
            ·
              refine ⟨7663901168484380803418765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109267445656253868945843 7663901168484380803418765)
              ·
                refine ⟨2873962938181642801282037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7663901168484380803418765 2873962938181642801282037)
                ·
                  refine ⟨269434025454529012620191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2873962938181642801282037 269434025454529012620191)
                  ·
                    rfl

theorem cell20_590311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_590311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590311 prefixEnd_590311 := by exact prefixLift 590311
  have htrace : WordTrace (prefixWord ++ tailWord_590311) baseStart_590311 baseEnd_590311 := by
    simpa [prefixWord, tailWord_590311, baseEnd_590311] using wordTrace_append hprefix tailTrace_590311
  have hstable : (prefixWord ++ tailWord_590311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590311).length < 2 ^ (prefixWord ++ tailWord_590311).sum := by decide
  have hdescent : baseEnd_590311 < baseStart_590311 := by decide
  rcases family_descends (prefixWord ++ tailWord_590311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590314 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_590314 : Nat := 118140960795 + 590314 * 2 ^ 59
def prefixEnd_590314 : Nat := 4983230072969 + 3 ^ 40 * 590314 * 2
def baseEnd_590314 : Nat := 269435394736274335520179

theorem tailTrace_590314 : CollatzResearch.WordTrace tailWord_590314 prefixEnd_590314 269435394736274335520179 := by
  unfold tailWord_590314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382630095850167612452499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14353680255600446966539997 5382630095850167612452499)
  ·
    refine ⟨8073945143775251418678749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5382630095850167612452499 8073945143775251418678749)
    ·
      refine ⟨3027729428915719282004531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8073945143775251418678749 3027729428915719282004531)
      ·
        refine ⟨4541594143373578923006797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027729428915719282004531 4541594143373578923006797)
        ·
          refine ⟨1703097803765092096127549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4541594143373578923006797 1703097803765092096127549)
          ·
            refine ⟨638661676411909536047831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1703097803765092096127549 638661676411909536047831)
            ·
              refine ⟨957992514617864304071747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638661676411909536047831 957992514617864304071747)
              ·
                refine ⟨1436988771926796456107621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957992514617864304071747 1436988771926796456107621)
                ·
                  refine ⟨269435394736274335520179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436988771926796456107621 269435394736274335520179)
                  ·
                    rfl

theorem cell20_590314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_590314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590314 prefixEnd_590314 := by exact prefixLift 590314
  have htrace : WordTrace (prefixWord ++ tailWord_590314) baseStart_590314 baseEnd_590314 := by
    simpa [prefixWord, tailWord_590314, baseEnd_590314] using wordTrace_append hprefix tailTrace_590314
  have hstable : (prefixWord ++ tailWord_590314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590314).length < 2 ^ (prefixWord ++ tailWord_590314).sum := by decide
  have hdescent : baseEnd_590314 < baseStart_590314 := by decide
  rcases family_descends (prefixWord ++ tailWord_590314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590359 : List Nat := [1, 1, 3, 6, 2, 7]
def baseStart_590359 : Nat := 118140960795 + 590359 * 2 ^ 59
def prefixEnd_590359 : Nat := 4983230072969 + 3 ^ 40 * 590359 * 2
def baseEnd_590359 : Nat := 9979849406016821445185

theorem tailTrace_590359 : CollatzResearch.WordTrace tailWord_590359 prefixEnd_590359 9979849406016821445185 := by
  unfold tailWord_590359
  simp only [CollatzResearch.WordTrace]
  refine ⟨21532161668237643135198131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14354774445491762090132087 21532161668237643135198131)
  ·
    refine ⟨32298242502356464702797197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21532161668237643135198131 32298242502356464702797197)
    ·
      refine ⟨12111840938383674263548949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32298242502356464702797197 12111840938383674263548949)
      ·
        refine ⟨567742543986734731103857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12111840938383674263548949 567742543986734731103857)
        ·
          refine ⟨425806907990051048327893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 567742543986734731103857 425806907990051048327893)
          ·
            refine ⟨9979849406016821445185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 425806907990051048327893 9979849406016821445185)
            ·
              rfl

theorem cell20_590359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 7].length) (baseStart_590359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590359 prefixEnd_590359 := by exact prefixLift 590359
  have htrace : WordTrace (prefixWord ++ tailWord_590359) baseStart_590359 baseEnd_590359 := by
    simpa [prefixWord, tailWord_590359, baseEnd_590359] using wordTrace_append hprefix tailTrace_590359
  have hstable : (prefixWord ++ tailWord_590359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590359).length < 2 ^ (prefixWord ++ tailWord_590359).sum := by decide
  have hdescent : baseEnd_590359 < baseStart_590359 := by decide
  rcases family_descends (prefixWord ++ tailWord_590359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590387 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 3]
def baseStart_590387 : Nat := 118140960795 + 590387 * 2 ^ 59
def prefixEnd_590387 : Nat := 4983230072969 + 3 ^ 40 * 590387 * 2
def baseEnd_590387 : Nat := 269468713925410526086547

theorem tailTrace_590387 : CollatzResearch.WordTrace tailWord_590387 prefixEnd_590387 269468713925410526086547 := by
  unfold tailWord_590387
  simp only [CollatzResearch.WordTrace]
  refine ⟨21533182912136203917217415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14355455274757469278144943 21533182912136203917217415)
  ·
    refine ⟨32299774368204305875826123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21533182912136203917217415 32299774368204305875826123)
    ·
      refine ⟨48449661552306458813739185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32299774368204305875826123 48449661552306458813739185)
      ·
        refine ⟨36337246164229844110304389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48449661552306458813739185 36337246164229844110304389)
        ·
          refine ⟨6813233655793095770682073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36337246164229844110304389 6813233655793095770682073)
          ·
            refine ⟨5109925241844821828011555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6813233655793095770682073 5109925241844821828011555)
            ·
              refine ⟨7664887862767232742017333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109925241844821828011555 7664887862767232742017333)
              ·
                refine ⟨718583237134428069564125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7664887862767232742017333 718583237134428069564125)
                ·
                  refine ⟨269468713925410526086547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718583237134428069564125 269468713925410526086547)
                  ·
                    rfl

theorem cell20_590387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_590387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590387 prefixEnd_590387 := by exact prefixLift 590387
  have htrace : WordTrace (prefixWord ++ tailWord_590387) baseStart_590387 baseEnd_590387 := by
    simpa [prefixWord, tailWord_590387, baseEnd_590387] using wordTrace_append hprefix tailTrace_590387
  have hstable : (prefixWord ++ tailWord_590387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590387).length < 2 ^ (prefixWord ++ tailWord_590387).sum := by decide
  have hdescent : baseEnd_590387 < baseStart_590387 := by decide
  rcases family_descends (prefixWord ++ tailWord_590387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590390 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_590390 : Nat := 118140960795 + 590390 * 2 ^ 59
def prefixEnd_590390 : Nat := 4983230072969 + 3 ^ 40 * 590390 * 2
def baseEnd_590390 : Nat := 269470083207155848986535

theorem tailTrace_590390 : CollatzResearch.WordTrace tailWord_590390 prefixEnd_590390 269470083207155848986535 := by
  unfold tailWord_590390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345830770695333464348539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14355528220750223619717749 1345830770695333464348539)
  ·
    refine ⟨2018746156043000196522809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345830770695333464348539 2018746156043000196522809)
    ·
      refine ⟨1514059617032250147392107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2018746156043000196522809 1514059617032250147392107)
      ·
        refine ⟨2271089425548375221088161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514059617032250147392107 2271089425548375221088161)
        ·
          refine ⟨1703317069161281415816121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2271089425548375221088161 1703317069161281415816121)
          ·
            refine ⟨1277487801870961061862091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1703317069161281415816121 1277487801870961061862091)
            ·
              refine ⟨1916231702806441592793137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277487801870961061862091 1916231702806441592793137)
              ·
                refine ⟨1437173777104831194594853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916231702806441592793137 1437173777104831194594853)
                ·
                  refine ⟨269470083207155848986535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437173777104831194594853 269470083207155848986535)
                  ·
                    rfl

theorem cell20_590390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_590390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590390 prefixEnd_590390 := by exact prefixLift 590390
  have htrace : WordTrace (prefixWord ++ tailWord_590390) baseStart_590390 baseEnd_590390 := by
    simpa [prefixWord, tailWord_590390, baseEnd_590390] using wordTrace_append hprefix tailTrace_590390
  have hstable : (prefixWord ++ tailWord_590390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590390).length < 2 ^ (prefixWord ++ tailWord_590390).sum := by decide
  have hdescent : baseEnd_590390 < baseStart_590390 := by decide
  rcases family_descends (prefixWord ++ tailWord_590390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590394 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_590394 : Nat := 118140960795 + 590394 * 2 ^ 59
def prefixEnd_590394 : Nat := 4983230072969 + 3 ^ 40 * 590394 * 2
def baseEnd_590394 : Nat := 269471908916149612853185

theorem tailTrace_590394 : CollatzResearch.WordTrace tailWord_590394 prefixEnd_590394 269471908916149612853185 := by
  unfold tailWord_590394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5383359555777711028180559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14355625482073896075148157 5383359555777711028180559)
  ·
    refine ⟨8075039333666566542270839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5383359555777711028180559 8075039333666566542270839)
    ·
      refine ⟨12112559000499849813406259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8075039333666566542270839 12112559000499849813406259)
      ·
        refine ⟨18168838500749774720109389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12112559000499849813406259 18168838500749774720109389)
        ·
          refine ⟨6813314437781165520041021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18168838500749774720109389 6813314437781165520041021)
          ·
            refine ⟨2554992914167937070015383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6813314437781165520041021 2554992914167937070015383)
            ·
              refine ⟨3832489371251905605023075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554992914167937070015383 3832489371251905605023075)
              ·
                refine ⟨5748734056877858407534613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832489371251905605023075 5748734056877858407534613)
                ·
                  refine ⟨269471908916149612853185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5748734056877858407534613 269471908916149612853185)
                  ·
                    rfl

theorem cell20_590394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_590394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590394 prefixEnd_590394 := by exact prefixLift 590394
  have htrace : WordTrace (prefixWord ++ tailWord_590394) baseStart_590394 baseEnd_590394 := by
    simpa [prefixWord, tailWord_590394, baseEnd_590394] using wordTrace_append hprefix tailTrace_590394
  have hstable : (prefixWord ++ tailWord_590394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590394).length < 2 ^ (prefixWord ++ tailWord_590394).sum := by decide
  have hdescent : baseEnd_590394 < baseStart_590394 := by decide
  rcases family_descends (prefixWord ++ tailWord_590394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590397 : List Nat := [1, 4, 1, 3, 2, 2, 3, 4]
def baseStart_590397 : Nat := 118140960795 + 590397 * 2 ^ 59
def prefixEnd_590397 : Nat := 4983230072969 + 3 ^ 40 * 590397 * 2
def baseEnd_590397 : Nat := 89824426065964978584391

theorem tailTrace_590397 : CollatzResearch.WordTrace tailWord_590397 prefixEnd_590397 89824426065964978584391 := by
  unfold tailWord_590397
  simp only [CollatzResearch.WordTrace]
  refine ⟨21533547642099975625081445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14355698428066650416720963 21533547642099975625081445)
  ·
    refine ⟨4037540182893745429702771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21533547642099975625081445 4037540182893745429702771)
    ·
      refine ⟨6056310274340618144554157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4037540182893745429702771 6056310274340618144554157)
      ·
        refine ⟨2271116352877731804207809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6056310274340618144554157 2271116352877731804207809)
        ·
          refine ⟨1703337264658298853155857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2271116352877731804207809 1703337264658298853155857)
          ·
            refine ⟨1277502948493724139866893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1703337264658298853155857 1277502948493724139866893)
            ·
              refine ⟨479063605685146552450085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1277502948493724139866893 479063605685146552450085)
              ·
                refine ⟨89824426065964978584391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 479063605685146552450085 89824426065964978584391)
                ·
                  rfl

theorem cell20_590397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_590397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590397 prefixEnd_590397 := by exact prefixLift 590397
  have htrace : WordTrace (prefixWord ++ tailWord_590397) baseStart_590397 baseEnd_590397 := by
    simpa [prefixWord, tailWord_590397, baseEnd_590397] using wordTrace_append hprefix tailTrace_590397
  have hstable : (prefixWord ++ tailWord_590397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590397).length < 2 ^ (prefixWord ++ tailWord_590397).sum := by decide
  have hdescent : baseEnd_590397 < baseStart_590397 := by decide
  rcases family_descends (prefixWord ++ tailWord_590397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590411 : List Nat := [1, 1, 1, 1, 3, 1, 5, 5, 2]
def baseStart_590411 : Nat := 118140960795 + 590411 * 2 ^ 59
def prefixEnd_590411 : Nat := 4983230072969 + 3 ^ 40 * 590411 * 2
def baseEnd_590411 : Nat := 269479668179373109286449

theorem tailTrace_590411 : CollatzResearch.WordTrace tailWord_590411 prefixEnd_590411 269479668179373109286449 := by
  unfold tailWord_590411
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534058264049256016091087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14356038842699504010727391 21534058264049256016091087)
  ·
    refine ⟨32301087396073884024136631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21534058264049256016091087 32301087396073884024136631)
    ·
      refine ⟨48451631094110826036204947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32301087396073884024136631 48451631094110826036204947)
      ·
        refine ⟨72677446641166239054307421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48451631094110826036204947 72677446641166239054307421)
        ·
          refine ⟨27254042490437339645365283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72677446641166239054307421 27254042490437339645365283)
          ·
            refine ⟨40881063735656009468047925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27254042490437339645365283 40881063735656009468047925)
            ·
              refine ⟨3832599725217750887629493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40881063735656009468047925 3832599725217750887629493)
              ·
                refine ⟨359306224239164145715265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3832599725217750887629493 359306224239164145715265)
                ·
                  refine ⟨269479668179373109286449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359306224239164145715265 269479668179373109286449)
                  ·
                    rfl

theorem cell20_590411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 2].length) (baseStart_590411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590411 prefixEnd_590411 := by exact prefixLift 590411
  have htrace : WordTrace (prefixWord ++ tailWord_590411) baseStart_590411 baseEnd_590411 := by
    simpa [prefixWord, tailWord_590411, baseEnd_590411] using wordTrace_append hprefix tailTrace_590411
  have hstable : (prefixWord ++ tailWord_590411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590411).length < 2 ^ (prefixWord ++ tailWord_590411).sum := by decide
  have hdescent : baseEnd_590411 < baseStart_590411 := by decide
  rcases family_descends (prefixWord ++ tailWord_590411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590428 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_590428 : Nat := 118140960795 + 590428 * 2 ^ 59
def prefixEnd_590428 : Nat := 4983230072969 + 3 ^ 40 * 590428 * 2
def baseEnd_590428 : Nat := 269487427442596605719713

theorem tailTrace_590428 : CollatzResearch.WordTrace tailWord_590428 prefixEnd_590428 269487427442596605719713 := by
  unfold tailWord_590428
  simp only [CollatzResearch.WordTrace]
  refine ⟨10767339152493833959729969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14356452203325111946306625 10767339152493833959729969)
  ·
    refine ⟨8075504364370375469797477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10767339152493833959729969 8075504364370375469797477)
    ·
      refine ⟨1514157068319445400587027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8075504364370375469797477 1514157068319445400587027)
      ·
        refine ⟨2271235602479168100880541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514157068319445400587027 2271235602479168100880541)
        ·
          refine ⟨851713350929688037830203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2271235602479168100880541 851713350929688037830203)
          ·
            refine ⟨1277570026394532056745305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851713350929688037830203 1277570026394532056745305)
            ·
              refine ⟨958177519795899042558979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277570026394532056745305 958177519795899042558979)
              ·
                refine ⟨1437266279693848563838469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958177519795899042558979 1437266279693848563838469)
                ·
                  refine ⟨269487427442596605719713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437266279693848563838469 269487427442596605719713)
                  ·
                    rfl

theorem cell20_590428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_590428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590428 prefixEnd_590428 := by exact prefixLift 590428
  have htrace : WordTrace (prefixWord ++ tailWord_590428) baseStart_590428 baseEnd_590428 := by
    simpa [prefixWord, tailWord_590428, baseEnd_590428] using wordTrace_append hprefix tailTrace_590428
  have hstable : (prefixWord ++ tailWord_590428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590428).length < 2 ^ (prefixWord ++ tailWord_590428).sum := by decide
  have hdescent : baseEnd_590428 < baseStart_590428 := by decide
  rcases family_descends (prefixWord ++ tailWord_590428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590432 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_590432 : Nat := 118140960795 + 590432 * 2 ^ 59
def prefixEnd_590432 : Nat := 4983230072969 + 3 ^ 40 * 590432 * 2
def baseEnd_590432 : Nat := 269489253151590369586363

theorem tailTrace_590432 : CollatzResearch.WordTrace tailWord_590432 prefixEnd_590432 269489253151590369586363 := by
  unfold tailWord_590432
  simp only [CollatzResearch.WordTrace]
  refine ⟨10767412098486588301302775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14356549464648784401737033 10767412098486588301302775)
  ·
    refine ⟨16151118147729882451954163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10767412098486588301302775 16151118147729882451954163)
    ·
      refine ⟨24226677221594823677931245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16151118147729882451954163 24226677221594823677931245)
      ·
        refine ⟨9085003958098058879224217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24226677221594823677931245 9085003958098058879224217)
        ·
          refine ⟨6813752968573544159418163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9085003958098058879224217 6813752968573544159418163)
          ·
            refine ⟨10220629452860316239127245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813752968573544159418163 10220629452860316239127245)
            ·
              refine ⟨3832736044822618589672717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10220629452860316239127245 3832736044822618589672717)
              ·
                refine ⟨1437276016808481971127269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3832736044822618589672717 1437276016808481971127269)
                ·
                  refine ⟨269489253151590369586363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437276016808481971127269 269489253151590369586363)
                  ·
                    rfl

theorem cell20_590432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_590432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590432 prefixEnd_590432 := by exact prefixLift 590432
  have htrace : WordTrace (prefixWord ++ tailWord_590432) baseStart_590432 baseEnd_590432 := by
    simpa [prefixWord, tailWord_590432, baseEnd_590432] using wordTrace_append hprefix tailTrace_590432
  have hstable : (prefixWord ++ tailWord_590432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590432).length < 2 ^ (prefixWord ++ tailWord_590432).sum := by decide
  have hdescent : baseEnd_590432 < baseStart_590432 := by decide
  rcases family_descends (prefixWord ++ tailWord_590432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590439 : List Nat := [1, 1, 5, 1, 1, 1, 1, 9]
def baseStart_590439 : Nat := 118140960795 + 590439 * 2 ^ 59
def prefixEnd_590439 : Nat := 4983230072969 + 3 ^ 40 * 590439 * 2
def baseEnd_590439 : Nat := 89830816047443152117667

theorem tailTrace_590439 : CollatzResearch.WordTrace tailWord_590439 prefixEnd_590439 89830816047443152117667 := by
  unfold tailWord_590439
  simp only [CollatzResearch.WordTrace]
  refine ⟨21535079507947816798110371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14356719671965211198740247 21535079507947816798110371)
  ·
    refine ⟨32302619261921725197165557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21535079507947816798110371 32302619261921725197165557)
    ·
      refine ⟨3028370555805161737234271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32302619261921725197165557 3028370555805161737234271)
      ·
        refine ⟨4542555833707742605851407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028370555805161737234271 4542555833707742605851407)
        ·
          refine ⟨6813833750561613908777111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542555833707742605851407 6813833750561613908777111)
          ·
            refine ⟨10220750625842420863165667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813833750561613908777111 10220750625842420863165667)
            ·
              refine ⟨15331125938763631294748501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10220750625842420863165667 15331125938763631294748501)
              ·
                refine ⟨89830816047443152117667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15331125938763631294748501 89830816047443152117667)
                ·
                  rfl

theorem cell20_590439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_590439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590439 prefixEnd_590439 := by exact prefixLift 590439
  have htrace : WordTrace (prefixWord ++ tailWord_590439) baseStart_590439 baseEnd_590439 := by
    simpa [prefixWord, tailWord_590439, baseEnd_590439] using wordTrace_append hprefix tailTrace_590439
  have hstable : (prefixWord ++ tailWord_590439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590439).length < 2 ^ (prefixWord ++ tailWord_590439).sum := by decide
  have hdescent : baseEnd_590439 < baseStart_590439 := by decide
  rcases family_descends (prefixWord ++ tailWord_590439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590515 : List Nat := [1, 1, 1, 2, 3, 4, 2, 6]
def baseStart_590515 : Nat := 118140960795 + 590515 * 2 ^ 59
def prefixEnd_590515 : Nat := 4983230072969 + 3 ^ 40 * 590515 * 2
def baseEnd_590515 : Nat := 89842378871070323273119

theorem tailTrace_590515 : CollatzResearch.WordTrace tailWord_590515 prefixEnd_590515 89842378871070323273119 := by
  unfold tailWord_590515
  simp only [CollatzResearch.WordTrace]
  refine ⟨21537851455672481777876999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14358567637114987851917999 21537851455672481777876999)
  ·
    refine ⟨32306777183508722666815499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21537851455672481777876999 32306777183508722666815499)
    ·
      refine ⟨48460165775263084000223249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32306777183508722666815499 48460165775263084000223249)
      ·
        refine ⟨36345124331447313000167437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48460165775263084000223249 36345124331447313000167437)
        ·
          refine ⟨13629421624292742375062789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36345124331447313000167437 13629421624292742375062789)
          ·
            refine ⟨2555516554554889195324273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13629421624292742375062789 2555516554554889195324273)
            ·
              refine ⟨1916637415916166896493205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555516554554889195324273 1916637415916166896493205)
              ·
                refine ⟨89842378871070323273119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1916637415916166896493205 89842378871070323273119)
                ·
                  rfl

theorem cell20_590515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_590515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590515 prefixEnd_590515 := by exact prefixLift 590515
  have htrace : WordTrace (prefixWord ++ tailWord_590515) baseStart_590515 baseEnd_590515 := by
    simpa [prefixWord, tailWord_590515, baseEnd_590515] using wordTrace_append hprefix tailTrace_590515
  have hstable : (prefixWord ++ tailWord_590515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590515).length < 2 ^ (prefixWord ++ tailWord_590515).sum := by decide
  have hdescent : baseEnd_590515 < baseStart_590515 := by decide
  rcases family_descends (prefixWord ++ tailWord_590515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590534 : List Nat := [6, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_590534 : Nat := 118140960795 + 590534 * 2 ^ 59
def prefixEnd_590534 : Nat := 4983230072969 + 3 ^ 40 * 590534 * 2
def baseEnd_590534 : Nat := 269535808730931348185947

theorem tailTrace_590534 : CollatzResearch.WordTrace tailWord_590534 prefixEnd_590534 269535808730931348185947 := by
  unfold tailWord_590534
  simp only [CollatzResearch.WordTrace]
  refine ⟨673079513831364000713083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14359029628402432015212437 673079513831364000713083)
  ·
    refine ⟨1009619270747046001069625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673079513831364000713083 1009619270747046001069625)
    ·
      refine ⟨757214453060284500802219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1009619270747046001069625 757214453060284500802219)
      ·
        refine ⟨1135821679590426751203329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757214453060284500802219 1135821679590426751203329)
        ·
          refine ⟨851866259692820063402497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135821679590426751203329 851866259692820063402497)
          ·
            refine ⟨638899694769615047551873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 851866259692820063402497 638899694769615047551873)
            ·
              refine ⟨479174771077211285663905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638899694769615047551873 479174771077211285663905)
              ·
                refine ⟨359381078307908464247929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479174771077211285663905 359381078307908464247929)
                ·
                  refine ⟨269535808730931348185947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359381078307908464247929 269535808730931348185947)
                  ·
                    rfl

theorem cell20_590534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_590534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590534 prefixEnd_590534 := by exact prefixLift 590534
  have htrace : WordTrace (prefixWord ++ tailWord_590534) baseStart_590534 baseEnd_590534 := by
    simpa [prefixWord, tailWord_590534, baseEnd_590534] using wordTrace_append hprefix tailTrace_590534
  have hstable : (prefixWord ++ tailWord_590534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590534).length < 2 ^ (prefixWord ++ tailWord_590534).sum := by decide
  have hdescent : baseEnd_590534 < baseStart_590534 := by decide
  rcases family_descends (prefixWord ++ tailWord_590534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590542 : List Nat := [4, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_590542 : Nat := 118140960795 + 590542 * 2 ^ 59
def prefixEnd_590542 : Nat := 4983230072969 + 3 ^ 40 * 590542 * 2
def baseEnd_590542 : Nat := 269539460148918875919247

theorem tailTrace_590542 : CollatzResearch.WordTrace tailWord_590542 prefixEnd_590542 269539460148918875919247 := by
  unfold tailWord_590542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692354528321833173638735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14359224151049776926073253 2692354528321833173638735)
  ·
    refine ⟨4038531792482749760458103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2692354528321833173638735 4038531792482749760458103)
    ·
      refine ⟨6057797688724124640687155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4038531792482749760458103 6057797688724124640687155)
      ·
        refine ⟨9086696533086186961030733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057797688724124640687155 9086696533086186961030733)
        ·
          refine ⟨3407511199907320110386525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9086696533086186961030733 3407511199907320110386525)
          ·
            refine ⟨1277816699965245041394947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3407511199907320110386525 1277816699965245041394947)
            ·
              refine ⟨1916725049947867562092421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277816699965245041394947 1916725049947867562092421)
              ·
                refine ⟨359385946865225167892329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1916725049947867562092421 359385946865225167892329)
                ·
                  refine ⟨269539460148918875919247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359385946865225167892329 269539460148918875919247)
                  ·
                    rfl

theorem cell20_590542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_590542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590542 prefixEnd_590542 := by exact prefixLift 590542
  have htrace : WordTrace (prefixWord ++ tailWord_590542) baseStart_590542 baseEnd_590542 := by
    simpa [prefixWord, tailWord_590542, baseEnd_590542] using wordTrace_append hprefix tailTrace_590542
  have hstable : (prefixWord ++ tailWord_590542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590542).length < 2 ^ (prefixWord ++ tailWord_590542).sum := by decide
  have hdescent : baseEnd_590542 < baseStart_590542 := by decide
  rcases family_descends (prefixWord ++ tailWord_590542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590560 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_590560 : Nat := 118140960795 + 590560 * 2 ^ 59
def prefixEnd_590560 : Nat := 4983230072969 + 3 ^ 40 * 590560 * 2
def baseEnd_590560 : Nat := 269547675839390813319173

theorem tailTrace_590560 : CollatzResearch.WordTrace tailWord_590560 prefixEnd_590560 269547675839390813319173 := by
  unfold tailWord_590560
  simp only [CollatzResearch.WordTrace]
  refine ⟨10769746370254727231632567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14359661827006302975510089 10769746370254727231632567)
  ·
    refine ⟨16154619555382090847448851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10769746370254727231632567 16154619555382090847448851)
    ·
      refine ⟨24231929333073136271173277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16154619555382090847448851 24231929333073136271173277)
      ·
        refine ⟨9086973499902426101689979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24231929333073136271173277 9086973499902426101689979)
        ·
          refine ⟨13630460249853639152534969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9086973499902426101689979 13630460249853639152534969)
          ·
            refine ⟨10222845187390229364401227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13630460249853639152534969 10222845187390229364401227)
            ·
              refine ⟨15334267781085344046601841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10222845187390229364401227 15334267781085344046601841)
              ·
                refine ⟨11500700835814008034951381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15334267781085344046601841 11500700835814008034951381)
                ·
                  refine ⟨269547675839390813319173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11500700835814008034951381 269547675839390813319173)
                  ·
                    rfl

theorem cell20_590560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_590560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590560 prefixEnd_590560 := by exact prefixLift 590560
  have htrace : WordTrace (prefixWord ++ tailWord_590560) baseStart_590560 baseEnd_590560 := by
    simpa [prefixWord, tailWord_590560, baseEnd_590560] using wordTrace_append hprefix tailTrace_590560
  have hstable : (prefixWord ++ tailWord_590560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590560).length < 2 ^ (prefixWord ++ tailWord_590560).sum := by decide
  have hdescent : baseEnd_590560 < baseStart_590560 := by decide
  rcases family_descends (prefixWord ++ tailWord_590560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590563 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_590563 : Nat := 118140960795 + 590563 * 2 ^ 59
def prefixEnd_590563 : Nat := 4983230072969 + 3 ^ 40 * 590563 * 2
def baseEnd_590563 : Nat := 269549045121136136219161

theorem tailTrace_590563 : CollatzResearch.WordTrace tailWord_590563 prefixEnd_590563 269549045121136136219161 := by
  unfold tailWord_590563
  simp only [CollatzResearch.WordTrace]
  refine ⟨21539602159498585975624343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14359734772999057317082895 21539602159498585975624343)
  ·
    refine ⟨32309403239247878963436515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21539602159498585975624343 32309403239247878963436515)
    ·
      refine ⟨48464104858871818445154773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32309403239247878963436515 48464104858871818445154773)
      ·
        refine ⟨1135877457629808244808315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 48464104858871818445154773 1135877457629808244808315)
        ·
          refine ⟨1703816186444712367212473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135877457629808244808315 1703816186444712367212473)
          ·
            refine ⟨1277862139833534275409355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1703816186444712367212473 1277862139833534275409355)
            ·
              refine ⟨1916793209750301413114033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277862139833534275409355 1916793209750301413114033)
              ·
                refine ⟨1437594907312726059835525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916793209750301413114033 1437594907312726059835525)
                ·
                  refine ⟨269549045121136136219161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437594907312726059835525 269549045121136136219161)
                  ·
                    rfl

theorem cell20_590563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_590563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590563 prefixEnd_590563 := by exact prefixLift 590563
  have htrace : WordTrace (prefixWord ++ tailWord_590563) baseStart_590563 baseEnd_590563 := by
    simpa [prefixWord, tailWord_590563, baseEnd_590563] using wordTrace_append hprefix tailTrace_590563
  have hstable : (prefixWord ++ tailWord_590563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590563).length < 2 ^ (prefixWord ++ tailWord_590563).sum := by decide
  have hdescent : baseEnd_590563 < baseStart_590563 := by decide
  rcases family_descends (prefixWord ++ tailWord_590563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590594 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_590594 : Nat := 118140960795 + 590594 * 2 ^ 59
def prefixEnd_590594 : Nat := 4983230072969 + 3 ^ 40 * 590594 * 2
def baseEnd_590594 : Nat := 269563194365837806185701

theorem tailTrace_590594 : CollatzResearch.WordTrace tailWord_590594 prefixEnd_590594 269563194365837806185701 := by
  unfold tailWord_590594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385183205596569567500709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14360488548257518846668557 5385183205596569567500709)
  ·
    refine ⟨1009721851049356793906383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5385183205596569567500709 1009721851049356793906383)
    ·
      refine ⟨1514582776574035190859575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009721851049356793906383 1514582776574035190859575)
      ·
        refine ⟨2271874164861052786289363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514582776574035190859575 2271874164861052786289363)
        ·
          refine ⟨3407811247291579179434045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271874164861052786289363 3407811247291579179434045)
          ·
            refine ⟨1277929217734342192287767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3407811247291579179434045 1277929217734342192287767)
            ·
              refine ⟨1916893826601513288431651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277929217734342192287767 1916893826601513288431651)
              ·
                refine ⟨2875340739902269932647477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916893826601513288431651 2875340739902269932647477)
                ·
                  refine ⟨269563194365837806185701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2875340739902269932647477 269563194365837806185701)
                  ·
                    rfl

theorem cell20_590594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_590594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590594 prefixEnd_590594 := by exact prefixLift 590594
  have htrace : WordTrace (prefixWord ++ tailWord_590594) baseStart_590594 baseEnd_590594 := by
    simpa [prefixWord, tailWord_590594, baseEnd_590594] using wordTrace_append hprefix tailTrace_590594
  have hstable : (prefixWord ++ tailWord_590594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590594).length < 2 ^ (prefixWord ++ tailWord_590594).sum := by decide
  have hdescent : baseEnd_590594 < baseStart_590594 := by decide
  rcases family_descends (prefixWord ++ tailWord_590594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590601 : List Nat := [1, 2, 1, 1, 3, 2, 4, 4, 2]
def baseStart_590601 : Nat := 118140960795 + 590601 * 2 ^ 59
def prefixEnd_590601 : Nat := 4983230072969 + 3 ^ 40 * 590601 * 2
def baseEnd_590601 : Nat := 269566389356576892952339

theorem tailTrace_590601 : CollatzResearch.WordTrace tailWord_590601 prefixEnd_590601 269566389356576892952339 := by
  unfold tailWord_590601
  simp only [CollatzResearch.WordTrace]
  refine ⟨21540988133360918465507657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14360658755573945643671771 21540988133360918465507657)
  ·
    refine ⟨16155741100020688849130743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21540988133360918465507657 16155741100020688849130743)
    ·
      refine ⟨24233611650031033273696115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16155741100020688849130743 24233611650031033273696115)
      ·
        refine ⟨36350417475046549910544173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24233611650031033273696115 36350417475046549910544173)
        ·
          refine ⟨13631406553142456216454065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36350417475046549910544173 13631406553142456216454065)
          ·
            refine ⟨10223554914856842162340549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13631406553142456216454065 10223554914856842162340549)
            ·
              refine ⟨1916916546535657905438853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10223554914856842162340549 1916916546535657905438853)
              ·
                refine ⟨359421852475435857269785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1916916546535657905438853 359421852475435857269785)
                ·
                  refine ⟨269566389356576892952339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359421852475435857269785 269566389356576892952339)
                  ·
                    rfl

theorem cell20_590601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_590601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590601 prefixEnd_590601 := by exact prefixLift 590601
  have htrace : WordTrace (prefixWord ++ tailWord_590601) baseStart_590601 baseEnd_590601 := by
    simpa [prefixWord, tailWord_590601, baseEnd_590601] using wordTrace_append hprefix tailTrace_590601
  have hstable : (prefixWord ++ tailWord_590601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590601).length < 2 ^ (prefixWord ++ tailWord_590601).sum := by decide
  have hdescent : baseEnd_590601 < baseStart_590601 := by decide
  rcases family_descends (prefixWord ++ tailWord_590601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590621 : List Nat := [1, 4, 2, 4, 2, 1, 2, 4]
def baseStart_590621 : Nat := 118140960795 + 590621 * 2 ^ 59
def prefixEnd_590621 : Nat := 4983230072969 + 3 ^ 40 * 590621 * 2
def baseEnd_590621 : Nat := 89858505967181904095197

theorem tailTrace_590621 : CollatzResearch.WordTrace tailWord_590621 prefixEnd_590621 89858505967181904095197 := by
  unfold tailWord_590621
  simp only [CollatzResearch.WordTrace]
  refine ⟨21541717593288461881235717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14361145062192307920823811 21541717593288461881235717)
  ·
    refine ⟨4039072048741586602731697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21541717593288461881235717 4039072048741586602731697)
    ·
      refine ⟨3029304036556189952048773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4039072048741586602731697 3029304036556189952048773)
      ·
        refine ⟨567994506854285616009145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3029304036556189952048773 567994506854285616009145)
        ·
          refine ⟨425995880140714212006859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 567994506854285616009145 425995880140714212006859)
          ·
            refine ⟨638993820211071318010289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425995880140714212006859 638993820211071318010289)
            ·
              refine ⟨479245365158303488507717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638993820211071318010289 479245365158303488507717)
              ·
                refine ⟨89858505967181904095197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 479245365158303488507717 89858505967181904095197)
                ·
                  rfl

theorem cell20_590621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 4].length) (baseStart_590621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590621 prefixEnd_590621 := by exact prefixLift 590621
  have htrace : WordTrace (prefixWord ++ tailWord_590621) baseStart_590621 baseEnd_590621 := by
    simpa [prefixWord, tailWord_590621, baseEnd_590621] using wordTrace_append hprefix tailTrace_590621
  have hstable : (prefixWord ++ tailWord_590621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590621).length < 2 ^ (prefixWord ++ tailWord_590621).sum := by decide
  have hdescent : baseEnd_590621 < baseStart_590621 := by decide
  rcases family_descends (prefixWord ++ tailWord_590621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590629 : List Nat := [1, 3, 1, 2, 3, 1, 3, 6]
def baseStart_590629 : Nat := 118140960795 + 590629 * 2 ^ 59
def prefixEnd_590629 : Nat := 4983230072969 + 3 ^ 40 * 590629 * 2
def baseEnd_590629 : Nat := 89859723106511080006297

theorem tailTrace_590629 : CollatzResearch.WordTrace tailWord_590629 prefixEnd_590629 89859723106511080006297 := by
  unfold tailWord_590629
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542009377259479247526941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14361339584839652831684627 21542009377259479247526941)
  ·
    refine ⟨8078253516472304717822603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21542009377259479247526941 8078253516472304717822603)
    ·
      refine ⟨12117380274708457076733905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8078253516472304717822603 12117380274708457076733905)
      ·
        refine ⟨9088035206031342807550429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12117380274708457076733905 9088035206031342807550429)
        ·
          refine ⟨3408013202261753552831411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9088035206031342807550429 3408013202261753552831411)
          ·
            refine ⟨5112019803392630329247117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408013202261753552831411 5112019803392630329247117)
            ·
              refine ⟨1917007426272236373467669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5112019803392630329247117 1917007426272236373467669)
              ·
                refine ⟨89859723106511080006297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1917007426272236373467669 89859723106511080006297)
                ·
                  rfl

theorem cell20_590629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_590629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590629 prefixEnd_590629 := by exact prefixLift 590629
  have htrace : WordTrace (prefixWord ++ tailWord_590629) baseStart_590629 baseEnd_590629 := by
    simpa [prefixWord, tailWord_590629, baseEnd_590629] using wordTrace_append hprefix tailTrace_590629
  have hstable : (prefixWord ++ tailWord_590629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590629).length < 2 ^ (prefixWord ++ tailWord_590629).sum := by decide
  have hdescent : baseEnd_590629 < baseStart_590629 := by decide
  rcases family_descends (prefixWord ++ tailWord_590629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590636 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_590636 : Nat := 118140960795 + 590636 * 2 ^ 59
def prefixEnd_590636 : Nat := 4983230072969 + 3 ^ 40 * 590636 * 2
def baseEnd_590636 : Nat := 269582364310272326785529

theorem tailTrace_590636 : CollatzResearch.WordTrace tailWord_590636 prefixEnd_590636 269582364310272326785529 := by
  unfold tailWord_590636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771132344117059721515881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14361509792156079628687841 10771132344117059721515881)
  ·
    refine ⟨8078349258087794791136911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10771132344117059721515881 8078349258087794791136911)
    ·
      refine ⟨12117523887131692186705367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8078349258087794791136911 12117523887131692186705367)
      ·
        refine ⟨18176285830697538280058051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12117523887131692186705367 18176285830697538280058051)
        ·
          refine ⟨27264428746046307420087077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18176285830697538280058051 27264428746046307420087077)
          ·
            refine ⟨5112080389883682641266327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27264428746046307420087077 5112080389883682641266327)
            ·
              refine ⟨7668120584825523961899491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112080389883682641266327 7668120584825523961899491)
              ·
                refine ⟨11502180877238285942849237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7668120584825523961899491 11502180877238285942849237)
                ·
                  refine ⟨269582364310272326785529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11502180877238285942849237 269582364310272326785529)
                  ·
                    rfl

theorem cell20_590636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_590636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590636 prefixEnd_590636 := by exact prefixLift 590636
  have htrace : WordTrace (prefixWord ++ tailWord_590636) baseStart_590636 baseEnd_590636 := by
    simpa [prefixWord, tailWord_590636, baseEnd_590636] using wordTrace_append hprefix tailTrace_590636
  have hstable : (prefixWord ++ tailWord_590636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590636).length < 2 ^ (prefixWord ++ tailWord_590636).sum := by decide
  have hdescent : baseEnd_590636 < baseStart_590636 := by decide
  rcases family_descends (prefixWord ++ tailWord_590636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590662 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_590662 : Nat := 118140960795 + 590662 * 2 ^ 59
def prefixEnd_590662 : Nat := 4983230072969 + 3 ^ 40 * 590662 * 2
def baseEnd_590662 : Nat := 269594231418731791918757

theorem tailTrace_590662 : CollatzResearch.WordTrace tailWord_590662 prefixEnd_590662 269594231418731791918757 := by
  unfold tailWord_590662
  simp only [CollatzResearch.WordTrace]
  refine ⟨673225405816872683858695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14362141990759950588985493 673225405816872683858695)
  ·
    refine ⟨1009838108725309025788043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673225405816872683858695 1009838108725309025788043)
    ·
      refine ⟨1514757163087963538682065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009838108725309025788043 1514757163087963538682065)
      ·
        refine ⟨1136067872315972654011549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1514757163087963538682065 1136067872315972654011549)
        ·
          refine ⟨426025452118489745254331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1136067872315972654011549 426025452118489745254331)
          ·
            refine ⟨639038178177734617881497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426025452118489745254331 639038178177734617881497)
            ·
              refine ⟨479278633633300963411123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639038178177734617881497 479278633633300963411123)
              ·
                refine ⟨718917950449951445116685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479278633633300963411123 718917950449951445116685)
                ·
                  refine ⟨269594231418731791918757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718917950449951445116685 269594231418731791918757)
                  ·
                    rfl

theorem cell20_590662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_590662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590662 prefixEnd_590662 := by exact prefixLift 590662
  have htrace : WordTrace (prefixWord ++ tailWord_590662) baseStart_590662 baseEnd_590662 := by
    simpa [prefixWord, tailWord_590662, baseEnd_590662] using wordTrace_append hprefix tailTrace_590662
  have hstable : (prefixWord ++ tailWord_590662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590662).length < 2 ^ (prefixWord ++ tailWord_590662).sum := by decide
  have hdescent : baseEnd_590662 < baseStart_590662 := by decide
  rcases family_descends (prefixWord ++ tailWord_590662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590684 : List Nat := [2, 2, 4, 2, 1, 1, 2, 6]
def baseStart_590684 : Nat := 118140960795 + 590684 * 2 ^ 59
def prefixEnd_590684 : Nat := 4983230072969 + 3 ^ 40 * 590684 * 2
def baseEnd_590684 : Nat := 89868090939399164395111

theorem tailTrace_590684 : CollatzResearch.WordTrace tailWord_590684 prefixEnd_590684 89868090939399164395111 := by
  unfold tailWord_590684
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772007696030111820389553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14362676928040149093852737 10772007696030111820389553)
  ·
    refine ⟨8079005772022583865292165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10772007696030111820389553 8079005772022583865292165)
    ·
      refine ⟨1514813582254234474742281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8079005772022583865292165 1514813582254234474742281)
      ·
        refine ⟨1136110186690675856056711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1514813582254234474742281 1136110186690675856056711)
        ·
          refine ⟨1704165280036013784085067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136110186690675856056711 1704165280036013784085067)
          ·
            refine ⟨2556247920054020676127601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704165280036013784085067 2556247920054020676127601)
            ·
              refine ⟨1917185940040515507095701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2556247920054020676127601 1917185940040515507095701)
              ·
                refine ⟨89868090939399164395111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1917185940040515507095701 89868090939399164395111)
                ·
                  rfl

theorem cell20_590684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_590684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590684 prefixEnd_590684 := by exact prefixLift 590684
  have htrace : WordTrace (prefixWord ++ tailWord_590684) baseStart_590684 baseEnd_590684 := by
    simpa [prefixWord, tailWord_590684, baseEnd_590684] using wordTrace_append hprefix tailTrace_590684
  have hstable : (prefixWord ++ tailWord_590684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590684).length < 2 ^ (prefixWord ++ tailWord_590684).sum := by decide
  have hdescent : baseEnd_590684 < baseStart_590684 := by decide
  rcases family_descends (prefixWord ++ tailWord_590684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590718 : List Nat := [4, 2, 3, 1, 2, 2, 1, 5]
def baseStart_590718 : Nat := 118140960795 + 590718 * 2 ^ 59
def prefixEnd_590718 : Nat := 4983230072969 + 3 ^ 40 * 590718 * 2
def baseEnd_590718 : Nat := 89873263781548162017287

theorem tailTrace_590718 : CollatzResearch.WordTrace tailWord_590718 prefixEnd_590718 89873263781548162017287 := by
  unfold tailWord_590718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693156934242130930939601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14363503649291364965011205 2693156934242130930939601)
  ·
    refine ⟨2019867700681598198204701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2693156934242130930939601 2019867700681598198204701)
    ·
      refine ⟨757450387755599324326763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2019867700681598198204701 757450387755599324326763)
      ·
        refine ⟨1136175581633398986490145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757450387755599324326763 1136175581633398986490145)
        ·
          refine ⟨852131686225049239867609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1136175581633398986490145 852131686225049239867609)
          ·
            refine ⟨639098764668786929900707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 852131686225049239867609 639098764668786929900707)
            ·
              refine ⟨958648147003180394851061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639098764668786929900707 958648147003180394851061)
              ·
                refine ⟨89873263781548162017287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 958648147003180394851061 89873263781548162017287)
                ·
                  rfl

theorem cell20_590718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_590718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590718 prefixEnd_590718 := by exact prefixLift 590718
  have htrace : WordTrace (prefixWord ++ tailWord_590718) baseStart_590718 baseEnd_590718 := by
    simpa [prefixWord, tailWord_590718, baseEnd_590718] using wordTrace_append hprefix tailTrace_590718
  have hstable : (prefixWord ++ tailWord_590718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590718).length < 2 ^ (prefixWord ++ tailWord_590718).sum := by decide
  have hdescent : baseEnd_590718 < baseStart_590718 := by decide
  rcases family_descends (prefixWord ++ tailWord_590718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590729 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 3]
def baseStart_590729 : Nat := 118140960795 + 590729 * 2 ^ 59
def prefixEnd_590729 : Nat := 4983230072969 + 3 ^ 40 * 590729 * 2
def baseEnd_590729 : Nat := 269624812044377336685149

theorem tailTrace_590729 : CollatzResearch.WordTrace tailWord_590729 prefixEnd_590729 269624812044377336685149 := by
  unfold tailWord_590729
  simp only [CollatzResearch.WordTrace]
  refine ⟨21545656676897196326167241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14363771117931464217444827 21545656676897196326167241)
  ·
    refine ⟨16159242507672897244625431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21545656676897196326167241 16159242507672897244625431)
    ·
      refine ⟨24238863761509345866938147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16159242507672897244625431 24238863761509345866938147)
      ·
        refine ⟨36358295642264018800407221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24238863761509345866938147 36358295642264018800407221)
        ·
          refine ⟨3408590216462251762538177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36358295642264018800407221 3408590216462251762538177)
          ·
            refine ⟨2556442662346688821903633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408590216462251762538177 2556442662346688821903633)
            ·
              refine ⟨1917331996760016616427725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2556442662346688821903633 1917331996760016616427725)
              ·
                refine ⟨718999498785006231160397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1917331996760016616427725 718999498785006231160397)
                ·
                  refine ⟨269624812044377336685149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718999498785006231160397 269624812044377336685149)
                  ·
                    rfl

theorem cell20_590729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_590729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590729 prefixEnd_590729 := by exact prefixLift 590729
  have htrace : WordTrace (prefixWord ++ tailWord_590729) baseStart_590729 baseEnd_590729 := by
    simpa [prefixWord, tailWord_590729, baseEnd_590729] using wordTrace_append hprefix tailTrace_590729
  have hstable : (prefixWord ++ tailWord_590729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590729).length < 2 ^ (prefixWord ++ tailWord_590729).sum := by decide
  have hdescent : baseEnd_590729 < baseStart_590729 := by decide
  rcases family_descends (prefixWord ++ tailWord_590729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590784 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_590784 : Nat := 118140960795 + 590784 * 2 ^ 59
def prefixEnd_590784 : Nat := 4983230072969 + 3 ^ 40 * 590784 * 2
def baseEnd_590784 : Nat := 269649915543041589851591

theorem tailTrace_590784 : CollatzResearch.WordTrace tailWord_590784 prefixEnd_590784 269649915543041589851591 := by
  unfold tailWord_590784
  simp only [CollatzResearch.WordTrace]
  refine ⟨10773831345848970359709703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14365108461131960479612937 10773831345848970359709703)
  ·
    refine ⟨16160747018773455539564555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10773831345848970359709703 16160747018773455539564555)
    ·
      refine ⟨24241120528160183309346833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16160747018773455539564555 24241120528160183309346833)
      ·
        refine ⟨18180840396120137482010125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24241120528160183309346833 18180840396120137482010125)
        ·
          refine ⟨6817815148545051555753797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18180840396120137482010125 6817815148545051555753797)
          ·
            refine ⟨1278340340352197166703837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6817815148545051555753797 1278340340352197166703837)
            ·
              refine ⟨479377627632073937513939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278340340352197166703837 479377627632073937513939)
              ·
                refine ⟨719066441448110906270909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479377627632073937513939 719066441448110906270909)
                ·
                  refine ⟨269649915543041589851591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719066441448110906270909 269649915543041589851591)
                  ·
                    rfl

theorem cell20_590784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_590784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590784 prefixEnd_590784 := by exact prefixLift 590784
  have htrace : WordTrace (prefixWord ++ tailWord_590784) baseStart_590784 baseEnd_590784 := by
    simpa [prefixWord, tailWord_590784, baseEnd_590784] using wordTrace_append hprefix tailTrace_590784
  have hstable : (prefixWord ++ tailWord_590784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590784).length < 2 ^ (prefixWord ++ tailWord_590784).sum := by decide
  have hdescent : baseEnd_590784 < baseStart_590784 := by decide
  rcases family_descends (prefixWord ++ tailWord_590784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590798 : List Nat := [4, 1, 1, 1, 2, 3, 4, 4]
def baseStart_590798 : Nat := 118140960795 + 590798 * 2 ^ 59
def prefixEnd_590798 : Nat := 4983230072969 + 3 ^ 40 * 590798 * 2
def baseEnd_590798 : Nat := 89885435174839921128289

theorem tailTrace_590798 : CollatzResearch.WordTrace tailWord_590798 prefixEnd_590798 89885435174839921128289 := by
  unfold tailWord_590798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693521664205902638803631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14365448875764814073619365 2693521664205902638803631)
  ·
    refine ⟨4040282496308853958205447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2693521664205902638803631 4040282496308853958205447)
    ·
      refine ⟨6060423744463280937308171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040282496308853958205447 6060423744463280937308171)
      ·
        refine ⟨9090635616694921405962257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6060423744463280937308171 9090635616694921405962257)
        ·
          refine ⟨6817976712521191054471693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9090635616694921405962257 6817976712521191054471693)
          ·
            refine ⟨2556741267195446645426885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6817976712521191054471693 2556741267195446645426885)
            ·
              refine ⟨479388987599146246017541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2556741267195446645426885 479388987599146246017541)
              ·
                refine ⟨89885435174839921128289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 479388987599146246017541 89885435174839921128289)
                ·
                  rfl

theorem cell20_590798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_590798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590798 prefixEnd_590798 := by exact prefixLift 590798
  have htrace : WordTrace (prefixWord ++ tailWord_590798) baseStart_590798 baseEnd_590798 := by
    simpa [prefixWord, tailWord_590798, baseEnd_590798] using wordTrace_append hprefix tailTrace_590798
  have hstable : (prefixWord ++ tailWord_590798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590798).length < 2 ^ (prefixWord ++ tailWord_590798).sum := by decide
  have hdescent : baseEnd_590798 < baseStart_590798 := by decide
  rcases family_descends (prefixWord ++ tailWord_590798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590808 : List Nat := [2, 1, 2, 2, 2, 5, 1, 3, 2]
def baseStart_590808 : Nat := 118140960795 + 590808 * 2 ^ 59
def prefixEnd_590808 : Nat := 4983230072969 + 3 ^ 40 * 590808 * 2
def baseEnd_590808 : Nat := 269660869797004173051493

theorem tailTrace_590808 : CollatzResearch.WordTrace tailWord_590808 prefixEnd_590808 269660869797004173051493 := by
  unfold tailWord_590808
  simp only [CollatzResearch.WordTrace]
  refine ⟨10774269021805496409146539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14365692029073995212195385 10774269021805496409146539)
  ·
    refine ⟨16161403532708244613719809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10774269021805496409146539 16161403532708244613719809)
    ·
      refine ⟨12121052649531183460289857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16161403532708244613719809 12121052649531183460289857)
      ·
        refine ⟨9090789487148387595217393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12121052649531183460289857 9090789487148387595217393)
        ·
          refine ⟨6818092115361290696413045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9090789487148387595217393 6818092115361290696413045)
          ·
            refine ⟨639196135815121002788723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6818092115361290696413045 639196135815121002788723)
            ·
              refine ⟨958794203722681504183085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639196135815121002788723 958794203722681504183085)
              ·
                refine ⟨359547826396005564068657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 958794203722681504183085 359547826396005564068657)
                ·
                  refine ⟨269660869797004173051493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359547826396005564068657 269660869797004173051493)
                  ·
                    rfl

theorem cell20_590808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 2].length) (baseStart_590808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590808 prefixEnd_590808 := by exact prefixLift 590808
  have htrace : WordTrace (prefixWord ++ tailWord_590808) baseStart_590808 baseEnd_590808 := by
    simpa [prefixWord, tailWord_590808, baseEnd_590808] using wordTrace_append hprefix tailTrace_590808
  have hstable : (prefixWord ++ tailWord_590808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590808).length < 2 ^ (prefixWord ++ tailWord_590808).sum := by decide
  have hdescent : baseEnd_590808 < baseStart_590808 := by decide
  rcases family_descends (prefixWord ++ tailWord_590808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590880 : List Nat := [2, 1, 1, 7, 1, 2, 2, 2, 2]
def baseStart_590880 : Nat := 118140960795 + 590880 * 2 ^ 59
def prefixEnd_590880 : Nat := 4983230072969 + 3 ^ 40 * 590880 * 2
def baseEnd_590880 : Nat := 269693732558891922651199

theorem tailTrace_590880 : CollatzResearch.WordTrace tailWord_590880 prefixEnd_590880 269693732558891922651199 := by
  unfold tailWord_590880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10775582049675074557457047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14367442732900099409942729 10775582049675074557457047)
  ·
    refine ⟨16163373074512611836185571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10775582049675074557457047 16163373074512611836185571)
    ·
      refine ⟨24245059611768917754278357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16163373074512611836185571 24245059611768917754278357)
      ·
        refine ⟨568243584650834009865899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24245059611768917754278357 568243584650834009865899)
        ·
          refine ⟨852365376976251014798849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568243584650834009865899 852365376976251014798849)
          ·
            refine ⟨639274032732188261099137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 852365376976251014798849 639274032732188261099137)
            ·
              refine ⟨479455524549141195824353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639274032732188261099137 479455524549141195824353)
              ·
                refine ⟨359591643411855896868265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479455524549141195824353 359591643411855896868265)
                ·
                  refine ⟨269693732558891922651199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359591643411855896868265 269693732558891922651199)
                  ·
                    rfl

theorem cell20_590880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 2].length) (baseStart_590880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590880 prefixEnd_590880 := by exact prefixLift 590880
  have htrace : WordTrace (prefixWord ++ tailWord_590880) baseStart_590880 baseEnd_590880 := by
    simpa [prefixWord, tailWord_590880, baseEnd_590880] using wordTrace_append hprefix tailTrace_590880
  have hstable : (prefixWord ++ tailWord_590880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590880).length < 2 ^ (prefixWord ++ tailWord_590880).sum := by decide
  have hdescent : baseEnd_590880 < baseStart_590880 := by decide
  rcases family_descends (prefixWord ++ tailWord_590880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590881 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 3]
def baseStart_590881 : Nat := 118140960795 + 590881 * 2 ^ 59
def prefixEnd_590881 : Nat := 4983230072969 + 3 ^ 40 * 590881 * 2
def baseEnd_590881 : Nat := 269694188986140363617861

theorem tailTrace_590881 : CollatzResearch.WordTrace tailWord_590881 prefixEnd_590881 269694188986140363617861 := by
  unfold tailWord_590881
  simp only [CollatzResearch.WordTrace]
  refine ⟨21551200572346526285700497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14367467048231017523800331 21551200572346526285700497)
  ·
    refine ⟨16163400429259894714275373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21551200572346526285700497 16163400429259894714275373)
    ·
      refine ⟨6061275160972460517853265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16163400429259894714275373 6061275160972460517853265)
      ·
        refine ⟨4545956370729345388389949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6061275160972460517853265 4545956370729345388389949)
        ·
          refine ⟨1704733639023504520646231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4545956370729345388389949 1704733639023504520646231)
          ·
            refine ⟨2557100458535256780969347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704733639023504520646231 2557100458535256780969347)
            ·
              refine ⟨3835650687802885171454021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557100458535256780969347 3835650687802885171454021)
              ·
                refine ⟨719184503963040969647629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3835650687802885171454021 719184503963040969647629)
                ·
                  refine ⟨269694188986140363617861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719184503963040969647629 269694188986140363617861)
                  ·
                    rfl

theorem cell20_590881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_590881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590881 prefixEnd_590881 := by exact prefixLift 590881
  have htrace : WordTrace (prefixWord ++ tailWord_590881) baseStart_590881 baseEnd_590881 := by
    simpa [prefixWord, tailWord_590881, baseEnd_590881] using wordTrace_append hprefix tailTrace_590881
  have hstable : (prefixWord ++ tailWord_590881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590881).length < 2 ^ (prefixWord ++ tailWord_590881).sum := by decide
  have hdescent : baseEnd_590881 < baseStart_590881 := by decide
  rcases family_descends (prefixWord ++ tailWord_590881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_590884 : List Nat := [2, 3, 1, 4, 1, 2, 1, 4, 2]
def baseStart_590884 : Nat := 118140960795 + 590884 * 2 ^ 59
def prefixEnd_590884 : Nat := 4983230072969 + 3 ^ 40 * 590884 * 2
def baseEnd_590884 : Nat := 269695558267885686517849

theorem tailTrace_590884 : CollatzResearch.WordTrace tailWord_590884 prefixEnd_590884 269695558267885686517849 := by
  unfold tailWord_590884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10775654995667828899029853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14367539994223771865373137 10775654995667828899029853)
  ·
    refine ⟨4040870623375435837136195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10775654995667828899029853 4040870623375435837136195)
    ·
      refine ⟨6061305935063153755704293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040870623375435837136195 6061305935063153755704293)
      ·
        refine ⟨1136494862824341329194555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6061305935063153755704293 1136494862824341329194555)
        ·
          refine ⟨1704742294236511993791833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136494862824341329194555 1704742294236511993791833)
          ·
            refine ⟨1278556720677383995343875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704742294236511993791833 1278556720677383995343875)
            ·
              refine ⟨1917835081016075993015813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278556720677383995343875 1917835081016075993015813)
              ·
                refine ⟨359594077690514248690465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1917835081016075993015813 359594077690514248690465)
                ·
                  refine ⟨269695558267885686517849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359594077690514248690465 269695558267885686517849)
                  ·
                    rfl

theorem cell20_590884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_590884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_590884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_590884 prefixEnd_590884 := by exact prefixLift 590884
  have htrace : WordTrace (prefixWord ++ tailWord_590884) baseStart_590884 baseEnd_590884 := by
    simpa [prefixWord, tailWord_590884, baseEnd_590884] using wordTrace_append hprefix tailTrace_590884
  have hstable : (prefixWord ++ tailWord_590884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_590884).length < 2 ^ (prefixWord ++ tailWord_590884).sum := by decide
  have hdescent : baseEnd_590884 < baseStart_590884 := by decide
  rcases family_descends (prefixWord ++ tailWord_590884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591009 : List Nat := [1, 2, 3, 3, 1, 1, 4, 5]
def baseStart_591009 : Nat := 118140960795 + 591009 * 2 ^ 59
def prefixEnd_591009 : Nat := 4983230072969 + 3 ^ 40 * 591009 * 2
def baseEnd_591009 : Nat := 89917537224646935783557

theorem tailTrace_591009 : CollatzResearch.WordTrace tailWord_591009 prefixEnd_591009 89917537224646935783557 := by
  unfold tailWord_591009
  simp only [CollatzResearch.WordTrace]
  refine ⟨21555869115882804146360081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14370579410588536097573387 21555869115882804146360081)
  ·
    refine ⟨16166901836912103109770061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21555869115882804146360081 16166901836912103109770061)
    ·
      refine ⟨6062588188842038666163773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16166901836912103109770061 6062588188842038666163773)
      ·
        refine ⟨2273470570815764499811415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6062588188842038666163773 2273470570815764499811415)
        ·
          refine ⟨3410205856223646749717123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273470570815764499811415 3410205856223646749717123)
          ·
            refine ⟨5115308784335470124575685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410205856223646749717123 5115308784335470124575685)
            ·
              refine ⟨959120397062900648357941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5115308784335470124575685 959120397062900648357941)
              ·
                refine ⟨89917537224646935783557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 959120397062900648357941 89917537224646935783557)
                ·
                  rfl

theorem cell20_591009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_591009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591009 prefixEnd_591009 := by exact prefixLift 591009
  have htrace : WordTrace (prefixWord ++ tailWord_591009) baseStart_591009 baseEnd_591009 := by
    simpa [prefixWord, tailWord_591009, baseEnd_591009] using wordTrace_append hprefix tailTrace_591009
  have hstable : (prefixWord ++ tailWord_591009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591009).length < 2 ^ (prefixWord ++ tailWord_591009).sum := by decide
  have hdescent : baseEnd_591009 < baseStart_591009 := by decide
  rcases family_descends (prefixWord ++ tailWord_591009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591012 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_591012 : Nat := 118140960795 + 591012 * 2 ^ 59
def prefixEnd_591012 : Nat := 4983230072969 + 3 ^ 40 * 591012 * 2
def baseEnd_591012 : Nat := 269753980955686130250659

theorem tailTrace_591012 : CollatzResearch.WordTrace tailWord_591012 prefixEnd_591012 269753980955686130250659 := by
  unfold tailWord_591012
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777989267435967829359645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14370652356581290439146193 10777989267435967829359645)
  ·
    refine ⟨4041745975288487936009867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10777989267435967829359645 4041745975288487936009867)
    ·
      refine ⟨6062618962932731904014801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4041745975288487936009867 6062618962932731904014801)
      ·
        refine ⟨4546964222199548928011101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6062618962932731904014801 4546964222199548928011101)
        ·
          refine ⟨1705111583324830848004163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4546964222199548928011101 1705111583324830848004163)
          ·
            refine ⟨2557667374987246272006245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705111583324830848004163 2557667374987246272006245)
            ·
              refine ⟨479562632810108676001171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2557667374987246272006245 479562632810108676001171)
              ·
                refine ⟨719343949215163014001757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479562632810108676001171 719343949215163014001757)
                ·
                  refine ⟨269753980955686130250659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719343949215163014001757 269753980955686130250659)
                  ·
                    rfl

theorem cell20_591012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_591012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591012 prefixEnd_591012 := by exact prefixLift 591012
  have htrace : WordTrace (prefixWord ++ tailWord_591012) baseStart_591012 baseEnd_591012 := by
    simpa [prefixWord, tailWord_591012, baseEnd_591012] using wordTrace_append hprefix tailTrace_591012
  have hstable : (prefixWord ++ tailWord_591012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591012).length < 2 ^ (prefixWord ++ tailWord_591012).sum := by decide
  have hdescent : baseEnd_591012 < baseStart_591012 := by decide
  rcases family_descends (prefixWord ++ tailWord_591012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591023 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_591023 : Nat := 118140960795 + 591023 * 2 ^ 59
def prefixEnd_591023 : Nat := 4983230072969 + 3 ^ 40 * 591023 * 2
def baseEnd_591023 : Nat := 269759001655418980883947

theorem tailTrace_591023 : CollatzResearch.WordTrace tailWord_591023 prefixEnd_591023 269759001655418980883947 := by
  unfold tailWord_591023
  simp only [CollatzResearch.WordTrace]
  refine ⟨21556379737832084537369723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14370919825221389691579815 21556379737832084537369723)
  ·
    refine ⟨32334569606748126806054585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21556379737832084537369723 32334569606748126806054585)
    ·
      refine ⟨24250927205061095104540939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32334569606748126806054585 24250927205061095104540939)
      ·
        refine ⟨36376390807591642656811409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24250927205061095104540939 36376390807591642656811409)
        ·
          refine ⟨27282293105693731992608557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36376390807591642656811409 27282293105693731992608557)
          ·
            refine ⟨10230859914635149497228209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27282293105693731992608557 10230859914635149497228209)
            ·
              refine ⟨7673144935976362122921157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10230859914635149497228209 7673144935976362122921157)
              ·
                refine ⟨1438714675495567898047717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7673144935976362122921157 1438714675495567898047717)
                ·
                  refine ⟨269759001655418980883947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1438714675495567898047717 269759001655418980883947)
                  ·
                    rfl

theorem cell20_591023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_591023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591023 prefixEnd_591023 := by exact prefixLift 591023
  have htrace : WordTrace (prefixWord ++ tailWord_591023) baseStart_591023 baseEnd_591023 := by
    simpa [prefixWord, tailWord_591023, baseEnd_591023] using wordTrace_append hprefix tailTrace_591023
  have hstable : (prefixWord ++ tailWord_591023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591023).length < 2 ^ (prefixWord ++ tailWord_591023).sum := by decide
  have hdescent : baseEnd_591023 < baseStart_591023 := by decide
  rcases family_descends (prefixWord ++ tailWord_591023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591060 : List Nat := [2, 4, 1, 4, 2, 1, 1, 5]
def baseStart_591060 : Nat := 118140960795 + 591060 * 2 ^ 59
def prefixEnd_591060 : Nat := 4983230072969 + 3 ^ 40 * 591060 * 2
def baseEnd_591060 : Nat := 89925296487870432216821

theorem tailTrace_591060 : CollatzResearch.WordTrace tailWord_591060 prefixEnd_591060 89925296487870432216821 := by
  unfold tailWord_591060
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778864619349019928233317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14371819492465359904311089 10778864619349019928233317)
  ·
    refine ⟨2021037116127941236543747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10778864619349019928233317 2021037116127941236543747)
    ·
      refine ⟨3031555674191911854815621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2021037116127941236543747 3031555674191911854815621)
      ·
        refine ⟨568416688910983472777929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3031555674191911854815621 568416688910983472777929)
        ·
          refine ⟨426312516683237604583447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568416688910983472777929 426312516683237604583447)
          ·
            refine ⟨639468775024856406875171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426312516683237604583447 639468775024856406875171)
            ·
              refine ⟨959203162537284610312757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639468775024856406875171 959203162537284610312757)
              ·
                refine ⟨89925296487870432216821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 959203162537284610312757 89925296487870432216821)
                ·
                  rfl

theorem cell20_591060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_591060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591060 prefixEnd_591060 := by exact prefixLift 591060
  have htrace : WordTrace (prefixWord ++ tailWord_591060) baseStart_591060 baseEnd_591060 := by
    simpa [prefixWord, tailWord_591060, baseEnd_591060] using wordTrace_append hprefix tailTrace_591060
  have hstable : (prefixWord ++ tailWord_591060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591060).length < 2 ^ (prefixWord ++ tailWord_591060).sum := by decide
  have hdescent : baseEnd_591060 < baseStart_591060 := by decide
  rcases family_descends (prefixWord ++ tailWord_591060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591064 : List Nat := [2, 1, 2, 2, 5, 2, 1, 5]
def baseStart_591064 : Nat := 118140960795 + 591064 * 2 ^ 59
def prefixEnd_591064 : Nat := 4983230072969 + 3 ^ 40 * 591064 * 2
def baseEnd_591064 : Nat := 89925905057535020172371

theorem tailTrace_591064 : CollatzResearch.WordTrace tailWord_591064 prefixEnd_591064 89925905057535020172371 := by
  unfold tailWord_591064
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778937565341774269806123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14371916753789032359741497 10778937565341774269806123)
  ·
    refine ⟨16168406348012661404709185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10778937565341774269806123 16168406348012661404709185)
    ·
      refine ⟨12126304761009496053531889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16168406348012661404709185 12126304761009496053531889)
      ·
        refine ⟨9094728570757122040148917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12126304761009496053531889 9094728570757122040148917)
        ·
          refine ⟨852630803508480191263961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9094728570757122040148917 852630803508480191263961)
          ·
            refine ⟨639473102631360143447971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 852630803508480191263961 639473102631360143447971)
            ·
              refine ⟨959209653947040215171957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639473102631360143447971 959209653947040215171957)
              ·
                refine ⟨89925905057535020172371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 959209653947040215171957 89925905057535020172371)
                ·
                  rfl

theorem cell20_591064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_591064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591064 prefixEnd_591064 := by exact prefixLift 591064
  have htrace : WordTrace (prefixWord ++ tailWord_591064) baseStart_591064 baseEnd_591064 := by
    simpa [prefixWord, tailWord_591064, baseEnd_591064] using wordTrace_append hprefix tailTrace_591064
  have hstable : (prefixWord ++ tailWord_591064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591064).length < 2 ^ (prefixWord ++ tailWord_591064).sum := by decide
  have hdescent : baseEnd_591064 < baseStart_591064 := by decide
  rcases family_descends (prefixWord ++ tailWord_591064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591116 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_591116 : Nat := 118140960795 + 591116 * 2 ^ 59
def prefixEnd_591116 : Nat := 4983230072969 + 3 ^ 40 * 591116 * 2
def baseEnd_591116 : Nat := 269801449389523990783567

theorem tailTrace_591116 : CollatzResearch.WordTrace tailWord_591116 prefixEnd_591116 269801449389523990783567 := by
  unfold tailWord_591116
  simp only [CollatzResearch.WordTrace]
  refine ⟨10779885863247580710252601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14373181150996774280336801 10779885863247580710252601)
  ·
    refine ⟨8084914397435685532689451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10779885863247580710252601 8084914397435685532689451)
    ·
      refine ⟨12127371596153528299034177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8084914397435685532689451 12127371596153528299034177)
      ·
        refine ⟨9095528697115146224275633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12127371596153528299034177 9095528697115146224275633)
        ·
          refine ⟨6821646522836359668206725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9095528697115146224275633 6821646522836359668206725)
          ·
            refine ⟨1279058723031817437788761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6821646522836359668206725 1279058723031817437788761)
            ·
              refine ⟨959294042273863078341571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279058723031817437788761 959294042273863078341571)
              ·
                refine ⟨1438941063410794617512357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959294042273863078341571 1438941063410794617512357)
                ·
                  refine ⟨269801449389523990783567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1438941063410794617512357 269801449389523990783567)
                  ·
                    rfl

theorem cell20_591116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_591116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591116 prefixEnd_591116 := by exact prefixLift 591116
  have htrace : WordTrace (prefixWord ++ tailWord_591116) baseStart_591116 baseEnd_591116 := by
    simpa [prefixWord, tailWord_591116, baseEnd_591116] using wordTrace_append hprefix tailTrace_591116
  have hstable : (prefixWord ++ tailWord_591116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591116).length < 2 ^ (prefixWord ++ tailWord_591116).sum := by decide
  have hdescent : baseEnd_591116 < baseStart_591116 := by decide
  rcases family_descends (prefixWord ++ tailWord_591116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591122 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_591122 : Nat := 118140960795 + 591122 * 2 ^ 59
def prefixEnd_591122 : Nat := 4983230072969 + 3 ^ 40 * 591122 * 2
def baseEnd_591122 : Nat := 269804187953014636583543

theorem tailTrace_591122 : CollatzResearch.WordTrace tailWord_591122 prefixEnd_591122 269804187953014636583543 := by
  unfold tailWord_591122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5389997641118356111305905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14373327042982282963482413 5389997641118356111305905)
  ·
    refine ⟨4042498230838767083479429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5389997641118356111305905 4042498230838767083479429)
    ·
      refine ⟨757968418282268828152393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4042498230838767083479429 757968418282268828152393)
      ·
        refine ⟨568476313711701621114295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 757968418282268828152393 568476313711701621114295)
        ·
          refine ⟨852714470567552431671443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568476313711701621114295 852714470567552431671443)
          ·
            refine ⟨1279071705851328647507165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852714470567552431671443 1279071705851328647507165)
            ·
              refine ⟨479651889694248242815187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1279071705851328647507165 479651889694248242815187)
              ·
                refine ⟨719477834541372364222781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479651889694248242815187 719477834541372364222781)
                ·
                  refine ⟨269804187953014636583543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719477834541372364222781 269804187953014636583543)
                  ·
                    rfl

theorem cell20_591122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_591122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591122 prefixEnd_591122 := by exact prefixLift 591122
  have htrace : WordTrace (prefixWord ++ tailWord_591122) baseStart_591122 baseEnd_591122 := by
    simpa [prefixWord, tailWord_591122, baseEnd_591122] using wordTrace_append hprefix tailTrace_591122
  have hstable : (prefixWord ++ tailWord_591122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591122).length < 2 ^ (prefixWord ++ tailWord_591122).sum := by decide
  have hdescent : baseEnd_591122 < baseStart_591122 := by decide
  rcases family_descends (prefixWord ++ tailWord_591122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591168 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_591168 : Nat := 118140960795 + 591168 * 2 ^ 59
def prefixEnd_591168 : Nat := 4983230072969 + 3 ^ 40 * 591168 * 2
def baseEnd_591168 : Nat := 269825183606442921050021

theorem tailTrace_591168 : CollatzResearch.WordTrace tailWord_591168 prefixEnd_591168 269825183606442921050021 := by
  unfold tailWord_591168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10780834161153387150699079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14374445548204516200932105 10780834161153387150699079)
  ·
    refine ⟨16171251241730080726048619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10780834161153387150699079 16171251241730080726048619)
    ·
      refine ⟨24256876862595121089072929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16171251241730080726048619 24256876862595121089072929)
      ·
        refine ⟨18192657646946340816804697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24256876862595121089072929 18192657646946340816804697)
        ·
          refine ⟨13644493235209755612603523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18192657646946340816804697 13644493235209755612603523)
          ·
            refine ⟨20466739852814633418905285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13644493235209755612603523 20466739852814633418905285)
            ·
              refine ⟨3837513722402743766044741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20466739852814633418905285 3837513722402743766044741)
              ·
                refine ⟨719533822950514456133389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3837513722402743766044741 719533822950514456133389)
                ·
                  refine ⟨269825183606442921050021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719533822950514456133389 269825183606442921050021)
                  ·
                    rfl

theorem cell20_591168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_591168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591168 prefixEnd_591168 := by exact prefixLift 591168
  have htrace : WordTrace (prefixWord ++ tailWord_591168) baseStart_591168 baseEnd_591168 := by
    simpa [prefixWord, tailWord_591168, baseEnd_591168] using wordTrace_append hprefix tailTrace_591168
  have hstable : (prefixWord ++ tailWord_591168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591168).length < 2 ^ (prefixWord ++ tailWord_591168).sum := by decide
  have hdescent : baseEnd_591168 < baseStart_591168 := by decide
  rcases family_descends (prefixWord ++ tailWord_591168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591174 : List Nat := [6, 1, 1, 3, 1, 1, 2, 5]
def baseStart_591174 : Nat := 118140960795 + 591174 * 2 ^ 59
def prefixEnd_591174 : Nat := 4983230072969 + 3 ^ 40 * 591174 * 2
def baseEnd_591174 : Nat := 89942640723311188949999

theorem tailTrace_591174 : CollatzResearch.WordTrace tailWord_591174 prefixEnd_591174 89942640723311188949999 := by
  unfold tailWord_591174
  simp only [CollatzResearch.WordTrace]
  refine ⟨673808973758907416441143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14374591440190024884077717 673808973758907416441143)
  ·
    refine ⟨1010713460638361124661715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673808973758907416441143 1010713460638361124661715)
    ·
      refine ⟨1516070190957541686992573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010713460638361124661715 1516070190957541686992573)
      ·
        refine ⟨568526321609078132622215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1516070190957541686992573 568526321609078132622215)
        ·
          refine ⟨852789482413617198933323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568526321609078132622215 852789482413617198933323)
          ·
            refine ⟨1279184223620425798399985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852789482413617198933323 1279184223620425798399985)
            ·
              refine ⟨959388167715319348799989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279184223620425798399985 959388167715319348799989)
              ·
                refine ⟨89942640723311188949999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 959388167715319348799989 89942640723311188949999)
                ·
                  rfl

theorem cell20_591174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_591174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591174 prefixEnd_591174 := by exact prefixLift 591174
  have htrace : WordTrace (prefixWord ++ tailWord_591174) baseStart_591174 baseEnd_591174 := by
    simpa [prefixWord, tailWord_591174, baseEnd_591174] using wordTrace_append hprefix tailTrace_591174
  have hstable : (prefixWord ++ tailWord_591174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591174).length < 2 ^ (prefixWord ++ tailWord_591174).sum := by decide
  have hdescent : baseEnd_591174 < baseStart_591174 := by decide
  rcases family_descends (prefixWord ++ tailWord_591174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591181 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 3]
def baseStart_591181 : Nat := 118140960795 + 591181 * 2 ^ 59
def prefixEnd_591181 : Nat := 4983230072969 + 3 ^ 40 * 591181 * 2
def baseEnd_591181 : Nat := 269831117160672653616635

theorem tailTrace_591181 : CollatzResearch.WordTrace tailWord_591181 prefixEnd_591181 269831117160672653616635 := by
  unfold tailWord_591181
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562142471259677521621397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14374761647506451681080931 21562142471259677521621397)
  ·
    refine ⟨1010725428340297383826003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21562142471259677521621397 1010725428340297383826003)
    ·
      refine ⟨1516088142510446075739005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010725428340297383826003 1516088142510446075739005)
      ·
        refine ⟨568533053441417278402127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1516088142510446075739005 568533053441417278402127)
        ·
          refine ⟨852799580162125917603191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568533053441417278402127 852799580162125917603191)
          ·
            refine ⟨1279199370243188876404787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852799580162125917603191 1279199370243188876404787)
            ·
              refine ⟨1918799055364783314607181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279199370243188876404787 1918799055364783314607181)
              ·
                refine ⟨719549645761793742977693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1918799055364783314607181 719549645761793742977693)
                ·
                  refine ⟨269831117160672653616635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719549645761793742977693 269831117160672653616635)
                  ·
                    rfl

theorem cell20_591181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_591181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591181 prefixEnd_591181 := by exact prefixLift 591181
  have htrace : WordTrace (prefixWord ++ tailWord_591181) baseStart_591181 baseEnd_591181 := by
    simpa [prefixWord, tailWord_591181, baseEnd_591181] using wordTrace_append hprefix tailTrace_591181
  have hstable : (prefixWord ++ tailWord_591181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591181).length < 2 ^ (prefixWord ++ tailWord_591181).sum := by decide
  have hdescent : baseEnd_591181 < baseStart_591181 := by decide
  rcases family_descends (prefixWord ++ tailWord_591181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591233 : List Nat := [1, 2, 4, 3, 3, 1, 1, 5]
def baseStart_591233 : Nat := 118140960795 + 591233 * 2 ^ 59
def prefixEnd_591233 : Nat := 4983230072969 + 3 ^ 40 * 591233 * 2
def baseEnd_591233 : Nat := 89951617125863861294363

theorem tailTrace_591233 : CollatzResearch.WordTrace tailWord_591233 prefixEnd_591233 89951617125863861294363 := by
  unfold tailWord_591233
  simp only [CollatzResearch.WordTrace]
  refine ⟨21564039067071290402514353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14376026044714193601676235 21564039067071290402514353)
  ·
    refine ⟨16173029300303467801885765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21564039067071290402514353 16173029300303467801885765)
    ·
      refine ⟨3032442993806900212853581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16173029300303467801885765 3032442993806900212853581)
      ·
        refine ⟨1137166122677587579820093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3032442993806900212853581 1137166122677587579820093)
        ·
          refine ⟨426437296004095342432535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1137166122677587579820093 426437296004095342432535)
          ·
            refine ⟨639655944006143013648803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426437296004095342432535 639655944006143013648803)
            ·
              refine ⟨959483916009214520473205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639655944006143013648803 959483916009214520473205)
              ·
                refine ⟨89951617125863861294363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 959483916009214520473205 89951617125863861294363)
                ·
                  rfl

theorem cell20_591233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 5].length) (baseStart_591233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591233 prefixEnd_591233 := by exact prefixLift 591233
  have htrace : WordTrace (prefixWord ++ tailWord_591233) baseStart_591233 baseEnd_591233 := by
    simpa [prefixWord, tailWord_591233, baseEnd_591233] using wordTrace_append hprefix tailTrace_591233
  have hstable : (prefixWord ++ tailWord_591233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591233).length < 2 ^ (prefixWord ++ tailWord_591233).sum := by decide
  have hdescent : baseEnd_591233 < baseStart_591233 := by decide
  rcases family_descends (prefixWord ++ tailWord_591233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591244 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_591244 : Nat := 118140960795 + 591244 * 2 ^ 59
def prefixEnd_591244 : Nat := 4983230072969 + 3 ^ 40 * 591244 * 2
def baseEnd_591244 : Nat := 269859872077324434516377

theorem tailTrace_591244 : CollatzResearch.WordTrace tailWord_591244 prefixEnd_591244 269859872077324434516377 := by
  unfold tailWord_591244
  simp only [CollatzResearch.WordTrace]
  refine ⟨10782220135015719640582393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14376293513354292854109857 10782220135015719640582393)
  ·
    refine ⟨8086665101261789730436795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10782220135015719640582393 8086665101261789730436795)
    ·
      refine ⟨12129997651892684595655193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8086665101261789730436795 12129997651892684595655193)
      ·
        refine ⟨9097498238919513446741395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12129997651892684595655193 9097498238919513446741395)
        ·
          refine ⟨13646247358379270170112093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9097498238919513446741395 13646247358379270170112093)
          ·
            refine ⟨5117342759392226313792035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13646247358379270170112093 5117342759392226313792035)
            ·
              refine ⟨7676014139088339470688053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117342759392226313792035 7676014139088339470688053)
              ·
                refine ⟨719626325539531825377005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7676014139088339470688053 719626325539531825377005)
                ·
                  refine ⟨269859872077324434516377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719626325539531825377005 269859872077324434516377)
                  ·
                    rfl

theorem cell20_591244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_591244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591244 prefixEnd_591244 := by exact prefixLift 591244
  have htrace : WordTrace (prefixWord ++ tailWord_591244) baseStart_591244 baseEnd_591244 := by
    simpa [prefixWord, tailWord_591244, baseEnd_591244] using wordTrace_append hprefix tailTrace_591244
  have hstable : (prefixWord ++ tailWord_591244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591244).length < 2 ^ (prefixWord ++ tailWord_591244).sum := by decide
  have hdescent : baseEnd_591244 < baseStart_591244 := by decide
  rcases family_descends (prefixWord ++ tailWord_591244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591282 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_591282 : Nat := 118140960795 + 591282 * 2 ^ 59
def prefixEnd_591282 : Nat := 4983230072969 + 3 ^ 40 * 591282 * 2
def baseEnd_591282 : Nat := 269877216312765191249555

theorem tailTrace_591282 : CollatzResearch.WordTrace tailWord_591282 prefixEnd_591282 269877216312765191249555 := by
  unfold tailWord_591282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391456560973442942762025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14377217495929181180698733 5391456560973442942762025)
  ·
    refine ⟨4043592420730082207071519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5391456560973442942762025 4043592420730082207071519)
    ·
      refine ⟨6065388631095123310607279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4043592420730082207071519 6065388631095123310607279)
      ·
        refine ⟨9098082946642684965910919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6065388631095123310607279 9098082946642684965910919)
        ·
          refine ⟨13647124419964027448866379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9098082946642684965910919 13647124419964027448866379)
          ·
            refine ⟨20470686629946041173299569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13647124419964027448866379 20470686629946041173299569)
            ·
              refine ⟨15353014972459530879974677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20470686629946041173299569 15353014972459530879974677)
              ·
                refine ⟨719672576834040509998813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15353014972459530879974677 719672576834040509998813)
                ·
                  refine ⟨269877216312765191249555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719672576834040509998813 269877216312765191249555)
                  ·
                    rfl

theorem cell20_591282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_591282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591282 prefixEnd_591282 := by exact prefixLift 591282
  have htrace : WordTrace (prefixWord ++ tailWord_591282) baseStart_591282 baseEnd_591282 := by
    simpa [prefixWord, tailWord_591282, baseEnd_591282] using wordTrace_append hprefix tailTrace_591282
  have hstable : (prefixWord ++ tailWord_591282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591282).length < 2 ^ (prefixWord ++ tailWord_591282).sum := by decide
  have hdescent : baseEnd_591282 < baseStart_591282 := by decide
  rcases family_descends (prefixWord ++ tailWord_591282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591285 : List Nat := [1, 3, 3, 2, 2, 1, 2, 4, 2]
def baseStart_591285 : Nat := 118140960795 + 591285 * 2 ^ 59
def prefixEnd_591285 : Nat := 4983230072969 + 3 ^ 40 * 591285 * 2
def baseEnd_591285 : Nat := 269878585594510514149543

theorem tailTrace_591285 : CollatzResearch.WordTrace tailWord_591285 prefixEnd_591285 269878585594510514149543 := by
  unfold tailWord_591285
  simp only [CollatzResearch.WordTrace]
  refine ⟨21565935662882903283407309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14377290441921935522271539 21565935662882903283407309)
  ·
    refine ⟨8087225873581088731277741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21565935662882903283407309 8087225873581088731277741)
    ·
      refine ⟨3032709702592908274229153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8087225873581088731277741 3032709702592908274229153)
      ·
        refine ⟨2274532276944681205671865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3032709702592908274229153 2274532276944681205671865)
        ·
          refine ⟨1705899207708510904253899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2274532276944681205671865 1705899207708510904253899)
          ·
            refine ⟨2558848811562766356380849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705899207708510904253899 2558848811562766356380849)
            ·
              refine ⟨1919136608672074767285637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558848811562766356380849 1919136608672074767285637)
              ·
                refine ⟨359838114126014018866057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1919136608672074767285637 359838114126014018866057)
                ·
                  refine ⟨269878585594510514149543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359838114126014018866057 269878585594510514149543)
                  ·
                    rfl

theorem cell20_591285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_591285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591285 prefixEnd_591285 := by exact prefixLift 591285
  have htrace : WordTrace (prefixWord ++ tailWord_591285) baseStart_591285 baseEnd_591285 := by
    simpa [prefixWord, tailWord_591285, baseEnd_591285] using wordTrace_append hprefix tailTrace_591285
  have hstable : (prefixWord ++ tailWord_591285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591285).length < 2 ^ (prefixWord ++ tailWord_591285).sum := by decide
  have hdescent : baseEnd_591285 < baseStart_591285 := by decide
  rcases family_descends (prefixWord ++ tailWord_591285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591344 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_591344 : Nat := 118140960795 + 591344 * 2 ^ 59
def prefixEnd_591344 : Nat := 4983230072969 + 3 ^ 40 * 591344 * 2
def baseEnd_591344 : Nat := 269905514802168531182635

theorem tailTrace_591344 : CollatzResearch.WordTrace tailWord_591344 prefixEnd_591344 269905514802168531182635 := by
  unfold tailWord_591344
  simp only [CollatzResearch.WordTrace]
  refine ⟨10784043784834578179902543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14378725046446104239870057 10784043784834578179902543)
  ·
    refine ⟨16176065677251867269853815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10784043784834578179902543 16176065677251867269853815)
    ·
      refine ⟨24264098515877800904780723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16176065677251867269853815 24264098515877800904780723)
      ·
        refine ⟨36396147773816701357171085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24264098515877800904780723 36396147773816701357171085)
        ·
          refine ⟨13648555415181263008939157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36396147773816701357171085 13648555415181263008939157)
          ·
            refine ⟨639776035086621703544023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13648555415181263008939157 639776035086621703544023)
            ·
              refine ⟨959664052629932555316035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639776035086621703544023 959664052629932555316035)
              ·
                refine ⟨1439496078944898832974053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959664052629932555316035 1439496078944898832974053)
                ·
                  refine ⟨269905514802168531182635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439496078944898832974053 269905514802168531182635)
                  ·
                    rfl

theorem cell20_591344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_591344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591344 prefixEnd_591344 := by exact prefixLift 591344
  have htrace : WordTrace (prefixWord ++ tailWord_591344) baseStart_591344 baseEnd_591344 := by
    simpa [prefixWord, tailWord_591344, baseEnd_591344] using wordTrace_append hprefix tailTrace_591344
  have hstable : (prefixWord ++ tailWord_591344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591344).length < 2 ^ (prefixWord ++ tailWord_591344).sum := by decide
  have hdescent : baseEnd_591344 < baseStart_591344 := by decide
  rcases family_descends (prefixWord ++ tailWord_591344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591395 : List Nat := [1, 1, 1, 4, 6, 1, 2, 2, 2]
def baseStart_591395 : Nat := 118140960795 + 591395 * 2 ^ 59
def prefixEnd_591395 : Nat := 4983230072969 + 3 ^ 40 * 591395 * 2
def baseEnd_591395 : Nat := 269928792591839020482427

theorem tailTrace_591395 : CollatzResearch.WordTrace tailWord_591395 prefixEnd_591395 269928792591839020482427 := by
  unfold tailWord_591395
  simp only [CollatzResearch.WordTrace]
  refine ⟨21569947692484392069911639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14379965128322928046607759 21569947692484392069911639)
  ·
    refine ⟨32354921538726588104867459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21569947692484392069911639 32354921538726588104867459)
    ·
      refine ⟨48532382308089882157301189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32354921538726588104867459 48532382308089882157301189)
      ·
        refine ⟨9099821682766852904493973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48532382308089882157301189 9099821682766852904493973)
        ·
          refine ⟨426554141379696229898155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9099821682766852904493973 426554141379696229898155)
          ·
            refine ⟨639831212069544344847233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426554141379696229898155 639831212069544344847233)
            ·
              refine ⟨479873409052158258635425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639831212069544344847233 479873409052158258635425)
              ·
                refine ⟨359905056789118693976569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479873409052158258635425 359905056789118693976569)
                ·
                  refine ⟨269928792591839020482427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359905056789118693976569 269928792591839020482427)
                  ·
                    rfl

theorem cell20_591395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 2].length) (baseStart_591395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591395 prefixEnd_591395 := by exact prefixLift 591395
  have htrace : WordTrace (prefixWord ++ tailWord_591395) baseStart_591395 baseEnd_591395 := by
    simpa [prefixWord, tailWord_591395, baseEnd_591395] using wordTrace_append hprefix tailTrace_591395
  have hstable : (prefixWord ++ tailWord_591395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591395).length < 2 ^ (prefixWord ++ tailWord_591395).sum := by decide
  have hdescent : baseEnd_591395 < baseStart_591395 := by decide
  rcases family_descends (prefixWord ++ tailWord_591395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591406 : List Nat := [4, 1, 3, 1, 2, 3, 1, 5]
def baseStart_591406 : Nat := 118140960795 + 591406 * 2 ^ 59
def prefixEnd_591406 : Nat := 4983230072969 + 3 ^ 40 * 591406 * 2
def baseEnd_591406 : Nat := 89977937763857290371905

theorem tailTrace_591406 : CollatzResearch.WordTrace tailWord_591406 prefixEnd_591406 89977937763857290371905 := by
  unfold tailWord_591406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696293611930567618570259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14380232596963027299041381 2696293611930567618570259)
  ·
    refine ⟨4044440417895851427855389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2696293611930567618570259 4044440417895851427855389)
    ·
      refine ⟨1516665156710944285445771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4044440417895851427855389 1516665156710944285445771)
      ·
        refine ⟨2274997735066416428168657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516665156710944285445771 2274997735066416428168657)
        ·
          refine ⟨1706248301299812321126493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2274997735066416428168657 1706248301299812321126493)
          ·
            refine ⟨639843112987429620422435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1706248301299812321126493 639843112987429620422435)
            ·
              refine ⟨959764669481144430633653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639843112987429620422435 959764669481144430633653)
              ·
                refine ⟨89977937763857290371905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 959764669481144430633653 89977937763857290371905)
                ·
                  rfl

theorem cell20_591406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_591406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591406 prefixEnd_591406 := by exact prefixLift 591406
  have htrace : WordTrace (prefixWord ++ tailWord_591406) baseStart_591406 baseEnd_591406 := by
    simpa [prefixWord, tailWord_591406, baseEnd_591406] using wordTrace_append hprefix tailTrace_591406
  have hstable : (prefixWord ++ tailWord_591406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591406).length < 2 ^ (prefixWord ++ tailWord_591406).sum := by decide
  have hdescent : baseEnd_591406 < baseStart_591406 := by decide
  rcases family_descends (prefixWord ++ tailWord_591406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591420 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_591420 : Nat := 118140960795 + 591420 * 2 ^ 59
def prefixEnd_591420 : Nat := 4983230072969 + 3 ^ 40 * 591420 * 2
def baseEnd_591420 : Nat := 269940203273050044648991

theorem tailTrace_591420 : CollatzResearch.WordTrace tailWord_591420 prefixEnd_591420 269940203273050044648991 := by
  unfold tailWord_591420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10785429758696910669785857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14380573011595880893047809 10785429758696910669785857)
  ·
    refine ⟨8089072319022683002339393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10785429758696910669785857 8089072319022683002339393)
    ·
      refine ⟨6066804239267012251754545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8089072319022683002339393 6066804239267012251754545)
      ·
        refine ⟨4550103179450259188815909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6066804239267012251754545 4550103179450259188815909)
        ·
          refine ⟨853144346146923597902983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4550103179450259188815909 853144346146923597902983)
          ·
            refine ⟨1279716519220385396854475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853144346146923597902983 1279716519220385396854475)
            ·
              refine ⟨1919574778830578095281713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279716519220385396854475 1919574778830578095281713)
              ·
                refine ⟨1439681084122933571461285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919574778830578095281713 1439681084122933571461285)
                ·
                  refine ⟨269940203273050044648991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439681084122933571461285 269940203273050044648991)
                  ·
                    rfl

theorem cell20_591420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_591420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591420 prefixEnd_591420 := by exact prefixLift 591420
  have htrace : WordTrace (prefixWord ++ tailWord_591420) baseStart_591420 baseEnd_591420 := by
    simpa [prefixWord, tailWord_591420, baseEnd_591420] using wordTrace_append hprefix tailTrace_591420
  have hstable : (prefixWord ++ tailWord_591420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591420).length < 2 ^ (prefixWord ++ tailWord_591420).sum := by decide
  have hdescent : baseEnd_591420 < baseStart_591420 := by decide
  rcases family_descends (prefixWord ++ tailWord_591420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591492 : List Nat := [2, 3, 2, 1, 4, 2, 1, 3, 2]
def baseStart_591492 : Nat := 118140960795 + 591492 * 2 ^ 59
def prefixEnd_591492 : Nat := 4983230072969 + 3 ^ 40 * 591492 * 2
def baseEnd_591492 : Nat := 269973066034937794248697

theorem tailTrace_591492 : CollatzResearch.WordTrace tailWord_591492 prefixEnd_591492 269973066034937794248697 := by
  unfold tailWord_591492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786742786566488818096365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14382323715421985090795153 10786742786566488818096365)
  ·
    refine ⟨4045028544962433306786137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10786742786566488818096365 4045028544962433306786137)
    ·
      refine ⟨3033771408721824980089603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4045028544962433306786137 3033771408721824980089603)
      ·
        refine ⟨4550657113082737470134405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3033771408721824980089603 4550657113082737470134405)
        ·
          refine ⟨853248208703013275650201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4550657113082737470134405 853248208703013275650201)
          ·
            refine ⟨639936156527259956737651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853248208703013275650201 639936156527259956737651)
            ·
              refine ⟨959904234790889935106477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639936156527259956737651 959904234790889935106477)
              ·
                refine ⟨359964088046583725664929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 959904234790889935106477 359964088046583725664929)
                ·
                  refine ⟨269973066034937794248697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359964088046583725664929 269973066034937794248697)
                  ·
                    rfl

theorem cell20_591492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_591492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591492 prefixEnd_591492 := by exact prefixLift 591492
  have htrace : WordTrace (prefixWord ++ tailWord_591492) baseStart_591492 baseEnd_591492 := by
    simpa [prefixWord, tailWord_591492, baseEnd_591492] using wordTrace_append hprefix tailTrace_591492
  have hstable : (prefixWord ++ tailWord_591492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591492).length < 2 ^ (prefixWord ++ tailWord_591492).sum := by decide
  have hdescent : baseEnd_591492 < baseStart_591492 := by decide
  rcases family_descends (prefixWord ++ tailWord_591492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591493 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_591493 : Nat := 118140960795 + 591493 * 2 ^ 59
def prefixEnd_591493 : Nat := 4983230072969 + 3 ^ 40 * 591493 * 2
def baseEnd_591493 : Nat := 269973522462186235215359

theorem tailTrace_591493 : CollatzResearch.WordTrace tailWord_591493 prefixEnd_591493 269973522462186235215359 := by
  unfold tailWord_591493
  simp only [CollatzResearch.WordTrace]
  refine ⟨21573522046129354806979133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14382348030752903204652755 21573522046129354806979133)
  ·
    refine ⟨8090070767298508052617175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21573522046129354806979133 8090070767298508052617175)
    ·
      refine ⟨12135106150947762078925763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8090070767298508052617175 12135106150947762078925763)
      ·
        refine ⟨18202659226421643118388645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12135106150947762078925763 18202659226421643118388645)
        ·
          refine ⟨3412998604954058084697871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18202659226421643118388645 3412998604954058084697871)
          ·
            refine ⟨5119497907431087127046807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412998604954058084697871 5119497907431087127046807)
            ·
              refine ⟨7679246861146630690570211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119497907431087127046807 7679246861146630690570211)
              ·
                refine ⟨11518870291719946035855317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7679246861146630690570211 11518870291719946035855317)
                ·
                  refine ⟨269973522462186235215359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11518870291719946035855317 269973522462186235215359)
                  ·
                    rfl

theorem cell20_591493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_591493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591493 prefixEnd_591493 := by exact prefixLift 591493
  have htrace : WordTrace (prefixWord ++ tailWord_591493) baseStart_591493 baseEnd_591493 := by
    simpa [prefixWord, tailWord_591493, baseEnd_591493] using wordTrace_append hprefix tailTrace_591493
  have hstable : (prefixWord ++ tailWord_591493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591493).length < 2 ^ (prefixWord ++ tailWord_591493).sum := by decide
  have hdescent : baseEnd_591493 < baseStart_591493 := by decide
  rcases family_descends (prefixWord ++ tailWord_591493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591524 : List Nat := [2, 3, 1, 2, 2, 2, 1, 7]
def baseStart_591524 : Nat := 118140960795 + 591524 * 2 ^ 59
def prefixEnd_591524 : Nat := 4983230072969 + 3 ^ 40 * 591524 * 2
def baseEnd_591524 : Nat := 89995890568962635060633

theorem tailTrace_591524 : CollatzResearch.WordTrace tailWord_591524 prefixEnd_591524 89995890568962635060633 := by
  unfold tailWord_591524
  simp only [CollatzResearch.WordTrace]
  refine ⟨10787326354508523550678813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14383101806011364734238417 10787326354508523550678813)
  ·
    refine ⟨4045247382940696331504555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10787326354508523550678813 4045247382940696331504555)
    ·
      refine ⟨6067871074411044497256833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4045247382940696331504555 6067871074411044497256833)
      ·
        refine ⟨4550903305808283372942625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6067871074411044497256833 4550903305808283372942625)
        ·
          refine ⟨3413177479356212529706969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4550903305808283372942625 3413177479356212529706969)
          ·
            refine ⟨2559883109517159397280227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3413177479356212529706969 2559883109517159397280227)
            ·
              refine ⟨3839824664275739095920341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559883109517159397280227 3839824664275739095920341)
              ·
                refine ⟨89995890568962635060633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3839824664275739095920341 89995890568962635060633)
                ·
                  rfl

theorem cell20_591524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_591524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591524 prefixEnd_591524 := by exact prefixLift 591524
  have htrace : WordTrace (prefixWord ++ tailWord_591524) baseStart_591524 baseEnd_591524 := by
    simpa [prefixWord, tailWord_591524, baseEnd_591524] using wordTrace_append hprefix tailTrace_591524
  have hstable : (prefixWord ++ tailWord_591524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591524).length < 2 ^ (prefixWord ++ tailWord_591524).sum := by decide
  have hdescent : baseEnd_591524 < baseStart_591524 := by decide
  rcases family_descends (prefixWord ++ tailWord_591524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591558 : List Nat := [6, 1, 2, 1, 1, 9]
def baseStart_591558 : Nat := 118140960795 + 591558 * 2 ^ 59
def prefixEnd_591558 : Nat := 4983230072969 + 3 ^ 40 * 591558 * 2
def baseEnd_591558 : Nat := 10000118156790181409201

theorem tailTrace_591558 : CollatzResearch.WordTrace tailWord_591558 prefixEnd_591558 10000118156790181409201 := by
  unfold tailWord_591558
  simp only [CollatzResearch.WordTrace]
  refine ⟨674246649715433465877979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14383928527262580605396885 674246649715433465877979)
  ·
    refine ⟨1011369974573150198816969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674246649715433465877979 1011369974573150198816969)
    ·
      refine ⟨758527480929862649112727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1011369974573150198816969 758527480929862649112727)
      ·
        refine ⟨1137791221394793973669091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758527480929862649112727 1137791221394793973669091)
        ·
          refine ⟨1706686832092190960503637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137791221394793973669091 1706686832092190960503637)
          ·
            refine ⟨10000118156790181409201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1706686832092190960503637 10000118156790181409201)
            ·
              rfl

theorem cell20_591558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 9].length) (baseStart_591558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591558 prefixEnd_591558 := by exact prefixLift 591558
  have htrace : WordTrace (prefixWord ++ tailWord_591558) baseStart_591558 baseEnd_591558 := by
    simpa [prefixWord, tailWord_591558, baseEnd_591558] using wordTrace_append hprefix tailTrace_591558
  have hstable : (prefixWord ++ tailWord_591558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591558).length < 2 ^ (prefixWord ++ tailWord_591558).sum := by decide
  have hdescent : baseEnd_591558 < baseStart_591558 := by decide
  rcases family_descends (prefixWord ++ tailWord_591558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591562 : List Nat := [3, 1, 2, 1, 5, 8]
def baseStart_591562 : Nat := 118140960795 + 591562 * 2 ^ 59
def prefixEnd_591562 : Nat := 4983230072969 + 3 ^ 40 * 591562 * 2
def baseEnd_591562 : Nat := 10000185775641802293151

theorem tailTrace_591562 : CollatzResearch.WordTrace tailWord_591562 prefixEnd_591562 10000185775641802293151 := by
  unfold tailWord_591562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394009670719844897810235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14384025788586253060827293 5394009670719844897810235)
  ·
    refine ⟨8091014506079767346715353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5394009670719844897810235 8091014506079767346715353)
    ·
      refine ⟨6068260879559825510036515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8091014506079767346715353 6068260879559825510036515)
      ·
        refine ⟨9102391319339738265054773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068260879559825510036515 9102391319339738265054773)
        ·
          refine ⟨853349186188100462348885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9102391319339738265054773 853349186188100462348885)
          ·
            refine ⟨10000185775641802293151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 853349186188100462348885 10000185775641802293151)
            ·
              rfl

theorem cell20_591562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 8].length) (baseStart_591562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591562 prefixEnd_591562 := by exact prefixLift 591562
  have htrace : WordTrace (prefixWord ++ tailWord_591562) baseStart_591562 baseEnd_591562 := by
    simpa [prefixWord, tailWord_591562, baseEnd_591562] using wordTrace_append hprefix tailTrace_591562
  have hstable : (prefixWord ++ tailWord_591562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591562).length < 2 ^ (prefixWord ++ tailWord_591562).sum := by decide
  have hdescent : baseEnd_591562 < baseStart_591562 := by decide
  rcases family_descends (prefixWord ++ tailWord_591562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591665 : List Nat := [1, 2, 2, 3, 2, 4, 1, 3, 2]
def baseStart_591665 : Nat := 118140960795 + 591665 * 2 ^ 59
def prefixEnd_591665 : Nat := 4983230072969 + 3 ^ 40 * 591665 * 2
def baseEnd_591665 : Nat := 270052027948918081481323

theorem tailTrace_591665 : CollatzResearch.WordTrace tailWord_591665 prefixEnd_591665 270052027948918081481323 := by
  unfold tailWord_591665
  simp only [CollatzResearch.WordTrace]
  refine ⟨21579795401506228182240449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14386530267670818788160299 21579795401506228182240449)
  ·
    refine ⟨16184846551129671136680337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21579795401506228182240449 16184846551129671136680337)
    ·
      refine ⟨12138634913347253352510253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16184846551129671136680337 12138634913347253352510253)
      ·
        refine ⟨4551988092505220007191345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12138634913347253352510253 4551988092505220007191345)
        ·
          refine ⟨3413991069378915005393509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4551988092505220007191345 3413991069378915005393509)
          ·
            refine ⟨640123325508546563511283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3413991069378915005393509 640123325508546563511283)
            ·
              refine ⟨960184988262819845266925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640123325508546563511283 960184988262819845266925)
              ·
                refine ⟨360069370598557441975097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 960184988262819845266925 360069370598557441975097)
                ·
                  refine ⟨270052027948918081481323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360069370598557441975097 270052027948918081481323)
                  ·
                    rfl

theorem cell20_591665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_591665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591665 prefixEnd_591665 := by exact prefixLift 591665
  have htrace : WordTrace (prefixWord ++ tailWord_591665) baseStart_591665 baseEnd_591665 := by
    simpa [prefixWord, tailWord_591665, baseEnd_591665] using wordTrace_append hprefix tailTrace_591665
  have hstable : (prefixWord ++ tailWord_591665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591665).length < 2 ^ (prefixWord ++ tailWord_591665).sum := by decide
  have hdescent : baseEnd_591665 < baseStart_591665 := by decide
  rcases family_descends (prefixWord ++ tailWord_591665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591683 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_591683 : Nat := 118140960795 + 591683 * 2 ^ 59
def prefixEnd_591683 : Nat := 4983230072969 + 3 ^ 40 * 591683 * 2
def baseEnd_591683 : Nat := 270060243639390018881249

theorem tailTrace_591683 : CollatzResearch.WordTrace tailWord_591683 prefixEnd_591683 270060243639390018881249 := by
  unfold tailWord_591683
  simp only [CollatzResearch.WordTrace]
  refine ⟨21580451915441017256395703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14386967943627344837597135 21580451915441017256395703)
  ·
    refine ⟨32370677873161525884593555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21580451915441017256395703 32370677873161525884593555)
    ·
      refine ⟨48556016809742288826890333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32370677873161525884593555 48556016809742288826890333)
      ·
        refine ⟨18208506303653358310083875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48556016809742288826890333 18208506303653358310083875)
        ·
          refine ⟨27312759455480037465125813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18208506303653358310083875 27312759455480037465125813)
          ·
            refine ⟨2560571198951253512355545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27312759455480037465125813 2560571198951253512355545)
            ·
              refine ⟨1920428399213440134266659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560571198951253512355545 1920428399213440134266659)
              ·
                refine ⟨2880642598820160201399989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920428399213440134266659 2880642598820160201399989)
                ·
                  refine ⟨270060243639390018881249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2880642598820160201399989 270060243639390018881249)
                  ·
                    rfl

theorem cell20_591683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_591683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591683 prefixEnd_591683 := by exact prefixLift 591683
  have htrace : WordTrace (prefixWord ++ tailWord_591683) baseStart_591683 baseEnd_591683 := by
    simpa [prefixWord, tailWord_591683, baseEnd_591683] using wordTrace_append hprefix tailTrace_591683
  have hstable : (prefixWord ++ tailWord_591683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591683).length < 2 ^ (prefixWord ++ tailWord_591683).sum := by decide
  have hdescent : baseEnd_591683 < baseStart_591683 := by decide
  rcases family_descends (prefixWord ++ tailWord_591683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591693 : List Nat := [1, 6, 1, 2, 1, 1, 1, 7]
def baseStart_591693 : Nat := 118140960795 + 591693 * 2 ^ 59
def prefixEnd_591693 : Nat := 4983230072969 + 3 ^ 40 * 591693 * 2
def baseEnd_591693 : Nat := 90021602637291476182625

theorem tailTrace_591693 : CollatzResearch.WordTrace tailWord_591693 prefixEnd_591693 90021602637291476182625 := by
  unfold tailWord_591693
  simp only [CollatzResearch.WordTrace]
  refine ⟨21580816645404788964259733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14387211096936525976173155 21580816645404788964259733)
  ·
    refine ⟨1011600780253349482699675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21580816645404788964259733 1011600780253349482699675)
    ·
      refine ⟨1517401170380024224049513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011600780253349482699675 1517401170380024224049513)
      ·
        refine ⟨1138050877785018168037135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1517401170380024224049513 1138050877785018168037135)
        ·
          refine ⟨1707076316677527252055703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138050877785018168037135 1707076316677527252055703)
          ·
            refine ⟨2560614475016290878083555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707076316677527252055703 2560614475016290878083555)
            ·
              refine ⟨3840921712524436317125333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560614475016290878083555 3840921712524436317125333)
              ·
                refine ⟨90021602637291476182625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3840921712524436317125333 90021602637291476182625)
                ·
                  rfl

theorem cell20_591693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_591693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591693 prefixEnd_591693 := by exact prefixLift 591693
  have htrace : WordTrace (prefixWord ++ tailWord_591693) baseStart_591693 baseEnd_591693 := by
    simpa [prefixWord, tailWord_591693, baseEnd_591693] using wordTrace_append hprefix tailTrace_591693
  have hstable : (prefixWord ++ tailWord_591693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591693).length < 2 ^ (prefixWord ++ tailWord_591693).sum := by decide
  have hdescent : baseEnd_591693 < baseStart_591693 := by decide
  rcases family_descends (prefixWord ++ tailWord_591693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591734 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_591734 : Nat := 118140960795 + 591734 * 2 ^ 59
def prefixEnd_591734 : Nat := 4983230072969 + 3 ^ 40 * 591734 * 2
def baseEnd_591734 : Nat := 270083521429060508181041

theorem tailTrace_591734 : CollatzResearch.WordTrace tailWord_591734 prefixEnd_591734 270083521429060508181041 := by
  unfold tailWord_591734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1348894502391015810406391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14388208025504168644334837 1348894502391015810406391)
  ·
    refine ⟨2023341753586523715609587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1348894502391015810406391 2023341753586523715609587)
    ·
      refine ⟨3035012630379785573414381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023341753586523715609587 3035012630379785573414381)
      ·
        refine ⟨1138129736392419590030393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3035012630379785573414381 1138129736392419590030393)
        ·
          refine ⟨853597302294314692522795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138129736392419590030393 853597302294314692522795)
          ·
            refine ⟨1280395953441472038784193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853597302294314692522795 1280395953441472038784193)
            ·
              refine ⟨960296965081104029088145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280395953441472038784193 960296965081104029088145)
              ·
                refine ⟨720222723810828021816109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960296965081104029088145 720222723810828021816109)
                ·
                  refine ⟨270083521429060508181041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720222723810828021816109 270083521429060508181041)
                  ·
                    rfl

theorem cell20_591734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_591734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591734 prefixEnd_591734 := by exact prefixLift 591734
  have htrace : WordTrace (prefixWord ++ tailWord_591734) baseStart_591734 baseEnd_591734 := by
    simpa [prefixWord, tailWord_591734, baseEnd_591734] using wordTrace_append hprefix tailTrace_591734
  have hstable : (prefixWord ++ tailWord_591734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591734).length < 2 ^ (prefixWord ++ tailWord_591734).sum := by decide
  have hdescent : baseEnd_591734 < baseStart_591734 := by decide
  rcases family_descends (prefixWord ++ tailWord_591734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591762 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_591762 : Nat := 118140960795 + 591762 * 2 ^ 59
def prefixEnd_591762 : Nat := 4983230072969 + 3 ^ 40 * 591762 * 2
def baseEnd_591762 : Nat := 270096301392016855247593

theorem tailTrace_591762 : CollatzResearch.WordTrace tailWord_591762 prefixEnd_591762 270096301392016855247593 := by
  unfold tailWord_591762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395833320538703437130385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14388888854769875832347693 5395833320538703437130385)
  ·
    refine ⟨4046874990404027577847789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5395833320538703437130385 4046874990404027577847789)
    ·
      refine ⟨1517578121401510341692921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4046874990404027577847789 1517578121401510341692921)
      ·
        refine ⟨1138183591051132756269691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1517578121401510341692921 1138183591051132756269691)
        ·
          refine ⟨1707275386576699134404537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138183591051132756269691 1707275386576699134404537)
          ·
            refine ⟨1280456539932524350803403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707275386576699134404537 1280456539932524350803403)
            ·
              refine ⟨1920684809898786526205105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280456539932524350803403 1920684809898786526205105)
              ·
                refine ⟨1440513607424089894653829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920684809898786526205105 1440513607424089894653829)
                ·
                  refine ⟨270096301392016855247593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1440513607424089894653829 270096301392016855247593)
                  ·
                    rfl

theorem cell20_591762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_591762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591762 prefixEnd_591762 := by exact prefixLift 591762
  have htrace : WordTrace (prefixWord ++ tailWord_591762) baseStart_591762 baseEnd_591762 := by
    simpa [prefixWord, tailWord_591762, baseEnd_591762] using wordTrace_append hprefix tailTrace_591762
  have hstable : (prefixWord ++ tailWord_591762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591762).length < 2 ^ (prefixWord ++ tailWord_591762).sum := by decide
  have hdescent : baseEnd_591762 < baseStart_591762 := by decide
  rcases family_descends (prefixWord ++ tailWord_591762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591793 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 3]
def baseStart_591793 : Nat := 118140960795 + 591793 * 2 ^ 59
def prefixEnd_591793 : Nat := 4983230072969 + 3 ^ 40 * 591793 * 2
def baseEnd_591793 : Nat := 270110450636718525214133

theorem tailTrace_591793 : CollatzResearch.WordTrace tailWord_591793 prefixEnd_591793 270110450636718525214133 := by
  unfold tailWord_591793
  simp only [CollatzResearch.WordTrace]
  refine ⟨21584463945042506042900033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14389642630028337361933355 21584463945042506042900033)
  ·
    refine ⟨16188347958781879532175025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21584463945042506042900033 16188347958781879532175025)
    ·
      refine ⟨12141260969086409649131269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16188347958781879532175025 12141260969086409649131269)
      ·
        refine ⟨2276486431703701809212113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12141260969086409649131269 2276486431703701809212113)
        ·
          refine ⟨1707364823777776356909085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276486431703701809212113 1707364823777776356909085)
          ·
            refine ⟨640261808916666133840907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1707364823777776356909085 640261808916666133840907)
            ·
              refine ⟨960392713374999200761361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640261808916666133840907 960392713374999200761361)
              ·
                refine ⟨720294535031249400571021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 960392713374999200761361 720294535031249400571021)
                ·
                  refine ⟨270110450636718525214133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720294535031249400571021 270110450636718525214133)
                  ·
                    rfl

theorem cell20_591793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_591793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591793 prefixEnd_591793 := by exact prefixLift 591793
  have htrace : WordTrace (prefixWord ++ tailWord_591793) baseStart_591793 baseEnd_591793 := by
    simpa [prefixWord, tailWord_591793, baseEnd_591793] using wordTrace_append hprefix tailTrace_591793
  have hstable : (prefixWord ++ tailWord_591793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591793).length < 2 ^ (prefixWord ++ tailWord_591793).sum := by decide
  have hdescent : baseEnd_591793 < baseStart_591793 := by decide
  rcases family_descends (prefixWord ++ tailWord_591793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591828 : List Nat := [2, 4, 1, 2, 1, 1, 3, 6]
def baseStart_591828 : Nat := 118140960795 + 591828 * 2 ^ 59
def prefixEnd_591828 : Nat := 4983230072969 + 3 ^ 40 * 591828 * 2
def baseEnd_591828 : Nat := 90042141863471319682441

theorem tailTrace_591828 : CollatzResearch.WordTrace tailWord_591828 prefixEnd_591828 90042141863471319682441 := by
  unfold tailWord_591828
  simp only [CollatzResearch.WordTrace]
  refine ⟨10792870249957853510212069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14390493666610471346949425 10792870249957853510212069)
  ·
    refine ⟨2023663171867097533164763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10792870249957853510212069 2023663171867097533164763)
    ·
      refine ⟨3035494757800646299747145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023663171867097533164763 3035494757800646299747145)
      ·
        refine ⟨2276621068350484724810359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3035494757800646299747145 2276621068350484724810359)
        ·
          refine ⟨3414931602525727087215539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276621068350484724810359 3414931602525727087215539)
          ·
            refine ⟨5122397403788590630823309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3414931602525727087215539 5122397403788590630823309)
            ·
              refine ⟨1920899026420721486558741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5122397403788590630823309 1920899026420721486558741)
              ·
                refine ⟨90042141863471319682441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1920899026420721486558741 90042141863471319682441)
                ·
                  rfl

theorem cell20_591828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_591828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591828 prefixEnd_591828 := by exact prefixLift 591828
  have htrace : WordTrace (prefixWord ++ tailWord_591828) baseStart_591828 baseEnd_591828 := by
    simpa [prefixWord, tailWord_591828, baseEnd_591828] using wordTrace_append hprefix tailTrace_591828
  have hstable : (prefixWord ++ tailWord_591828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591828).length < 2 ^ (prefixWord ++ tailWord_591828).sum := by decide
  have hdescent : baseEnd_591828 < baseStart_591828 := by decide
  rcases family_descends (prefixWord ++ tailWord_591828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591834 : List Nat := [3, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_591834 : Nat := 118140960795 + 591834 * 2 ^ 59
def prefixEnd_591834 : Nat := 4983230072969 + 3 ^ 40 * 591834 * 2
def baseEnd_591834 : Nat := 270129164153904604847299

theorem tailTrace_591834 : CollatzResearch.WordTrace tailWord_591834 prefixEnd_591834 270129164153904604847299 := by
  unfold tailWord_591834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5396489834473492511285639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14390639558595980030095037 5396489834473492511285639)
  ·
    refine ⟨8094734751710238766928459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5396489834473492511285639 8094734751710238766928459)
    ·
      refine ⟨12142102127565358150392689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8094734751710238766928459 12142102127565358150392689)
      ·
        refine ⟨9106576595674018612794517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12142102127565358150392689 9106576595674018612794517)
        ·
          refine ⟨426870777922219622474743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9106576595674018612794517 426870777922219622474743)
          ·
            refine ⟨640306166883329433712115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426870777922219622474743 640306166883329433712115)
            ·
              refine ⟨960459250324994150568173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640306166883329433712115 960459250324994150568173)
              ·
                refine ⟨360172218871872806463065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 960459250324994150568173 360172218871872806463065)
                ·
                  refine ⟨270129164153904604847299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360172218871872806463065 270129164153904604847299)
                  ·
                    rfl

theorem cell20_591834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_591834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591834 prefixEnd_591834 := by exact prefixLift 591834
  have htrace : WordTrace (prefixWord ++ tailWord_591834) baseStart_591834 baseEnd_591834 := by
    simpa [prefixWord, tailWord_591834, baseEnd_591834] using wordTrace_append hprefix tailTrace_591834
  have hstable : (prefixWord ++ tailWord_591834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591834).length < 2 ^ (prefixWord ++ tailWord_591834).sum := by decide
  have hdescent : baseEnd_591834 < baseStart_591834 := by decide
  rcases family_descends (prefixWord ++ tailWord_591834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591859 : List Nat := [1, 1, 1, 2, 2, 2, 1, 8, 2]
def baseStart_591859 : Nat := 118140960795 + 591859 * 2 ^ 59
def prefixEnd_591859 : Nat := 4983230072969 + 3 ^ 40 * 591859 * 2
def baseEnd_591859 : Nat := 270140574835115629013863

theorem tailTrace_591859 : CollatzResearch.WordTrace tailWord_591859 prefixEnd_591859 270140574835115629013863 := by
  unfold tailWord_591859
  simp only [CollatzResearch.WordTrace]
  refine ⟨21586871162803399314802631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14391247441868932876535087 21586871162803399314802631)
  ·
    refine ⟨32380306744205098972203947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21586871162803399314802631 32380306744205098972203947)
    ·
      refine ⟨48570460116307648458305921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32380306744205098972203947 48570460116307648458305921)
      ·
        refine ⟨36427845087230736343729441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48570460116307648458305921 36427845087230736343729441)
        ·
          refine ⟨27320883815423052257797081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36427845087230736343729441 27320883815423052257797081)
          ·
            refine ⟨20490662861567289193347811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27320883815423052257797081 20490662861567289193347811)
            ·
              refine ⟨30735994292350933790021717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20490662861567289193347811 30735994292350933790021717)
              ·
                refine ⟨360187433113487505351817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 30735994292350933790021717 360187433113487505351817)
                ·
                  refine ⟨270140574835115629013863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360187433113487505351817 270140574835115629013863)
                  ·
                    rfl

theorem cell20_591859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 2].length) (baseStart_591859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591859 prefixEnd_591859 := by exact prefixLift 591859
  have htrace : WordTrace (prefixWord ++ tailWord_591859) baseStart_591859 baseEnd_591859 := by
    simpa [prefixWord, tailWord_591859, baseEnd_591859] using wordTrace_append hprefix tailTrace_591859
  have hstable : (prefixWord ++ tailWord_591859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591859).length < 2 ^ (prefixWord ++ tailWord_591859).sum := by decide
  have hdescent : baseEnd_591859 < baseStart_591859 := by decide
  rcases family_descends (prefixWord ++ tailWord_591859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591880 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_591880 : Nat := 118140960795 + 591880 * 2 ^ 59
def prefixEnd_591880 : Nat := 4983230072969 + 3 ^ 40 * 591880 * 2
def baseEnd_591880 : Nat := 270150159807332889313777

theorem tailTrace_591880 : CollatzResearch.WordTrace tailWord_591880 prefixEnd_591880 270150159807332889313777 := by
  unfold tailWord_591880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10793818547863659950658547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14391758063818213267544729 10793818547863659950658547)
  ·
    refine ⟨16190727821795489925987821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10793818547863659950658547 16190727821795489925987821)
    ·
      refine ⟨6071522933173308722245433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16190727821795489925987821 6071522933173308722245433)
      ·
        refine ⟨4553642199879981541684075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6071522933173308722245433 4553642199879981541684075)
        ·
          refine ⟨6830463299819972312526113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4553642199879981541684075 6830463299819972312526113)
          ·
            refine ⟨5122847474864979234394585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6830463299819972312526113 5122847474864979234394585)
            ·
              refine ⟨3842135606148734425795939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5122847474864979234394585 3842135606148734425795939)
              ·
                refine ⟨5763203409223101638693909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842135606148734425795939 5763203409223101638693909)
                ·
                  refine ⟨270150159807332889313777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5763203409223101638693909 270150159807332889313777)
                  ·
                    rfl

theorem cell20_591880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_591880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591880 prefixEnd_591880 := by exact prefixLift 591880
  have htrace : WordTrace (prefixWord ++ tailWord_591880) baseStart_591880 baseEnd_591880 := by
    simpa [prefixWord, tailWord_591880, baseEnd_591880] using wordTrace_append hprefix tailTrace_591880
  have hstable : (prefixWord ++ tailWord_591880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591880).length < 2 ^ (prefixWord ++ tailWord_591880).sum := by decide
  have hdescent : baseEnd_591880 < baseStart_591880 := by decide
  rcases family_descends (prefixWord ++ tailWord_591880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591897 : List Nat := [1, 2, 1, 2, 1, 1, 3, 7, 2]
def baseStart_591897 : Nat := 118140960795 + 591897 * 2 ^ 59
def prefixEnd_591897 : Nat := 4983230072969 + 3 ^ 40 * 591897 * 2
def baseEnd_591897 : Nat := 270157919070556385747041

theorem tailTrace_591897 : CollatzResearch.WordTrace tailWord_591897 prefixEnd_591897 270157919070556385747041 := by
  unfold tailWord_591897
  simp only [CollatzResearch.WordTrace]
  refine ⟨21588257136665731804685945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14392171424443821203123963 21588257136665731804685945)
  ·
    refine ⟨16191192852499298853514459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21588257136665731804685945 16191192852499298853514459)
    ·
      refine ⟨24286789278748948280271689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16191192852499298853514459 24286789278748948280271689)
      ·
        refine ⟨18215091959061711210203767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24286789278748948280271689 18215091959061711210203767)
        ·
          refine ⟨27322637938592566815305651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18215091959061711210203767 27322637938592566815305651)
          ·
            refine ⟨40983956907888850222958477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27322637938592566815305651 40983956907888850222958477)
            ·
              refine ⟨15368983840458318833609429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40983956907888850222958477 15368983840458318833609429)
              ·
                refine ⟨360210558760741847662721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15368983840458318833609429 360210558760741847662721)
                ·
                  refine ⟨270157919070556385747041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360210558760741847662721 270157919070556385747041)
                  ·
                    rfl

theorem cell20_591897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_591897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591897 prefixEnd_591897 := by exact prefixLift 591897
  have htrace : WordTrace (prefixWord ++ tailWord_591897) baseStart_591897 baseEnd_591897 := by
    simpa [prefixWord, tailWord_591897, baseEnd_591897] using wordTrace_append hprefix tailTrace_591897
  have hstable : (prefixWord ++ tailWord_591897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591897).length < 2 ^ (prefixWord ++ tailWord_591897).sum := by decide
  have hdescent : baseEnd_591897 < baseStart_591897 := by decide
  rcases family_descends (prefixWord ++ tailWord_591897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591956 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_591956 : Nat := 118140960795 + 591956 * 2 ^ 59
def prefixEnd_591956 : Nat := 4983230072969 + 3 ^ 40 * 591956 * 2
def baseEnd_591956 : Nat := 270184848278214402780133

theorem tailTrace_591956 : CollatzResearch.WordTrace tailWord_591956 prefixEnd_591956 270184848278214402780133 := by
  unfold tailWord_591956
  simp only [CollatzResearch.WordTrace]
  refine ⟨10795204521725992440541861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14393606028967989920722481 10795204521725992440541861)
  ·
    refine ⟨2024100847823623582601599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10795204521725992440541861 2024100847823623582601599)
    ·
      refine ⟨3036151271735435373902399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024100847823623582601599 3036151271735435373902399)
      ·
        refine ⟨4554226907603153060853599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036151271735435373902399 4554226907603153060853599)
        ·
          refine ⟨6831340361404729591280399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4554226907603153060853599 6831340361404729591280399)
          ·
            refine ⟨10247010542107094386920599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831340361404729591280399 10247010542107094386920599)
            ·
              refine ⟨15370515813160641580380899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10247010542107094386920599 15370515813160641580380899)
              ·
                refine ⟨23055773719740962370571349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15370515813160641580380899 23055773719740962370571349)
                ·
                  refine ⟨270184848278214402780133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23055773719740962370571349 270184848278214402780133)
                  ·
                    rfl

theorem cell20_591956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_591956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591956 prefixEnd_591956 := by exact prefixLift 591956
  have htrace : WordTrace (prefixWord ++ tailWord_591956) baseStart_591956 baseEnd_591956 := by
    simpa [prefixWord, tailWord_591956, baseEnd_591956] using wordTrace_append hprefix tailTrace_591956
  have hstable : (prefixWord ++ tailWord_591956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591956).length < 2 ^ (prefixWord ++ tailWord_591956).sum := by decide
  have hdescent : baseEnd_591956 < baseStart_591956 := by decide
  rcases family_descends (prefixWord ++ tailWord_591956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591973 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_591973 : Nat := 118140960795 + 591973 * 2 ^ 59
def prefixEnd_591973 : Nat := 4983230072969 + 3 ^ 40 * 591973 * 2
def baseEnd_591973 : Nat := 270192607541437899213397

theorem tailTrace_591973 : CollatzResearch.WordTrace tailWord_591973 prefixEnd_591973 270192607541437899213397 := by
  unfold tailWord_591973
  simp only [CollatzResearch.WordTrace]
  refine ⟨21591029084390396784452573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14394019389593597856301715 21591029084390396784452573)
  ·
    refine ⟨8096635906646398794169715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21591029084390396784452573 8096635906646398794169715)
    ·
      refine ⟨12144953859969598191254573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8096635906646398794169715 12144953859969598191254573)
      ·
        refine ⟨4554357697488599321720465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12144953859969598191254573 4554357697488599321720465)
        ·
          refine ⟨3415768273116449491290349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4554357697488599321720465 3415768273116449491290349)
          ·
            refine ⟨1280913102418668559233881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3415768273116449491290349 1280913102418668559233881)
            ·
              refine ⟨960684826814001419425411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280913102418668559233881 960684826814001419425411)
              ·
                refine ⟨1441027240221002129138117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960684826814001419425411 1441027240221002129138117)
                ·
                  refine ⟨270192607541437899213397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441027240221002129138117 270192607541437899213397)
                  ·
                    rfl

theorem cell20_591973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_591973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591973 prefixEnd_591973 := by exact prefixLift 591973
  have htrace : WordTrace (prefixWord ++ tailWord_591973) baseStart_591973 baseEnd_591973 := by
    simpa [prefixWord, tailWord_591973, baseEnd_591973] using wordTrace_append hprefix tailTrace_591973
  have hstable : (prefixWord ++ tailWord_591973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591973).length < 2 ^ (prefixWord ++ tailWord_591973).sum := by decide
  have hdescent : baseEnd_591973 < baseStart_591973 := by decide
  rcases family_descends (prefixWord ++ tailWord_591973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_591997 : List Nat := [1, 4, 1, 1, 3, 4, 2, 4]
def baseStart_591997 : Nat := 118140960795 + 591997 * 2 ^ 59
def prefixEnd_591997 : Nat := 4983230072969 + 3 ^ 40 * 591997 * 2
def baseEnd_591997 : Nat := 90067853931800160804433

theorem tailTrace_591997 : CollatzResearch.WordTrace tailWord_591997 prefixEnd_591997 90067853931800160804433 := by
  unfold tailWord_591997
  simp only [CollatzResearch.WordTrace]
  refine ⟨21591904436303448883326245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14394602957535632588884163 21591904436303448883326245)
  ·
    refine ⟨4048482081806896665623671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21591904436303448883326245 4048482081806896665623671)
    ·
      refine ⟨6072723122710344998435507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048482081806896665623671 6072723122710344998435507)
      ·
        refine ⟨9109084684065517497653261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072723122710344998435507 9109084684065517497653261)
        ·
          refine ⟨3415906756524569061619973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9109084684065517497653261 3415906756524569061619973)
          ·
            refine ⟨640482516848356699053745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3415906756524569061619973 640482516848356699053745)
            ·
              refine ⟨480361887636267524290309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640482516848356699053745 480361887636267524290309)
              ·
                refine ⟨90067853931800160804433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 480361887636267524290309 90067853931800160804433)
                ·
                  rfl

theorem cell20_591997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_591997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_591997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_591997 prefixEnd_591997 := by exact prefixLift 591997
  have htrace : WordTrace (prefixWord ++ tailWord_591997) baseStart_591997 baseEnd_591997 := by
    simpa [prefixWord, tailWord_591997, baseEnd_591997] using wordTrace_append hprefix tailTrace_591997
  have hstable : (prefixWord ++ tailWord_591997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_591997).length < 2 ^ (prefixWord ++ tailWord_591997).sum := by decide
  have hdescent : baseEnd_591997 < baseStart_591997 := by decide
  rcases family_descends (prefixWord ++ tailWord_591997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592108 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_592108 : Nat := 118140960795 + 592108 * 2 ^ 59
def prefixEnd_592108 : Nat := 4983230072969 + 3 ^ 40 * 592108 * 2
def baseEnd_592108 : Nat := 270254225219977429712845

theorem tailTrace_592108 : CollatzResearch.WordTrace tailWord_592108 prefixEnd_592108 270254225219977429712845 := by
  unfold tailWord_592108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10797976469450657420308489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14397301959267543227077985 10797976469450657420308489)
  ·
    refine ⟨8098482352087993065231367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10797976469450657420308489 8098482352087993065231367)
    ·
      refine ⟨12147723528131989597847051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8098482352087993065231367 12147723528131989597847051)
      ·
        refine ⟨18221585292197984396770577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12147723528131989597847051 18221585292197984396770577)
        ·
          refine ⟨13666188969148488297577933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18221585292197984396770577 13666188969148488297577933)
          ·
            refine ⟨5124820863430683111591725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13666188969148488297577933 5124820863430683111591725)
            ·
              refine ⟨1921807823786506166846897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5124820863430683111591725 1921807823786506166846897)
              ·
                refine ⟨1441355867839879625135173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921807823786506166846897 1441355867839879625135173)
                ·
                  refine ⟨270254225219977429712845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441355867839879625135173 270254225219977429712845)
                  ·
                    rfl

theorem cell20_592108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_592108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592108 prefixEnd_592108 := by exact prefixLift 592108
  have htrace : WordTrace (prefixWord ++ tailWord_592108) baseStart_592108 baseEnd_592108 := by
    simpa [prefixWord, tailWord_592108, baseEnd_592108] using wordTrace_append hprefix tailTrace_592108
  have hstable : (prefixWord ++ tailWord_592108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592108).length < 2 ^ (prefixWord ++ tailWord_592108).sum := by decide
  have hdescent : baseEnd_592108 < baseStart_592108 := by decide
  rcases family_descends (prefixWord ++ tailWord_592108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592132 : List Nat := [2, 3, 2, 2, 3, 1, 7]
def baseStart_592132 : Nat := 118140960795 + 592132 * 2 ^ 59
def prefixEnd_592132 : Nat := 4983230072969 + 3 ^ 40 * 592132 * 2
def baseEnd_592132 : Nat := 30029464385993334768083

theorem tailTrace_592132 : CollatzResearch.WordTrace tailWord_592132 prefixEnd_592132 30029464385993334768083 := by
  unfold tailWord_592132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10798414145407183469745325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14397885527209577959660433 10798414145407183469745325)
  ·
    refine ⟨4049405304527693801154497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10798414145407183469745325 4049405304527693801154497)
    ·
      refine ⟨3037053978395770350865873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4049405304527693801154497 3037053978395770350865873)
      ·
        refine ⟨2277790483796827763149405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3037053978395770350865873 2277790483796827763149405)
        ·
          refine ⟨854171431423810411181027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2277790483796827763149405 854171431423810411181027)
          ·
            refine ⟨1281257147135715616771541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854171431423810411181027 1281257147135715616771541)
            ·
              refine ⟨30029464385993334768083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1281257147135715616771541 30029464385993334768083)
              ·
                rfl

theorem cell20_592132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 7].length) (baseStart_592132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592132 prefixEnd_592132 := by exact prefixLift 592132
  have htrace : WordTrace (prefixWord ++ tailWord_592132) baseStart_592132 baseEnd_592132 := by
    simpa [prefixWord, tailWord_592132, baseEnd_592132] using wordTrace_append hprefix tailTrace_592132
  have hstable : (prefixWord ++ tailWord_592132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592132).length < 2 ^ (prefixWord ++ tailWord_592132).sum := by decide
  have hdescent : baseEnd_592132 < baseStart_592132 := by decide
  rcases family_descends (prefixWord ++ tailWord_592132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592215 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 3]
def baseStart_592215 : Nat := 118140960795 + 592215 * 2 ^ 59
def prefixEnd_592215 : Nat := 4983230072969 + 3 ^ 40 * 592215 * 2
def baseEnd_592215 : Nat := 270303062935560613145741

theorem tailTrace_592215 : CollatzResearch.WordTrace tailWord_592215 prefixEnd_592215 270303062935560613145741 := by
  unfold tailWord_592215
  simp only [CollatzResearch.WordTrace]
  refine ⟨21599855549513672114762099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14399903699675781409841399 21599855549513672114762099)
  ·
    refine ⟨32399783324270508172143149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21599855549513672114762099 32399783324270508172143149)
    ·
      refine ⟨12149918746601440564553681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32399783324270508172143149 12149918746601440564553681)
      ·
        refine ⟨9112439059951080423415261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12149918746601440564553681 9112439059951080423415261)
        ·
          refine ⟨3417164647481655158780723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9112439059951080423415261 3417164647481655158780723)
          ·
            refine ⟨5125746971222482738171085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417164647481655158780723 5125746971222482738171085)
            ·
              refine ⟨1922155114208431026814157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5125746971222482738171085 1922155114208431026814157)
              ·
                refine ⟨720808167828161635055309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1922155114208431026814157 720808167828161635055309)
                ·
                  refine ⟨270303062935560613145741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720808167828161635055309 270303062935560613145741)
                  ·
                    rfl

theorem cell20_592215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_592215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592215 prefixEnd_592215 := by exact prefixLift 592215
  have htrace : WordTrace (prefixWord ++ tailWord_592215) baseStart_592215 baseEnd_592215 := by
    simpa [prefixWord, tailWord_592215, baseEnd_592215] using wordTrace_append hprefix tailTrace_592215
  have hstable : (prefixWord ++ tailWord_592215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592215).length < 2 ^ (prefixWord ++ tailWord_592215).sum := by decide
  have hdescent : baseEnd_592215 < baseStart_592215 := by decide
  rcases family_descends (prefixWord ++ tailWord_592215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592229 : List Nat := [1, 3, 1, 3, 1, 3, 2, 6]
def baseStart_592229 : Nat := 118140960795 + 592229 * 2 ^ 59
def prefixEnd_592229 : Nat := 4983230072969 + 3 ^ 40 * 592229 * 2
def baseEnd_592229 : Nat := 90103150972346262226339

theorem tailTrace_592229 : CollatzResearch.WordTrace tailWord_592229 prefixEnd_592229 90103150972346262226339 := by
  unfold tailWord_592229
  simp only [CollatzResearch.WordTrace]
  refine ⟨21600366171462952505771741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14400244114308635003847827 21600366171462952505771741)
  ·
    refine ⟨8100137314298607189664403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21600366171462952505771741 8100137314298607189664403)
    ·
      refine ⟨12150205971447910784496605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8100137314298607189664403 12150205971447910784496605)
      ·
        refine ⟨4556327239292966544186227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12150205971447910784496605 4556327239292966544186227)
        ·
          refine ⟨6834490858939449816279341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556327239292966544186227 6834490858939449816279341)
          ·
            refine ⟨2562934072102293681104753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6834490858939449816279341 2562934072102293681104753)
            ·
              refine ⟨1922200554076720260828565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2562934072102293681104753 1922200554076720260828565)
              ·
                refine ⟨90103150972346262226339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1922200554076720260828565 90103150972346262226339)
                ·
                  rfl

theorem cell20_592229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_592229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592229 prefixEnd_592229 := by exact prefixLift 592229
  have htrace : WordTrace (prefixWord ++ tailWord_592229) baseStart_592229 baseEnd_592229 := by
    simpa [prefixWord, tailWord_592229, baseEnd_592229] using wordTrace_append hprefix tailTrace_592229
  have hstable : (prefixWord ++ tailWord_592229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592229).length < 2 ^ (prefixWord ++ tailWord_592229).sum := by decide
  have hdescent : baseEnd_592229 < baseStart_592229 := by decide
  rcases family_descends (prefixWord ++ tailWord_592229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592243 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_592243 : Nat := 118140960795 + 592243 * 2 ^ 59
def prefixEnd_592243 : Nat := 4983230072969 + 3 ^ 40 * 592243 * 2
def baseEnd_592243 : Nat := 270315842898516960212293

theorem tailTrace_592243 : CollatzResearch.WordTrace tailWord_592243 prefixEnd_592243 270315842898516960212293 := by
  unfold tailWord_592243
  simp only [CollatzResearch.WordTrace]
  refine ⟨21600876793412232896781383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14400584528941488597854255 21600876793412232896781383)
  ·
    refine ⟨32401315190118349345172075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21600876793412232896781383 32401315190118349345172075)
    ·
      refine ⟨48601972785177524017758113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32401315190118349345172075 48601972785177524017758113)
      ·
        refine ⟨36451479588883143013318585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48601972785177524017758113 36451479588883143013318585)
        ·
          refine ⟨27338609691662357259988939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36451479588883143013318585 27338609691662357259988939)
          ·
            refine ⟨41007914537493535889983409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27338609691662357259988939 41007914537493535889983409)
            ·
              refine ⟨30755935903120151917487557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41007914537493535889983409 30755935903120151917487557)
              ·
                refine ⟨5766737981835028484528917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30755935903120151917487557 5766737981835028484528917)
                ·
                  refine ⟨270315842898516960212293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5766737981835028484528917 270315842898516960212293)
                  ·
                    rfl

theorem cell20_592243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_592243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592243 prefixEnd_592243 := by exact prefixLift 592243
  have htrace : WordTrace (prefixWord ++ tailWord_592243) baseStart_592243 baseEnd_592243 := by
    simpa [prefixWord, tailWord_592243, baseEnd_592243] using wordTrace_append hprefix tailTrace_592243
  have hstable : (prefixWord ++ tailWord_592243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592243).length < 2 ^ (prefixWord ++ tailWord_592243).sum := by decide
  have hdescent : baseEnd_592243 < baseStart_592243 := by decide
  rcases family_descends (prefixWord ++ tailWord_592243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592246 : List Nat := [5, 1, 1, 4, 9]
def baseStart_592246 : Nat := 118140960795 + 592246 * 2 ^ 59
def prefixEnd_592246 : Nat := 4983230072969 + 3 ^ 40 * 592246 * 2
def baseEnd_592246 : Nat := 3337249533089657816201

theorem tailTrace_592246 : CollatzResearch.WordTrace tailWord_592246 prefixEnd_592246 3337249533089657816201 := by
  unfold tailWord_592246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350061638275085275571287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14400657474934242939427061 1350061638275085275571287)
  ·
    refine ⟨2025092457412627913356931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1350061638275085275571287 2025092457412627913356931)
    ·
      refine ⟨3037638686118941870035397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2025092457412627913356931 3037638686118941870035397)
      ·
        refine ⟨569557253647301600631637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3037638686118941870035397 569557253647301600631637)
        ·
          refine ⟨3337249533089657816201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 569557253647301600631637 3337249533089657816201)
          ·
            rfl

theorem cell20_592246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 9].length) (baseStart_592246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592246 prefixEnd_592246 := by exact prefixLift 592246
  have htrace : WordTrace (prefixWord ++ tailWord_592246) baseStart_592246 baseEnd_592246 := by
    simpa [prefixWord, tailWord_592246, baseEnd_592246] using wordTrace_append hprefix tailTrace_592246
  have hstable : (prefixWord ++ tailWord_592246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592246).length < 2 ^ (prefixWord ++ tailWord_592246).sum := by decide
  have hdescent : baseEnd_592246 < baseStart_592246 := by decide
  rcases family_descends (prefixWord ++ tailWord_592246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592253 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 3]
def baseStart_592253 : Nat := 118140960795 + 592253 * 2 ^ 59
def prefixEnd_592253 : Nat := 4983230072969 + 3 ^ 40 * 592253 * 2
def baseEnd_592253 : Nat := 270320407171001369878919

theorem tailTrace_592253 : CollatzResearch.WordTrace tailWord_592253 prefixEnd_592253 270320407171001369878919 := by
  unfold tailWord_592253
  simp only [CollatzResearch.WordTrace]
  refine ⟨21601241523376004604645413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14400827682250669736430275 21601241523376004604645413)
  ·
    refine ⟨4050232785633000863371015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21601241523376004604645413 4050232785633000863371015)
    ·
      refine ⟨6075349178449501295056523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050232785633000863371015 6075349178449501295056523)
      ·
        refine ⟨9113023767674251942584785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075349178449501295056523 9113023767674251942584785)
        ·
          refine ⟨6834767825755688956938589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9113023767674251942584785 6834767825755688956938589)
          ·
            refine ⟨2563037934658383358851971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6834767825755688956938589 2563037934658383358851971)
            ·
              refine ⟨3844556901987575038277957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563037934658383358851971 3844556901987575038277957)
              ·
                refine ⟨720854419122670319677117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3844556901987575038277957 720854419122670319677117)
                ·
                  refine ⟨270320407171001369878919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720854419122670319677117 270320407171001369878919)
                  ·
                    rfl

theorem cell20_592253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_592253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592253 prefixEnd_592253 := by exact prefixLift 592253
  have htrace : WordTrace (prefixWord ++ tailWord_592253) baseStart_592253 baseEnd_592253 := by
    simpa [prefixWord, tailWord_592253, baseEnd_592253] using wordTrace_append hprefix tailTrace_592253
  have hstable : (prefixWord ++ tailWord_592253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592253).length < 2 ^ (prefixWord ++ tailWord_592253).sum := by decide
  have hdescent : baseEnd_592253 < baseStart_592253 := by decide
  rcases family_descends (prefixWord ++ tailWord_592253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592260 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_592260 : Nat := 118140960795 + 592260 * 2 ^ 59
def prefixEnd_592260 : Nat := 4983230072969 + 3 ^ 40 * 592260 * 2
def baseEnd_592260 : Nat := 270323602161740456645557

theorem tailTrace_592260 : CollatzResearch.WordTrace tailWord_592260 prefixEnd_592260 270323602161740456645557 := by
  unfold tailWord_592260
  simp only [CollatzResearch.WordTrace]
  refine ⟨10800748417175322400075117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14400997889567096533433489 10800748417175322400075117)
  ·
    refine ⟨4050280656440745900028169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10800748417175322400075117 4050280656440745900028169)
    ·
      refine ⟨3037710492330559425021127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4050280656440745900028169 3037710492330559425021127)
      ·
        refine ⟨4556565738495839137531691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037710492330559425021127 4556565738495839137531691)
        ·
          refine ⟨6834848607743758706297537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556565738495839137531691 6834848607743758706297537)
          ·
            refine ⟨5126136455807819029723153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6834848607743758706297537 5126136455807819029723153)
            ·
              refine ⟨3844602341855864272292365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126136455807819029723153 3844602341855864272292365)
              ·
                refine ⟨1441725878195949102109637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3844602341855864272292365 1441725878195949102109637)
                ·
                  refine ⟨270323602161740456645557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441725878195949102109637 270323602161740456645557)
                  ·
                    rfl

theorem cell20_592260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_592260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592260 prefixEnd_592260 := by exact prefixLift 592260
  have htrace : WordTrace (prefixWord ++ tailWord_592260) baseStart_592260 baseEnd_592260 := by
    simpa [prefixWord, tailWord_592260, baseEnd_592260] using wordTrace_append hprefix tailTrace_592260
  have hstable : (prefixWord ++ tailWord_592260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592260).length < 2 ^ (prefixWord ++ tailWord_592260).sum := by decide
  have hdescent : baseEnd_592260 < baseStart_592260 := by decide
  rcases family_descends (prefixWord ++ tailWord_592260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592267 : List Nat := [1, 1, 1, 1, 4, 4, 3, 5]
def baseStart_592267 : Nat := 118140960795 + 592267 * 2 ^ 59
def prefixEnd_592267 : Nat := 4983230072969 + 3 ^ 40 * 592267 * 2
def baseEnd_592267 : Nat := 90108932384159847804065

theorem tailTrace_592267 : CollatzResearch.WordTrace tailWord_592267 prefixEnd_592267 90108932384159847804065 := by
  unfold tailWord_592267
  simp only [CollatzResearch.WordTrace]
  refine ⟨21601752145325284995655055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14401168096883523330436703 21601752145325284995655055)
  ·
    refine ⟨32402628217987927493482583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21601752145325284995655055 32402628217987927493482583)
    ·
      refine ⟨48603942326981891240223875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32402628217987927493482583 48603942326981891240223875)
      ·
        refine ⟨72905913490472836860335813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48603942326981891240223875 72905913490472836860335813)
        ·
          refine ⟨13669858779463656911312965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72905913490472836860335813 13669858779463656911312965)
          ·
            refine ⟨2563098521149435670871181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13669858779463656911312965 2563098521149435670871181)
            ·
              refine ⟨961161945431038376576693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2563098521149435670871181 961161945431038376576693)
              ·
                refine ⟨90108932384159847804065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 961161945431038376576693 90108932384159847804065)
                ·
                  rfl

theorem cell20_592267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_592267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592267 prefixEnd_592267 := by exact prefixLift 592267
  have htrace : WordTrace (prefixWord ++ tailWord_592267) baseStart_592267 baseEnd_592267 := by
    simpa [prefixWord, tailWord_592267, baseEnd_592267] using wordTrace_append hprefix tailTrace_592267
  have hstable : (prefixWord ++ tailWord_592267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592267).length < 2 ^ (prefixWord ++ tailWord_592267).sum := by decide
  have hdescent : baseEnd_592267 < baseStart_592267 := by decide
  rcases family_descends (prefixWord ++ tailWord_592267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592270 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_592270 : Nat := 118140960795 + 592270 * 2 ^ 59
def prefixEnd_592270 : Nat := 4983230072969 + 3 ^ 40 * 592270 * 2
def baseEnd_592270 : Nat := 270328166434224866312183

theorem tailTrace_592270 : CollatzResearch.WordTrace tailWord_592270 prefixEnd_592270 270328166434224866312183 := by
  unfold tailWord_592270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700232695539302063501783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14401241042876277672009509 2700232695539302063501783)
  ·
    refine ⟨4050349043308953095252675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2700232695539302063501783 4050349043308953095252675)
    ·
      refine ⟨6075523564963429642879013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050349043308953095252675 6075523564963429642879013)
      ·
        refine ⟨1139160668430643058039815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6075523564963429642879013 1139160668430643058039815)
        ·
          refine ⟨1708741002645964587059723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139160668430643058039815 1708741002645964587059723)
          ·
            refine ⟨2563111503968946880589585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708741002645964587059723 2563111503968946880589585)
            ·
              refine ⟨1922333627976710160442189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2563111503968946880589585 1922333627976710160442189)
              ·
                refine ⟨720875110491266310165821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1922333627976710160442189 720875110491266310165821)
                ·
                  refine ⟨270328166434224866312183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720875110491266310165821 270328166434224866312183)
                  ·
                    rfl

theorem cell20_592270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_592270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592270 prefixEnd_592270 := by exact prefixLift 592270
  have htrace : WordTrace (prefixWord ++ tailWord_592270) baseStart_592270 baseEnd_592270 := by
    simpa [prefixWord, tailWord_592270, baseEnd_592270] using wordTrace_append hprefix tailTrace_592270
  have hstable : (prefixWord ++ tailWord_592270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592270).length < 2 ^ (prefixWord ++ tailWord_592270).sum := by decide
  have hdescent : baseEnd_592270 < baseStart_592270 := by decide
  rcases family_descends (prefixWord ++ tailWord_592270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592305 : List Nat := [1, 2, 2, 4, 1, 3, 7]
def baseStart_592305 : Nat := 118140960795 + 592305 * 2 ^ 59
def prefixEnd_592305 : Nat := 4983230072969 + 3 ^ 40 * 592305 * 2
def baseEnd_592305 : Nat := 30038237931991144460597

theorem tailTrace_592305 : CollatzResearch.WordTrace tailWord_592305 prefixEnd_592305 30038237931991144460597 := by
  unfold tailWord_592305
  simp only [CollatzResearch.WordTrace]
  refine ⟨21603138119187617485538369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14402092079458411657025579 21603138119187617485538369)
  ·
    refine ⟨16202353589390713114153777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21603138119187617485538369 16202353589390713114153777)
    ·
      refine ⟨12151765192043034835615333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16202353589390713114153777 12151765192043034835615333)
      ·
        refine ⟨2278455973508069031677875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12151765192043034835615333 2278455973508069031677875)
        ·
          refine ⟨3417683960262103547516813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278455973508069031677875 3417683960262103547516813)
          ·
            refine ⟨1281631485098288830318805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3417683960262103547516813 1281631485098288830318805)
            ·
              refine ⟨30038237931991144460597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1281631485098288830318805 30038237931991144460597)
              ·
                rfl

theorem cell20_592305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_592305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592305 prefixEnd_592305 := by exact prefixLift 592305
  have htrace : WordTrace (prefixWord ++ tailWord_592305) baseStart_592305 baseEnd_592305 := by
    simpa [prefixWord, tailWord_592305, baseEnd_592305] using wordTrace_append hprefix tailTrace_592305
  have hstable : (prefixWord ++ tailWord_592305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592305).length < 2 ^ (prefixWord ++ tailWord_592305).sum := by decide
  have hdescent : baseEnd_592305 < baseStart_592305 := by decide
  rcases family_descends (prefixWord ++ tailWord_592305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592321 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 3]
def baseStart_592321 : Nat := 118140960795 + 592321 * 2 ^ 59
def prefixEnd_592321 : Nat := 4983230072969 + 3 ^ 40 * 592321 * 2
def baseEnd_592321 : Nat := 270351444223895355611975

theorem tailTrace_592321 : CollatzResearch.WordTrace tailWord_592321 prefixEnd_592321 270351444223895355611975 := by
  unfold tailWord_592321
  simp only [CollatzResearch.WordTrace]
  refine ⟨21603721687129652218120817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14402481124753101478747211 21603721687129652218120817)
  ·
    refine ⟨16202791265347239163590613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21603721687129652218120817 16202791265347239163590613)
    ·
      refine ⟨379752920281575917896655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16202791265347239163590613 379752920281575917896655)
      ·
        refine ⟨569629380422363876844983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379752920281575917896655 569629380422363876844983)
        ·
          refine ⟨854444070633545815267475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569629380422363876844983 854444070633545815267475)
          ·
            refine ⟨1281666105950318722901213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854444070633545815267475 1281666105950318722901213)
            ·
              refine ⟨480624789731369521087955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1281666105950318722901213 480624789731369521087955)
              ·
                refine ⟨720937184597054281631933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480624789731369521087955 720937184597054281631933)
                ·
                  refine ⟨270351444223895355611975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720937184597054281631933 270351444223895355611975)
                  ·
                    rfl

theorem cell20_592321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_592321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592321 prefixEnd_592321 := by exact prefixLift 592321
  have htrace : WordTrace (prefixWord ++ tailWord_592321) baseStart_592321 baseEnd_592321 := by
    simpa [prefixWord, tailWord_592321, baseEnd_592321] using wordTrace_append hprefix tailTrace_592321
  have hstable : (prefixWord ++ tailWord_592321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592321).length < 2 ^ (prefixWord ++ tailWord_592321).sum := by decide
  have hdescent : baseEnd_592321 < baseStart_592321 := by decide
  rcases family_descends (prefixWord ++ tailWord_592321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592370 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_592370 : Nat := 118140960795 + 592370 * 2 ^ 59
def prefixEnd_592370 : Nat := 4983230072969 + 3 ^ 40 * 592370 * 2
def baseEnd_592370 : Nat := 270373809159068962978441

theorem tailTrace_592370 : CollatzResearch.WordTrace tailWord_592370 prefixEnd_592370 270373809159068962978441 := by
  unfold tailWord_592370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401377215988033396663641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14403672575968089057769709 5401377215988033396663641)
  ·
    refine ⟨4051032911991025047497731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5401377215988033396663641 4051032911991025047497731)
    ·
      refine ⟨6076549367986537571246597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051032911991025047497731 6076549367986537571246597)
      ·
        refine ⟨1139353006497475794608737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6076549367986537571246597 1139353006497475794608737)
        ·
          refine ⟨854514754873106845956553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1139353006497475794608737 854514754873106845956553)
          ·
            refine ⟨640886066154830134467415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854514754873106845956553 640886066154830134467415)
            ·
              refine ⟨961329099232245201701123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640886066154830134467415 961329099232245201701123)
              ·
                refine ⟨1441993648848367802551685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961329099232245201701123 1441993648848367802551685)
                ·
                  refine ⟨270373809159068962978441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441993648848367802551685 270373809159068962978441)
                  ·
                    rfl

theorem cell20_592370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_592370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592370 prefixEnd_592370 := by exact prefixLift 592370
  have htrace : WordTrace (prefixWord ++ tailWord_592370) baseStart_592370 baseEnd_592370 := by
    simpa [prefixWord, tailWord_592370, baseEnd_592370] using wordTrace_append hprefix tailTrace_592370
  have hstable : (prefixWord ++ tailWord_592370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592370).length < 2 ^ (prefixWord ++ tailWord_592370).sum := by decide
  have hdescent : baseEnd_592370 < baseStart_592370 := by decide
  rcases family_descends (prefixWord ++ tailWord_592370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592381 : List Nat := [1, 4, 1, 1, 1, 3, 4, 5]
def baseStart_592381 : Nat := 118140960795 + 592381 * 2 ^ 59
def prefixEnd_592381 : Nat := 4983230072969 + 3 ^ 40 * 592381 * 2
def baseEnd_592381 : Nat := 90126276619600604537243

theorem tailTrace_592381 : CollatzResearch.WordTrace tailWord_592381 prefixEnd_592381 90126276619600604537243 := by
  unfold tailWord_592381
  simp only [CollatzResearch.WordTrace]
  refine ⟨21605910066912282465304997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14403940044608188310203331 21605910066912282465304997)
  ·
    refine ⟨4051108137546052962244687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21605910066912282465304997 4051108137546052962244687)
    ·
      refine ⟨6076662206319079443367031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051108137546052962244687 6076662206319079443367031)
      ·
        refine ⟨9114993309478619165050547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076662206319079443367031 9114993309478619165050547)
        ·
          refine ⟨13672489964217928747575821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9114993309478619165050547 13672489964217928747575821)
          ·
            refine ⟨5127183736581723280340933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13672489964217928747575821 5127183736581723280340933)
            ·
              refine ⟨961346950609073115063925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5127183736581723280340933 961346950609073115063925)
              ·
                refine ⟨90126276619600604537243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 961346950609073115063925 90126276619600604537243)
                ·
                  rfl

theorem cell20_592381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_592381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592381 prefixEnd_592381 := by exact prefixLift 592381
  have htrace : WordTrace (prefixWord ++ tailWord_592381) baseStart_592381 baseEnd_592381 := by
    simpa [prefixWord, tailWord_592381, baseEnd_592381] using wordTrace_append hprefix tailTrace_592381
  have hstable : (prefixWord ++ tailWord_592381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592381).length < 2 ^ (prefixWord ++ tailWord_592381).sum := by decide
  have hdescent : baseEnd_592381 < baseStart_592381 := by decide
  rcases family_descends (prefixWord ++ tailWord_592381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592446 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_592446 : Nat := 118140960795 + 592446 * 2 ^ 59
def prefixEnd_592446 : Nat := 4983230072969 + 3 ^ 40 * 592446 * 2
def baseEnd_592446 : Nat := 270408497629950476444797

theorem tailTrace_592446 : CollatzResearch.WordTrace tailWord_592446 prefixEnd_592446 270408497629950476444797 := by
  unfold tailWord_592446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701035101459599820802649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14405520541117865710947461 2701035101459599820802649)
  ·
    refine ⟨2025776326094699865601987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2701035101459599820802649 2025776326094699865601987)
    ·
      refine ⟨3038664489142049798402981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2025776326094699865601987 3038664489142049798402981)
      ·
        refine ⟨569749591714134337200559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3038664489142049798402981 569749591714134337200559)
        ·
          refine ⟨854624387571201505800839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569749591714134337200559 854624387571201505800839)
          ·
            refine ⟨1281936581356802258701259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854624387571201505800839 1281936581356802258701259)
            ·
              refine ⟨1922904872035203388051889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281936581356802258701259 1922904872035203388051889)
              ·
                refine ⟨1442178654026402541038917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922904872035203388051889 1442178654026402541038917)
                ·
                  refine ⟨270408497629950476444797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442178654026402541038917 270408497629950476444797)
                  ·
                    rfl

theorem cell20_592446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_592446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592446 prefixEnd_592446 := by exact prefixLift 592446
  have htrace : WordTrace (prefixWord ++ tailWord_592446) baseStart_592446 baseEnd_592446 := by
    simpa [prefixWord, tailWord_592446, baseEnd_592446] using wordTrace_append hprefix tailTrace_592446
  have hstable : (prefixWord ++ tailWord_592446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592446).length < 2 ^ (prefixWord ++ tailWord_592446).sum := by decide
  have hdescent : baseEnd_592446 < baseStart_592446 := by decide
  rcases family_descends (prefixWord ++ tailWord_592446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592471 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_592471 : Nat := 118140960795 + 592471 * 2 ^ 59
def prefixEnd_592471 : Nat := 4983230072969 + 3 ^ 40 * 592471 * 2
def baseEnd_592471 : Nat := 270419908311161500611361

theorem tailTrace_592471 : CollatzResearch.WordTrace tailWord_592471 prefixEnd_592471 270419908311161500611361 := by
  unfold tailWord_592471
  simp only [CollatzResearch.WordTrace]
  refine ⟨21609192636586227836081267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14406128424390818557387511 21609192636586227836081267)
  ·
    refine ⟨32413788954879341754121901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21609192636586227836081267 32413788954879341754121901)
    ·
      refine ⟨12155170858079753157795713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32413788954879341754121901 12155170858079753157795713)
      ·
        refine ⟨9116378143559814868346785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12155170858079753157795713 9116378143559814868346785)
        ·
          refine ⟨6837283607669861151260089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9116378143559814868346785 6837283607669861151260089)
          ·
            refine ⟨5127962705752395863445067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6837283607669861151260089 5127962705752395863445067)
            ·
              refine ⟨7691944058628593795167601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127962705752395863445067 7691944058628593795167601)
              ·
                refine ⟨5768958043971445346375701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7691944058628593795167601 5768958043971445346375701)
                ·
                  refine ⟨270419908311161500611361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5768958043971445346375701 270419908311161500611361)
                  ·
                    rfl

theorem cell20_592471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_592471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592471 prefixEnd_592471 := by exact prefixLift 592471
  have htrace : WordTrace (prefixWord ++ tailWord_592471) baseStart_592471 baseEnd_592471 := by
    simpa [prefixWord, tailWord_592471, baseEnd_592471] using wordTrace_append hprefix tailTrace_592471
  have hstable : (prefixWord ++ tailWord_592471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592471).length < 2 ^ (prefixWord ++ tailWord_592471).sum := by decide
  have hdescent : baseEnd_592471 < baseStart_592471 := by decide
  rcases family_descends (prefixWord ++ tailWord_592471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592481 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 3]
def baseStart_592481 : Nat := 118140960795 + 592481 * 2 ^ 59
def prefixEnd_592481 : Nat := 4983230072969 + 3 ^ 40 * 592481 * 2
def baseEnd_592481 : Nat := 270424472583645910277987

theorem tailTrace_592481 : CollatzResearch.WordTrace tailWord_592481 prefixEnd_592481 270424472583645910277987 := by
  unfold tailWord_592481
  simp only [CollatzResearch.WordTrace]
  refine ⟨21609557366549999543945297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14406371577699999695963531 21609557366549999543945297)
  ·
    refine ⟨16207168024912499657958973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21609557366549999543945297 16207168024912499657958973)
    ·
      refine ⟨6077688009342187371734615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16207168024912499657958973 6077688009342187371734615)
      ·
        refine ⟨9116532014013281057601923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6077688009342187371734615 9116532014013281057601923)
        ·
          refine ⟨13674798021019921586402885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9116532014013281057601923 13674798021019921586402885)
          ·
            refine ⟨2564024628941235297450541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13674798021019921586402885 2564024628941235297450541)
            ·
              refine ⟨961509235852963236543953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2564024628941235297450541 961509235852963236543953)
              ·
                refine ⟨721131926889722427407965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961509235852963236543953 721131926889722427407965)
                ·
                  refine ⟨270424472583645910277987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721131926889722427407965 270424472583645910277987)
                  ·
                    rfl

theorem cell20_592481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_592481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592481 prefixEnd_592481 := by exact prefixLift 592481
  have htrace : WordTrace (prefixWord ++ tailWord_592481) baseStart_592481 baseEnd_592481 := by
    simpa [prefixWord, tailWord_592481, baseEnd_592481] using wordTrace_append hprefix tailTrace_592481
  have hstable : (prefixWord ++ tailWord_592481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592481).length < 2 ^ (prefixWord ++ tailWord_592481).sum := by decide
  have hdescent : baseEnd_592481 < baseStart_592481 := by decide
  rcases family_descends (prefixWord ++ tailWord_592481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592512 : List Nat := [2, 1, 1, 2, 1, 7, 2, 4]
def baseStart_592512 : Nat := 118140960795 + 592512 * 2 ^ 59
def prefixEnd_592512 : Nat := 4983230072969 + 3 ^ 40 * 592512 * 2
def baseEnd_592512 : Nat := 90146207276115860081509

theorem tailTrace_592512 : CollatzResearch.WordTrace tailWord_592512 prefixEnd_592512 90146207276115860081509 := by
  unfold tailWord_592512
  simp only [CollatzResearch.WordTrace]
  refine ⟨10805344014718845919161895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14407125352958461225549193 10805344014718845919161895)
  ·
    refine ⟨16208016022078268878742843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10805344014718845919161895 16208016022078268878742843)
    ·
      refine ⟨24312024033117403318114265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16208016022078268878742843 24312024033117403318114265)
      ·
        refine ⟨18234018024838052488585699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24312024033117403318114265 18234018024838052488585699)
        ·
          refine ⟨27351027037257078732878549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18234018024838052488585699 27351027037257078732878549)
          ·
            refine ⟨641039696185712782801841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27351027037257078732878549 641039696185712782801841)
            ·
              refine ⟨480779772139284587101381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641039696185712782801841 480779772139284587101381)
              ·
                refine ⟨90146207276115860081509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 480779772139284587101381 90146207276115860081509)
                ·
                  rfl

theorem cell20_592512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_592512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592512 prefixEnd_592512 := by exact prefixLift 592512
  have htrace : WordTrace (prefixWord ++ tailWord_592512) baseStart_592512 baseEnd_592512 := by
    simpa [prefixWord, tailWord_592512, baseEnd_592512] using wordTrace_append hprefix tailTrace_592512
  have hstable : (prefixWord ++ tailWord_592512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592512).length < 2 ^ (prefixWord ++ tailWord_592512).sum := by decide
  have hdescent : baseEnd_592512 < baseStart_592512 := by decide
  rcases family_descends (prefixWord ++ tailWord_592512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592514 : List Nat := [3, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_592514 : Nat := 118140960795 + 592514 * 2 ^ 59
def prefixEnd_592514 : Nat := 4983230072969 + 3 ^ 40 * 592514 * 2
def baseEnd_592514 : Nat := 270439534682844462177853

theorem tailTrace_592514 : CollatzResearch.WordTrace tailWord_592514 prefixEnd_592514 270439534682844462177853 := by
  unfold tailWord_592514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5402690243857611544974149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14407173983620297453264397 5402690243857611544974149)
  ·
    refine ⟨1013004420723302164682653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5402690243857611544974149 1013004420723302164682653)
    ·
      refine ⟨379876657771238311755995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1013004420723302164682653 379876657771238311755995)
      ·
        refine ⟨569814986656857467633993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379876657771238311755995 569814986656857467633993)
        ·
          refine ⟨427361239992643100725495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 569814986656857467633993 427361239992643100725495)
          ·
            refine ⟨641041859988964651088243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427361239992643100725495 641041859988964651088243)
            ·
              refine ⟨961562789983446976632365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641041859988964651088243 961562789983446976632365)
              ·
                refine ⟨360586046243792616237137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 961562789983446976632365 360586046243792616237137)
                ·
                  refine ⟨270439534682844462177853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360586046243792616237137 270439534682844462177853)
                  ·
                    rfl

theorem cell20_592514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_592514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592514 prefixEnd_592514 := by exact prefixLift 592514
  have htrace : WordTrace (prefixWord ++ tailWord_592514) baseStart_592514 baseEnd_592514 := by
    simpa [prefixWord, tailWord_592514, baseEnd_592514] using wordTrace_append hprefix tailTrace_592514
  have hstable : (prefixWord ++ tailWord_592514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592514).length < 2 ^ (prefixWord ++ tailWord_592514).sum := by decide
  have hdescent : baseEnd_592514 < baseStart_592514 := by decide
  rcases family_descends (prefixWord ++ tailWord_592514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592547 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_592547 : Nat := 118140960795 + 592547 * 2 ^ 59
def prefixEnd_592547 : Nat := 4983230072969 + 3 ^ 40 * 592547 * 2
def baseEnd_592547 : Nat := 270454596782043014077717

theorem tailTrace_592547 : CollatzResearch.WordTrace tailWord_592547 prefixEnd_592547 270454596782043014077717 := by
  unfold tailWord_592547
  simp only [CollatzResearch.WordTrace]
  refine ⟨21611964584310892815847895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14407976389540595210565263 21611964584310892815847895)
  ·
    refine ⟨32417946876466339223771843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21611964584310892815847895 32417946876466339223771843)
    ·
      refine ⟨48626920314699508835657765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32417946876466339223771843 48626920314699508835657765)
      ·
        refine ⟨9117547559006157906685831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48626920314699508835657765 9117547559006157906685831)
        ·
          refine ⟨13676321338509236860028747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117547559006157906685831 13676321338509236860028747)
          ·
            refine ⟨20514482007763855290043121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13676321338509236860028747 20514482007763855290043121)
            ·
              refine ⟨15385861505822891467532341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20514482007763855290043121 15385861505822891467532341)
              ·
                refine ⟨1442424516170896075081157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15385861505822891467532341 1442424516170896075081157)
                ·
                  refine ⟨270454596782043014077717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442424516170896075081157 270454596782043014077717)
                  ·
                    rfl

theorem cell20_592547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_592547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592547 prefixEnd_592547 := by exact prefixLift 592547
  have htrace : WordTrace (prefixWord ++ tailWord_592547) baseStart_592547 baseEnd_592547 := by
    simpa [prefixWord, tailWord_592547, baseEnd_592547] using wordTrace_append hprefix tailTrace_592547
  have hstable : (prefixWord ++ tailWord_592547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592547).length < 2 ^ (prefixWord ++ tailWord_592547).sum := by decide
  have hdescent : baseEnd_592547 < baseStart_592547 := by decide
  rcases family_descends (prefixWord ++ tailWord_592547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592594 : List Nat := [3, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_592594 : Nat := 118140960795 + 592594 * 2 ^ 59
def prefixEnd_592594 : Nat := 4983230072969 + 3 ^ 40 * 592594 * 2
def baseEnd_592594 : Nat := 270476048862719739510859

theorem tailTrace_592594 : CollatzResearch.WordTrace tailWord_592594 prefixEnd_592594 270476048862719739510859 := by
  unfold tailWord_592594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403419703785154960702209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14409119210093746561872557 5403419703785154960702209)
  ·
    refine ⟨4052564777838866220526657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5403419703785154960702209 4052564777838866220526657)
    ·
      refine ⟨3039423583379149665394993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4052564777838866220526657 3039423583379149665394993)
      ·
        refine ⟨2279567687534362249046245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3039423583379149665394993 2279567687534362249046245)
        ·
          refine ⟨427418941412692921696171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2279567687534362249046245 427418941412692921696171)
          ·
            refine ⟨641128412119039382544257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427418941412692921696171 641128412119039382544257)
            ·
              refine ⟨480846309089279536908193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641128412119039382544257 480846309089279536908193)
              ·
                refine ⟨360634731816959652681145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480846309089279536908193 360634731816959652681145)
                ·
                  refine ⟨270476048862719739510859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360634731816959652681145 270476048862719739510859)
                  ·
                    rfl

theorem cell20_592594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_592594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592594 prefixEnd_592594 := by exact prefixLift 592594
  have htrace : WordTrace (prefixWord ++ tailWord_592594) baseStart_592594 baseEnd_592594 := by
    simpa [prefixWord, tailWord_592594, baseEnd_592594] using wordTrace_append hprefix tailTrace_592594
  have hstable : (prefixWord ++ tailWord_592594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592594).length < 2 ^ (prefixWord ++ tailWord_592594).sum := by decide
  have hdescent : baseEnd_592594 < baseStart_592594 := by decide
  rcases family_descends (prefixWord ++ tailWord_592594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592609 : List Nat := [1, 2, 3, 1, 4, 1, 3, 5]
def baseStart_592609 : Nat := 118140960795 + 592609 * 2 ^ 59
def prefixEnd_592609 : Nat := 4983230072969 + 3 ^ 40 * 592609 * 2
def baseEnd_592609 : Nat := 90160965090482118003599

theorem tailTrace_592609 : CollatzResearch.WordTrace tailWord_592609 prefixEnd_592609 90160965090482118003599 := by
  unfold tailWord_592609
  simp only [CollatzResearch.WordTrace]
  refine ⟨21614225910086277404604881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14409483940057518269736587 21614225910086277404604881)
  ·
    refine ⟨16210669432564708053453661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21614225910086277404604881 16210669432564708053453661)
    ·
      refine ⟨6079001037211765520045123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16210669432564708053453661 6079001037211765520045123)
      ·
        refine ⟨9118501555817648280067685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6079001037211765520045123 9118501555817648280067685)
        ·
          refine ⟨1709719041715809052512691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9118501555817648280067685 1709719041715809052512691)
          ·
            refine ⟨2564578562573713578769037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709719041715809052512691 2564578562573713578769037)
            ·
              refine ⟨961716960965142592038389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2564578562573713578769037 961716960965142592038389)
              ·
                refine ⟨90160965090482118003599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 961716960965142592038389 90160965090482118003599)
                ·
                  rfl

theorem cell20_592609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_592609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592609 prefixEnd_592609 := by exact prefixLift 592609
  have htrace : WordTrace (prefixWord ++ tailWord_592609) baseStart_592609 baseEnd_592609 := by
    simpa [prefixWord, tailWord_592609, baseEnd_592609] using wordTrace_append hprefix tailTrace_592609
  have hstable : (prefixWord ++ tailWord_592609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592609).length < 2 ^ (prefixWord ++ tailWord_592609).sum := by decide
  have hdescent : baseEnd_592609 < baseStart_592609 := by decide
  rcases family_descends (prefixWord ++ tailWord_592609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592623 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_592623 : Nat := 118140960795 + 592623 * 2 ^ 59
def prefixEnd_592623 : Nat := 4983230072969 + 3 ^ 40 * 592623 * 2
def baseEnd_592623 : Nat := 270489285252924527544073

theorem tailTrace_592623 : CollatzResearch.WordTrace tailWord_592623 prefixEnd_592623 270489285252924527544073 := by
  unfold tailWord_592623
  simp only [CollatzResearch.WordTrace]
  refine ⟨21614736532035557795614523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14409824354690371863743015 21614736532035557795614523)
  ·
    refine ⟨32422104798053336693421785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21614736532035557795614523 32422104798053336693421785)
    ·
      refine ⟨24316578598540002520066339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32422104798053336693421785 24316578598540002520066339)
      ·
        refine ⟨36474867897810003780099509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24316578598540002520066339 36474867897810003780099509)
        ·
          refine ⟨3419518865419687854384329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36474867897810003780099509 3419518865419687854384329)
          ·
            refine ⟨2564639149064765890788247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419518865419687854384329 2564639149064765890788247)
            ·
              refine ⟨3846958723597148836182371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564639149064765890788247 3846958723597148836182371)
              ·
                refine ⟨5770438085395723254273557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846958723597148836182371 5770438085395723254273557)
                ·
                  refine ⟨270489285252924527544073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5770438085395723254273557 270489285252924527544073)
                  ·
                    rfl

theorem cell20_592623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_592623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592623 prefixEnd_592623 := by exact prefixLift 592623
  have htrace : WordTrace (prefixWord ++ tailWord_592623) baseStart_592623 baseEnd_592623 := by
    simpa [prefixWord, tailWord_592623, baseEnd_592623] using wordTrace_append hprefix tailTrace_592623
  have hstable : (prefixWord ++ tailWord_592623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592623).length < 2 ^ (prefixWord ++ tailWord_592623).sum := by decide
  have hdescent : baseEnd_592623 < baseStart_592623 := by decide
  rcases family_descends (prefixWord ++ tailWord_592623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592626 : List Nat := [3, 2, 1, 3, 1, 3, 3, 4]
def baseStart_592626 : Nat := 118140960795 + 592626 * 2 ^ 59
def prefixEnd_592626 : Nat := 4983230072969 + 3 ^ 40 * 592626 * 2
def baseEnd_592626 : Nat := 90163551511556616814687

theorem tailTrace_592626 : CollatzResearch.WordTrace tailWord_592626 prefixEnd_592626 90163551511556616814687 := by
  unfold tailWord_592626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403711487756172326993433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14409897300683126205315821 5403711487756172326993433)
  ·
    refine ⟨4052783615817129245245075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5403711487756172326993433 4052783615817129245245075)
    ·
      refine ⟨6079175423725693867867613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4052783615817129245245075 6079175423725693867867613)
      ·
        refine ⟨2279690783897135200450355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6079175423725693867867613 2279690783897135200450355)
        ·
          refine ⟨3419536175845702800675533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279690783897135200450355 3419536175845702800675533)
          ·
            refine ⟨1282326065942138550253325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3419536175845702800675533 1282326065942138550253325)
            ·
              refine ⟨480872274728301956344997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1282326065942138550253325 480872274728301956344997)
              ·
                refine ⟨90163551511556616814687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 480872274728301956344997 90163551511556616814687)
                ·
                  rfl

theorem cell20_592626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_592626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592626 prefixEnd_592626 := by exact prefixLift 592626
  have htrace : WordTrace (prefixWord ++ tailWord_592626) baseStart_592626 baseEnd_592626 := by
    simpa [prefixWord, tailWord_592626, baseEnd_592626] using wordTrace_append hprefix tailTrace_592626
  have hstable : (prefixWord ++ tailWord_592626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592626).length < 2 ^ (prefixWord ++ tailWord_592626).sum := by decide
  have hdescent : baseEnd_592626 < baseStart_592626 := by decide
  rcases family_descends (prefixWord ++ tailWord_592626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592647 : List Nat := [1, 1, 4, 4, 1, 2, 7]
def baseStart_592647 : Nat := 118140960795 + 592647 * 2 ^ 59
def prefixEnd_592647 : Nat := 4983230072969 + 3 ^ 40 * 592647 * 2
def baseEnd_592647 : Nat := 30055582167431901193775

theorem tailTrace_592647 : CollatzResearch.WordTrace tailWord_592647 prefixEnd_592647 30055582167431901193775 := by
  unfold tailWord_592647
  simp only [CollatzResearch.WordTrace]
  refine ⟨21615611883948609894488195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14410407922632406596325463 21615611883948609894488195)
  ·
    refine ⟨32423417825922914841732293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21615611883948609894488195 32423417825922914841732293)
    ·
      refine ⟨6079390842360546532824805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32423417825922914841732293 6079390842360546532824805)
      ·
        refine ⟨1139885782942602474904651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6079390842360546532824805 1139885782942602474904651)
        ·
          refine ⟨1709828674413903712356977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139885782942602474904651 1709828674413903712356977)
          ·
            refine ⟨1282371505810427784267733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709828674413903712356977 1282371505810427784267733)
            ·
              refine ⟨30055582167431901193775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1282371505810427784267733 30055582167431901193775)
              ·
                rfl

theorem cell20_592647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_592647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592647 prefixEnd_592647 := by exact prefixLift 592647
  have htrace : WordTrace (prefixWord ++ tailWord_592647) baseStart_592647 baseEnd_592647 := by
    simpa [prefixWord, tailWord_592647, baseEnd_592647] using wordTrace_append hprefix tailTrace_592647
  have hstable : (prefixWord ++ tailWord_592647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592647).length < 2 ^ (prefixWord ++ tailWord_592647).sum := by decide
  have hdescent : baseEnd_592647 < baseStart_592647 := by decide
  rcases family_descends (prefixWord ++ tailWord_592647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592702 : List Nat := [4, 2, 1, 2, 3, 2, 6]
def baseStart_592702 : Nat := 118140960795 + 592702 * 2 ^ 59
def prefixEnd_592702 : Nat := 4983230072969 + 3 ^ 40 * 592702 * 2
def baseEnd_592702 : Nat := 30058371445061262656713

theorem tailTrace_592702 : CollatzResearch.WordTrace tailWord_592702 prefixEnd_592702 30058371445061262656713 := by
  unfold tailWord_592702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702202237343669285967545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14411745265832902858493573 2702202237343669285967545)
  ·
    refine ⟨2026651678007751964475659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2702202237343669285967545 2026651678007751964475659)
    ·
      refine ⟨3039977517011627946713489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026651678007751964475659 3039977517011627946713489)
      ·
        refine ⟨2279983137758720960035117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3039977517011627946713489 2279983137758720960035117)
        ·
          refine ⟨854993676659520360013169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2279983137758720960035117 854993676659520360013169)
          ·
            refine ⟨641245257494640270009877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854993676659520360013169 641245257494640270009877)
            ·
              refine ⟨30058371445061262656713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 641245257494640270009877 30058371445061262656713)
              ·
                rfl

theorem cell20_592702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 6].length) (baseStart_592702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592702 prefixEnd_592702 := by exact prefixLift 592702
  have htrace : WordTrace (prefixWord ++ tailWord_592702) baseStart_592702 baseEnd_592702 := by
    simpa [prefixWord, tailWord_592702, baseEnd_592702] using wordTrace_append hprefix tailTrace_592702
  have hstable : (prefixWord ++ tailWord_592702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592702).length < 2 ^ (prefixWord ++ tailWord_592702).sum := by decide
  have hdescent : baseEnd_592702 < baseStart_592702 := by decide
  rcases family_descends (prefixWord ++ tailWord_592702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592708 : List Nat := [2, 3, 4, 2, 1, 1, 3, 2, 2]
def baseStart_592708 : Nat := 118140960795 + 592708 * 2 ^ 59
def prefixEnd_592708 : Nat := 4983230072969 + 3 ^ 40 * 592708 * 2
def baseEnd_592708 : Nat := 270528081569042009710393

theorem tailTrace_592708 : CollatzResearch.WordTrace tailWord_592708 prefixEnd_592708 270528081569042009710393 := by
  unfold tailWord_592708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10808918368363808656229389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14411891157818411541639185 10808918368363808656229389)
  ·
    refine ⟨4053344388136428246086021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10808918368363808656229389 4053344388136428246086021)
    ·
      refine ⟨760002072775580296141129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4053344388136428246086021 760002072775580296141129)
      ·
        refine ⟨570001554581685222105847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760002072775580296141129 570001554581685222105847)
        ·
          refine ⟨855002331872527833158771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570001554581685222105847 855002331872527833158771)
          ·
            refine ⟨1282503497808791749738157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855002331872527833158771 1282503497808791749738157)
            ·
              refine ⟨480938811678296906151809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1282503497808791749738157 480938811678296906151809)
              ·
                refine ⟨360704108758722679613857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480938811678296906151809 360704108758722679613857)
                ·
                  refine ⟨270528081569042009710393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360704108758722679613857 270528081569042009710393)
                  ·
                    rfl

theorem cell20_592708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_592708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592708 prefixEnd_592708 := by exact prefixLift 592708
  have htrace : WordTrace (prefixWord ++ tailWord_592708) baseStart_592708 baseEnd_592708 := by
    simpa [prefixWord, tailWord_592708, baseEnd_592708] using wordTrace_append hprefix tailTrace_592708
  have hstable : (prefixWord ++ tailWord_592708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592708).length < 2 ^ (prefixWord ++ tailWord_592708).sum := by decide
  have hdescent : baseEnd_592708 < baseStart_592708 := by decide
  rcases family_descends (prefixWord ++ tailWord_592708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592716 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_592716 : Nat := 118140960795 + 592716 * 2 ^ 59
def prefixEnd_592716 : Nat := 4983230072969 + 3 ^ 40 * 592716 * 2
def baseEnd_592716 : Nat := 270531732987029537443693

theorem tailTrace_592716 : CollatzResearch.WordTrace tailWord_592716 prefixEnd_592716 270531732987029537443693 := by
  unfold tailWord_592716
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809064260349317339375001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14412085680465756452500001 10809064260349317339375001)
  ·
    refine ⟨8106798195261988004531251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10809064260349317339375001 8106798195261988004531251)
    ·
      refine ⟨12160197292892982006796877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8106798195261988004531251 12160197292892982006796877)
      ·
        refine ⟨4560073984834868252548829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12160197292892982006796877 4560073984834868252548829)
        ·
          refine ⟨1710027744313075594705811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4560073984834868252548829 1710027744313075594705811)
          ·
            refine ⟨2565041616469613392058717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710027744313075594705811 2565041616469613392058717)
            ·
              refine ⟨961890606176105022022019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2565041616469613392058717 961890606176105022022019)
              ·
                refine ⟨1442835909264157533033029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961890606176105022022019 1442835909264157533033029)
                ·
                  refine ⟨270531732987029537443693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442835909264157533033029 270531732987029537443693)
                  ·
                    rfl

theorem cell20_592716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_592716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592716 prefixEnd_592716 := by exact prefixLift 592716
  have htrace : WordTrace (prefixWord ++ tailWord_592716) baseStart_592716 baseEnd_592716 := by
    simpa [prefixWord, tailWord_592716, baseEnd_592716] using wordTrace_append hprefix tailTrace_592716
  have hstable : (prefixWord ++ tailWord_592716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592716).length < 2 ^ (prefixWord ++ tailWord_592716).sum := by decide
  have hdescent : baseEnd_592716 < baseStart_592716 := by decide
  rcases family_descends (prefixWord ++ tailWord_592716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592751 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_592751 : Nat := 118140960795 + 592751 * 2 ^ 59
def prefixEnd_592751 : Nat := 4983230072969 + 3 ^ 40 * 592751 * 2
def baseEnd_592751 : Nat := 270547707940724971276883

theorem tailTrace_592751 : CollatzResearch.WordTrace tailWord_592751 prefixEnd_592751 270547707940724971276883 := by
  unfold tailWord_592751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21619405075571835656274107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14412936717047890437516071 21619405075571835656274107)
  ·
    refine ⟨32429107613357753484411161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21619405075571835656274107 32429107613357753484411161)
    ·
      refine ⟨24321830710018315113308371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32429107613357753484411161 24321830710018315113308371)
      ·
        refine ⟨36482746065027472669962557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24321830710018315113308371 36482746065027472669962557)
        ·
          refine ⟨13681029774385302251235959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36482746065027472669962557 13681029774385302251235959)
          ·
            refine ⟨20521544661577953376853939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13681029774385302251235959 20521544661577953376853939)
            ·
              refine ⟨30782316992366930065280909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20521544661577953376853939 30782316992366930065280909)
              ·
                refine ⟨11543368872137598774480341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30782316992366930065280909 11543368872137598774480341)
                ·
                  refine ⟨270547707940724971276883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11543368872137598774480341 270547707940724971276883)
                  ·
                    rfl

theorem cell20_592751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_592751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592751 prefixEnd_592751 := by exact prefixLift 592751
  have htrace : WordTrace (prefixWord ++ tailWord_592751) baseStart_592751 baseEnd_592751 := by
    simpa [prefixWord, tailWord_592751, baseEnd_592751] using wordTrace_append hprefix tailTrace_592751
  have hstable : (prefixWord ++ tailWord_592751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592751).length < 2 ^ (prefixWord ++ tailWord_592751).sum := by decide
  have hdescent : baseEnd_592751 < baseStart_592751 := by decide
  rcases family_descends (prefixWord ++ tailWord_592751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592778 : List Nat := [3, 1, 2, 4, 1, 3, 1, 5]
def baseStart_592778 : Nat := 118140960795 + 592778 * 2 ^ 59
def prefixEnd_592778 : Nat := 4983230072969 + 3 ^ 40 * 592778 * 2
def baseEnd_592778 : Nat := 90186677158810959125591

theorem tailTrace_592778 : CollatzResearch.WordTrace tailWord_592778 prefixEnd_592778 90186677158810959125591 := by
  unfold tailWord_592778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405097461618504816876747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14413593230982679511671325 5405097461618504816876747)
  ·
    refine ⟨8107646192427757225315121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405097461618504816876747 8107646192427757225315121)
    ·
      refine ⟨6080734644320817918986341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8107646192427757225315121 6080734644320817918986341)
      ·
        refine ⟨1140137745810153359809939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6080734644320817918986341 1140137745810153359809939)
        ·
          refine ⟨1710206618715230039714909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140137745810153359809939 1710206618715230039714909)
          ·
            refine ⟨641327482018211264893091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1710206618715230039714909 641327482018211264893091)
            ·
              refine ⟨961991223027316897339637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641327482018211264893091 961991223027316897339637)
              ·
                refine ⟨90186677158810959125591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 961991223027316897339637 90186677158810959125591)
                ·
                  rfl

theorem cell20_592778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_592778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592778 prefixEnd_592778 := by exact prefixLift 592778
  have htrace : WordTrace (prefixWord ++ tailWord_592778) baseStart_592778 baseEnd_592778 := by
    simpa [prefixWord, tailWord_592778, baseEnd_592778] using wordTrace_append hprefix tailTrace_592778
  have hstable : (prefixWord ++ tailWord_592778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592778).length < 2 ^ (prefixWord ++ tailWord_592778).sum := by decide
  have hdescent : baseEnd_592778 < baseStart_592778 := by decide
  rcases family_descends (prefixWord ++ tailWord_592778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592830 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_592830 : Nat := 118140960795 + 592830 * 2 ^ 59
def prefixEnd_592830 : Nat := 4983230072969 + 3 ^ 40 * 592830 * 2
def baseEnd_592830 : Nat := 270583765693351807643227

theorem tailTrace_592830 : CollatzResearch.WordTrace tailWord_592830 prefixEnd_592830 270583765693351807643227 := by
  unfold tailWord_592830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702785805285704018549993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14414857628190421432266629 2702785805285704018549993)
  ·
    refine ⟨2027089353964278013912495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2702785805285704018549993 2027089353964278013912495)
    ·
      refine ⟨3040634030946417020868743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2027089353964278013912495 3040634030946417020868743)
      ·
        refine ⟨4560951046419625531303115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040634030946417020868743 4560951046419625531303115)
        ·
          refine ⟨6841426569629438296954673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560951046419625531303115 6841426569629438296954673)
          ·
            refine ⟨5131069927222078722716005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6841426569629438296954673 5131069927222078722716005)
            ·
              refine ⟨962075611354139760509251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5131069927222078722716005 962075611354139760509251)
              ·
                refine ⟨1443113417031209640763877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962075611354139760509251 1443113417031209640763877)
                ·
                  refine ⟨270583765693351807643227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443113417031209640763877 270583765693351807643227)
                  ·
                    rfl

theorem cell20_592830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_592830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592830 prefixEnd_592830 := by exact prefixLift 592830
  have htrace : WordTrace (prefixWord ++ tailWord_592830) baseStart_592830 baseEnd_592830 := by
    simpa [prefixWord, tailWord_592830, baseEnd_592830] using wordTrace_append hprefix tailTrace_592830
  have hstable : (prefixWord ++ tailWord_592830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592830).length < 2 ^ (prefixWord ++ tailWord_592830).sum := by decide
  have hdescent : baseEnd_592830 < baseStart_592830 := by decide
  rcases family_descends (prefixWord ++ tailWord_592830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592840 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_592840 : Nat := 118140960795 + 592840 * 2 ^ 59
def prefixEnd_592840 : Nat := 4983230072969 + 3 ^ 40 * 592840 * 2
def baseEnd_592840 : Nat := 270588329965836217309853

theorem tailTrace_592840 : CollatzResearch.WordTrace tailWord_592840 prefixEnd_592840 270588329965836217309853 := by
  unfold tailWord_592840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811325586124701928131987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14415100781499602570842649 10811325586124701928131987)
  ·
    refine ⟨16216988379187052892197981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10811325586124701928131987 16216988379187052892197981)
    ·
      refine ⟨6081370642195144834574243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16216988379187052892197981 6081370642195144834574243)
      ·
        refine ⟨9122055963292717251861365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081370642195144834574243 9122055963292717251861365)
        ·
          refine ⟨855192746558692242362003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9122055963292717251861365 855192746558692242362003)
          ·
            refine ⟨1282789119838038363543005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855192746558692242362003 1282789119838038363543005)
            ·
              refine ⟨481045919939264386328627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1282789119838038363543005 481045919939264386328627)
              ·
                refine ⟨721568879908896579492941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481045919939264386328627 721568879908896579492941)
                ·
                  refine ⟨270588329965836217309853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721568879908896579492941 270588329965836217309853)
                  ·
                    rfl

theorem cell20_592840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_592840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592840 prefixEnd_592840 := by exact prefixLift 592840
  have htrace : WordTrace (prefixWord ++ tailWord_592840) baseStart_592840 baseEnd_592840 := by
    simpa [prefixWord, tailWord_592840, baseEnd_592840] using wordTrace_append hprefix tailTrace_592840
  have hstable : (prefixWord ++ tailWord_592840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592840).length < 2 ^ (prefixWord ++ tailWord_592840).sum := by decide
  have hdescent : baseEnd_592840 < baseStart_592840 := by decide
  rcases family_descends (prefixWord ++ tailWord_592840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592854 : List Nat := [5, 2, 1, 1, 2, 2, 1, 6]
def baseStart_592854 : Nat := 118140960795 + 592854 * 2 ^ 59
def prefixEnd_592854 : Nat := 4983230072969 + 3 ^ 40 * 592854 * 2
def baseEnd_592854 : Nat := 90198239982438130281043

theorem tailTrace_592854 : CollatzResearch.WordTrace tailWord_592854 prefixEnd_592854 90198239982438130281043 := by
  unfold tailWord_592854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351447612137417765454601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14415441196132456164849077 1351447612137417765454601)
  ·
    refine ⟨1013585709103063324090951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1351447612137417765454601 1013585709103063324090951)
    ·
      refine ⟨1520378563654594986136427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013585709103063324090951 1520378563654594986136427)
      ·
        refine ⟨2280567845481892479204641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520378563654594986136427 2280567845481892479204641)
        ·
          refine ⟨1710425884111419359403481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2280567845481892479204641 1710425884111419359403481)
          ·
            refine ⟨1282819413083564519552611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710425884111419359403481 1282819413083564519552611)
            ·
              refine ⟨1924229119625346779328917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282819413083564519552611 1924229119625346779328917)
              ·
                refine ⟨90198239982438130281043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1924229119625346779328917 90198239982438130281043)
                ·
                  rfl

theorem cell20_592854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_592854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592854 prefixEnd_592854 := by exact prefixLift 592854
  have htrace : WordTrace (prefixWord ++ tailWord_592854) baseStart_592854 baseEnd_592854 := by
    simpa [prefixWord, tailWord_592854, baseEnd_592854] using wordTrace_append hprefix tailTrace_592854
  have hstable : (prefixWord ++ tailWord_592854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592854).length < 2 ^ (prefixWord ++ tailWord_592854).sum := by decide
  have hdescent : baseEnd_592854 < baseStart_592854 := by decide
  rcases family_descends (prefixWord ++ tailWord_592854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592868 : List Nat := [2, 3, 1, 1, 1, 1, 2, 7, 2]
def baseStart_592868 : Nat := 118140960795 + 592868 * 2 ^ 59
def prefixEnd_592868 : Nat := 4983230072969 + 3 ^ 40 * 592868 * 2
def baseEnd_592868 : Nat := 270601109928792564376405

theorem tailTrace_592868 : CollatzResearch.WordTrace tailWord_592868 prefixEnd_592868 270601109928792564376405 := by
  unfold tailWord_592868
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811836208073982319141629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14415781610765309758855505 10811836208073982319141629)
  ·
    refine ⟨4054438578027743369678111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10811836208073982319141629 4054438578027743369678111)
    ·
      refine ⟨6081657867041615054517167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054438578027743369678111 6081657867041615054517167)
      ·
        refine ⟨9122486800562422581775751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081657867041615054517167 9122486800562422581775751)
        ·
          refine ⟨13683730200843633872663627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9122486800562422581775751 13683730200843633872663627)
          ·
            refine ⟨20525595301265450808995441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13683730200843633872663627 20525595301265450808995441)
            ·
              refine ⟨15394196475949088106746581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20525595301265450808995441 15394196475949088106746581)
              ·
                refine ⟨360801479905056752501873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15394196475949088106746581 360801479905056752501873)
                ·
                  refine ⟨270601109928792564376405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360801479905056752501873 270601109928792564376405)
                  ·
                    rfl

theorem cell20_592868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_592868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592868 prefixEnd_592868 := by exact prefixLift 592868
  have htrace : WordTrace (prefixWord ++ tailWord_592868) baseStart_592868 baseEnd_592868 := by
    simpa [prefixWord, tailWord_592868, baseEnd_592868] using wordTrace_append hprefix tailTrace_592868
  have hstable : (prefixWord ++ tailWord_592868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592868).length < 2 ^ (prefixWord ++ tailWord_592868).sum := by decide
  have hdescent : baseEnd_592868 < baseStart_592868 := by decide
  rcases family_descends (prefixWord ++ tailWord_592868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_592944 : List Nat := [2, 1, 1, 1, 2, 4, 3, 4, 2]
def baseStart_592944 : Nat := 118140960795 + 592944 * 2 ^ 59
def prefixEnd_592944 : Nat := 4983230072969 + 3 ^ 40 * 592944 * 2
def baseEnd_592944 : Nat := 270635798399674077842761

theorem tailTrace_592944 : CollatzResearch.WordTrace tailWord_592944 prefixEnd_592944 270635798399674077842761 := by
  unfold tailWord_592944
  simp only [CollatzResearch.WordTrace]
  refine ⟨10813222181936314809024943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14417629575915086412033257 10813222181936314809024943)
  ·
    refine ⟨16219833272904472213537415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10813222181936314809024943 16219833272904472213537415)
    ·
      refine ⟨24329749909356708320306123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16219833272904472213537415 24329749909356708320306123)
      ·
        refine ⟨36494624864035062480459185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24329749909356708320306123 36494624864035062480459185)
        ·
          refine ⟨27370968648026296860344389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36494624864035062480459185 27370968648026296860344389)
          ·
            refine ⟨5132056621504930661314573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27370968648026296860344389 5132056621504930661314573)
            ·
              refine ⟨1924521233064348997992965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5132056621504930661314573 1924521233064348997992965)
              ·
                refine ⟨360847731199565437123681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1924521233064348997992965 360847731199565437123681)
                ·
                  refine ⟨270635798399674077842761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360847731199565437123681 270635798399674077842761)
                  ·
                    rfl

theorem cell20_592944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_592944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_592944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_592944 prefixEnd_592944 := by exact prefixLift 592944
  have htrace : WordTrace (prefixWord ++ tailWord_592944) baseStart_592944 baseEnd_592944 := by
    simpa [prefixWord, tailWord_592944, baseEnd_592944] using wordTrace_append hprefix tailTrace_592944
  have hstable : (prefixWord ++ tailWord_592944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_592944).length < 2 ^ (prefixWord ++ tailWord_592944).sum := by decide
  have hdescent : baseEnd_592944 < baseStart_592944 := by decide
  rcases family_descends (prefixWord ++ tailWord_592944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593010 : List Nat := [3, 2, 1, 2, 2, 1, 2, 7]
def baseStart_593010 : Nat := 118140960795 + 593010 * 2 ^ 59
def prefixEnd_593010 : Nat := 4983230072969 + 3 ^ 40 * 593010 * 2
def baseEnd_593010 : Nat := 90221974199357060547497

theorem tailTrace_593010 : CollatzResearch.WordTrace tailWord_593010 prefixEnd_593010 90221974199357060547497 := by
  unfold tailWord_593010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407212895408380722488121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14419234387755681926634989 5407212895408380722488121)
  ·
    refine ⟨4055409671556285541866091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5407212895408380722488121 4055409671556285541866091)
    ·
      refine ⟨6083114507334428312799137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055409671556285541866091 6083114507334428312799137)
      ·
        refine ⟨4562335880500821234599353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6083114507334428312799137 4562335880500821234599353)
        ·
          refine ⟨3421751910375615925949515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4562335880500821234599353 3421751910375615925949515)
          ·
            refine ⟨5132627865563423888924273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3421751910375615925949515 5132627865563423888924273)
            ·
              refine ⟨3849470899172567916693205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5132627865563423888924273 3849470899172567916693205)
              ·
                refine ⟨90221974199357060547497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3849470899172567916693205 90221974199357060547497)
                ·
                  rfl

theorem cell20_593010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_593010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593010 prefixEnd_593010 := by exact prefixLift 593010
  have htrace : WordTrace (prefixWord ++ tailWord_593010) baseStart_593010 baseEnd_593010 := by
    simpa [prefixWord, tailWord_593010, baseEnd_593010] using wordTrace_append hprefix tailTrace_593010
  have hstable : (prefixWord ++ tailWord_593010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593010).length < 2 ^ (prefixWord ++ tailWord_593010).sum := by decide
  have hdescent : baseEnd_593010 < baseStart_593010 := by decide
  rcases family_descends (prefixWord ++ tailWord_593010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593048 : List Nat := [2, 1, 2, 4, 2, 1, 8]
def baseStart_593048 : Nat := 118140960795 + 593048 * 2 ^ 59
def prefixEnd_593048 : Nat := 4983230072969 + 3 ^ 40 * 593048 * 2
def baseEnd_593048 : Nat := 30075918537056882041741

theorem tailTrace_593048 : CollatzResearch.WordTrace tailWord_593048 prefixEnd_593048 30075918537056882041741 := by
  unfold tailWord_593048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10815118777747927689917899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14420158370330570253223865 10815118777747927689917899)
  ·
    refine ⟨16222678166621891534876849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10815118777747927689917899 16222678166621891534876849)
    ·
      refine ⟨12167008624966418651157637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16222678166621891534876849 12167008624966418651157637)
      ·
        refine ⟨2281314117181203497092057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12167008624966418651157637 2281314117181203497092057)
        ·
          refine ⟨1710985587885902622819043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2281314117181203497092057 1710985587885902622819043)
          ·
            refine ⟨2566478381828853934228565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710985587885902622819043 2566478381828853934228565)
            ·
              refine ⟨30075918537056882041741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2566478381828853934228565 30075918537056882041741)
              ·
                rfl

theorem cell20_593048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 8].length) (baseStart_593048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593048 prefixEnd_593048 := by exact prefixLift 593048
  have htrace : WordTrace (prefixWord ++ tailWord_593048) baseStart_593048 baseEnd_593048 := by
    simpa [prefixWord, tailWord_593048, baseEnd_593048] using wordTrace_append hprefix tailTrace_593048
  have hstable : (prefixWord ++ tailWord_593048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593048).length < 2 ^ (prefixWord ++ tailWord_593048).sum := by decide
  have hdescent : baseEnd_593048 < baseStart_593048 := by decide
  rcases family_descends (prefixWord ++ tailWord_593048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593124 : List Nat := [2, 3, 1, 1, 1, 2, 5, 5]
def baseStart_593124 : Nat := 118140960795 + 593124 * 2 ^ 59
def prefixEnd_593124 : Nat := 4983230072969 + 3 ^ 40 * 593124 * 2
def baseEnd_593124 : Nat := 90239318434797817280675

theorem tailTrace_593124 : CollatzResearch.WordTrace tailWord_593124 prefixEnd_593124 90239318434797817280675 := by
  unfold tailWord_593124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10816504751610260179801213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14422006335480346906401617 10816504751610260179801213)
  ·
    refine ⟨4056189281853847567425455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10816504751610260179801213 4056189281853847567425455)
    ·
      refine ⟨6084283922780771351138183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4056189281853847567425455 6084283922780771351138183)
      ·
        refine ⟨9126425884171157026707275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6084283922780771351138183 9126425884171157026707275)
        ·
          refine ⟨13689638826256735540060913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9126425884171157026707275 13689638826256735540060913)
          ·
            refine ⟨10267229119692551655045685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13689638826256735540060913 10267229119692551655045685)
            ·
              refine ⟨962552729971176717660533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10267229119692551655045685 962552729971176717660533)
              ·
                refine ⟨90239318434797817280675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 962552729971176717660533 90239318434797817280675)
                ·
                  rfl

theorem cell20_593124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_593124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593124 prefixEnd_593124 := by exact prefixLift 593124
  have htrace : WordTrace (prefixWord ++ tailWord_593124) baseStart_593124 baseEnd_593124 := by
    simpa [prefixWord, tailWord_593124, baseEnd_593124] using wordTrace_append hprefix tailTrace_593124
  have hstable : (prefixWord ++ tailWord_593124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593124).length < 2 ^ (prefixWord ++ tailWord_593124).sum := by decide
  have hdescent : baseEnd_593124 < baseStart_593124 := by decide
  rcases family_descends (prefixWord ++ tailWord_593124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593169 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_593169 : Nat := 118140960795 + 593169 * 2 ^ 59
def prefixEnd_593169 : Nat := 4983230072969 + 3 ^ 40 * 593169 * 2
def baseEnd_593169 : Nat := 270738494530573295341841

theorem tailTrace_593169 : CollatzResearch.WordTrace tailWord_593169 prefixEnd_593169 270738494530573295341841 := by
  unfold tailWord_593169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21634650788057493044990561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14423100525371662029993707 21634650788057493044990561)
  ·
    refine ⟨16225988091043119783742921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21634650788057493044990561 16225988091043119783742921)
    ·
      refine ⟨12169491068282339837807191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16225988091043119783742921 12169491068282339837807191)
      ·
        refine ⟨18254236602423509756710787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169491068282339837807191 18254236602423509756710787)
        ·
          refine ⟨27381354903635264635066181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18254236602423509756710787 27381354903635264635066181)
          ·
            refine ⟨5134004044431612119074909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27381354903635264635066181 5134004044431612119074909)
            ·
              refine ⟨1925251516661854544653091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5134004044431612119074909 1925251516661854544653091)
              ·
                refine ⟨2887877274992781816979637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925251516661854544653091 2887877274992781816979637)
                ·
                  refine ⟨270738494530573295341841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2887877274992781816979637 270738494530573295341841)
                  ·
                    rfl

theorem cell20_593169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_593169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593169 prefixEnd_593169 := by exact prefixLift 593169
  have htrace : WordTrace (prefixWord ++ tailWord_593169) baseStart_593169 baseEnd_593169 := by
    simpa [prefixWord, tailWord_593169, baseEnd_593169] using wordTrace_append hprefix tailTrace_593169
  have hstable : (prefixWord ++ tailWord_593169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593169).length < 2 ^ (prefixWord ++ tailWord_593169).sum := by decide
  have hdescent : baseEnd_593169 < baseStart_593169 := by decide
  rcases family_descends (prefixWord ++ tailWord_593169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593217 : List Nat := [1, 2, 5, 2, 1, 3, 6]
def baseStart_593217 : Nat := 118140960795 + 593217 * 2 ^ 59
def prefixEnd_593217 : Nat := 4983230072969 + 3 ^ 40 * 593217 * 2
def baseEnd_593217 : Nat := 30084489226499829082405

theorem tailTrace_593217 : CollatzResearch.WordTrace tailWord_593217 prefixEnd_593217 30084489226499829082405 := by
  unfold tailWord_593217
  simp only [CollatzResearch.WordTrace]
  refine ⟨21636401491883597242737905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14424267661255731495158603 21636401491883597242737905)
  ·
    refine ⟨16227301118912697932053429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21636401491883597242737905 16227301118912697932053429)
    ·
      refine ⟨1521309479898065431130009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16227301118912697932053429 1521309479898065431130009)
      ·
        refine ⟨1140982109923549073347507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1521309479898065431130009 1140982109923549073347507)
        ·
          refine ⟨1711473164885323610021261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140982109923549073347507 1711473164885323610021261)
          ·
            refine ⟨641802436831996353757973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1711473164885323610021261 641802436831996353757973)
            ·
              refine ⟨30084489226499829082405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 641802436831996353757973 30084489226499829082405)
              ·
                rfl

theorem cell20_593217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 6].length) (baseStart_593217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593217 prefixEnd_593217 := by exact prefixLift 593217
  have htrace : WordTrace (prefixWord ++ tailWord_593217) baseStart_593217 baseEnd_593217 := by
    simpa [prefixWord, tailWord_593217, baseEnd_593217] using wordTrace_append hprefix tailTrace_593217
  have hstable : (prefixWord ++ tailWord_593217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593217).length < 2 ^ (prefixWord ++ tailWord_593217).sum := by decide
  have hdescent : baseEnd_593217 < baseStart_593217 := by decide
  rcases family_descends (prefixWord ++ tailWord_593217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593278 : List Nat := [4, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_593278 : Nat := 118140960795 + 593278 * 2 ^ 59
def prefixEnd_593278 : Nat := 4983230072969 + 3 ^ 40 * 593278 * 2
def baseEnd_593278 : Nat := 270788245100653360708063

theorem tailTrace_593278 : CollatzResearch.WordTrace tailWord_593278 prefixEnd_593278 270788245100653360708063 := by
  unfold tailWord_593278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704828293082825582588561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14425750896441736440472325 2704828293082825582588561)
  ·
    refine ⟨2028621219812119186941421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2704828293082825582588561 2028621219812119186941421)
    ·
      refine ⟨760732957429544695103033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2028621219812119186941421 760732957429544695103033)
      ·
        refine ⟨570549718072158521327275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760732957429544695103033 570549718072158521327275)
        ·
          refine ⟨855824577108237781990913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570549718072158521327275 855824577108237781990913)
          ·
            refine ⟨641868432831178336493185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855824577108237781990913 641868432831178336493185)
            ·
              refine ⟨481401324623383752369889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641868432831178336493185 481401324623383752369889)
              ·
                refine ⟨361050993467537814277417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481401324623383752369889 361050993467537814277417)
                ·
                  refine ⟨270788245100653360708063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361050993467537814277417 270788245100653360708063)
                  ·
                    rfl

theorem cell20_593278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_593278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593278 prefixEnd_593278 := by exact prefixLift 593278
  have htrace : WordTrace (prefixWord ++ tailWord_593278) baseStart_593278 baseEnd_593278 := by
    simpa [prefixWord, tailWord_593278, baseEnd_593278] using wordTrace_append hprefix tailTrace_593278
  have hstable : (prefixWord ++ tailWord_593278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593278).length < 2 ^ (prefixWord ++ tailWord_593278).sum := by decide
  have hdescent : baseEnd_593278 < baseStart_593278 := by decide
  rcases family_descends (prefixWord ++ tailWord_593278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593282 : List Nat := [3, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_593282 : Nat := 118140960795 + 593282 * 2 ^ 59
def prefixEnd_593282 : Nat := 4983230072969 + 3 ^ 40 * 593282 * 2
def baseEnd_593282 : Nat := 270790070809647124574713

theorem tailTrace_593282 : CollatzResearch.WordTrace tailWord_593282 prefixEnd_593282 270790070809647124574713 := by
  unfold tailWord_593282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409693059162028335963525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14425848157765408895902733 5409693059162028335963525)
  ·
    refine ⟨1014317448592880312993161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5409693059162028335963525 1014317448592880312993161)
    ·
      refine ⟨760738086444660234744871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1014317448592880312993161 760738086444660234744871)
      ·
        refine ⟨1141107129666990352117307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760738086444660234744871 1141107129666990352117307)
        ·
          refine ⟨1711660694500485528175961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1141107129666990352117307 1711660694500485528175961)
          ·
            refine ⟨1283745520875364146131971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1711660694500485528175961 1283745520875364146131971)
            ·
              refine ⟨1925618281313046219197957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283745520875364146131971 1925618281313046219197957)
              ·
                refine ⟨361053427746196166099617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1925618281313046219197957 361053427746196166099617)
                ·
                  refine ⟨270790070809647124574713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361053427746196166099617 270790070809647124574713)
                  ·
                    rfl

theorem cell20_593282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_593282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593282 prefixEnd_593282 := by exact prefixLift 593282
  have htrace : WordTrace (prefixWord ++ tailWord_593282) baseStart_593282 baseEnd_593282 := by
    simpa [prefixWord, tailWord_593282, baseEnd_593282] using wordTrace_append hprefix tailTrace_593282
  have hstable : (prefixWord ++ tailWord_593282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593282).length < 2 ^ (prefixWord ++ tailWord_593282).sum := by decide
  have hdescent : baseEnd_593282 < baseStart_593282 := by decide
  rcases family_descends (prefixWord ++ tailWord_593282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593320 : List Nat := [2, 1, 6, 1, 2, 1, 2, 3, 2]
def baseStart_593320 : Nat := 118140960795 + 593320 * 2 ^ 59
def prefixEnd_593320 : Nat := 4983230072969 + 3 ^ 40 * 593320 * 2
def baseEnd_593320 : Nat := 270807415045087881307891

theorem tailTrace_593320 : CollatzResearch.WordTrace tailWord_593320 prefixEnd_593320 270807415045087881307891 := by
  unfold tailWord_593320
  simp only [CollatzResearch.WordTrace]
  refine ⟨10820079105255222916868707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14426772140340297222491609 10820079105255222916868707)
  ·
    refine ⟨16230118657882834375303061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10820079105255222916868707 16230118657882834375303061)
    ·
      refine ⟨760786812088257861342331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16230118657882834375303061 760786812088257861342331)
      ·
        refine ⟨1141180218132386792013497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760786812088257861342331 1141180218132386792013497)
        ·
          refine ⟨855885163599290094010123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141180218132386792013497 855885163599290094010123)
          ·
            refine ⟨1283827745398935141015185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855885163599290094010123 1283827745398935141015185)
            ·
              refine ⟨962870809049201355761389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283827745398935141015185 962870809049201355761389)
              ·
                refine ⟨361076553393450508410521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 962870809049201355761389 361076553393450508410521)
                ·
                  refine ⟨270807415045087881307891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361076553393450508410521 270807415045087881307891)
                  ·
                    rfl

theorem cell20_593320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_593320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593320 prefixEnd_593320 := by exact prefixLift 593320
  have htrace : WordTrace (prefixWord ++ tailWord_593320) baseStart_593320 baseEnd_593320 := by
    simpa [prefixWord, tailWord_593320, baseEnd_593320] using wordTrace_append hprefix tailTrace_593320
  have hstable : (prefixWord ++ tailWord_593320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593320).length < 2 ^ (prefixWord ++ tailWord_593320).sum := by decide
  have hdescent : baseEnd_593320 < baseStart_593320 := by decide
  rcases family_descends (prefixWord ++ tailWord_593320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593335 : List Nat := [1, 1, 3, 1, 3, 2, 9]
def baseStart_593335 : Nat := 118140960795 + 593335 * 2 ^ 59
def prefixEnd_593335 : Nat := 4983230072969 + 3 ^ 40 * 593335 * 2
def baseEnd_593335 : Nat := 30090473494868277311981

theorem tailTrace_593335 : CollatzResearch.WordTrace tailWord_593335 prefixEnd_593335 30090473494868277311981 := by
  unfold tailWord_593335
  simp only [CollatzResearch.WordTrace]
  refine ⟨21640705305456103395533459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14427136870304068930355639 21640705305456103395533459)
  ·
    refine ⟨32461057958184155093300189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21640705305456103395533459 32461057958184155093300189)
    ·
      refine ⟨12172896734319058159987571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32461057958184155093300189 12172896734319058159987571)
      ·
        refine ⟨18259345101478587239981357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12172896734319058159987571 18259345101478587239981357)
        ·
          refine ⟨6847254413054470214993009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18259345101478587239981357 6847254413054470214993009)
          ·
            refine ⟨5135440809790852661244757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6847254413054470214993009 5135440809790852661244757)
            ·
              refine ⟨30090473494868277311981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5135440809790852661244757 30090473494868277311981)
              ·
                rfl

theorem cell20_593335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_593335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593335 prefixEnd_593335 := by exact prefixLift 593335
  have htrace : WordTrace (prefixWord ++ tailWord_593335) baseStart_593335 baseEnd_593335 := by
    simpa [prefixWord, tailWord_593335, baseEnd_593335] using wordTrace_append hprefix tailTrace_593335
  have hstable : (prefixWord ++ tailWord_593335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593335).length < 2 ^ (prefixWord ++ tailWord_593335).sum := by decide
  have hdescent : baseEnd_593335 < baseStart_593335 := by decide
  rcases family_descends (prefixWord ++ tailWord_593335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593359 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 3]
def baseStart_593359 : Nat := 118140960795 + 593359 * 2 ^ 59
def prefixEnd_593359 : Nat := 4983230072969 + 3 ^ 40 * 593359 * 2
def baseEnd_593359 : Nat := 270825215707777079007731

theorem tailTrace_593359 : CollatzResearch.WordTrace tailWord_593359 prefixEnd_593359 270825215707777079007731 := by
  unfold tailWord_593359
  simp only [CollatzResearch.WordTrace]
  refine ⟨21641580657369155494407131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14427720438246103662938087 21641580657369155494407131)
  ·
    refine ⟨32462370986053733241610697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21641580657369155494407131 32462370986053733241610697)
    ·
      refine ⟨24346778239540299931208023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32462370986053733241610697 24346778239540299931208023)
      ·
        refine ⟨36520167359310449896812035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24346778239540299931208023 36520167359310449896812035)
        ·
          refine ⟨54780251038965674845218053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36520167359310449896812035 54780251038965674845218053)
          ·
            refine ⟨10271297069806064033478385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54780251038965674845218053 10271297069806064033478385)
            ·
              refine ⟨7703472802354548025108789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10271297069806064033478385 7703472802354548025108789)
              ·
                refine ⟨722200575220738877353949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7703472802354548025108789 722200575220738877353949)
                ·
                  refine ⟨270825215707777079007731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722200575220738877353949 270825215707777079007731)
                  ·
                    rfl

theorem cell20_593359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_593359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593359 prefixEnd_593359 := by exact prefixLift 593359
  have htrace : WordTrace (prefixWord ++ tailWord_593359) baseStart_593359 baseEnd_593359 := by
    simpa [prefixWord, tailWord_593359, baseEnd_593359] using wordTrace_append hprefix tailTrace_593359
  have hstable : (prefixWord ++ tailWord_593359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593359).length < 2 ^ (prefixWord ++ tailWord_593359).sum := by decide
  have hdescent : baseEnd_593359 < baseStart_593359 := by decide
  rcases family_descends (prefixWord ++ tailWord_593359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593369 : List Nat := [1, 2, 1, 2, 4, 4, 2, 4]
def baseStart_593369 : Nat := 118140960795 + 593369 * 2 ^ 59
def prefixEnd_593369 : Nat := 4983230072969 + 3 ^ 40 * 593369 * 2
def baseEnd_593369 : Nat := 90276593326753829558119

theorem tailTrace_593369 : CollatzResearch.WordTrace tailWord_593369 prefixEnd_593369 90276593326753829558119 := by
  unfold tailWord_593369
  simp only [CollatzResearch.WordTrace]
  refine ⟨21641945387332927202271161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14427963591555284801514107 21641945387332927202271161)
  ·
    refine ⟨16231459040499695401703371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21641945387332927202271161 16231459040499695401703371)
    ·
      refine ⟨24347188560749543102555057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16231459040499695401703371 24347188560749543102555057)
      ·
        refine ⟨18260391420562157326916293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24347188560749543102555057 18260391420562157326916293)
        ·
          refine ⟨3423823391355404498796805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18260391420562157326916293 3423823391355404498796805)
          ·
            refine ⟨641966885879138343524401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3423823391355404498796805 641966885879138343524401)
            ·
              refine ⟨481475164409353757643301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641966885879138343524401 481475164409353757643301)
              ·
                refine ⟨90276593326753829558119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481475164409353757643301 90276593326753829558119)
                ·
                  rfl

theorem cell20_593369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_593369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593369 prefixEnd_593369 := by exact prefixLift 593369
  have htrace : WordTrace (prefixWord ++ tailWord_593369) baseStart_593369 baseEnd_593369 := by
    simpa [prefixWord, tailWord_593369, baseEnd_593369] using wordTrace_append hprefix tailTrace_593369
  have hstable : (prefixWord ++ tailWord_593369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593369).length < 2 ^ (prefixWord ++ tailWord_593369).sum := by decide
  have hdescent : baseEnd_593369 < baseStart_593369 := by decide
  rcases family_descends (prefixWord ++ tailWord_593369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593379 : List Nat := [1, 1, 1, 6, 2, 3, 1, 3, 2]
def baseStart_593379 : Nat := 118140960795 + 593379 * 2 ^ 59
def prefixEnd_593379 : Nat := 4983230072969 + 3 ^ 40 * 593379 * 2
def baseEnd_593379 : Nat := 270834344252745898340983

theorem tailTrace_593379 : CollatzResearch.WordTrace tailWord_593379 prefixEnd_593379 270834344252745898340983 := by
  unfold tailWord_593379
  simp only [CollatzResearch.WordTrace]
  refine ⟨21642310117296698910135191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14428206744864465940090127 21642310117296698910135191)
  ·
    refine ⟨32463465175945048365202787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21642310117296698910135191 32463465175945048365202787)
    ·
      refine ⟨48695197763917572547804181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32463465175945048365202787 48695197763917572547804181)
      ·
        refine ⟨2282587395183636213178321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48695197763917572547804181 2282587395183636213178321)
        ·
          refine ⟨1711940546387727159883741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2282587395183636213178321 1711940546387727159883741)
          ·
            refine ⟨641977704895397684956403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1711940546387727159883741 641977704895397684956403)
            ·
              refine ⟨962966557343096527434605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641977704895397684956403 962966557343096527434605)
              ·
                refine ⟨361112459003661197787977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 962966557343096527434605 361112459003661197787977)
                ·
                  refine ⟨270834344252745898340983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361112459003661197787977 270834344252745898340983)
                  ·
                    rfl

theorem cell20_593379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 2].length) (baseStart_593379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593379 prefixEnd_593379 := by exact prefixLift 593379
  have htrace : WordTrace (prefixWord ++ tailWord_593379) baseStart_593379 baseEnd_593379 := by
    simpa [prefixWord, tailWord_593379, baseEnd_593379] using wordTrace_append hprefix tailTrace_593379
  have hstable : (prefixWord ++ tailWord_593379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593379).length < 2 ^ (prefixWord ++ tailWord_593379).sum := by decide
  have hdescent : baseEnd_593379 < baseStart_593379 := by decide
  rcases family_descends (prefixWord ++ tailWord_593379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593406 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_593406 : Nat := 118140960795 + 593406 * 2 ^ 59
def prefixEnd_593406 : Nat := 4983230072969 + 3 ^ 40 * 593406 * 2
def baseEnd_593406 : Nat := 270846667788453804440873

theorem tailTrace_593406 : CollatzResearch.WordTrace tailWord_593406 prefixEnd_593406 270846667788453804440873 := by
  unfold tailWord_593406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2705411861024860315171009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14428863258799255014245381 2705411861024860315171009)
  ·
    refine ⟨2029058895768645236378257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2705411861024860315171009 2029058895768645236378257)
    ·
      refine ⟨1521794171826483927283693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2029058895768645236378257 1521794171826483927283693)
      ·
        refine ⟨570672814434931472731385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1521794171826483927283693 570672814434931472731385)
        ·
          refine ⟨428004610826198604548539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570672814434931472731385 428004610826198604548539)
          ·
            refine ⟨642006916239297906822809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428004610826198604548539 642006916239297906822809)
            ·
              refine ⟨481505187179473430117107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642006916239297906822809 481505187179473430117107)
              ·
                refine ⟨722257780769210145175661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481505187179473430117107 722257780769210145175661)
                ·
                  refine ⟨270846667788453804440873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722257780769210145175661 270846667788453804440873)
                  ·
                    rfl

theorem cell20_593406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_593406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593406 prefixEnd_593406 := by exact prefixLift 593406
  have htrace : WordTrace (prefixWord ++ tailWord_593406) baseStart_593406 baseEnd_593406 := by
    simpa [prefixWord, tailWord_593406, baseEnd_593406] using wordTrace_append hprefix tailTrace_593406
  have hstable : (prefixWord ++ tailWord_593406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593406).length < 2 ^ (prefixWord ++ tailWord_593406).sum := by decide
  have hdescent : baseEnd_593406 < baseStart_593406 := by decide
  rcases family_descends (prefixWord ++ tailWord_593406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593410 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_593410 : Nat := 118140960795 + 593410 * 2 ^ 59
def prefixEnd_593410 : Nat := 4983230072969 + 3 ^ 40 * 593410 * 2
def baseEnd_593410 : Nat := 270848493497447568307523

theorem tailTrace_593410 : CollatzResearch.WordTrace tailWord_593410 prefixEnd_593410 270848493497447568307523 := by
  unfold tailWord_593410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5410860195046097801128421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14428960520122927469675789 5410860195046097801128421)
  ·
    refine ⟨1014536286571143337711579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5410860195046097801128421 1014536286571143337711579)
    ·
      refine ⟨1521804429856715006567369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014536286571143337711579 1521804429856715006567369)
      ·
        refine ⟨1141353322392536254925527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1521804429856715006567369 1141353322392536254925527)
        ·
          refine ⟨1712029983588804382388291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1141353322392536254925527 1712029983588804382388291)
          ·
            refine ⟨2568044975383206573582437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712029983588804382388291 2568044975383206573582437)
            ·
              refine ⟨481508432884351232546707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2568044975383206573582437 481508432884351232546707)
              ·
                refine ⟨722262649326526848820061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481508432884351232546707 722262649326526848820061)
                ·
                  refine ⟨270848493497447568307523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722262649326526848820061 270848493497447568307523)
                  ·
                    rfl

theorem cell20_593410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_593410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593410 prefixEnd_593410 := by exact prefixLift 593410
  have htrace : WordTrace (prefixWord ++ tailWord_593410) baseStart_593410 baseEnd_593410 := by
    simpa [prefixWord, tailWord_593410, baseEnd_593410] using wordTrace_append hprefix tailTrace_593410
  have hstable : (prefixWord ++ tailWord_593410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593410).length < 2 ^ (prefixWord ++ tailWord_593410).sum := by decide
  have hdescent : baseEnd_593410 < baseStart_593410 := by decide
  rcases family_descends (prefixWord ++ tailWord_593410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593462 : List Nat := [5, 1, 2, 1, 3, 2, 1, 5]
def baseStart_593462 : Nat := 118140960795 + 593462 * 2 ^ 59
def prefixEnd_593462 : Nat := 4983230072969 + 3 ^ 40 * 593462 * 2
def baseEnd_593462 : Nat := 90290742571455499524659

theorem tailTrace_593462 : CollatzResearch.WordTrace tailWord_593462 prefixEnd_593462 90290742571455499524659 := by
  unfold tailWord_593462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1352833585999750255337915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14430224917330669390271093 1352833585999750255337915)
  ·
    refine ⟨2029250378999625383006873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1352833585999750255337915 2029250378999625383006873)
    ·
      refine ⟨1521937784249719037255155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2029250378999625383006873 1521937784249719037255155)
      ·
        refine ⟨2282906676374578555882733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521937784249719037255155 2282906676374578555882733)
        ·
          refine ⟨856090003640466958456025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2282906676374578555882733 856090003640466958456025)
          ·
            refine ⟨642067502730350218842019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856090003640466958456025 642067502730350218842019)
            ·
              refine ⟨963101254095525328263029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642067502730350218842019 963101254095525328263029)
              ·
                refine ⟨90290742571455499524659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 963101254095525328263029 90290742571455499524659)
                ·
                  rfl

theorem cell20_593462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_593462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593462 prefixEnd_593462 := by exact prefixLift 593462
  have htrace : WordTrace (prefixWord ++ tailWord_593462) baseStart_593462 baseEnd_593462 := by
    simpa [prefixWord, tailWord_593462, baseEnd_593462] using wordTrace_append hprefix tailTrace_593462
  have hstable : (prefixWord ++ tailWord_593462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593462).length < 2 ^ (prefixWord ++ tailWord_593462).sum := by decide
  have hdescent : baseEnd_593462 < baseStart_593462 := by decide
  rcases family_descends (prefixWord ++ tailWord_593462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593514 : List Nat := [3, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_593514 : Nat := 118140960795 + 593514 * 2 ^ 59
def prefixEnd_593514 : Nat := 4983230072969 + 3 ^ 40 * 593514 * 2
def baseEnd_593514 : Nat := 270895961931285428840431

theorem tailTrace_593514 : CollatzResearch.WordTrace tailWord_593514 prefixEnd_593514 270895961931285428840431 := by
  unfold tailWord_593514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5411808492951904241574899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14431489314538411310866397 5411808492951904241574899)
  ·
    refine ⟨8117712739427856362362349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5411808492951904241574899 8117712739427856362362349)
    ·
      refine ⟨3044142277285446135885881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8117712739427856362362349 3044142277285446135885881)
      ·
        refine ⟨2283106707964084601914411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3044142277285446135885881 2283106707964084601914411)
        ·
          refine ⟨3424660061946126902871617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283106707964084601914411 3424660061946126902871617)
          ·
            refine ⟨2568495046459595177153713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3424660061946126902871617 2568495046459595177153713)
            ·
              refine ⟨1926371284844696382865285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568495046459595177153713 1926371284844696382865285)
              ·
                refine ⟨361194615908380571787241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1926371284844696382865285 361194615908380571787241)
                ·
                  refine ⟨270895961931285428840431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361194615908380571787241 270895961931285428840431)
                  ·
                    rfl

theorem cell20_593514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_593514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593514 prefixEnd_593514 := by exact prefixLift 593514
  have htrace : WordTrace (prefixWord ++ tailWord_593514) baseStart_593514 baseEnd_593514 := by
    simpa [prefixWord, tailWord_593514, baseEnd_593514] using wordTrace_append hprefix tailTrace_593514
  have hstable : (prefixWord ++ tailWord_593514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593514).length < 2 ^ (prefixWord ++ tailWord_593514).sum := by decide
  have hdescent : baseEnd_593514 < baseStart_593514 := by decide
  rcases family_descends (prefixWord ++ tailWord_593514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593566 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_593566 : Nat := 118140960795 + 593566 * 2 ^ 59
def prefixEnd_593566 : Nat := 4983230072969 + 3 ^ 40 * 593566 * 2
def baseEnd_593566 : Nat := 270919696148204359106885

theorem tailTrace_593566 : CollatzResearch.WordTrace tailWord_593566 prefixEnd_593566 270919696148204359106885 := by
  unfold tailWord_593566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706141320952403730899069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14432753711746153231461701 2706141320952403730899069)
  ·
    refine ⟨1014802995357151399087151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2706141320952403730899069 1014802995357151399087151)
    ·
      refine ⟨1522204493035727098630727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014802995357151399087151 1522204493035727098630727)
      ·
        refine ⟨2283306739553590647946091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522204493035727098630727 2283306739553590647946091)
        ·
          refine ⟨3424960109330385971919137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283306739553590647946091 3424960109330385971919137)
          ·
            refine ⟨2568720081997789478939353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3424960109330385971919137 2568720081997789478939353)
            ·
              refine ⟨1926540061498342109204515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568720081997789478939353 1926540061498342109204515)
              ·
                refine ⟨2889810092247513163806773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926540061498342109204515 2889810092247513163806773)
                ·
                  refine ⟨270919696148204359106885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889810092247513163806773 270919696148204359106885)
                  ·
                    rfl

theorem cell20_593566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_593566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593566 prefixEnd_593566 := by exact prefixLift 593566
  have htrace : WordTrace (prefixWord ++ tailWord_593566) baseStart_593566 baseEnd_593566 := by
    simpa [prefixWord, tailWord_593566, baseEnd_593566] using wordTrace_append hprefix tailTrace_593566
  have hstable : (prefixWord ++ tailWord_593566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593566).length < 2 ^ (prefixWord ++ tailWord_593566).sum := by decide
  have hdescent : baseEnd_593566 < baseStart_593566 := by decide
  rcases family_descends (prefixWord ++ tailWord_593566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593569 : List Nat := [1, 2, 3, 3, 2, 2, 3, 2, 2]
def baseStart_593569 : Nat := 118140960795 + 593569 * 2 ^ 59
def prefixEnd_593569 : Nat := 4983230072969 + 3 ^ 40 * 593569 * 2
def baseEnd_593569 : Nat := 270921065429949682006873

theorem tailTrace_593569 : CollatzResearch.WordTrace tailWord_593569 prefixEnd_593569 270921065429949682006873 := by
  unfold tailWord_593569
  simp only [CollatzResearch.WordTrace]
  refine ⟨21649239986608361359551761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14432826657738907573034507 21649239986608361359551761)
  ·
    refine ⟨16236929989956271019663821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21649239986608361359551761 16236929989956271019663821)
    ·
      refine ⟨6088848746233601632373933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16236929989956271019663821 6088848746233601632373933)
      ·
        refine ⟨2283318279837600612140225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6088848746233601632373933 2283318279837600612140225)
        ·
          refine ⟨1712488709878200459105169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2283318279837600612140225 1712488709878200459105169)
          ·
            refine ⟨1284366532408650344328877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1712488709878200459105169 1284366532408650344328877)
            ·
              refine ⟨481637449653243879123329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1284366532408650344328877 481637449653243879123329)
              ·
                refine ⟨361228087239932909342497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481637449653243879123329 361228087239932909342497)
                ·
                  refine ⟨270921065429949682006873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361228087239932909342497 270921065429949682006873)
                  ·
                    rfl

theorem cell20_593569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_593569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593569 prefixEnd_593569 := by exact prefixLift 593569
  have htrace : WordTrace (prefixWord ++ tailWord_593569) baseStart_593569 baseEnd_593569 := by
    simpa [prefixWord, tailWord_593569, baseEnd_593569] using wordTrace_append hprefix tailTrace_593569
  have hstable : (prefixWord ++ tailWord_593569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593569).length < 2 ^ (prefixWord ++ tailWord_593569).sum := by decide
  have hdescent : baseEnd_593569 < baseStart_593569 := by decide
  rcases family_descends (prefixWord ++ tailWord_593569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593573 : List Nat := [1, 3, 1, 2, 1, 2, 2, 6, 2]
def baseStart_593573 : Nat := 118140960795 + 593573 * 2 ^ 59
def prefixEnd_593573 : Nat := 4983230072969 + 3 ^ 40 * 593573 * 2
def baseEnd_593573 : Nat := 270922891138943445873523

theorem tailTrace_593573 : CollatzResearch.WordTrace tailWord_593573 prefixEnd_593573 270922891138943445873523 := by
  unfold tailWord_593573
  simp only [CollatzResearch.WordTrace]
  refine ⟨21649385878593870042697373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14432923919062580028464915 21649385878593870042697373)
  ·
    refine ⟨8118519704472701266011515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21649385878593870042697373 8118519704472701266011515)
    ·
      refine ⟨12177779556709051899017273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8118519704472701266011515 12177779556709051899017273)
      ·
        refine ⟨9133334667531788924262955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12177779556709051899017273 9133334667531788924262955)
        ·
          refine ⟨13700002001297683386394433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9133334667531788924262955 13700002001297683386394433)
          ·
            refine ⟨10275001500973262539795825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13700002001297683386394433 10275001500973262539795825)
            ·
              refine ⟨7706251125729946904846869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10275001500973262539795825 7706251125729946904846869)
              ·
                refine ⟨361230521518591261164697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7706251125729946904846869 361230521518591261164697)
                ·
                  refine ⟨270922891138943445873523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361230521518591261164697 270922891138943445873523)
                  ·
                    rfl

theorem cell20_593573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_593573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593573 prefixEnd_593573 := by exact prefixLift 593573
  have htrace : WordTrace (prefixWord ++ tailWord_593573) baseStart_593573 baseEnd_593573 := by
    simpa [prefixWord, tailWord_593573, baseEnd_593573] using wordTrace_append hprefix tailTrace_593573
  have hstable : (prefixWord ++ tailWord_593573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593573).length < 2 ^ (prefixWord ++ tailWord_593573).sum := by decide
  have hdescent : baseEnd_593573 < baseStart_593573 := by decide
  rcases family_descends (prefixWord ++ tailWord_593573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593587 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 3]
def baseStart_593587 : Nat := 118140960795 + 593587 * 2 ^ 59
def prefixEnd_593587 : Nat := 4983230072969 + 3 ^ 40 * 593587 * 2
def baseEnd_593587 : Nat := 270929281120421619406799

theorem tailTrace_593587 : CollatzResearch.WordTrace tailWord_593587 prefixEnd_593587 270929281120421619406799 := by
  unfold tailWord_593587
  simp only [CollatzResearch.WordTrace]
  refine ⟨21649896500543150433707015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14433264333695433622471343 21649896500543150433707015)
  ·
    refine ⟨32474844750814725650560523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21649896500543150433707015 32474844750814725650560523)
    ·
      refine ⟨48712267126222088475840785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32474844750814725650560523 48712267126222088475840785)
      ·
        refine ⟨36534200344666566356880589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48712267126222088475840785 36534200344666566356880589)
        ·
          refine ⟨13700325129249962383830221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36534200344666566356880589 13700325129249962383830221)
          ·
            refine ⟨5137621923468735893936333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13700325129249962383830221 5137621923468735893936333)
            ·
              refine ⟨1926608221300775960226125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5137621923468735893936333 1926608221300775960226125)
              ·
                refine ⟨722478082987790985084797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1926608221300775960226125 722478082987790985084797)
                ·
                  refine ⟨270929281120421619406799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722478082987790985084797 270929281120421619406799)
                  ·
                    rfl

theorem cell20_593587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_593587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593587 prefixEnd_593587 := by exact prefixLift 593587
  have htrace : WordTrace (prefixWord ++ tailWord_593587) baseStart_593587 baseEnd_593587 := by
    simpa [prefixWord, tailWord_593587, baseEnd_593587] using wordTrace_append hprefix tailTrace_593587
  have hstable : (prefixWord ++ tailWord_593587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593587).length < 2 ^ (prefixWord ++ tailWord_593587).sum := by decide
  have hdescent : baseEnd_593587 < baseStart_593587 := by decide
  rcases family_descends (prefixWord ++ tailWord_593587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593625 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 3]
def baseStart_593625 : Nat := 118140960795 + 593625 * 2 ^ 59
def prefixEnd_593625 : Nat := 4983230072969 + 3 ^ 40 * 593625 * 2
def baseEnd_593625 : Nat := 270946625355862376139977

theorem tailTrace_593625 : CollatzResearch.WordTrace tailWord_593625 prefixEnd_593625 270946625355862376139977 := by
  unfold tailWord_593625
  simp only [CollatzResearch.WordTrace]
  refine ⟨21651282474405482923590329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14434188316270321949060219 21651282474405482923590329)
  ·
    refine ⟨16238461855804112192692747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21651282474405482923590329 16238461855804112192692747)
    ·
      refine ⟨24357692783706168289039121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16238461855804112192692747 24357692783706168289039121)
      ·
        refine ⟨18268269587779626216779341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24357692783706168289039121 18268269587779626216779341)
        ·
          refine ⟨6850601095417359831292253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18268269587779626216779341 6850601095417359831292253)
          ·
            refine ⟨2568975410781509936734595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6850601095417359831292253 2568975410781509936734595)
            ·
              refine ⟨3853463116172264905101893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568975410781509936734595 3853463116172264905101893)
              ·
                refine ⟨722524334282299669706605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3853463116172264905101893 722524334282299669706605)
                ·
                  refine ⟨270946625355862376139977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722524334282299669706605 270946625355862376139977)
                  ·
                    rfl

theorem cell20_593625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_593625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593625 prefixEnd_593625 := by exact prefixLift 593625
  have htrace : WordTrace (prefixWord ++ tailWord_593625) baseStart_593625 baseEnd_593625 := by
    simpa [prefixWord, tailWord_593625, baseEnd_593625] using wordTrace_append hprefix tailTrace_593625
  have hstable : (prefixWord ++ tailWord_593625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593625).length < 2 ^ (prefixWord ++ tailWord_593625).sum := by decide
  have hdescent : baseEnd_593625 < baseStart_593625 := by decide
  rcases family_descends (prefixWord ++ tailWord_593625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593635 : List Nat := [1, 1, 1, 7, 2, 2, 1, 5]
def baseStart_593635 : Nat := 118140960795 + 593635 * 2 ^ 59
def prefixEnd_593635 : Nat := 4983230072969 + 3 ^ 40 * 593635 * 2
def baseEnd_593635 : Nat := 90317063209448928602201

theorem tailTrace_593635 : CollatzResearch.WordTrace tailWord_593635 prefixEnd_593635 90317063209448928602201 := by
  unfold tailWord_593635
  simp only [CollatzResearch.WordTrace]
  refine ⟨21651647204369254631454359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14434431469579503087636239 21651647204369254631454359)
  ·
    refine ⟨32477470806553881947181539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21651647204369254631454359 32477470806553881947181539)
    ·
      refine ⟨48716206209830822920772309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32477470806553881947181539 48716206209830822920772309)
      ·
        refine ⟨1141786083042909912205601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 48716206209830822920772309 1141786083042909912205601)
        ·
          refine ⟨856339562282182434154201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141786083042909912205601 856339562282182434154201)
          ·
            refine ⟨642254671711636825615651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856339562282182434154201 642254671711636825615651)
            ·
              refine ⟨963382007567455238423477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642254671711636825615651 963382007567455238423477)
              ·
                refine ⟨90317063209448928602201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 963382007567455238423477 90317063209448928602201)
                ·
                  rfl

theorem cell20_593635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_593635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593635 prefixEnd_593635 := by exact prefixLift 593635
  have htrace : WordTrace (prefixWord ++ tailWord_593635) baseStart_593635 baseEnd_593635 := by
    simpa [prefixWord, tailWord_593635, baseEnd_593635] using wordTrace_append hprefix tailTrace_593635
  have hstable : (prefixWord ++ tailWord_593635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593635).length < 2 ^ (prefixWord ++ tailWord_593635).sum := by decide
  have hdescent : baseEnd_593635 < baseStart_593635 := by decide
  rcases family_descends (prefixWord ++ tailWord_593635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593687 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_593687 : Nat := 118140960795 + 593687 * 2 ^ 59
def prefixEnd_593687 : Nat := 4983230072969 + 3 ^ 40 * 593687 * 2
def baseEnd_593687 : Nat := 270974923845265716073057

theorem tailTrace_593687 : CollatzResearch.WordTrace tailWord_593687 prefixEnd_593687 270974923845265716073057 := by
  unfold tailWord_593687
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653543800180867512347315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14435695866787245008231543 21653543800180867512347315)
  ·
    refine ⟨32480315700271301268520973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21653543800180867512347315 32480315700271301268520973)
    ·
      refine ⟨12180118387601737975695365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32480315700271301268520973 12180118387601737975695365)
      ·
        refine ⟨2283772197675325870442881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12180118387601737975695365 2283772197675325870442881)
        ·
          refine ⟨1712829148256494402832161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2283772197675325870442881 1712829148256494402832161)
          ·
            refine ⟨1284621861192370802124121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1712829148256494402832161 1284621861192370802124121)
            ·
              refine ⟨963466395894278101593091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284621861192370802124121 963466395894278101593091)
              ·
                refine ⟨1445199593841417152389637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963466395894278101593091 1445199593841417152389637)
                ·
                  refine ⟨270974923845265716073057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445199593841417152389637 270974923845265716073057)
                  ·
                    rfl

theorem cell20_593687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_593687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593687 prefixEnd_593687 := by exact prefixLift 593687
  have htrace : WordTrace (prefixWord ++ tailWord_593687) baseStart_593687 baseEnd_593687 := by
    simpa [prefixWord, tailWord_593687, baseEnd_593687] using wordTrace_append hprefix tailTrace_593687
  have hstable : (prefixWord ++ tailWord_593687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593687).length < 2 ^ (prefixWord ++ tailWord_593687).sum := by decide
  have hdescent : baseEnd_593687 < baseStart_593687 := by decide
  rcases family_descends (prefixWord ++ tailWord_593687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593691 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_593691 : Nat := 118140960795 + 593691 * 2 ^ 59
def prefixEnd_593691 : Nat := 4983230072969 + 3 ^ 40 * 593691 * 2
def baseEnd_593691 : Nat := 270976749554259479939707

theorem tailTrace_593691 : CollatzResearch.WordTrace tailWord_593691 prefixEnd_593691 270976749554259479939707 := by
  unfold tailWord_593691
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653689692166376195492927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14435793128110917463661951 21653689692166376195492927)
  ·
    refine ⟨32480534538249564293239391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21653689692166376195492927 32480534538249564293239391)
    ·
      refine ⟨48720801807374346439859087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32480534538249564293239391 48720801807374346439859087)
      ·
        refine ⟨73081202711061519659788631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48720801807374346439859087 73081202711061519659788631)
        ·
          refine ⟨109621804066592279489682947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73081202711061519659788631 109621804066592279489682947)
          ·
            refine ⟨164432706099888419234524421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109621804066592279489682947 164432706099888419234524421)
            ·
              refine ⟨30831132393729078606473329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164432706099888419234524421 30831132393729078606473329)
              ·
                refine ⟨23123349295296808954854997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30831132393729078606473329 23123349295296808954854997)
                ·
                  refine ⟨270976749554259479939707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23123349295296808954854997 270976749554259479939707)
                  ·
                    rfl

theorem cell20_593691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_593691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593691 prefixEnd_593691 := by exact prefixLift 593691
  have htrace : WordTrace (prefixWord ++ tailWord_593691) baseStart_593691 baseEnd_593691 := by
    simpa [prefixWord, tailWord_593691, baseEnd_593691] using wordTrace_append hprefix tailTrace_593691
  have hstable : (prefixWord ++ tailWord_593691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593691).length < 2 ^ (prefixWord ++ tailWord_593691).sum := by decide
  have hdescent : baseEnd_593691 < baseStart_593691 := by decide
  rcases family_descends (prefixWord ++ tailWord_593691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593708 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_593708 : Nat := 118140960795 + 593708 * 2 ^ 59
def prefixEnd_593708 : Nat := 4983230072969 + 3 ^ 40 * 593708 * 2
def baseEnd_593708 : Nat := 270984508817482976372971

theorem tailTrace_593708 : CollatzResearch.WordTrace tailWord_593708 prefixEnd_593708 270984508817482976372971 := by
  unfold tailWord_593708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827154866552394049430889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14436206488736525399241185 10827154866552394049430889)
  ·
    refine ⟨8120366149914295537073167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10827154866552394049430889 8120366149914295537073167)
    ·
      refine ⟨12180549224871443305609751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8120366149914295537073167 12180549224871443305609751)
      ·
        refine ⟨18270823837307164958414627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12180549224871443305609751 18270823837307164958414627)
        ·
          refine ⟨27406235755960747437621941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18270823837307164958414627 27406235755960747437621941)
          ·
            refine ⟨2569334602121320072277057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27406235755960747437621941 2569334602121320072277057)
            ·
              refine ⟨1927000951590990054207793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569334602121320072277057 1927000951590990054207793)
              ·
                refine ⟨1445250713693242540655845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927000951590990054207793 1445250713693242540655845)
                ·
                  refine ⟨270984508817482976372971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445250713693242540655845 270984508817482976372971)
                  ·
                    rfl

theorem cell20_593708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_593708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593708 prefixEnd_593708 := by exact prefixLift 593708
  have htrace : WordTrace (prefixWord ++ tailWord_593708) baseStart_593708 baseEnd_593708 := by
    simpa [prefixWord, tailWord_593708, baseEnd_593708] using wordTrace_append hprefix tailTrace_593708
  have hstable : (prefixWord ++ tailWord_593708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593708).length < 2 ^ (prefixWord ++ tailWord_593708).sum := by decide
  have hdescent : baseEnd_593708 < baseStart_593708 := by decide
  rcases family_descends (prefixWord ++ tailWord_593708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593718 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_593718 : Nat := 118140960795 + 593718 * 2 ^ 59
def prefixEnd_593718 : Nat := 4983230072969 + 3 ^ 40 * 593718 * 2
def baseEnd_593718 : Nat := 270989073089967386039597

theorem tailTrace_593718 : CollatzResearch.WordTrace tailWord_593718 prefixEnd_593718 270989073089967386039597 := by
  unfold tailWord_593718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353417153941784987920363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14436449642045706537817205 1353417153941784987920363)
  ·
    refine ⟨2030125730912677481880545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1353417153941784987920363 2030125730912677481880545)
    ·
      refine ⟨1522594298184508111410409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2030125730912677481880545 1522594298184508111410409)
      ·
        refine ⟨1141945723638381083557807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1522594298184508111410409 1141945723638381083557807)
        ·
          refine ⟨1712918585457571625336711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1141945723638381083557807 1712918585457571625336711)
          ·
            refine ⟨2569377878186357438005067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712918585457571625336711 2569377878186357438005067)
            ·
              refine ⟨3854066817279536157007601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2569377878186357438005067 3854066817279536157007601)
              ·
                refine ⟨2890550112959652117755701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3854066817279536157007601 2890550112959652117755701)
                ·
                  refine ⟨270989073089967386039597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890550112959652117755701 270989073089967386039597)
                  ·
                    rfl

theorem cell20_593718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_593718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593718 prefixEnd_593718 := by exact prefixLift 593718
  have htrace : WordTrace (prefixWord ++ tailWord_593718) baseStart_593718 baseEnd_593718 := by
    simpa [prefixWord, tailWord_593718, baseEnd_593718] using wordTrace_append hprefix tailTrace_593718
  have hstable : (prefixWord ++ tailWord_593718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593718).length < 2 ^ (prefixWord ++ tailWord_593718).sum := by decide
  have hdescent : baseEnd_593718 < baseStart_593718 := by decide
  rcases family_descends (prefixWord ++ tailWord_593718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593753 : List Nat := [1, 2, 1, 2, 2, 3, 4, 5]
def baseStart_593753 : Nat := 118140960795 + 593753 * 2 ^ 59
def prefixEnd_593753 : Nat := 4983230072969 + 3 ^ 40 * 593753 * 2
def baseEnd_593753 : Nat := 90335016014554273290929

theorem tailTrace_593753 : CollatzResearch.WordTrace tailWord_593753 prefixEnd_593753 90335016014554273290929 := by
  unfold tailWord_593753
  simp only [CollatzResearch.WordTrace]
  refine ⟨21655951017941760784249913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14437300678627840522833275 21655951017941760784249913)
  ·
    refine ⟨16241963263456320588187435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21655951017941760784249913 16241963263456320588187435)
    ·
      refine ⟨24362944895184480882281153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16241963263456320588187435 24362944895184480882281153)
      ·
        refine ⟨18272208671388360661710865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24362944895184480882281153 18272208671388360661710865)
        ·
          refine ⟨13704156503541270496283149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18272208671388360661710865 13704156503541270496283149)
          ·
            refine ⟨5139058688827976436106181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13704156503541270496283149 5139058688827976436106181)
            ·
              refine ⟨963573504155245581769909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5139058688827976436106181 963573504155245581769909)
              ·
                refine ⟨90335016014554273290929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 963573504155245581769909 90335016014554273290929)
                ·
                  rfl

theorem cell20_593753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_593753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593753 prefixEnd_593753 := by exact prefixLift 593753
  have htrace : WordTrace (prefixWord ++ tailWord_593753) baseStart_593753 baseEnd_593753 := by
    simpa [prefixWord, tailWord_593753, baseEnd_593753] using wordTrace_append hprefix tailTrace_593753
  have hstable : (prefixWord ++ tailWord_593753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593753).length < 2 ^ (prefixWord ++ tailWord_593753).sum := by decide
  have hdescent : baseEnd_593753 < baseStart_593753 := by decide
  rcases family_descends (prefixWord ++ tailWord_593753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593793 : List Nat := [1, 2, 4, 4, 2, 1, 2, 2, 2]
def baseStart_593793 : Nat := 118140960795 + 593793 * 2 ^ 59
def prefixEnd_593793 : Nat := 4983230072969 + 3 ^ 40 * 593793 * 2
def baseEnd_593793 : Nat := 271023305133600458539291

theorem tailTrace_593793 : CollatzResearch.WordTrace tailWord_593793 prefixEnd_593793 271023305133600458539291 := by
  unfold tailWord_593793
  simp only [CollatzResearch.WordTrace]
  refine ⟨21657409937796847615706033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14438273291864565077137355 21657409937796847615706033)
  ·
    refine ⟨16243057453347635711779525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21657409937796847615706033 16243057453347635711779525)
    ·
      refine ⟨3045573272502681695958661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16243057453347635711779525 3045573272502681695958661)
      ·
        refine ⟨571044988594252817992249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3045573272502681695958661 571044988594252817992249)
        ·
          refine ⟨428283741445689613494187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571044988594252817992249 428283741445689613494187)
          ·
            refine ⟨642425612168534420241281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428283741445689613494187 642425612168534420241281)
            ·
              refine ⟨481819209126400815180961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642425612168534420241281 481819209126400815180961)
              ·
                refine ⟨361364406844800611385721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481819209126400815180961 361364406844800611385721)
                ·
                  refine ⟨271023305133600458539291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361364406844800611385721 271023305133600458539291)
                  ·
                    rfl

theorem cell20_593793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_593793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593793 prefixEnd_593793 := by exact prefixLift 593793
  have htrace : WordTrace (prefixWord ++ tailWord_593793) baseStart_593793 baseEnd_593793 := by
    simpa [prefixWord, tailWord_593793, baseEnd_593793] using wordTrace_append hprefix tailTrace_593793
  have hstable : (prefixWord ++ tailWord_593793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593793).length < 2 ^ (prefixWord ++ tailWord_593793).sum := by decide
  have hdescent : baseEnd_593793 < baseStart_593793 := by decide
  rcases family_descends (prefixWord ++ tailWord_593793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593801 : List Nat := [1, 2, 1, 1, 5, 1, 3, 4, 2]
def baseStart_593801 : Nat := 118140960795 + 593801 * 2 ^ 59
def prefixEnd_593801 : Nat := 4983230072969 + 3 ^ 40 * 593801 * 2
def baseEnd_593801 : Nat := 271026956551587986272591

theorem tailTrace_593801 : CollatzResearch.WordTrace tailWord_593801 prefixEnd_593801 271026956551587986272591 := by
  unfold tailWord_593801
  simp only [CollatzResearch.WordTrace]
  refine ⟨21657701721767864981997257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14438467814511909987998171 21657701721767864981997257)
  ·
    refine ⟨16243276291325898736497943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21657701721767864981997257 16243276291325898736497943)
    ·
      refine ⟨24364914436988848104746915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16243276291325898736497943 24364914436988848104746915)
      ·
        refine ⟨36547371655483272157120373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24364914436988848104746915 36547371655483272157120373)
        ·
          refine ⟨3426316092701556764730035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36547371655483272157120373 3426316092701556764730035)
          ·
            refine ⟨5139474139052335147095053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3426316092701556764730035 5139474139052335147095053)
            ·
              refine ⟨1927302802144625680160645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5139474139052335147095053 1927302802144625680160645)
              ·
                refine ⟨361369275402117315030121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1927302802144625680160645 361369275402117315030121)
                ·
                  refine ⟨271026956551587986272591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361369275402117315030121 271026956551587986272591)
                  ·
                    rfl

theorem cell20_593801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_593801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593801 prefixEnd_593801 := by exact prefixLift 593801
  have htrace : WordTrace (prefixWord ++ tailWord_593801) baseStart_593801 baseEnd_593801 := by
    simpa [prefixWord, tailWord_593801, baseEnd_593801] using wordTrace_append hprefix tailTrace_593801
  have hstable : (prefixWord ++ tailWord_593801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593801).length < 2 ^ (prefixWord ++ tailWord_593801).sum := by decide
  have hdescent : baseEnd_593801 < baseStart_593801 := by decide
  rcases family_descends (prefixWord ++ tailWord_593801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593815 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 3]
def baseStart_593815 : Nat := 118140960795 + 593815 * 2 ^ 59
def prefixEnd_593815 : Nat := 4983230072969 + 3 ^ 40 * 593815 * 2
def baseEnd_593815 : Nat := 271033346533066159805867

theorem tailTrace_593815 : CollatzResearch.WordTrace tailWord_593815 prefixEnd_593815 271033346533066159805867 := by
  unfold tailWord_593815
  simp only [CollatzResearch.WordTrace]
  refine ⟨21658212343717145373006899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14438808229144763582004599 21658212343717145373006899)
  ·
    refine ⟨32487318515575718059510349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21658212343717145373006899 32487318515575718059510349)
    ·
      refine ⟨12182744443340894272316381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32487318515575718059510349 12182744443340894272316381)
      ·
        refine ⟨4568529166252835352118643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12182744443340894272316381 4568529166252835352118643)
        ·
          refine ⟨6852793749379253028177965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4568529166252835352118643 6852793749379253028177965)
          ·
            refine ⟨2569797656017219885566737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6852793749379253028177965 2569797656017219885566737)
            ·
              refine ⟨1927348242012914914175053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569797656017219885566737 1927348242012914914175053)
              ·
                refine ⟨722755590754843092815645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1927348242012914914175053 722755590754843092815645)
                ·
                  refine ⟨271033346533066159805867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722755590754843092815645 271033346533066159805867)
                  ·
                    rfl

theorem cell20_593815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_593815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593815 prefixEnd_593815 := by exact prefixLift 593815
  have htrace : WordTrace (prefixWord ++ tailWord_593815) baseStart_593815 baseEnd_593815 := by
    simpa [prefixWord, tailWord_593815, baseEnd_593815] using wordTrace_append hprefix tailTrace_593815
  have hstable : (prefixWord ++ tailWord_593815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593815).length < 2 ^ (prefixWord ++ tailWord_593815).sum := by decide
  have hdescent : baseEnd_593815 < baseStart_593815 := by decide
  rcases family_descends (prefixWord ++ tailWord_593815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593825 : List Nat := [1, 2, 3, 4, 2, 1, 3, 4]
def baseStart_593825 : Nat := 118140960795 + 593825 * 2 ^ 59
def prefixEnd_593825 : Nat := 4983230072969 + 3 ^ 40 * 593825 * 2
def baseEnd_593825 : Nat := 90345970268516856490831

theorem tailTrace_593825 : CollatzResearch.WordTrace tailWord_593825 prefixEnd_593825 90345970268516856490831 := by
  unfold tailWord_593825
  simp only [CollatzResearch.WordTrace]
  refine ⟨21658577073680917080870929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14439051382453944720580619 21658577073680917080870929)
  ·
    refine ⟨16243932805260687810653197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21658577073680917080870929 16243932805260687810653197)
    ·
      refine ⟨6091474801972757928994949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16243932805260687810653197 6091474801972757928994949)
      ·
        refine ⟨1142151525369892111686553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6091474801972757928994949 1142151525369892111686553)
        ·
          refine ⟨856613644027419083764915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142151525369892111686553 856613644027419083764915)
          ·
            refine ⟨1284920466041128625647373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856613644027419083764915 1284920466041128625647373)
            ·
              refine ⟨481845174765423234617765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1284920466041128625647373 481845174765423234617765)
              ·
                refine ⟨90345970268516856490831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481845174765423234617765 90345970268516856490831)
                ·
                  rfl

theorem cell20_593825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_593825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593825 prefixEnd_593825 := by exact prefixLift 593825
  have htrace : WordTrace (prefixWord ++ tailWord_593825) baseStart_593825 baseEnd_593825 := by
    simpa [prefixWord, tailWord_593825, baseEnd_593825] using wordTrace_append hprefix tailTrace_593825
  have hstable : (prefixWord ++ tailWord_593825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593825).length < 2 ^ (prefixWord ++ tailWord_593825).sum := by decide
  have hdescent : baseEnd_593825 < baseStart_593825 := by decide
  rcases family_descends (prefixWord ++ tailWord_593825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593839 : List Nat := [1, 1, 2, 1, 2, 2, 6, 3, 2]
def baseStart_593839 : Nat := 118140960795 + 593839 * 2 ^ 59
def prefixEnd_593839 : Nat := 4983230072969 + 3 ^ 40 * 593839 * 2
def baseEnd_593839 : Nat := 271044300787028743005769

theorem tailTrace_593839 : CollatzResearch.WordTrace tailWord_593839 prefixEnd_593839 271044300787028743005769 := by
  unfold tailWord_593839
  simp only [CollatzResearch.WordTrace]
  refine ⟨21659087695630197471880571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14439391797086798314587047 21659087695630197471880571)
  ·
    refine ⟨32488631543445296207820857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21659087695630197471880571 32488631543445296207820857)
    ·
      refine ⟨24366473657583972155865643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32488631543445296207820857 24366473657583972155865643)
      ·
        refine ⟨36549710486375958233798465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24366473657583972155865643 36549710486375958233798465)
        ·
          refine ⟨27412282864781968675348849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36549710486375958233798465 27412282864781968675348849)
          ·
            refine ⟨20559212148586476506511637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27412282864781968675348849 20559212148586476506511637)
            ·
              refine ⟨963713069464991086242733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20559212148586476506511637 963713069464991086242733)
              ·
                refine ⟨361392401049371657341025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 963713069464991086242733 361392401049371657341025)
                ·
                  refine ⟨271044300787028743005769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361392401049371657341025 271044300787028743005769)
                  ·
                    rfl

theorem cell20_593839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 2].length) (baseStart_593839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593839 prefixEnd_593839 := by exact prefixLift 593839
  have htrace : WordTrace (prefixWord ++ tailWord_593839) baseStart_593839 baseEnd_593839 := by
    simpa [prefixWord, tailWord_593839, baseEnd_593839] using wordTrace_append hprefix tailTrace_593839
  have hstable : (prefixWord ++ tailWord_593839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593839).length < 2 ^ (prefixWord ++ tailWord_593839).sum := by decide
  have hdescent : baseEnd_593839 < baseStart_593839 := by decide
  rcases family_descends (prefixWord ++ tailWord_593839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593843 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_593843 : Nat := 118140960795 + 593843 * 2 ^ 59
def prefixEnd_593843 : Nat := 4983230072969 + 3 ^ 40 * 593843 * 2
def baseEnd_593843 : Nat := 271046126496022506872419

theorem tailTrace_593843 : CollatzResearch.WordTrace tailWord_593843 prefixEnd_593843 271046126496022506872419 := by
  unfold tailWord_593843
  simp only [CollatzResearch.WordTrace]
  refine ⟨21659233587615706155026183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14439489058410470770017455 21659233587615706155026183)
  ·
    refine ⟨32488850381423559232539275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21659233587615706155026183 32488850381423559232539275)
    ·
      refine ⟨48733275572135338848808913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32488850381423559232539275 48733275572135338848808913)
      ·
        refine ⟨36549956679101504136606685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48733275572135338848808913 36549956679101504136606685)
        ·
          refine ⟨13706233754663064051227507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36549956679101504136606685 13706233754663064051227507)
          ·
            refine ⟨20559350631994596076841261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13706233754663064051227507 20559350631994596076841261)
            ·
              refine ⟨7709756486997973528815473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20559350631994596076841261 7709756486997973528815473)
              ·
                refine ⟨5782317365248480146611605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7709756486997973528815473 5782317365248480146611605)
                ·
                  refine ⟨271046126496022506872419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5782317365248480146611605 271046126496022506872419)
                  ·
                    rfl

theorem cell20_593843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_593843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593843 prefixEnd_593843 := by exact prefixLift 593843
  have htrace : WordTrace (prefixWord ++ tailWord_593843) baseStart_593843 baseEnd_593843 := by
    simpa [prefixWord, tailWord_593843, baseEnd_593843] using wordTrace_append hprefix tailTrace_593843
  have hstable : (prefixWord ++ tailWord_593843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593843).length < 2 ^ (prefixWord ++ tailWord_593843).sum := by decide
  have hdescent : baseEnd_593843 < baseStart_593843 := by decide
  rcases family_descends (prefixWord ++ tailWord_593843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593853 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_593853 : Nat := 118140960795 + 593853 * 2 ^ 59
def prefixEnd_593853 : Nat := 4983230072969 + 3 ^ 40 * 593853 * 2
def baseEnd_593853 : Nat := 271050690768506916539045

theorem tailTrace_593853 : CollatzResearch.WordTrace tailWord_593853 prefixEnd_593853 271050690768506916539045 := by
  unfold tailWord_593853
  simp only [CollatzResearch.WordTrace]
  refine ⟨21659598317579477862890213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14439732211719651908593475 21659598317579477862890213)
  ·
    refine ⟨4061174684546152099291915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21659598317579477862890213 4061174684546152099291915)
    ·
      refine ⟨6091762026819228148937873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061174684546152099291915 6091762026819228148937873)
      ·
        refine ⟨4568821520114421111703405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6091762026819228148937873 4568821520114421111703405)
        ·
          refine ⟨1713308070042907916888777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4568821520114421111703405 1713308070042907916888777)
          ·
            refine ⟨1284981052532180937666583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713308070042907916888777 1284981052532180937666583)
            ·
              refine ⟨1927471578798271406499875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284981052532180937666583 1927471578798271406499875)
              ·
                refine ⟨2891207368197407109749813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927471578798271406499875 2891207368197407109749813)
                ·
                  refine ⟨271050690768506916539045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2891207368197407109749813 271050690768506916539045)
                  ·
                    rfl

theorem cell20_593853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_593853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593853 prefixEnd_593853 := by exact prefixLift 593853
  have htrace : WordTrace (prefixWord ++ tailWord_593853) baseStart_593853 baseEnd_593853 := by
    simpa [prefixWord, tailWord_593853, baseEnd_593853] using wordTrace_append hprefix tailTrace_593853
  have hstable : (prefixWord ++ tailWord_593853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593853).length < 2 ^ (prefixWord ++ tailWord_593853).sum := by decide
  have hdescent : baseEnd_593853 < baseStart_593853 := by decide
  rcases family_descends (prefixWord ++ tailWord_593853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593870 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_593870 : Nat := 118140960795 + 593870 * 2 ^ 59
def prefixEnd_593870 : Nat := 4983230072969 + 3 ^ 40 * 593870 * 2
def baseEnd_593870 : Nat := 271058450031730412972309

theorem tailTrace_593870 : CollatzResearch.WordTrace tailWord_593870 prefixEnd_593870 271058450031730412972309 := by
  unfold tailWord_593870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2707527294814736220782383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14440145572345259844172709 2707527294814736220782383)
  ·
    refine ⟨4061290942222104331173575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2707527294814736220782383 4061290942222104331173575)
    ·
      refine ⟨6091936413333156496760363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061290942222104331173575 6091936413333156496760363)
      ·
        refine ⟨9137904619999734745140545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091936413333156496760363 9137904619999734745140545)
        ·
          refine ⟨6853428464999801058855409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9137904619999734745140545 6853428464999801058855409)
          ·
            refine ⟨5140071348749850794141557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6853428464999801058855409 5140071348749850794141557)
            ·
              refine ⟨481881688945298511950771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5140071348749850794141557 481881688945298511950771)
              ·
                refine ⟨722822533417947767926157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481881688945298511950771 722822533417947767926157)
                ·
                  refine ⟨271058450031730412972309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722822533417947767926157 271058450031730412972309)
                  ·
                    rfl

theorem cell20_593870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_593870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593870 prefixEnd_593870 := by exact prefixLift 593870
  have htrace : WordTrace (prefixWord ++ tailWord_593870) baseStart_593870 baseEnd_593870 := by
    simpa [prefixWord, tailWord_593870, baseEnd_593870] using wordTrace_append hprefix tailTrace_593870
  have hstable : (prefixWord ++ tailWord_593870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593870).length < 2 ^ (prefixWord ++ tailWord_593870).sum := by decide
  have hdescent : baseEnd_593870 < baseStart_593870 := by decide
  rcases family_descends (prefixWord ++ tailWord_593870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593890 : List Nat := [3, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_593890 : Nat := 118140960795 + 593890 * 2 ^ 59
def prefixEnd_593890 : Nat := 4983230072969 + 3 ^ 40 * 593890 * 2
def baseEnd_593890 : Nat := 271067578576699232305561

theorem tailTrace_593890 : CollatzResearch.WordTrace tailWord_593890 prefixEnd_593890 271067578576699232305561 := by
  unfold tailWord_593890
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415236954611358295496781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14440631878963622121324749 5415236954611358295496781)
  ·
    refine ⟨2030713857979259360811293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5415236954611358295496781 2030713857979259360811293)
    ·
      refine ⟨761517696742222260304235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2030713857979259360811293 761517696742222260304235)
      ·
        refine ⟨1142276545113333390456353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761517696742222260304235 1142276545113333390456353)
        ·
          refine ⟨856707408835000042842265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142276545113333390456353 856707408835000042842265)
          ·
            refine ⟨642530556626250032131699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856707408835000042842265 642530556626250032131699)
            ·
              refine ⟨963795834939375048197549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642530556626250032131699 963795834939375048197549)
              ·
                refine ⟨361423438102265643074081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 963795834939375048197549 361423438102265643074081)
                ·
                  refine ⟨271067578576699232305561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361423438102265643074081 271067578576699232305561)
                  ·
                    rfl

theorem cell20_593890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_593890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593890 prefixEnd_593890 := by exact prefixLift 593890
  have htrace : WordTrace (prefixWord ++ tailWord_593890) baseStart_593890 baseEnd_593890 := by
    simpa [prefixWord, tailWord_593890, baseEnd_593890] using wordTrace_append hprefix tailTrace_593890
  have hstable : (prefixWord ++ tailWord_593890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593890).length < 2 ^ (prefixWord ++ tailWord_593890).sum := by decide
  have hdescent : baseEnd_593890 < baseStart_593890 := by decide
  rcases family_descends (prefixWord ++ tailWord_593890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593901 : List Nat := [1, 5, 1, 4, 1, 2, 6]
def baseStart_593901 : Nat := 118140960795 + 593901 * 2 ^ 59
def prefixEnd_593901 : Nat := 4983230072969 + 3 ^ 40 * 593901 * 2
def baseEnd_593901 : Nat := 30119177697381342548761

theorem tailTrace_593901 : CollatzResearch.WordTrace tailWord_593901 prefixEnd_593901 30119177697381342548761 := by
  unfold tailWord_593901
  simp only [CollatzResearch.WordTrace]
  refine ⟨21661349021405582060637557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14440899347603721373758371 21661349021405582060637557)
  ·
    refine ⟨2030751470756773318184771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21661349021405582060637557 2030751470756773318184771)
    ·
      refine ⟨3046127206135159977277157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030751470756773318184771 3046127206135159977277157)
      ·
        refine ⟨571148851150342495739467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3046127206135159977277157 571148851150342495739467)
        ·
          refine ⟨856723276725513743609201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571148851150342495739467 856723276725513743609201)
          ·
            refine ⟨642542457544135307706901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856723276725513743609201 642542457544135307706901)
            ·
              refine ⟨30119177697381342548761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 642542457544135307706901 30119177697381342548761)
              ·
                rfl

theorem cell20_593901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 6].length) (baseStart_593901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593901 prefixEnd_593901 := by exact prefixLift 593901
  have htrace : WordTrace (prefixWord ++ tailWord_593901) baseStart_593901 baseEnd_593901 := by
    simpa [prefixWord, tailWord_593901, baseEnd_593901] using wordTrace_append hprefix tailTrace_593901
  have hstable : (prefixWord ++ tailWord_593901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593901).length < 2 ^ (prefixWord ++ tailWord_593901).sum := by decide
  have hdescent : baseEnd_593901 < baseStart_593901 := by decide
  rcases family_descends (prefixWord ++ tailWord_593901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593912 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_593912 : Nat := 118140960795 + 593912 * 2 ^ 59
def prefixEnd_593912 : Nat := 4983230072969 + 3 ^ 40 * 593912 * 2
def baseEnd_593912 : Nat := 271077619976164933572137

theorem tailTrace_593912 : CollatzResearch.WordTrace tailWord_593912 prefixEnd_593912 271077619976164933572137 := by
  unfold tailWord_593912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10830875112182865469643995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14441166816243820626191993 10830875112182865469643995)
  ·
    refine ⟨16246312668274298204465993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10830875112182865469643995 16246312668274298204465993)
    ·
      refine ⟨12184734501205723653349495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16246312668274298204465993 12184734501205723653349495)
      ·
        refine ⟨18277101751808585480024243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12184734501205723653349495 18277101751808585480024243)
        ·
          refine ⟨27415652627712878220036365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18277101751808585480024243 27415652627712878220036365)
          ·
            refine ⟨10280869735392329332513637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27415652627712878220036365 10280869735392329332513637)
            ·
              refine ⟨1927663075386061749846307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10280869735392329332513637 1927663075386061749846307)
              ·
                refine ⟨2891494613079092624769461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927663075386061749846307 2891494613079092624769461)
                ·
                  refine ⟨271077619976164933572137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2891494613079092624769461 271077619976164933572137)
                  ·
                    rfl

theorem cell20_593912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_593912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593912 prefixEnd_593912 := by exact prefixLift 593912
  have htrace : WordTrace (prefixWord ++ tailWord_593912) baseStart_593912 baseEnd_593912 := by
    simpa [prefixWord, tailWord_593912, baseEnd_593912] using wordTrace_append hprefix tailTrace_593912
  have hstable : (prefixWord ++ tailWord_593912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593912).length < 2 ^ (prefixWord ++ tailWord_593912).sum := by decide
  have hdescent : baseEnd_593912 < baseStart_593912 := by decide
  rcases family_descends (prefixWord ++ tailWord_593912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593960 : List Nat := [2, 1, 5, 3, 1, 8]
def baseStart_593960 : Nat := 118140960795 + 593960 * 2 ^ 59
def prefixEnd_593960 : Nat := 4983230072969 + 3 ^ 40 * 593960 * 2
def baseEnd_593960 : Nat := 10040723277188522221183

theorem tailTrace_593960 : CollatzResearch.WordTrace tailWord_593960 prefixEnd_593960 10040723277188522221183 := by
  unfold tailWord_593960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10831750464095917568517667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14442333952127890091356889 10831750464095917568517667)
  ·
    refine ⟨16247625696143876352776501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10831750464095917568517667 16247625696143876352776501)
    ·
      refine ⟨1523214909013488408072797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16247625696143876352776501 1523214909013488408072797)
      ·
        refine ⟨571205590880058153027299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1523214909013488408072797 571205590880058153027299)
        ·
          refine ⟨856808386320087229540949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571205590880058153027299 856808386320087229540949)
          ·
            refine ⟨10040723277188522221183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 856808386320087229540949 10040723277188522221183)
            ·
              rfl

theorem cell20_593960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 8].length) (baseStart_593960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593960 prefixEnd_593960 := by exact prefixLift 593960
  have htrace : WordTrace (prefixWord ++ tailWord_593960) baseStart_593960 baseEnd_593960 := by
    simpa [prefixWord, tailWord_593960, baseEnd_593960] using wordTrace_append hprefix tailTrace_593960
  have hstable : (prefixWord ++ tailWord_593960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593960).length < 2 ^ (prefixWord ++ tailWord_593960).sum := by decide
  have hdescent : baseEnd_593960 < baseStart_593960 := by decide
  rcases family_descends (prefixWord ++ tailWord_593960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593970 : List Nat := [3, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_593970 : Nat := 118140960795 + 593970 * 2 ^ 59
def prefixEnd_593970 : Nat := 4983230072969 + 3 ^ 40 * 593970 * 2
def baseEnd_593970 : Nat := 271104092756574509638567

theorem tailTrace_593970 : CollatzResearch.WordTrace tailWord_593970 prefixEnd_593970 271104092756574509638567 := by
  unfold tailWord_593970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415966414538901711224841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14442577105437071229932909 5415966414538901711224841)
  ·
    refine ⟨4061974810904176283418631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5415966414538901711224841 4061974810904176283418631)
    ·
      refine ⟨6092962216356264425127947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061974810904176283418631 6092962216356264425127947)
      ·
        refine ⟨9139443324534396637691921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6092962216356264425127947 9139443324534396637691921)
        ·
          refine ⟨6854582493400797478268941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9139443324534396637691921 6854582493400797478268941)
          ·
            refine ⟨2570468435025299054350853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6854582493400797478268941 2570468435025299054350853)
            ·
              refine ⟨481962831567243572690785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2570468435025299054350853 481962831567243572690785)
              ·
                refine ⟨361472123675432679518089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481962831567243572690785 361472123675432679518089)
                ·
                  refine ⟨271104092756574509638567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361472123675432679518089 271104092756574509638567)
                  ·
                    rfl

theorem cell20_593970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_593970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593970 prefixEnd_593970 := by exact prefixLift 593970
  have htrace : WordTrace (prefixWord ++ tailWord_593970) baseStart_593970 baseEnd_593970 := by
    simpa [prefixWord, tailWord_593970, baseEnd_593970] using wordTrace_append hprefix tailTrace_593970
  have hstable : (prefixWord ++ tailWord_593970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593970).length < 2 ^ (prefixWord ++ tailWord_593970).sum := by decide
  have hdescent : baseEnd_593970 < baseStart_593970 := by decide
  rcases family_descends (prefixWord ++ tailWord_593970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593977 : List Nat := [1, 2, 1, 5, 4, 1, 1, 5]
def baseStart_593977 : Nat := 118140960795 + 593977 * 2 ^ 59
def prefixEnd_593977 : Nat := 4983230072969 + 3 ^ 40 * 593977 * 2
def baseEnd_593977 : Nat := 90369095915771198801735

theorem tailTrace_593977 : CollatzResearch.WordTrace tailWord_593977 prefixEnd_593977 90369095915771198801735 := by
  unfold tailWord_593977
  simp only [CollatzResearch.WordTrace]
  refine ⟨21664120969130247040404185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14442747312753498026936123 21664120969130247040404185)
  ·
    refine ⟨16248090726847685280303139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21664120969130247040404185 16248090726847685280303139)
    ·
      refine ⟨24372136090271527920454709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16248090726847685280303139 24372136090271527920454709)
      ·
        refine ⟨2284887758462955742542629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24372136090271527920454709 2284887758462955742542629)
        ·
          refine ⟨428416454711804201726743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2284887758462955742542629 428416454711804201726743)
          ·
            refine ⟨642624682067706302590115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428416454711804201726743 642624682067706302590115)
            ·
              refine ⟨963937023101559453885173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642624682067706302590115 963937023101559453885173)
              ·
                refine ⟨90369095915771198801735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 963937023101559453885173 90369095915771198801735)
                ·
                  rfl

theorem cell20_593977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5].length) (baseStart_593977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593977 prefixEnd_593977 := by exact prefixLift 593977
  have htrace : WordTrace (prefixWord ++ tailWord_593977) baseStart_593977 baseEnd_593977 := by
    simpa [prefixWord, tailWord_593977, baseEnd_593977] using wordTrace_append hprefix tailTrace_593977
  have hstable : (prefixWord ++ tailWord_593977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593977).length < 2 ^ (prefixWord ++ tailWord_593977).sum := by decide
  have hdescent : baseEnd_593977 < baseStart_593977 := by decide
  rcases family_descends (prefixWord ++ tailWord_593977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593995 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_593995 : Nat := 118140960795 + 593995 * 2 ^ 59
def prefixEnd_593995 : Nat := 4983230072969 + 3 ^ 40 * 593995 * 2
def baseEnd_593995 : Nat := 271115503437785533805131

theorem tailTrace_593995 : CollatzResearch.WordTrace tailWord_593995 prefixEnd_593995 271115503437785533805131 := by
  unfold tailWord_593995
  simp only [CollatzResearch.WordTrace]
  refine ⟨21664777483065036114559439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14443184988710024076372959 21664777483065036114559439)
  ·
    refine ⟨32497166224597554171839159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21664777483065036114559439 32497166224597554171839159)
    ·
      refine ⟨48745749336896331257758739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32497166224597554171839159 48745749336896331257758739)
      ·
        refine ⟨73118624005344496886638109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48745749336896331257758739 73118624005344496886638109)
        ·
          refine ⟨27419484002004186332489291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73118624005344496886638109 27419484002004186332489291)
          ·
            refine ⟨41129226003006279498733937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27419484002004186332489291 41129226003006279498733937)
            ·
              refine ⟨30846919502254709624050453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41129226003006279498733937 30846919502254709624050453)
              ·
                refine ⟨1445949351668189513627365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30846919502254709624050453 1445949351668189513627365)
                ·
                  refine ⟨271115503437785533805131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445949351668189513627365 271115503437785533805131)
                  ·
                    rfl

theorem cell20_593995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_593995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593995 prefixEnd_593995 := by exact prefixLift 593995
  have htrace : WordTrace (prefixWord ++ tailWord_593995) baseStart_593995 baseEnd_593995 := by
    simpa [prefixWord, tailWord_593995, baseEnd_593995] using wordTrace_append hprefix tailTrace_593995
  have hstable : (prefixWord ++ tailWord_593995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593995).length < 2 ^ (prefixWord ++ tailWord_593995).sum := by decide
  have hdescent : baseEnd_593995 < baseStart_593995 := by decide
  rcases family_descends (prefixWord ++ tailWord_593995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_593998 : List Nat := [4, 1, 1, 1, 1, 5, 3, 4]
def baseStart_593998 : Nat := 118140960795 + 593998 * 2 ^ 59
def prefixEnd_593998 : Nat := 4983230072969 + 3 ^ 40 * 593998 * 2
def baseEnd_593998 : Nat := 90372290906510285568373

theorem tailTrace_593998 : CollatzResearch.WordTrace tailWord_593998 prefixEnd_593998 90372290906510285568373 := by
  unfold tailWord_593998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708110862756770953364831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14443257934702778417945765 2708110862756770953364831)
  ·
    refine ⟨4062166294135156430047247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2708110862756770953364831 4062166294135156430047247)
    ·
      refine ⟨6093249441202734645070871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4062166294135156430047247 6093249441202734645070871)
      ·
        refine ⟨9139874161804101967606307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6093249441202734645070871 9139874161804101967606307)
        ·
          refine ⟨13709811242706152951409461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9139874161804101967606307 13709811242706152951409461)
          ·
            refine ⟨1285294804003701839194637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13709811242706152951409461 1285294804003701839194637)
            ·
              refine ⟨481985551501388189697989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285294804003701839194637 481985551501388189697989)
              ·
                refine ⟨90372290906510285568373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481985551501388189697989 90372290906510285568373)
                ·
                  rfl

theorem cell20_593998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_593998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_593998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_593998 prefixEnd_593998 := by exact prefixLift 593998
  have htrace : WordTrace (prefixWord ++ tailWord_593998) baseStart_593998 baseEnd_593998 := by
    simpa [prefixWord, tailWord_593998, baseEnd_593998] using wordTrace_append hprefix tailTrace_593998
  have hstable : (prefixWord ++ tailWord_593998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_593998).length < 2 ^ (prefixWord ++ tailWord_593998).sum := by decide
  have hdescent : baseEnd_593998 < baseStart_593998 := by decide
  rcases family_descends (prefixWord ++ tailWord_593998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594018 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_594018 : Nat := 118140960795 + 594018 * 2 ^ 59
def prefixEnd_594018 : Nat := 4983230072969 + 3 ^ 40 * 594018 * 2
def baseEnd_594018 : Nat := 271126001264499676038371

theorem tailTrace_594018 : CollatzResearch.WordTrace tailWord_594018 prefixEnd_594018 271126001264499676038371 := by
  unfold tailWord_594018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416404090495427760661677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14443744241321140695097805 5416404090495427760661677)
  ·
    refine ⟨2031151533935785410248129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5416404090495427760661677 2031151533935785410248129)
    ·
      refine ⟨1523363650451839057686097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2031151533935785410248129 1523363650451839057686097)
      ·
        refine ⟨1142522737838879293264573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1523363650451839057686097 1142522737838879293264573)
        ·
          refine ⟨428446026689579734974215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1142522737838879293264573 428446026689579734974215)
          ·
            refine ⟨642669040034369602461323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428446026689579734974215 642669040034369602461323)
            ·
              refine ⟨964003560051554403691985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642669040034369602461323 964003560051554403691985)
              ·
                refine ⟨723002670038665802768989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964003560051554403691985 723002670038665802768989)
                ·
                  refine ⟨271126001264499676038371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723002670038665802768989 271126001264499676038371)
                  ·
                    rfl

theorem cell20_594018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_594018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594018 prefixEnd_594018 := by exact prefixLift 594018
  have htrace : WordTrace (prefixWord ++ tailWord_594018) baseStart_594018 baseEnd_594018 := by
    simpa [prefixWord, tailWord_594018, baseEnd_594018] using wordTrace_append hprefix tailTrace_594018
  have hstable : (prefixWord ++ tailWord_594018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594018).length < 2 ^ (prefixWord ++ tailWord_594018).sum := by decide
  have hdescent : baseEnd_594018 < baseStart_594018 := by decide
  rcases family_descends (prefixWord ++ tailWord_594018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594029 : List Nat := [1, 5, 1, 1, 2, 1, 1, 6, 2]
def baseStart_594029 : Nat := 118140960795 + 594029 * 2 ^ 59
def prefixEnd_594029 : Nat := 4983230072969 + 3 ^ 40 * 594029 * 2
def baseEnd_594029 : Nat := 271131021964232526671659

theorem tailTrace_594029 : CollatzResearch.WordTrace tailWord_594029 prefixEnd_594029 271131021964232526671659 := by
  unfold tailWord_594029
  simp only [CollatzResearch.WordTrace]
  refine ⟨21666017564941859921297141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14444011709961239947531427 21666017564941859921297141)
  ·
    refine ⟨2031189146713299367621607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21666017564941859921297141 2031189146713299367621607)
    ·
      refine ⟨3046783720069949051432411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031189146713299367621607 3046783720069949051432411)
      ·
        refine ⟨4570175580104923577148617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3046783720069949051432411 4570175580104923577148617)
        ·
          refine ⟨3427631685078692682861463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4570175580104923577148617 3427631685078692682861463)
          ·
            refine ⟨5141447527618039024292195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3427631685078692682861463 5141447527618039024292195)
            ·
              refine ⟨7712171291427058536438293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5141447527618039024292195 7712171291427058536438293)
              ·
                refine ⟨361508029285643368895545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7712171291427058536438293 361508029285643368895545)
                ·
                  refine ⟨271131021964232526671659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361508029285643368895545 271131021964232526671659)
                  ·
                    rfl

theorem cell20_594029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_594029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594029 prefixEnd_594029 := by exact prefixLift 594029
  have htrace : WordTrace (prefixWord ++ tailWord_594029) baseStart_594029 baseEnd_594029 := by
    simpa [prefixWord, tailWord_594029, baseEnd_594029] using wordTrace_append hprefix tailTrace_594029
  have hstable : (prefixWord ++ tailWord_594029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594029).length < 2 ^ (prefixWord ++ tailWord_594029).sum := by decide
  have hdescent : baseEnd_594029 < baseStart_594029 := by decide
  rcases family_descends (prefixWord ++ tailWord_594029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594040 : List Nat := [2, 1, 2, 1, 1, 1, 3, 9]
def baseStart_594040 : Nat := 118140960795 + 594040 * 2 ^ 59
def prefixEnd_594040 : Nat := 4983230072969 + 3 ^ 40 * 594040 * 2
def baseEnd_594040 : Nat := 90378680887988459101649

theorem tailTrace_594040 : CollatzResearch.WordTrace tailWord_594040 prefixEnd_594040 90378680887988459101649 := by
  unfold tailWord_594040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10833209383951004399973787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14444279178601339199965049 10833209383951004399973787)
  ·
    refine ⟨16249814075926506599960681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10833209383951004399973787 16249814075926506599960681)
    ·
      refine ⟨12187360556944879949970511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16249814075926506599960681 12187360556944879949970511)
      ·
        refine ⟨18281040835417319924955767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12187360556944879949970511 18281040835417319924955767)
        ·
          refine ⟨27421561253125979887433651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18281040835417319924955767 27421561253125979887433651)
          ·
            refine ⟨41132341879688969831150477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27421561253125979887433651 41132341879688969831150477)
            ·
              refine ⟨15424628204883363686681429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41132341879688969831150477 15424628204883363686681429)
              ·
                refine ⟨90378680887988459101649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15424628204883363686681429 90378680887988459101649)
                ·
                  rfl

theorem cell20_594040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_594040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594040 prefixEnd_594040 := by exact prefixLift 594040
  have htrace : WordTrace (prefixWord ++ tailWord_594040) baseStart_594040 baseEnd_594040 := by
    simpa [prefixWord, tailWord_594040, baseEnd_594040] using wordTrace_append hprefix tailTrace_594040
  have hstable : (prefixWord ++ tailWord_594040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594040).length < 2 ^ (prefixWord ++ tailWord_594040).sum := by decide
  have hdescent : baseEnd_594040 < baseStart_594040 := by decide
  rcases family_descends (prefixWord ++ tailWord_594040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594074 : List Nat := [3, 1, 1, 5, 2, 2, 6]
def baseStart_594074 : Nat := 118140960795 + 594074 * 2 ^ 59
def prefixEnd_594074 : Nat := 4983230072969 + 3 ^ 40 * 594074 * 2
def baseEnd_594074 : Nat := 30127951243379152241275

theorem tailTrace_594074 : CollatzResearch.WordTrace tailWord_594074 prefixEnd_594074 30127951243379152241275 := by
  unfold tailWord_594074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416914712444708151671319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14445105899852555071123517 5416914712444708151671319)
  ·
    refine ⟨8125372068667062227506979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5416914712444708151671319 8125372068667062227506979)
    ·
      refine ⟨12188058103000593341260469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8125372068667062227506979 12188058103000593341260469)
      ·
        refine ⟨1142630447156305625743169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12188058103000593341260469 1142630447156305625743169)
        ·
          refine ⟨856972835367229219307377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142630447156305625743169 856972835367229219307377)
          ·
            refine ⟨642729626525421914480533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856972835367229219307377 642729626525421914480533)
            ·
              refine ⟨30127951243379152241275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 642729626525421914480533 30127951243379152241275)
              ·
                rfl

theorem cell20_594074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 6].length) (baseStart_594074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594074 prefixEnd_594074 := by exact prefixLift 594074
  have htrace : WordTrace (prefixWord ++ tailWord_594074) baseStart_594074 baseEnd_594074 := by
    simpa [prefixWord, tailWord_594074, baseEnd_594074] using wordTrace_append hprefix tailTrace_594074
  have hstable : (prefixWord ++ tailWord_594074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594074).length < 2 ^ (prefixWord ++ tailWord_594074).sum := by decide
  have hdescent : baseEnd_594074 < baseStart_594074 := by decide
  rcases family_descends (prefixWord ++ tailWord_594074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594084 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 4]
def baseStart_594084 : Nat := 118140960795 + 594084 * 2 ^ 59
def prefixEnd_594084 : Nat := 4983230072969 + 3 ^ 40 * 594084 * 2
def baseEnd_594084 : Nat := 271156125462896779838101

theorem tailTrace_594084 : CollatzResearch.WordTrace tailWord_594084 prefixEnd_594084 271156125462896779838101 := by
  unfold tailWord_594084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10834011789871302157274653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14445349053161736209699537 10834011789871302157274653)
  ·
    refine ⟨4062754421201738308977995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10834011789871302157274653 4062754421201738308977995)
    ·
      refine ⟨6094131631802607463466993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4062754421201738308977995 6094131631802607463466993)
      ·
        refine ⟨4570598723851955597600245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6094131631802607463466993 4570598723851955597600245)
        ·
          refine ⟨428493630361120837275023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4570598723851955597600245 428493630361120837275023)
          ·
            refine ⟨642740445541681255912535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428493630361120837275023 642740445541681255912535)
            ·
              refine ⟨964110668312521883868803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642740445541681255912535 964110668312521883868803)
              ·
                refine ⟨1446166002468782825803205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964110668312521883868803 1446166002468782825803205)
                ·
                  refine ⟨271156125462896779838101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446166002468782825803205 271156125462896779838101)
                  ·
                    rfl

theorem cell20_594084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_594084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594084 prefixEnd_594084 := by exact prefixLift 594084
  have htrace : WordTrace (prefixWord ++ tailWord_594084) baseStart_594084 baseEnd_594084 := by
    simpa [prefixWord, tailWord_594084, baseEnd_594084] using wordTrace_append hprefix tailTrace_594084
  have hstable : (prefixWord ++ tailWord_594084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594084).length < 2 ^ (prefixWord ++ tailWord_594084).sum := by decide
  have hdescent : baseEnd_594084 < baseStart_594084 := by decide
  rcases family_descends (prefixWord ++ tailWord_594084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594109 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_594109 : Nat := 118140960795 + 594109 * 2 ^ 59
def prefixEnd_594109 : Nat := 4983230072969 + 3 ^ 40 * 594109 * 2
def baseEnd_594109 : Nat := 271167536144107804004665

theorem tailTrace_594109 : CollatzResearch.WordTrace tailWord_594109 prefixEnd_594109 271167536144107804004665 := by
  unfold tailWord_594109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21668935404652033584209381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14445956936434689056139587 21668935404652033584209381)
  ·
    refine ⟨4062925388372256297039259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21668935404652033584209381 4062925388372256297039259)
    ·
      refine ⟨6094388082558384445558889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4062925388372256297039259 6094388082558384445558889)
      ·
        refine ⟨4570791061918788334169167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6094388082558384445558889 4570791061918788334169167)
        ·
          refine ⟨6856186592878182501253751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4570791061918788334169167 6856186592878182501253751)
          ·
            refine ⟨10284279889317273751880627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6856186592878182501253751 10284279889317273751880627)
            ·
              refine ⟨15426419833975910627820941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10284279889317273751880627 15426419833975910627820941)
              ·
                refine ⟨5784907437740966485432853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15426419833975910627820941 5784907437740966485432853)
                ·
                  refine ⟨271167536144107804004665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5784907437740966485432853 271167536144107804004665)
                  ·
                    rfl

theorem cell20_594109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_594109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594109 prefixEnd_594109 := by exact prefixLift 594109
  have htrace : WordTrace (prefixWord ++ tailWord_594109) baseStart_594109 baseEnd_594109 := by
    simpa [prefixWord, tailWord_594109, baseEnd_594109] using wordTrace_append hprefix tailTrace_594109
  have hstable : (prefixWord ++ tailWord_594109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594109).length < 2 ^ (prefixWord ++ tailWord_594109).sum := by decide
  have hdescent : baseEnd_594109 < baseStart_594109 := by decide
  rcases family_descends (prefixWord ++ tailWord_594109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594133 : List Nat := [1, 3, 2, 4, 2, 8]
def baseStart_594133 : Nat := 118140960795 + 594133 * 2 ^ 59
def prefixEnd_594133 : Nat := 4983230072969 + 3 ^ 40 * 594133 * 2
def baseEnd_594133 : Nat := 10043647792521125452021

theorem tailTrace_594133 : CollatzResearch.WordTrace tailWord_594133 prefixEnd_594133 10043647792521125452021 := by
  unfold tailWord_594133
  simp only [CollatzResearch.WordTrace]
  refine ⟨21669810756565085683083053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14446540504376723788722035 21669810756565085683083053)
  ·
    refine ⟨8126179033711907131156145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21669810756565085683083053 8126179033711907131156145)
    ·
      refine ⟨6094634275283930348367109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8126179033711907131156145 6094634275283930348367109)
      ·
        refine ⟨1142743926615736940318833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6094634275283930348367109 1142743926615736940318833)
        ·
          refine ⟨857057944961802705239125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142743926615736940318833 857057944961802705239125)
          ·
            refine ⟨10043647792521125452021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 857057944961802705239125 10043647792521125452021)
            ·
              rfl

theorem cell20_594133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 8].length) (baseStart_594133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594133 prefixEnd_594133 := by exact prefixLift 594133
  have htrace : WordTrace (prefixWord ++ tailWord_594133) baseStart_594133 baseEnd_594133 := by
    simpa [prefixWord, tailWord_594133, baseEnd_594133] using wordTrace_append hprefix tailTrace_594133
  have hstable : (prefixWord ++ tailWord_594133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594133).length < 2 ^ (prefixWord ++ tailWord_594133).sum := by decide
  have hdescent : baseEnd_594133 < baseStart_594133 := by decide
  rcases family_descends (prefixWord ++ tailWord_594133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594212 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_594212 : Nat := 118140960795 + 594212 * 2 ^ 59
def prefixEnd_594212 : Nat := 4983230072969 + 3 ^ 40 * 594212 * 2
def baseEnd_594212 : Nat := 271214548150697223570911

theorem tailTrace_594212 : CollatzResearch.WordTrace tailWord_594212 prefixEnd_594212 271214548150697223570911 := by
  unfold tailWord_594212
  simp only [CollatzResearch.WordTrace]
  refine ⟨10836346061639441087604445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14448461415519254783472593 10836346061639441087604445)
  ·
    refine ⟨4063629773114790407851667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10836346061639441087604445 4063629773114790407851667)
    ·
      refine ⟨6095444659672185611777501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4063629773114790407851667 6095444659672185611777501)
      ·
        refine ⟨2285791747377069604416563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6095444659672185611777501 2285791747377069604416563)
        ·
          refine ⟨3428687621065604406624845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2285791747377069604416563 3428687621065604406624845)
          ·
            refine ⟨1285757857899601652484317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3428687621065604406624845 1285757857899601652484317)
            ·
              refine ⟨482159196712350619681619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1285757857899601652484317 482159196712350619681619)
              ·
                refine ⟨723238795068525929522429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482159196712350619681619 723238795068525929522429)
                ·
                  refine ⟨271214548150697223570911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723238795068525929522429 271214548150697223570911)
                  ·
                    rfl

theorem cell20_594212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_594212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594212 prefixEnd_594212 := by exact prefixLift 594212
  have htrace : WordTrace (prefixWord ++ tailWord_594212) baseStart_594212 baseEnd_594212 := by
    simpa [prefixWord, tailWord_594212, baseEnd_594212] using wordTrace_append hprefix tailTrace_594212
  have hstable : (prefixWord ++ tailWord_594212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594212).length < 2 ^ (prefixWord ++ tailWord_594212).sum := by decide
  have hdescent : baseEnd_594212 < baseStart_594212 := by decide
  rcases family_descends (prefixWord ++ tailWord_594212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594222 : List Nat := [4, 1, 3, 3, 1, 2, 2, 4]
def baseStart_594222 : Nat := 118140960795 + 594222 * 2 ^ 59
def prefixEnd_594222 : Nat := 4983230072969 + 3 ^ 40 * 594222 * 2
def baseEnd_594222 : Nat := 90406370807727211079179

theorem tailTrace_594222 : CollatzResearch.WordTrace tailWord_594222 prefixEnd_594222 90406370807727211079179 := by
  unfold tailWord_594222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709132106655331735384115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14448704568828435922048613 2709132106655331735384115)
  ·
    refine ⟨4063698159982997603076173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2709132106655331735384115 4063698159982997603076173)
    ·
      refine ⟨1523886809993624101153565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4063698159982997603076173 1523886809993624101153565)
      ·
        refine ⟨571457553747609037932587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1523886809993624101153565 571457553747609037932587)
        ·
          refine ⟨857186330621413556898881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571457553747609037932587 857186330621413556898881)
          ·
            refine ⟨642889747966060167674161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857186330621413556898881 642889747966060167674161)
            ·
              refine ⟨482167310974545125755621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642889747966060167674161 482167310974545125755621)
              ·
                refine ⟨90406370807727211079179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482167310974545125755621 90406370807727211079179)
                ·
                  rfl

theorem cell20_594222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_594222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594222 prefixEnd_594222 := by exact prefixLift 594222
  have htrace : WordTrace (prefixWord ++ tailWord_594222) baseStart_594222 baseEnd_594222 := by
    simpa [prefixWord, tailWord_594222, baseEnd_594222] using wordTrace_append hprefix tailTrace_594222
  have hstable : (prefixWord ++ tailWord_594222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594222).length < 2 ^ (prefixWord ++ tailWord_594222).sum := by decide
  have hdescent : baseEnd_594222 < baseStart_594222 := by decide
  rcases family_descends (prefixWord ++ tailWord_594222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594223 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_594223 : Nat := 118140960795 + 594223 * 2 ^ 59
def prefixEnd_594223 : Nat := 4983230072969 + 3 ^ 40 * 594223 * 2
def baseEnd_594223 : Nat := 271219568850430074204199

theorem tailTrace_594223 : CollatzResearch.WordTrace tailWord_594223 prefixEnd_594223 271219568850430074204199 := by
  unfold tailWord_594223
  simp only [CollatzResearch.WordTrace]
  refine ⟨21673093326239031053859323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14448728884159354035906215 21673093326239031053859323)
  ·
    refine ⟨32509639989358546580788985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21673093326239031053859323 32509639989358546580788985)
    ·
      refine ⟨24382229992018909935591739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32509639989358546580788985 24382229992018909935591739)
      ·
        refine ⟨36573344988028364903387609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24382229992018909935591739 36573344988028364903387609)
        ·
          refine ⟨27430008741021273677540707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36573344988028364903387609 27430008741021273677540707)
          ·
            refine ⟨41145013111531910516311061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27430008741021273677540707 41145013111531910516311061)
            ·
              refine ⟨1928672489603058305452081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41145013111531910516311061 1928672489603058305452081)
              ·
                refine ⟨1446504367202293729089061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928672489603058305452081 1446504367202293729089061)
                ·
                  refine ⟨271219568850430074204199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446504367202293729089061 271219568850430074204199)
                  ·
                    rfl

theorem cell20_594223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_594223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594223 prefixEnd_594223 := by exact prefixLift 594223
  have htrace : WordTrace (prefixWord ++ tailWord_594223) baseStart_594223 baseEnd_594223 := by
    simpa [prefixWord, tailWord_594223, baseEnd_594223] using wordTrace_append hprefix tailTrace_594223
  have hstable : (prefixWord ++ tailWord_594223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594223).length < 2 ^ (prefixWord ++ tailWord_594223).sum := by decide
  have hdescent : baseEnd_594223 < baseStart_594223 := by decide
  rcases family_descends (prefixWord ++ tailWord_594223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594240 : List Nat := [2, 1, 1, 2, 2, 1, 2, 7, 2]
def baseStart_594240 : Nat := 118140960795 + 594240 * 2 ^ 59
def prefixEnd_594240 : Nat := 4983230072969 + 3 ^ 40 * 594240 * 2
def baseEnd_594240 : Nat := 271227328113653570637463

theorem tailTrace_594240 : CollatzResearch.WordTrace tailWord_594240 prefixEnd_594240 271227328113653570637463 := by
  unfold tailWord_594240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10836856683588721478614087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14449142244784961971485449 10836856683588721478614087)
  ·
    refine ⟨16255285025383082217921131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10836856683588721478614087 16255285025383082217921131)
    ·
      refine ⟨24382927538074623326881697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16255285025383082217921131 24382927538074623326881697)
      ·
        refine ⟨18287195653555967495161273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24382927538074623326881697 18287195653555967495161273)
        ·
          refine ⟨13715396740166975621370955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18287195653555967495161273 13715396740166975621370955)
          ·
            refine ⟨20573095110250463432056433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13715396740166975621370955 20573095110250463432056433)
            ·
              refine ⟨15429821332687847574042325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20573095110250463432056433 15429821332687847574042325)
              ·
                refine ⟨361636437484871427516617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15429821332687847574042325 361636437484871427516617)
                ·
                  refine ⟨271227328113653570637463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361636437484871427516617 271227328113653570637463)
                  ·
                    rfl

theorem cell20_594240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_594240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594240 prefixEnd_594240 := by exact prefixLift 594240
  have htrace : WordTrace (prefixWord ++ tailWord_594240) baseStart_594240 baseEnd_594240 := by
    simpa [prefixWord, tailWord_594240, baseEnd_594240] using wordTrace_append hprefix tailTrace_594240
  have hstable : (prefixWord ++ tailWord_594240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594240).length < 2 ^ (prefixWord ++ tailWord_594240).sum := by decide
  have hdescent : baseEnd_594240 < baseStart_594240 := by decide
  rcases family_descends (prefixWord ++ tailWord_594240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594271 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 3]
def baseStart_594271 : Nat := 118140960795 + 594271 * 2 ^ 59
def prefixEnd_594271 : Nat := 4983230072969 + 3 ^ 40 * 594271 * 2
def baseEnd_594271 : Nat := 271241477358355240604003

theorem tailTrace_594271 : CollatzResearch.WordTrace tailWord_594271 prefixEnd_594271 271241477358355240604003 := by
  unfold tailWord_594271
  simp only [CollatzResearch.WordTrace]
  refine ⟨21674844030065135251606667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14449896020043423501071111 21674844030065135251606667)
  ·
    refine ⟨32512266045097702877410001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21674844030065135251606667 32512266045097702877410001)
    ·
      refine ⟨24384199533823277158057501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32512266045097702877410001 24384199533823277158057501)
      ·
        refine ⟨9144074825183728934271563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24384199533823277158057501 9144074825183728934271563)
        ·
          refine ⟨13716112237775593401407345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9144074825183728934271563 13716112237775593401407345)
          ·
            refine ⟨10287084178331695051055509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13716112237775593401407345 10287084178331695051055509)
            ·
              refine ⟨482207070859298205518227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10287084178331695051055509 482207070859298205518227)
              ·
                refine ⟨723310606288947308277341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482207070859298205518227 723310606288947308277341)
                ·
                  refine ⟨271241477358355240604003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723310606288947308277341 271241477358355240604003)
                  ·
                    rfl

theorem cell20_594271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 3].length) (baseStart_594271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594271 prefixEnd_594271 := by exact prefixLift 594271
  have htrace : WordTrace (prefixWord ++ tailWord_594271) baseStart_594271 baseEnd_594271 := by
    simpa [prefixWord, tailWord_594271, baseEnd_594271] using wordTrace_append hprefix tailTrace_594271
  have hstable : (prefixWord ++ tailWord_594271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594271).length < 2 ^ (prefixWord ++ tailWord_594271).sum := by decide
  have hdescent : baseEnd_594271 < baseStart_594271 := by decide
  rcases family_descends (prefixWord ++ tailWord_594271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594346 : List Nat := [3, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_594346 : Nat := 118140960795 + 594346 * 2 ^ 59
def prefixEnd_594346 : Nat := 4983230072969 + 3 ^ 40 * 594346 * 2
def baseEnd_594346 : Nat := 271275709401988313103697

theorem tailTrace_594346 : CollatzResearch.WordTrace tailWord_594346 prefixEnd_594346 271275709401988313103697 := by
  unfold tailWord_594346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5419394876198355765146723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14451719669862282040391261 5419394876198355765146723)
  ·
    refine ⟨8129092314297533647720085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5419394876198355765146723 8129092314297533647720085)
    ·
      refine ⟨381051202232696889736879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8129092314297533647720085 381051202232696889736879)
      ·
        refine ⟨571576803349045334605319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381051202232696889736879 571576803349045334605319)
        ·
          refine ⟨857365205023568001907979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571576803349045334605319 857365205023568001907979)
          ·
            refine ⟨1286047807535352002861969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857365205023568001907979 1286047807535352002861969)
            ·
              refine ⟨964535855651514002146477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286047807535352002861969 964535855651514002146477)
              ·
                refine ⟨361700945869317750804929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964535855651514002146477 361700945869317750804929)
                ·
                  refine ⟨271275709401988313103697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361700945869317750804929 271275709401988313103697)
                  ·
                    rfl

theorem cell20_594346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_594346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594346 prefixEnd_594346 := by exact prefixLift 594346
  have htrace : WordTrace (prefixWord ++ tailWord_594346) baseStart_594346 baseEnd_594346 := by
    simpa [prefixWord, tailWord_594346, baseEnd_594346] using wordTrace_append hprefix tailTrace_594346
  have hstable : (prefixWord ++ tailWord_594346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594346).length < 2 ^ (prefixWord ++ tailWord_594346).sum := by decide
  have hdescent : baseEnd_594346 < baseStart_594346 := by decide
  rcases family_descends (prefixWord ++ tailWord_594346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594364 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_594364 : Nat := 118140960795 + 594364 * 2 ^ 59
def prefixEnd_594364 : Nat := 4983230072969 + 3 ^ 40 * 594364 * 2
def baseEnd_594364 : Nat := 271283925092460250503623

theorem tailTrace_594364 : CollatzResearch.WordTrace tailWord_594364 prefixEnd_594364 271283925092460250503623 := by
  unfold tailWord_594364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10839118009364106067371073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14452157345818808089828097 10839118009364106067371073)
  ·
    refine ⟨8129338507023079550528305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10839118009364106067371073 8129338507023079550528305)
    ·
      refine ⟨6097003880267309662896229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8129338507023079550528305 6097003880267309662896229)
      ·
        refine ⟨1143188227550120561793043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6097003880267309662896229 1143188227550120561793043)
        ·
          refine ⟨1714782341325180842689565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143188227550120561793043 1714782341325180842689565)
          ·
            refine ⟨643043377996942816008587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1714782341325180842689565 643043377996942816008587)
            ·
              refine ⟨964565066995414224012881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643043377996942816008587 964565066995414224012881)
              ·
                refine ⟨723423800246560668009661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964565066995414224012881 723423800246560668009661)
                ·
                  refine ⟨271283925092460250503623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723423800246560668009661 271283925092460250503623)
                  ·
                    rfl

theorem cell20_594364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_594364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594364 prefixEnd_594364 := by exact prefixLift 594364
  have htrace : WordTrace (prefixWord ++ tailWord_594364) baseStart_594364 baseEnd_594364 := by
    simpa [prefixWord, tailWord_594364, baseEnd_594364] using wordTrace_append hprefix tailTrace_594364
  have hstable : (prefixWord ++ tailWord_594364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594364).length < 2 ^ (prefixWord ++ tailWord_594364).sum := by decide
  have hdescent : baseEnd_594364 < baseStart_594364 := by decide
  rcases family_descends (prefixWord ++ tailWord_594364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594375 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_594375 : Nat := 118140960795 + 594375 * 2 ^ 59
def prefixEnd_594375 : Nat := 4983230072969 + 3 ^ 40 * 594375 * 2
def baseEnd_594375 : Nat := 271288945792193101136911

theorem tailTrace_594375 : CollatzResearch.WordTrace tailWord_594375 prefixEnd_594375 271288945792193101136911 := by
  unfold tailWord_594375
  simp only [CollatzResearch.WordTrace]
  refine ⟨21678637221688361013392579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14452424814458907342261719 21678637221688361013392579)
  ·
    refine ⟨32517955832532541520088869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21678637221688361013392579 32517955832532541520088869)
    ·
      refine ⟨6097116718599851535016663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32517955832532541520088869 6097116718599851535016663)
      ·
        refine ⟨9145675077899777302524995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097116718599851535016663 9145675077899777302524995)
        ·
          refine ⟨13718512616849665953787493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9145675077899777302524995 13718512616849665953787493)
          ·
            refine ⟨2572221115659312366335155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13718512616849665953787493 2572221115659312366335155)
            ·
              refine ⟨3858331673488968549502733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572221115659312366335155 3858331673488968549502733)
              ·
                refine ⟨1446874377558363206063525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3858331673488968549502733 1446874377558363206063525)
                ·
                  refine ⟨271288945792193101136911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446874377558363206063525 271288945792193101136911)
                  ·
                    rfl

theorem cell20_594375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_594375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594375 prefixEnd_594375 := by exact prefixLift 594375
  have htrace : WordTrace (prefixWord ++ tailWord_594375) baseStart_594375 baseEnd_594375 := by
    simpa [prefixWord, tailWord_594375, baseEnd_594375] using wordTrace_append hprefix tailTrace_594375
  have hstable : (prefixWord ++ tailWord_594375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594375).length < 2 ^ (prefixWord ++ tailWord_594375).sum := by decide
  have hdescent : baseEnd_594375 < baseStart_594375 := by decide
  rcases family_descends (prefixWord ++ tailWord_594375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594382 : List Nat := [4, 1, 1, 1, 2, 1, 1, 9]
def baseStart_594382 : Nat := 118140960795 + 594382 * 2 ^ 59
def prefixEnd_594382 : Nat := 4983230072969 + 3 ^ 40 * 594382 * 2
def baseEnd_594382 : Nat := 90430713594310729301183

theorem tailTrace_594382 : CollatzResearch.WordTrace tailWord_594382 prefixEnd_594382 90430713594310729301183 := by
  unfold tailWord_594382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709861566582875151112175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14452595021775334139264933 2709861566582875151112175)
  ·
    refine ⟨4064792349874312726668263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2709861566582875151112175 4064792349874312726668263)
    ·
      refine ⟨6097188524811469090002395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4064792349874312726668263 6097188524811469090002395)
      ·
        refine ⟨9145782787217203635003593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097188524811469090002395 9145782787217203635003593)
        ·
          refine ⟨6859337090412902726252695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9145782787217203635003593 6859337090412902726252695)
          ·
            refine ⟨10289005635619354089379043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6859337090412902726252695 10289005635619354089379043)
            ·
              refine ⟨15433508453429031134068565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10289005635619354089379043 15433508453429031134068565)
              ·
                refine ⟨90430713594310729301183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15433508453429031134068565 90430713594310729301183)
                ·
                  rfl

theorem cell20_594382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_594382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594382 prefixEnd_594382 := by exact prefixLift 594382
  have htrace : WordTrace (prefixWord ++ tailWord_594382) baseStart_594382 baseEnd_594382 := by
    simpa [prefixWord, tailWord_594382, baseEnd_594382] using wordTrace_append hprefix tailTrace_594382
  have hstable : (prefixWord ++ tailWord_594382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594382).length < 2 ^ (prefixWord ++ tailWord_594382).sum := by decide
  have hdescent : baseEnd_594382 < baseStart_594382 := by decide
  rcases family_descends (prefixWord ++ tailWord_594382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594399 : List Nat := [1, 1, 2, 3, 3, 2, 4, 4]
def baseStart_594399 : Nat := 118140960795 + 594399 * 2 ^ 59
def prefixEnd_594399 : Nat := 4983230072969 + 3 ^ 40 * 594399 * 2
def baseEnd_594399 : Nat := 90433300015385228112271

theorem tailTrace_594399 : CollatzResearch.WordTrace tailWord_594399 prefixEnd_594399 90433300015385228112271 := by
  unfold tailWord_594399
  simp only [CollatzResearch.WordTrace]
  refine ⟨21679512573601413112266251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14453008382400942074844167 21679512573601413112266251)
  ·
    refine ⟨32519268860402119668399377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21679512573601413112266251 32519268860402119668399377)
    ·
      refine ⟨24389451645301589751299533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32519268860402119668399377 24389451645301589751299533)
      ·
        refine ⟨9146044366988096156737325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24389451645301589751299533 9146044366988096156737325)
        ·
          refine ⟨3429766637620536058776497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9146044366988096156737325 3429766637620536058776497)
          ·
            refine ⟨2572324978215402044082373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3429766637620536058776497 2572324978215402044082373)
            ·
              refine ⟨482310933415387883265445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2572324978215402044082373 482310933415387883265445)
              ·
                refine ⟨90433300015385228112271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482310933415387883265445 90433300015385228112271)
                ·
                  rfl

theorem cell20_594399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 4].length) (baseStart_594399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594399 prefixEnd_594399 := by exact prefixLift 594399
  have htrace : WordTrace (prefixWord ++ tailWord_594399) baseStart_594399 baseEnd_594399 := by
    simpa [prefixWord, tailWord_594399, baseEnd_594399] using wordTrace_append hprefix tailTrace_594399
  have hstable : (prefixWord ++ tailWord_594399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594399).length < 2 ^ (prefixWord ++ tailWord_594399).sum := by decide
  have hdescent : baseEnd_594399 < baseStart_594399 := by decide
  rcases family_descends (prefixWord ++ tailWord_594399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594405 : List Nat := [1, 3, 1, 5, 3, 1, 1, 3, 2]
def baseStart_594405 : Nat := 118140960795 + 594405 * 2 ^ 59
def prefixEnd_594405 : Nat := 4983230072969 + 3 ^ 40 * 594405 * 2
def baseEnd_594405 : Nat := 271302638609646330136789

theorem tailTrace_594405 : CollatzResearch.WordTrace tailWord_594405 prefixEnd_594405 271302638609646330136789 := by
  unfold tailWord_594405
  simp only [CollatzResearch.WordTrace]
  refine ⟨21679731411579676136984669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14453154274386450757989779 21679731411579676136984669)
  ·
    refine ⟨8129899279342378551369251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21679731411579676136984669 8129899279342378551369251)
    ·
      refine ⟨12194848919013567827053877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8129899279342378551369251 12194848919013567827053877)
      ·
        refine ⟨1143267086157521983786301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12194848919013567827053877 1143267086157521983786301)
        ·
          refine ⟨428725157309070743919863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1143267086157521983786301 428725157309070743919863)
          ·
            refine ⟨643087735963606115879795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428725157309070743919863 643087735963606115879795)
            ·
              refine ⟨964631603945409173819693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643087735963606115879795 964631603945409173819693)
              ·
                refine ⟨361736851479528440182385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964631603945409173819693 361736851479528440182385)
                ·
                  refine ⟨271302638609646330136789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361736851479528440182385 271302638609646330136789)
                  ·
                    rfl

theorem cell20_594405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_594405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594405 prefixEnd_594405 := by exact prefixLift 594405
  have htrace : WordTrace (prefixWord ++ tailWord_594405) baseStart_594405 baseEnd_594405 := by
    simpa [prefixWord, tailWord_594405, baseEnd_594405] using wordTrace_append hprefix tailTrace_594405
  have hstable : (prefixWord ++ tailWord_594405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594405).length < 2 ^ (prefixWord ++ tailWord_594405).sum := by decide
  have hdescent : baseEnd_594405 < baseStart_594405 := by decide
  rcases family_descends (prefixWord ++ tailWord_594405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594458 : List Nat := [3, 1, 1, 3, 1, 1, 4, 6]
def baseStart_594458 : Nat := 118140960795 + 594458 * 2 ^ 59
def prefixEnd_594458 : Nat := 4983230072969 + 3 ^ 40 * 594458 * 2
def baseEnd_594458 : Nat := 90442276417937900456635

theorem tailTrace_594458 : CollatzResearch.WordTrace tailWord_594458 prefixEnd_594458 90442276417937900456635 := by
  unfold tailWord_594458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420416120096916547166007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14454442986925110792442685 5420416120096916547166007)
  ·
    refine ⟨8130624180145374820749011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5420416120096916547166007 8130624180145374820749011)
    ·
      refine ⟨12195936270218062231123517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8130624180145374820749011 12195936270218062231123517)
      ·
        refine ⟨4573476101331773336671319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12195936270218062231123517 4573476101331773336671319)
        ·
          refine ⟨6860214151997660005006979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4573476101331773336671319 6860214151997660005006979)
          ·
            refine ⟨10290321227996490007510469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6860214151997660005006979 10290321227996490007510469)
            ·
              refine ⟨1929435230249341876408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10290321227996490007510469 1929435230249341876408213)
              ·
                refine ⟨90442276417937900456635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1929435230249341876408213 90442276417937900456635)
                ·
                  rfl

theorem cell20_594458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_594458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594458 prefixEnd_594458 := by exact prefixLift 594458
  have htrace : WordTrace (prefixWord ++ tailWord_594458) baseStart_594458 baseEnd_594458 := by
    simpa [prefixWord, tailWord_594458, baseEnd_594458] using wordTrace_append hprefix tailTrace_594458
  have hstable : (prefixWord ++ tailWord_594458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594458).length < 2 ^ (prefixWord ++ tailWord_594458).sum := by decide
  have hdescent : baseEnd_594458 < baseStart_594458 := by decide
  rcases family_descends (prefixWord ++ tailWord_594458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594477 : List Nat := [1, 5, 4, 1, 1, 2, 2, 2, 2]
def baseStart_594477 : Nat := 118140960795 + 594477 * 2 ^ 59
def prefixEnd_594477 : Nat := 4983230072969 + 3 ^ 40 * 594477 * 2
def baseEnd_594477 : Nat := 271335501371534079736495

theorem tailTrace_594477 : CollatzResearch.WordTrace tailWord_594477 prefixEnd_594477 271335501371534079736495 := by
  unfold tailWord_594477
  simp only [CollatzResearch.WordTrace]
  refine ⟨21682357467318832433605685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14454904978212554955737123 21682357467318832433605685)
  ·
    refine ⟨2032721012561140540650533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21682357467318832433605685 2032721012561140540650533)
    ·
      refine ⟨381135189855213851371975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2032721012561140540650533 381135189855213851371975)
      ·
        refine ⟨571702784782820777057963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381135189855213851371975 571702784782820777057963)
        ·
          refine ⟨857554177174231165586945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571702784782820777057963 857554177174231165586945)
          ·
            refine ⟨643165632880673374190209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857554177174231165586945 643165632880673374190209)
            ·
              refine ⟨482374224660505030642657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643165632880673374190209 482374224660505030642657)
              ·
                refine ⟨361780668495378772981993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482374224660505030642657 361780668495378772981993)
                ·
                  refine ⟨271335501371534079736495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361780668495378772981993 271335501371534079736495)
                  ·
                    rfl

theorem cell20_594477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_594477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594477 prefixEnd_594477 := by exact prefixLift 594477
  have htrace : WordTrace (prefixWord ++ tailWord_594477) baseStart_594477 baseEnd_594477 := by
    simpa [prefixWord, tailWord_594477, baseEnd_594477] using wordTrace_append hprefix tailTrace_594477
  have hstable : (prefixWord ++ tailWord_594477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594477).length < 2 ^ (prefixWord ++ tailWord_594477).sum := by decide
  have hdescent : baseEnd_594477 < baseStart_594477 := by decide
  rcases family_descends (prefixWord ++ tailWord_594477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594478 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_594478 : Nat := 118140960795 + 594478 * 2 ^ 59
def prefixEnd_594478 : Nat := 4983230072969 + 3 ^ 40 * 594478 * 2
def baseEnd_594478 : Nat := 271335957798782520703157

theorem tailTrace_594478 : CollatzResearch.WordTrace tailWord_594478 prefixEnd_594478 271335957798782520703157 := by
  unfold tailWord_594478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710299242539401200549011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14454929293543473069594725 2710299242539401200549011)
  ·
    refine ⟨4065448863809101800823517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2710299242539401200549011 4065448863809101800823517)
    ·
      refine ⟨1524543323928413175308819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4065448863809101800823517 1524543323928413175308819)
      ·
        refine ⟨2286814985892619762963229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524543323928413175308819 2286814985892619762963229)
        ·
          refine ⟨857555619709732411111211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2286814985892619762963229 857555619709732411111211)
          ·
            refine ⟨1286333429564598616666817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857555619709732411111211 1286333429564598616666817)
            ·
              refine ⟨964750072173448962500113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286333429564598616666817 964750072173448962500113)
              ·
                refine ⟨723562554130086721875085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964750072173448962500113 723562554130086721875085)
                ·
                  refine ⟨271335957798782520703157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723562554130086721875085 271335957798782520703157)
                  ·
                    rfl

theorem cell20_594478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_594478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594478 prefixEnd_594478 := by exact prefixLift 594478
  have htrace : WordTrace (prefixWord ++ tailWord_594478) baseStart_594478 baseEnd_594478 := by
    simpa [prefixWord, tailWord_594478, baseEnd_594478] using wordTrace_append hprefix tailTrace_594478
  have hstable : (prefixWord ++ tailWord_594478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594478).length < 2 ^ (prefixWord ++ tailWord_594478).sum := by decide
  have hdescent : baseEnd_594478 < baseStart_594478 := by decide
  rcases family_descends (prefixWord ++ tailWord_594478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594482 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_594482 : Nat := 118140960795 + 594482 * 2 ^ 59
def prefixEnd_594482 : Nat := 4983230072969 + 3 ^ 40 * 594482 * 2
def baseEnd_594482 : Nat := 271337783507776284569807

theorem tailTrace_594482 : CollatzResearch.WordTrace tailWord_594482 prefixEnd_594482 271337783507776284569807 := by
  unfold tailWord_594482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420634958075179571884425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14455026554867145525025133 5420634958075179571884425)
  ·
    refine ⟨4065476218556384678913319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5420634958075179571884425 4065476218556384678913319)
    ·
      refine ⟨6098214327834577018369979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4065476218556384678913319 6098214327834577018369979)
      ·
        refine ⟨9147321491751865527554969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6098214327834577018369979 9147321491751865527554969)
        ·
          refine ⟨6860491118813899145666227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9147321491751865527554969 6860491118813899145666227)
          ·
            refine ⟨10290736678220848718499341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6860491118813899145666227 10290736678220848718499341)
            ·
              refine ⟨3859026254332818269437253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10290736678220848718499341 3859026254332818269437253)
              ·
                refine ⟨723567422687403425519485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3859026254332818269437253 723567422687403425519485)
                ·
                  refine ⟨271337783507776284569807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723567422687403425519485 271337783507776284569807)
                  ·
                    rfl

theorem cell20_594482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_594482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594482 prefixEnd_594482 := by exact prefixLift 594482
  have htrace : WordTrace (prefixWord ++ tailWord_594482) baseStart_594482 baseEnd_594482 := by
    simpa [prefixWord, tailWord_594482, baseEnd_594482] using wordTrace_append hprefix tailTrace_594482
  have hstable : (prefixWord ++ tailWord_594482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594482).length < 2 ^ (prefixWord ++ tailWord_594482).sum := by decide
  have hdescent : baseEnd_594482 < baseStart_594482 := by decide
  rcases family_descends (prefixWord ++ tailWord_594482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594489 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_594489 : Nat := 118140960795 + 594489 * 2 ^ 59
def prefixEnd_594489 : Nat := 4983230072969 + 3 ^ 40 * 594489 * 2
def baseEnd_594489 : Nat := 271340978498515371336445

theorem tailTrace_594489 : CollatzResearch.WordTrace tailWord_594489 prefixEnd_594489 271340978498515371336445 := by
  unfold tailWord_594489
  simp only [CollatzResearch.WordTrace]
  refine ⟨21682795143275358483042521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14455196762183572322028347 21682795143275358483042521)
  ·
    refine ⟨16262096357456518862281891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21682795143275358483042521 16262096357456518862281891)
    ·
      refine ⟨24393144536184778293422837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16262096357456518862281891 24393144536184778293422837)
      ·
        refine ⟨2286857300267322965008391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24393144536184778293422837 2286857300267322965008391)
        ·
          refine ⟨3430285950400984447512587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286857300267322965008391 3430285950400984447512587)
          ·
            refine ⟨5145428925601476671268881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430285950400984447512587 5145428925601476671268881)
            ·
              refine ⟨3859071694201107503451661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5145428925601476671268881 3859071694201107503451661)
              ·
                refine ⟨1447151885325415313794373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3859071694201107503451661 1447151885325415313794373)
                ·
                  refine ⟨271340978498515371336445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1447151885325415313794373 271340978498515371336445)
                  ·
                    rfl

theorem cell20_594489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_594489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594489 prefixEnd_594489 := by exact prefixLift 594489
  have htrace : WordTrace (prefixWord ++ tailWord_594489) baseStart_594489 baseEnd_594489 := by
    simpa [prefixWord, tailWord_594489, baseEnd_594489] using wordTrace_append hprefix tailTrace_594489
  have hstable : (prefixWord ++ tailWord_594489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594489).length < 2 ^ (prefixWord ++ tailWord_594489).sum := by decide
  have hdescent : baseEnd_594489 < baseStart_594489 := by decide
  rcases family_descends (prefixWord ++ tailWord_594489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594496 : List Nat := [2, 1, 1, 2, 2, 2, 5, 5]
def baseStart_594496 : Nat := 118140960795 + 594496 * 2 ^ 59
def prefixEnd_594496 : Nat := 4983230072969 + 3 ^ 40 * 594496 * 2
def baseEnd_594496 : Nat := 90448057829751486034361

theorem tailTrace_594496 : CollatzResearch.WordTrace tailWord_594496 prefixEnd_594496 90448057829751486034361 := by
  unfold tailWord_594496
  simp only [CollatzResearch.WordTrace]
  refine ⟨10841525227124999339273671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14455366969499999119031561 10841525227124999339273671)
  ·
    refine ⟨16262287840687499008910507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10841525227124999339273671 16262287840687499008910507)
    ·
      refine ⟨24393431761031248513365761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16262287840687499008910507 24393431761031248513365761)
      ·
        refine ⟨18295073820773436385024321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24393431761031248513365761 18295073820773436385024321)
        ·
          refine ⟨13721305365580077288768241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18295073820773436385024321 13721305365580077288768241)
          ·
            refine ⟨10290979024185057966576181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13721305365580077288768241 10290979024185057966576181)
            ·
              refine ⟨964779283517349184366517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10290979024185057966576181 964779283517349184366517)
              ·
                refine ⟨90448057829751486034361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 964779283517349184366517 90448057829751486034361)
                ·
                  rfl

theorem cell20_594496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_594496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594496 prefixEnd_594496 := by exact prefixLift 594496
  have htrace : WordTrace (prefixWord ++ tailWord_594496) baseStart_594496 baseEnd_594496 := by
    simpa [prefixWord, tailWord_594496, baseEnd_594496] using wordTrace_append hprefix tailTrace_594496
  have hstable : (prefixWord ++ tailWord_594496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594496).length < 2 ^ (prefixWord ++ tailWord_594496).sum := by decide
  have hdescent : baseEnd_594496 < baseStart_594496 := by decide
  rcases family_descends (prefixWord ++ tailWord_594496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594513 : List Nat := [1, 2, 2, 1, 3, 4, 3, 4]
def baseStart_594513 : Nat := 118140960795 + 594513 * 2 ^ 59
def prefixEnd_594513 : Nat := 4983230072969 + 3 ^ 40 * 594513 * 2
def baseEnd_594513 : Nat := 90450644250825984845449

theorem tailTrace_594513 : CollatzResearch.WordTrace tailWord_594513 prefixEnd_594513 90450644250825984845449 := by
  unfold tailWord_594513
  simp only [CollatzResearch.WordTrace]
  refine ⟨21683670495188410581916193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14455780330125607054610795 21683670495188410581916193)
  ·
    refine ⟨16262752871391307936437145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21683670495188410581916193 16262752871391307936437145)
    ·
      refine ⟨12197064653543480952327859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16262752871391307936437145 12197064653543480952327859)
      ·
        refine ⟨18295596980315221428491789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12197064653543480952327859 18295596980315221428491789)
        ·
          refine ⟨6860848867618208035684421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18295596980315221428491789 6860848867618208035684421)
          ·
            refine ⟨1286409162678414006690829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6860848867618208035684421 1286409162678414006690829)
            ·
              refine ⟨482403436004405252509061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1286409162678414006690829 482403436004405252509061)
              ·
                refine ⟨90450644250825984845449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482403436004405252509061 90450644250825984845449)
                ·
                  rfl

theorem cell20_594513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_594513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594513 prefixEnd_594513 := by exact prefixLift 594513
  have htrace : WordTrace (prefixWord ++ tailWord_594513) baseStart_594513 baseEnd_594513 := by
    simpa [prefixWord, tailWord_594513, baseEnd_594513] using wordTrace_append hprefix tailTrace_594513
  have hstable : (prefixWord ++ tailWord_594513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594513).length < 2 ^ (prefixWord ++ tailWord_594513).sum := by decide
  have hdescent : baseEnd_594513 < baseStart_594513 := by decide
  rcases family_descends (prefixWord ++ tailWord_594513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594530 : List Nat := [3, 3, 2, 3, 1, 1, 7]
def baseStart_594530 : Nat := 118140960795 + 594530 * 2 ^ 59
def prefixEnd_594530 : Nat := 4983230072969 + 3 ^ 40 * 594530 * 2
def baseEnd_594530 : Nat := 30151076890633494552179

theorem tailTrace_594530 : CollatzResearch.WordTrace tailWord_594530 prefixEnd_594530 30151076890633494552179 := by
  unfold tailWord_594530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421072634031705621321261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14456193690751214990190029 5421072634031705621321261)
  ·
    refine ⟨2032902237761889607995473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5421072634031705621321261 2032902237761889607995473)
    ·
      refine ⟨1524676678321417205996605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2032902237761889607995473 1524676678321417205996605)
      ·
        refine ⟨571753754370531452248727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1524676678321417205996605 571753754370531452248727)
        ·
          refine ⟨857630631555797178373091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571753754370531452248727 857630631555797178373091)
          ·
            refine ⟨1286445947333695767559637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857630631555797178373091 1286445947333695767559637)
            ·
              refine ⟨30151076890633494552179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1286445947333695767559637 30151076890633494552179)
              ·
                rfl

theorem cell20_594530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 7].length) (baseStart_594530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594530 prefixEnd_594530 := by exact prefixLift 594530
  have htrace : WordTrace (prefixWord ++ tailWord_594530) baseStart_594530 baseEnd_594530 := by
    simpa [prefixWord, tailWord_594530, baseEnd_594530] using wordTrace_append hprefix tailTrace_594530
  have hstable : (prefixWord ++ tailWord_594530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594530).length < 2 ^ (prefixWord ++ tailWord_594530).sum := by decide
  have hdescent : baseEnd_594530 < baseStart_594530 := by decide
  rcases family_descends (prefixWord ++ tailWord_594530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594544 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_594544 : Nat := 118140960795 + 594544 * 2 ^ 59
def prefixEnd_594544 : Nat := 4983230072969 + 3 ^ 40 * 594544 * 2
def baseEnd_594544 : Nat := 271366081997179624502887

theorem tailTrace_594544 : CollatzResearch.WordTrace tailWord_594544 prefixEnd_594544 271366081997179624502887 := by
  unfold tailWord_594544
  simp only [CollatzResearch.WordTrace]
  refine ⟨10842400579038051438147343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14456534105384068584196457 10842400579038051438147343)
  ·
    refine ⟨16263600868557077157221015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10842400579038051438147343 16263600868557077157221015)
    ·
      refine ⟨24395401302835615735831523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16263600868557077157221015 24395401302835615735831523)
      ·
        refine ⟨36593101954253423603747285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24395401302835615735831523 36593101954253423603747285)
        ·
          refine ⟨857650827052814615712827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36593101954253423603747285 857650827052814615712827)
          ·
            refine ⟨1286476240579221923569241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857650827052814615712827 1286476240579221923569241)
            ·
              refine ⟨964857180434416442676931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286476240579221923569241 964857180434416442676931)
              ·
                refine ⟨1447285770651624664015397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964857180434416442676931 1447285770651624664015397)
                ·
                  refine ⟨271366081997179624502887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1447285770651624664015397 271366081997179624502887)
                  ·
                    rfl

theorem cell20_594544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_594544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594544 prefixEnd_594544 := by exact prefixLift 594544
  have htrace : WordTrace (prefixWord ++ tailWord_594544) baseStart_594544 baseEnd_594544 := by
    simpa [prefixWord, tailWord_594544, baseEnd_594544] using wordTrace_append hprefix tailTrace_594544
  have hstable : (prefixWord ++ tailWord_594544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594544).length < 2 ^ (prefixWord ++ tailWord_594544).sum := by decide
  have hdescent : baseEnd_594544 < baseStart_594544 := by decide
  rcases family_descends (prefixWord ++ tailWord_594544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594565 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_594565 : Nat := 118140960795 + 594565 * 2 ^ 59
def prefixEnd_594565 : Nat := 4983230072969 + 3 ^ 40 * 594565 * 2
def baseEnd_594565 : Nat := 271375666969396884802801

theorem tailTrace_594565 : CollatzResearch.WordTrace tailWord_594565 prefixEnd_594565 271375666969396884802801 := by
  unfold tailWord_594565
  simp only [CollatzResearch.WordTrace]
  refine ⟨21685567091000023462809149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14457044727333348975206099 21685567091000023462809149)
  ·
    refine ⟨8132087659125008798553431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21685567091000023462809149 8132087659125008798553431)
    ·
      refine ⟨12198131488687513197830147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8132087659125008798553431 12198131488687513197830147)
      ·
        refine ⟨18297197233031269796745221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12198131488687513197830147 18297197233031269796745221)
        ·
          refine ⟨3430724481193363086889729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18297197233031269796745221 3430724481193363086889729)
          ·
            refine ⟨2573043360895022315167297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3430724481193363086889729 2573043360895022315167297)
            ·
              refine ⟨1929782520671266736375473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573043360895022315167297 1929782520671266736375473)
              ·
                refine ⟨1447336890503450052281605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929782520671266736375473 1447336890503450052281605)
                ·
                  refine ⟨271375666969396884802801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1447336890503450052281605 271375666969396884802801)
                  ·
                    rfl

theorem cell20_594565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_594565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594565 prefixEnd_594565 := by exact prefixLift 594565
  have htrace : WordTrace (prefixWord ++ tailWord_594565) baseStart_594565 baseEnd_594565 := by
    simpa [prefixWord, tailWord_594565, baseEnd_594565] using wordTrace_append hprefix tailTrace_594565
  have hstable : (prefixWord ++ tailWord_594565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594565).length < 2 ^ (prefixWord ++ tailWord_594565).sum := by decide
  have hdescent : baseEnd_594565 < baseStart_594565 := by decide
  rcases family_descends (prefixWord ++ tailWord_594565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594578 : List Nat := [3, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_594578 : Nat := 118140960795 + 594578 * 2 ^ 59
def prefixEnd_594578 : Nat := 4983230072969 + 3 ^ 40 * 594578 * 2
def baseEnd_594578 : Nat := 271381600523626617369415

theorem tailTrace_594578 : CollatzResearch.WordTrace tailWord_594578 prefixEnd_594578 271381600523626617369415 := by
  unfold tailWord_594578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421510309988231670758097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14457360826635284455354925 5421510309988231670758097)
  ·
    refine ⟨4066132732491173753068573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5421510309988231670758097 4066132732491173753068573)
    ·
      refine ⟨1524799774684190157400715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4066132732491173753068573 1524799774684190157400715)
      ·
        refine ⟨2287199662026285236101073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524799774684190157400715 2287199662026285236101073)
        ·
          refine ⟨1715399746519713927075805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2287199662026285236101073 1715399746519713927075805)
          ·
            refine ⟨643274904944892722653427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1715399746519713927075805 643274904944892722653427)
            ·
              refine ⟨964912357417339083980141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643274904944892722653427 964912357417339083980141)
              ·
                refine ⟨361842134031502156492553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964912357417339083980141 361842134031502156492553)
                ·
                  refine ⟨271381600523626617369415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361842134031502156492553 271381600523626617369415)
                  ·
                    rfl

theorem cell20_594578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_594578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594578 prefixEnd_594578 := by exact prefixLift 594578
  have htrace : WordTrace (prefixWord ++ tailWord_594578) baseStart_594578 baseEnd_594578 := by
    simpa [prefixWord, tailWord_594578, baseEnd_594578] using wordTrace_append hprefix tailTrace_594578
  have hstable : (prefixWord ++ tailWord_594578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594578).length < 2 ^ (prefixWord ++ tailWord_594578).sum := by decide
  have hdescent : baseEnd_594578 < baseStart_594578 := by decide
  rcases family_descends (prefixWord ++ tailWord_594578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594596 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_594596 : Nat := 118140960795 + 594596 * 2 ^ 59
def prefixEnd_594596 : Nat := 4983230072969 + 3 ^ 40 * 594596 * 2
def baseEnd_594596 : Nat := 271389816214098554769341

theorem tailTrace_594596 : CollatzResearch.WordTrace tailWord_594596 prefixEnd_594596 271389816214098554769341 := by
  unfold tailWord_594596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10843348876943857878593821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14457798502591810504791761 10843348876943857878593821)
  ·
    refine ⟨4066255828853946704472683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10843348876943857878593821 4066255828853946704472683)
    ·
      refine ⟨6099383743280920056709025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4066255828853946704472683 6099383743280920056709025)
      ·
        refine ⟨4574537807460690042531769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6099383743280920056709025 4574537807460690042531769)
        ·
          refine ⟨3430903355595517531898827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4574537807460690042531769 3430903355595517531898827)
          ·
            refine ⟨5146355033393276297848241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3430903355595517531898827 5146355033393276297848241)
            ·
              refine ⟨3859766275044957223386181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146355033393276297848241 3859766275044957223386181)
              ·
                refine ⟨723706176570929479384909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3859766275044957223386181 723706176570929479384909)
                ·
                  refine ⟨271389816214098554769341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723706176570929479384909 271389816214098554769341)
                  ·
                    rfl

theorem cell20_594596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_594596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594596 prefixEnd_594596 := by exact prefixLift 594596
  have htrace : WordTrace (prefixWord ++ tailWord_594596) baseStart_594596 baseEnd_594596 := by
    simpa [prefixWord, tailWord_594596, baseEnd_594596] using wordTrace_append hprefix tailTrace_594596
  have hstable : (prefixWord ++ tailWord_594596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594596).length < 2 ^ (prefixWord ++ tailWord_594596).sum := by decide
  have hdescent : baseEnd_594596 < baseStart_594596 := by decide
  rcases family_descends (prefixWord ++ tailWord_594596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594606 : List Nat := [4, 1, 4, 1, 1, 2, 2, 5]
def baseStart_594606 : Nat := 118140960795 + 594606 * 2 ^ 59
def prefixEnd_594606 : Nat := 4983230072969 + 3 ^ 40 * 594606 * 2
def baseEnd_594606 : Nat := 90464793495527654811989

theorem tailTrace_594606 : CollatzResearch.WordTrace tailWord_594606 prefixEnd_594606 90464793495527654811989 := by
  unfold tailWord_594606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710882810481435933131459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14458041655900991643367781 2710882810481435933131459)
  ·
    refine ⟨4066324215722153899697189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2710882810481435933131459 4066324215722153899697189)
    ·
      refine ⟨762435790447903856193223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4066324215722153899697189 762435790447903856193223)
      ·
        refine ⟨1143653685671855784289835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762435790447903856193223 1143653685671855784289835)
        ·
          refine ⟨1715480528507783676434753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143653685671855784289835 1715480528507783676434753)
          ·
            refine ⟨1286610396380837757326065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1715480528507783676434753 1286610396380837757326065)
            ·
              refine ⟨964957797285628317994549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286610396380837757326065 964957797285628317994549)
              ·
                refine ⟨90464793495527654811989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 964957797285628317994549 90464793495527654811989)
                ·
                  rfl

theorem cell20_594606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_594606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594606 prefixEnd_594606 := by exact prefixLift 594606
  have htrace : WordTrace (prefixWord ++ tailWord_594606) baseStart_594606 baseEnd_594606 := by
    simpa [prefixWord, tailWord_594606, baseEnd_594606] using wordTrace_append hprefix tailTrace_594606
  have hstable : (prefixWord ++ tailWord_594606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594606).length < 2 ^ (prefixWord ++ tailWord_594606).sum := by decide
  have hdescent : baseEnd_594606 < baseStart_594606 := by decide
  rcases family_descends (prefixWord ++ tailWord_594606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594609 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 3]
def baseStart_594609 : Nat := 118140960795 + 594609 * 2 ^ 59
def prefixEnd_594609 : Nat := 4983230072969 + 3 ^ 40 * 594609 * 2
def baseEnd_594609 : Nat := 271395749768328287335955

theorem tailTrace_594609 : CollatzResearch.WordTrace tailWord_594609 prefixEnd_594609 271395749768328287335955 := by
  unfold tailWord_594609
  simp only [CollatzResearch.WordTrace]
  refine ⟨21687171902840618977410881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14458114601893745984940587 21687171902840618977410881)
  ·
    refine ⟨16265378927130464233058161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21687171902840618977410881 16265378927130464233058161)
    ·
      refine ⟨12199034195347848174793621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16265378927130464233058161 12199034195347848174793621)
      ·
        refine ⟨571829727906930383193451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12199034195347848174793621 571829727906930383193451)
        ·
          refine ⟨857744591860395574790177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571829727906930383193451 857744591860395574790177)
          ·
            refine ⟨643308443895296681092633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857744591860395574790177 643308443895296681092633)
            ·
              refine ⟨482481332921472510819475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643308443895296681092633 482481332921472510819475)
              ·
                refine ⟨723721999382208766229213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482481332921472510819475 723721999382208766229213)
                ·
                  refine ⟨271395749768328287335955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723721999382208766229213 271395749768328287335955)
                  ·
                    rfl

theorem cell20_594609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_594609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594609 prefixEnd_594609 := by exact prefixLift 594609
  have htrace : WordTrace (prefixWord ++ tailWord_594609) baseStart_594609 baseEnd_594609 := by
    simpa [prefixWord, tailWord_594609, baseEnd_594609] using wordTrace_append hprefix tailTrace_594609
  have hstable : (prefixWord ++ tailWord_594609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594609).length < 2 ^ (prefixWord ++ tailWord_594609).sum := by decide
  have hdescent : baseEnd_594609 < baseStart_594609 := by decide
  rcases family_descends (prefixWord ++ tailWord_594609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594613 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 3]
def baseStart_594613 : Nat := 118140960795 + 594613 * 2 ^ 59
def prefixEnd_594613 : Nat := 4983230072969 + 3 ^ 40 * 594613 * 2
def baseEnd_594613 : Nat := 271397575477322051202605

theorem tailTrace_594613 : CollatzResearch.WordTrace tailWord_594613 prefixEnd_594613 271397575477322051202605 := by
  unfold tailWord_594613
  simp only [CollatzResearch.WordTrace]
  refine ⟨21687317794826127660556493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14458211863217418440370995 21687317794826127660556493)
  ·
    refine ⟨8132744173059797872708685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21687317794826127660556493 8132744173059797872708685)
    ·
      refine ⟨3049779064897424202265757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8132744173059797872708685 3049779064897424202265757)
      ·
        refine ⟨1143667149336534075849659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3049779064897424202265757 1143667149336534075849659)
        ·
          refine ⟨1715500724004801113774489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143667149336534075849659 1715500724004801113774489)
          ·
            refine ⟨1286625543003600835330867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1715500724004801113774489 1286625543003600835330867)
            ·
              refine ⟨1929938314505401252996301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286625543003600835330867 1929938314505401252996301)
              ·
                refine ⟨723726867939525469873613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929938314505401252996301 723726867939525469873613)
                ·
                  refine ⟨271397575477322051202605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723726867939525469873613 271397575477322051202605)
                  ·
                    rfl

theorem cell20_594613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_594613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594613 prefixEnd_594613 := by exact prefixLift 594613
  have htrace : WordTrace (prefixWord ++ tailWord_594613) baseStart_594613 baseEnd_594613 := by
    simpa [prefixWord, tailWord_594613, baseEnd_594613] using wordTrace_append hprefix tailTrace_594613
  have hstable : (prefixWord ++ tailWord_594613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594613).length < 2 ^ (prefixWord ++ tailWord_594613).sum := by decide
  have hdescent : baseEnd_594613 < baseStart_594613 := by decide
  rcases family_descends (prefixWord ++ tailWord_594613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594696 : List Nat := [2, 1, 3, 2, 2, 2, 1, 5, 2]
def baseStart_594696 : Nat := 118140960795 + 594696 * 2 ^ 59
def prefixEnd_594696 : Nat := 4983230072969 + 3 ^ 40 * 594696 * 2
def baseEnd_594696 : Nat := 271435458938942651435599

theorem tailTrace_594696 : CollatzResearch.WordTrace tailWord_594696 prefixEnd_594696 271435458938942651435599 := by
  unfold tailWord_594696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845172526762716417913971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14460230035683621890551961 10845172526762716417913971)
  ·
    refine ⟨16267758790144074626870957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10845172526762716417913971 16267758790144074626870957)
    ·
      refine ⟨6100409546304027985076609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16267758790144074626870957 6100409546304027985076609)
      ·
        refine ⟨4575307159728020988807457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6100409546304027985076609 4575307159728020988807457)
        ·
          refine ⟨3431480369796015741605593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4575307159728020988807457 3431480369796015741605593)
          ·
            refine ⟨2573610277347011806204195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3431480369796015741605593 2573610277347011806204195)
            ·
              refine ⟨3860415416020517709306293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2573610277347011806204195 3860415416020517709306293)
              ·
                refine ⟨361913945251923535247465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3860415416020517709306293 361913945251923535247465)
                ·
                  refine ⟨271435458938942651435599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361913945251923535247465 271435458938942651435599)
                  ·
                    rfl

theorem cell20_594696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_594696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594696 prefixEnd_594696 := by exact prefixLift 594696
  have htrace : WordTrace (prefixWord ++ tailWord_594696) baseStart_594696 baseEnd_594696 := by
    simpa [prefixWord, tailWord_594696, baseEnd_594696] using wordTrace_append hprefix tailTrace_594696
  have hstable : (prefixWord ++ tailWord_594696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594696).length < 2 ^ (prefixWord ++ tailWord_594696).sum := by decide
  have hdescent : baseEnd_594696 < baseStart_594696 := by decide
  rcases family_descends (prefixWord ++ tailWord_594696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594700 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_594700 : Nat := 118140960795 + 594700 * 2 ^ 59
def prefixEnd_594700 : Nat := 4983230072969 + 3 ^ 40 * 594700 * 2
def baseEnd_594700 : Nat := 271437284647936415302249

theorem tailTrace_594700 : CollatzResearch.WordTrace tailWord_594700 prefixEnd_594700 271437284647936415302249 := by
  unfold tailWord_594700
  simp only [CollatzResearch.WordTrace]
  refine ⟨10845245472755470759486777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14460327297007294345982369 10845245472755470759486777)
  ·
    refine ⟨8133934104566603069615083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10845245472755470759486777 8133934104566603069615083)
    ·
      refine ⟨12200901156849904604422625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8133934104566603069615083 12200901156849904604422625)
      ·
        refine ⟨9150675867637428453316969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12200901156849904604422625 9150675867637428453316969)
        ·
          refine ⟨6863006900728071339987727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9150675867637428453316969 6863006900728071339987727)
          ·
            refine ⟨10294510351092107009981591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6863006900728071339987727 10294510351092107009981591)
            ·
              refine ⟨15441765526638160514972387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10294510351092107009981591 15441765526638160514972387)
              ·
                refine ⟨23162648289957240772458581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15441765526638160514972387 23162648289957240772458581)
                ·
                  refine ⟨271437284647936415302249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23162648289957240772458581 271437284647936415302249)
                  ·
                    rfl

theorem cell20_594700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_594700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594700 prefixEnd_594700 := by exact prefixLift 594700
  have htrace : WordTrace (prefixWord ++ tailWord_594700) baseStart_594700 baseEnd_594700 := by
    simpa [prefixWord, tailWord_594700, baseEnd_594700] using wordTrace_append hprefix tailTrace_594700
  have hstable : (prefixWord ++ tailWord_594700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594700).length < 2 ^ (prefixWord ++ tailWord_594700).sum := by decide
  have hdescent : baseEnd_594700 < baseStart_594700 := by decide
  rcases family_descends (prefixWord ++ tailWord_594700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594707 : List Nat := [1, 1, 1, 2, 1, 3, 11]
def baseStart_594707 : Nat := 118140960795 + 594707 * 2 ^ 59
def prefixEnd_594707 : Nat := 4983230072969 + 3 ^ 40 * 594707 * 2
def baseEnd_594707 : Nat := 30160053293186166896543

theorem tailTrace_594707 : CollatzResearch.WordTrace tailWord_594707 prefixEnd_594707 30160053293186166896543 := by
  unfold tailWord_594707
  simp only [CollatzResearch.WordTrace]
  refine ⟨21690746256485581714478375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14460497504323721142985583 21690746256485581714478375)
  ·
    refine ⟨32536119384728372571717563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21690746256485581714478375 32536119384728372571717563)
    ·
      refine ⟨48804179077092558857576345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32536119384728372571717563 48804179077092558857576345)
      ·
        refine ⟨36603134307819419143182259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48804179077092558857576345 36603134307819419143182259)
        ·
          refine ⟨54904701461729128714773389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36603134307819419143182259 54904701461729128714773389)
          ·
            refine ⟨20589263048148423268040021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54904701461729128714773389 20589263048148423268040021)
            ·
              refine ⟨30160053293186166896543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20589263048148423268040021 30160053293186166896543)
              ·
                rfl

theorem cell20_594707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_594707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594707 prefixEnd_594707 := by exact prefixLift 594707
  have htrace : WordTrace (prefixWord ++ tailWord_594707) baseStart_594707 baseEnd_594707 := by
    simpa [prefixWord, tailWord_594707, baseEnd_594707] using wordTrace_append hprefix tailTrace_594707
  have hstable : (prefixWord ++ tailWord_594707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594707).length < 2 ^ (prefixWord ++ tailWord_594707).sum := by decide
  have hdescent : baseEnd_594707 < baseStart_594707 := by decide
  rcases family_descends (prefixWord ++ tailWord_594707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594734 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_594734 : Nat := 118140960795 + 594734 * 2 ^ 59
def prefixEnd_594734 : Nat := 4983230072969 + 3 ^ 40 * 594734 * 2
def baseEnd_594734 : Nat := 271452803174383408168777

theorem tailTrace_594734 : CollatzResearch.WordTrace tailWord_594734 prefixEnd_594734 271452803174383408168777 := by
  unfold tailWord_594734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711466378423470665713907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14461154018258510217140837 2711466378423470665713907)
  ·
    refine ⟨4067199567635205998570861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2711466378423470665713907 4067199567635205998570861)
    ·
      refine ⟨1525199837863202249464073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4067199567635205998570861 1525199837863202249464073)
      ·
        refine ⟨1143899878397401687098055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1525199837863202249464073 1143899878397401687098055)
        ·
          refine ⟨1715849817596102530647083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143899878397401687098055 1715849817596102530647083)
          ·
            refine ⟨2573774726394153795970625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715849817596102530647083 2573774726394153795970625)
            ·
              refine ⟨1930331044795615346977969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573774726394153795970625 1930331044795615346977969)
              ·
                refine ⟨1447748283596711510233477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1930331044795615346977969 1447748283596711510233477)
                ·
                  refine ⟨271452803174383408168777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1447748283596711510233477 271452803174383408168777)
                  ·
                    rfl

theorem cell20_594734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_594734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594734 prefixEnd_594734 := by exact prefixLift 594734
  have htrace : WordTrace (prefixWord ++ tailWord_594734) baseStart_594734 baseEnd_594734 := by
    simpa [prefixWord, tailWord_594734, baseEnd_594734] using wordTrace_append hprefix tailTrace_594734
  have hstable : (prefixWord ++ tailWord_594734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594734).length < 2 ^ (prefixWord ++ tailWord_594734).sum := by decide
  have hdescent : baseEnd_594734 < baseStart_594734 := by decide
  rcases family_descends (prefixWord ++ tailWord_594734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594741 : List Nat := [1, 3, 3, 1, 3, 1, 4, 4]
def baseStart_594741 : Nat := 118140960795 + 594741 * 2 ^ 59
def prefixEnd_594741 : Nat := 4983230072969 + 3 ^ 40 * 594741 * 2
def baseEnd_594741 : Nat := 90485332721707498311805

theorem tailTrace_594741 : CollatzResearch.WordTrace tailWord_594741 prefixEnd_594741 90485332721707498311805 := by
  unfold tailWord_594741
  simp only [CollatzResearch.WordTrace]
  refine ⟨21691986338362405521216077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14461324225574937014144051 21691986338362405521216077)
  ·
    refine ⟨8134494876885902070456029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21691986338362405521216077 8134494876885902070456029)
    ·
      refine ⟨3050435578832213276421011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8134494876885902070456029 3050435578832213276421011)
      ·
        refine ⟨4575653368248319914631517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050435578832213276421011 4575653368248319914631517)
        ·
          refine ⟨1715870013093119967986819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4575653368248319914631517 1715870013093119967986819)
          ·
            refine ⟨2573805019639679951980229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715870013093119967986819 2573805019639679951980229)
            ·
              refine ⟨482588441182439990996293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2573805019639679951980229 482588441182439990996293)
              ·
                refine ⟨90485332721707498311805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482588441182439990996293 90485332721707498311805)
                ·
                  rfl

theorem cell20_594741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_594741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594741 prefixEnd_594741 := by exact prefixLift 594741
  have htrace : WordTrace (prefixWord ++ tailWord_594741) baseStart_594741 baseEnd_594741 := by
    simpa [prefixWord, tailWord_594741, baseEnd_594741] using wordTrace_append hprefix tailTrace_594741
  have hstable : (prefixWord ++ tailWord_594741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594741).length < 2 ^ (prefixWord ++ tailWord_594741).sum := by decide
  have hdescent : baseEnd_594741 < baseStart_594741 := by decide
  rcases family_descends (prefixWord ++ tailWord_594741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594751 : List Nat := [1, 1, 2, 2, 5, 3, 1, 3, 2]
def baseStart_594751 : Nat := 118140960795 + 594751 * 2 ^ 59
def prefixEnd_594751 : Nat := 4983230072969 + 3 ^ 40 * 594751 * 2
def baseEnd_594751 : Nat := 271460562437606904602041

theorem tailTrace_594751 : CollatzResearch.WordTrace tailWord_594751 prefixEnd_594751 271460562437606904602041 := by
  unfold tailWord_594751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21692351068326177229080107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14461567378884118152720071 21692351068326177229080107)
  ·
    refine ⟨32538526602489265843620161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21692351068326177229080107 32538526602489265843620161)
    ·
      refine ⟨24403894951866949382715121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32538526602489265843620161 24403894951866949382715121)
      ·
        refine ⟨18302921213900212037036341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24403894951866949382715121 18302921213900212037036341)
        ·
          refine ⟨1715898863803144878472157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18302921213900212037036341 1715898863803144878472157)
          ·
            refine ⟨643462073926179329427059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1715898863803144878472157 643462073926179329427059)
            ·
              refine ⟨965193110889268994140589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643462073926179329427059 965193110889268994140589)
              ·
                refine ⟨361947416583475872802721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 965193110889268994140589 361947416583475872802721)
                ·
                  refine ⟨271460562437606904602041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361947416583475872802721 271460562437606904602041)
                  ·
                    rfl

theorem cell20_594751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 2].length) (baseStart_594751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594751 prefixEnd_594751 := by exact prefixLift 594751
  have htrace : WordTrace (prefixWord ++ tailWord_594751) baseStart_594751 baseEnd_594751 := by
    simpa [prefixWord, tailWord_594751, baseEnd_594751] using wordTrace_append hprefix tailTrace_594751
  have hstable : (prefixWord ++ tailWord_594751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594751).length < 2 ^ (prefixWord ++ tailWord_594751).sum := by decide
  have hdescent : baseEnd_594751 < baseStart_594751 := by decide
  rcases family_descends (prefixWord ++ tailWord_594751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594821 : List Nat := [1, 3, 1, 1, 3, 11]
def baseStart_594821 : Nat := 118140960795 + 594821 * 2 ^ 59
def prefixEnd_594821 : Nat := 4983230072969 + 3 ^ 40 * 594821 * 2
def baseEnd_594821 : Nat := 10055278234999917491423

theorem tailTrace_594821 : CollatzResearch.WordTrace tailWord_594821 prefixEnd_594821 10055278234999917491423 := by
  unfold tailWord_594821
  simp only [CollatzResearch.WordTrace]
  refine ⟨21694904178072579184128317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14463269452048386122752211 21694904178072579184128317)
  ·
    refine ⟨8135589066777217194048119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21694904178072579184128317 8135589066777217194048119)
    ·
      refine ⟨12203383600165825791072179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8135589066777217194048119 12203383600165825791072179)
      ·
        refine ⟨18305075400248738686608269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12203383600165825791072179 18305075400248738686608269)
        ·
          refine ⟨6864403275093277007478101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18305075400248738686608269 6864403275093277007478101)
          ·
            refine ⟨10055278234999917491423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6864403275093277007478101 10055278234999917491423)
            ·
              rfl

theorem cell20_594821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 11].length) (baseStart_594821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594821 prefixEnd_594821 := by exact prefixLift 594821
  have htrace : WordTrace (prefixWord ++ tailWord_594821) baseStart_594821 baseEnd_594821 := by
    simpa [prefixWord, tailWord_594821, baseEnd_594821] using wordTrace_append hprefix tailTrace_594821
  have hstable : (prefixWord ++ tailWord_594821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594821).length < 2 ^ (prefixWord ++ tailWord_594821).sum := by decide
  have hdescent : baseEnd_594821 < baseStart_594821 := by decide
  rcases family_descends (prefixWord ++ tailWord_594821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594824 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_594824 : Nat := 118140960795 + 594824 * 2 ^ 59
def prefixEnd_594824 : Nat := 4983230072969 + 3 ^ 40 * 594824 * 2
def baseEnd_594824 : Nat := 271493881626743095168409

theorem tailTrace_594824 : CollatzResearch.WordTrace tailWord_594824 prefixEnd_594824 271493881626743095168409 := by
  unfold tailWord_594824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10847506798530855348243763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14463342398041140464325017 10847506798530855348243763)
  ·
    refine ⟨16271260197796283022365645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10847506798530855348243763 16271260197796283022365645)
    ·
      refine ⟨6101722574173606133387117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16271260197796283022365645 6101722574173606133387117)
      ·
        refine ⟨2288145965315102300020169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6101722574173606133387117 2288145965315102300020169)
        ·
          refine ⟨1716109473986326725015127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2288145965315102300020169 1716109473986326725015127)
          ·
            refine ⟨2574164210979490087522691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716109473986326725015127 2574164210979490087522691)
            ·
              refine ⟨3861246316469235131284037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2574164210979490087522691 3861246316469235131284037)
              ·
                refine ⟨723983684337981587115757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3861246316469235131284037 723983684337981587115757)
                ·
                  refine ⟨271493881626743095168409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723983684337981587115757 271493881626743095168409)
                  ·
                    rfl

theorem cell20_594824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_594824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594824 prefixEnd_594824 := by exact prefixLift 594824
  have htrace : WordTrace (prefixWord ++ tailWord_594824) baseStart_594824 baseEnd_594824 := by
    simpa [prefixWord, tailWord_594824, baseEnd_594824] using wordTrace_append hprefix tailTrace_594824
  have hstable : (prefixWord ++ tailWord_594824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594824).length < 2 ^ (prefixWord ++ tailWord_594824).sum := by decide
  have hdescent : baseEnd_594824 < baseStart_594824 := by decide
  rcases family_descends (prefixWord ++ tailWord_594824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594834 : List Nat := [3, 2, 3, 2, 2, 2, 1, 5]
def baseStart_594834 : Nat := 118140960795 + 594834 * 2 ^ 59
def prefixEnd_594834 : Nat := 4983230072969 + 3 ^ 40 * 594834 * 2
def baseEnd_594834 : Nat := 90499481966409168278345

theorem tailTrace_594834 : CollatzResearch.WordTrace tailWord_594834 prefixEnd_594834 90499481966409168278345 := by
  unfold tailWord_594834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5423844581756370601087889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14463585551350321602901037 5423844581756370601087889)
  ·
    refine ⟨4067883436317277950815917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5423844581756370601087889 4067883436317277950815917)
    ·
      refine ⟨1525456288618979231555969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4067883436317277950815917 1525456288618979231555969)
      ·
        refine ⟨1144092216464234423666977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1525456288618979231555969 1144092216464234423666977)
        ·
          refine ⟨858069162348175817750233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1144092216464234423666977 858069162348175817750233)
          ·
            refine ⟨643551871761131863312675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858069162348175817750233 643551871761131863312675)
            ·
              refine ⟨965327807641697794969013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643551871761131863312675 965327807641697794969013)
              ·
                refine ⟨90499481966409168278345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 965327807641697794969013 90499481966409168278345)
                ·
                  rfl

theorem cell20_594834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_594834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594834 prefixEnd_594834 := by exact prefixLift 594834
  have htrace : WordTrace (prefixWord ++ tailWord_594834) baseStart_594834 baseEnd_594834 := by
    simpa [prefixWord, tailWord_594834, baseEnd_594834] using wordTrace_append hprefix tailTrace_594834
  have hstable : (prefixWord ++ tailWord_594834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594834).length < 2 ^ (prefixWord ++ tailWord_594834).sum := by decide
  have hdescent : baseEnd_594834 < baseStart_594834 := by decide
  rcases family_descends (prefixWord ++ tailWord_594834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594865 : List Nat := [1, 2, 2, 4, 3, 1, 2, 3, 2]
def baseStart_594865 : Nat := 118140960795 + 594865 * 2 ^ 59
def prefixEnd_594865 : Nat := 4983230072969 + 3 ^ 40 * 594865 * 2
def baseEnd_594865 : Nat := 271512595143929174801575

theorem tailTrace_594865 : CollatzResearch.WordTrace tailWord_594865 prefixEnd_594865 271512595143929174801575 := by
  unfold tailWord_594865
  simp only [CollatzResearch.WordTrace]
  refine ⟨21696508989913174698730049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14464339326608783132486699 21696508989913174698730049)
  ·
    refine ⟨16272381742434881024047537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21696508989913174698730049 16272381742434881024047537)
    ·
      refine ⟨12204286306826160768035653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16272381742434881024047537 12204286306826160768035653)
      ·
        refine ⟨2288303682529905144006685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12204286306826160768035653 2288303682529905144006685)
        ·
          refine ⟨858113880948714429002507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2288303682529905144006685 858113880948714429002507)
          ·
            refine ⟨1287170821423071643503761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858113880948714429002507 1287170821423071643503761)
            ·
              refine ⟨965378116067303732627821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287170821423071643503761 965378116067303732627821)
              ·
                refine ⟨362016793525238899735433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 965378116067303732627821 362016793525238899735433)
                ·
                  refine ⟨271512595143929174801575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362016793525238899735433 271512595143929174801575)
                  ·
                    rfl

theorem cell20_594865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_594865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594865 prefixEnd_594865 := by exact prefixLift 594865
  have htrace : WordTrace (prefixWord ++ tailWord_594865) baseStart_594865 baseEnd_594865 := by
    simpa [prefixWord, tailWord_594865, baseEnd_594865] using wordTrace_append hprefix tailTrace_594865
  have hstable : (prefixWord ++ tailWord_594865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594865).length < 2 ^ (prefixWord ++ tailWord_594865).sum := by decide
  have hdescent : baseEnd_594865 < baseStart_594865 := by decide
  rcases family_descends (prefixWord ++ tailWord_594865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594897 : List Nat := [1, 2, 2, 1, 2, 1, 4, 7]
def baseStart_594897 : Nat := 118140960795 + 594897 * 2 ^ 59
def prefixEnd_594897 : Nat := 4983230072969 + 3 ^ 40 * 594897 * 2
def baseEnd_594897 : Nat := 90509066938626428578259

theorem tailTrace_594897 : CollatzResearch.WordTrace tailWord_594897 prefixEnd_594897 90509066938626428578259 := by
  unfold tailWord_594897
  simp only [CollatzResearch.WordTrace]
  refine ⟨21697676125797244163894945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14465117417198162775929963 21697676125797244163894945)
  ·
    refine ⟨16273257094347933122921209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21697676125797244163894945 16273257094347933122921209)
    ·
      refine ⟨12204942820760949842190907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16273257094347933122921209 12204942820760949842190907)
      ·
        refine ⟨18307414231141424763286361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12204942820760949842190907 18307414231141424763286361)
        ·
          refine ⟨13730560673356068572464771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18307414231141424763286361 13730560673356068572464771)
          ·
            refine ⟨20595841010034102858697157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13730560673356068572464771 20595841010034102858697157)
            ·
              refine ⟨3861720189381394286005717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20595841010034102858697157 3861720189381394286005717)
              ·
                refine ⟨90509066938626428578259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3861720189381394286005717 90509066938626428578259)
                ·
                  rfl

theorem cell20_594897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_594897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594897 prefixEnd_594897 := by exact prefixLift 594897
  have htrace : WordTrace (prefixWord ++ tailWord_594897) baseStart_594897 baseEnd_594897 := by
    simpa [prefixWord, tailWord_594897, baseEnd_594897] using wordTrace_append hprefix tailTrace_594897
  have hstable : (prefixWord ++ tailWord_594897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594897).length < 2 ^ (prefixWord ++ tailWord_594897).sum := by decide
  have hdescent : baseEnd_594897 < baseStart_594897 := by decide
  rcases family_descends (prefixWord ++ tailWord_594897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594945 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_594945 : Nat := 118140960795 + 594945 * 2 ^ 59
def prefixEnd_594945 : Nat := 4983230072969 + 3 ^ 40 * 594945 * 2
def baseEnd_594945 : Nat := 271549109323804452134581

theorem tailTrace_594945 : CollatzResearch.WordTrace tailWord_594945 prefixEnd_594945 271549109323804452134581 := by
  unfold tailWord_594945
  simp only [CollatzResearch.WordTrace]
  refine ⟨21699426829623348361642289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14466284553082232241094859 21699426829623348361642289)
  ·
    refine ⟨16274570122217511271231717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21699426829623348361642289 16274570122217511271231717)
    ·
      refine ⟨3051481897915783363355947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16274570122217511271231717 3051481897915783363355947)
      ·
        refine ⟨4577222846873675045033921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3051481897915783363355947 4577222846873675045033921)
        ·
          refine ⟨3432917135155256283775441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4577222846873675045033921 3432917135155256283775441)
          ·
            refine ⟨2574687851366442212831581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3432917135155256283775441 2574687851366442212831581)
            ·
              refine ⟨965507944262415829811843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2574687851366442212831581 965507944262415829811843)
              ·
                refine ⟨1448261916393623744717765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965507944262415829811843 1448261916393623744717765)
                ·
                  refine ⟨271549109323804452134581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1448261916393623744717765 271549109323804452134581)
                  ·
                    rfl

theorem cell20_594945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_594945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594945 prefixEnd_594945 := by exact prefixLift 594945
  have htrace : WordTrace (prefixWord ++ tailWord_594945) baseStart_594945 baseEnd_594945 := by
    simpa [prefixWord, tailWord_594945, baseEnd_594945] using wordTrace_append hprefix tailTrace_594945
  have hstable : (prefixWord ++ tailWord_594945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594945).length < 2 ^ (prefixWord ++ tailWord_594945).sum := by decide
  have hdescent : baseEnd_594945 < baseStart_594945 := by decide
  rcases family_descends (prefixWord ++ tailWord_594945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594952 : List Nat := [2, 1, 3, 2, 1, 4, 2, 5]
def baseStart_594952 : Nat := 118140960795 + 594952 * 2 ^ 59
def prefixEnd_594952 : Nat := 4983230072969 + 3 ^ 40 * 594952 * 2
def baseEnd_594952 : Nat := 90517434771514512967073

theorem tailTrace_594952 : CollatzResearch.WordTrace tailWord_594952 prefixEnd_594952 90517434771514512967073 := by
  unfold tailWord_594952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10849841070298994278573555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14466454760398659038098073 10849841070298994278573555)
  ·
    refine ⟨16274761605448491417860333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10849841070298994278573555 16274761605448491417860333)
    ·
      refine ⟨6103035602043184281697625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16274761605448491417860333 6103035602043184281697625)
      ·
        refine ⟨4577276701532388211273219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6103035602043184281697625 4577276701532388211273219)
        ·
          refine ⟨6865915052298582316909829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577276701532388211273219 6865915052298582316909829)
          ·
            refine ⟨1287359072305984184420593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6865915052298582316909829 1287359072305984184420593)
            ·
              refine ⟨965519304229488138315445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287359072305984184420593 965519304229488138315445)
              ·
                refine ⟨90517434771514512967073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 965519304229488138315445 90517434771514512967073)
                ·
                  rfl

theorem cell20_594952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_594952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594952 prefixEnd_594952 := by exact prefixLift 594952
  have htrace : WordTrace (prefixWord ++ tailWord_594952) baseStart_594952 baseEnd_594952 := by
    simpa [prefixWord, tailWord_594952, baseEnd_594952] using wordTrace_append hprefix tailTrace_594952
  have hstable : (prefixWord ++ tailWord_594952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594952).length < 2 ^ (prefixWord ++ tailWord_594952).sum := by decide
  have hdescent : baseEnd_594952 < baseStart_594952 := by decide
  rcases family_descends (prefixWord ++ tailWord_594952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594955 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 3]
def baseStart_594955 : Nat := 118140960795 + 594955 * 2 ^ 59
def prefixEnd_594955 : Nat := 4983230072969 + 3 ^ 40 * 594955 * 2
def baseEnd_594955 : Nat := 271553673596288861801207

theorem tailTrace_594955 : CollatzResearch.WordTrace tailWord_594955 prefixEnd_594955 271553673596288861801207 := by
  unfold tailWord_594955
  simp only [CollatzResearch.WordTrace]
  refine ⟨21699791559587120069506319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14466527706391413379670879 21699791559587120069506319)
  ·
    refine ⟨32549687339380680104259479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21699791559587120069506319 32549687339380680104259479)
    ·
      refine ⟨48824531009071020156389219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32549687339380680104259479 48824531009071020156389219)
      ·
        refine ⟨73236796513606530234583829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48824531009071020156389219 73236796513606530234583829)
        ·
          refine ⟨3432974836575306104746117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73236796513606530234583829 3432974836575306104746117)
          ·
            refine ⟨643682781857869894639897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3432974836575306104746117 643682781857869894639897)
            ·
              refine ⟨482762086393402420979923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643682781857869894639897 482762086393402420979923)
              ·
                refine ⟨724143129590103631469885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482762086393402420979923 724143129590103631469885)
                ·
                  refine ⟨271553673596288861801207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724143129590103631469885 271553673596288861801207)
                  ·
                    rfl

theorem cell20_594955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 3].length) (baseStart_594955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594955 prefixEnd_594955 := by exact prefixLift 594955
  have htrace : WordTrace (prefixWord ++ tailWord_594955) baseStart_594955 baseEnd_594955 := by
    simpa [prefixWord, tailWord_594955, baseEnd_594955] using wordTrace_append hprefix tailTrace_594955
  have hstable : (prefixWord ++ tailWord_594955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594955).length < 2 ^ (prefixWord ++ tailWord_594955).sum := by decide
  have hdescent : baseEnd_594955 < baseStart_594955 := by decide
  rcases family_descends (prefixWord ++ tailWord_594955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_594996 : List Nat := [2, 5, 1, 2, 1, 1, 4, 2, 2]
def baseStart_594996 : Nat := 118140960795 + 594996 * 2 ^ 59
def prefixEnd_594996 : Nat := 4983230072969 + 3 ^ 40 * 594996 * 2
def baseEnd_594996 : Nat := 271572387113474941434373

theorem tailTrace_594996 : CollatzResearch.WordTrace tailWord_594996 prefixEnd_594996 271572387113474941434373 := by
  unfold tailWord_594996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10850643476219292035874421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14467524634959056047832561 10850643476219292035874421)
  ·
    refine ⟨1017247825895558628363227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10850643476219292035874421 1017247825895558628363227)
    ·
      refine ⟨1525871738843337942544841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017247825895558628363227 1525871738843337942544841)
      ·
        refine ⟨1144403804132503456908631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1525871738843337942544841 1144403804132503456908631)
        ·
          refine ⟨1716605706198755185362947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144403804132503456908631 1716605706198755185362947)
          ·
            refine ⟨2574908559298132778044421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716605706198755185362947 2574908559298132778044421)
            ·
              refine ⟨482795354868399895883329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2574908559298132778044421 482795354868399895883329)
              ·
                refine ⟨362096516151299921912497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482795354868399895883329 362096516151299921912497)
                ·
                  refine ⟨271572387113474941434373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362096516151299921912497 271572387113474941434373)
                  ·
                    rfl

theorem cell20_594996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_594996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_594996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_594996 prefixEnd_594996 := by exact prefixLift 594996
  have htrace : WordTrace (prefixWord ++ tailWord_594996) baseStart_594996 baseEnd_594996 := by
    simpa [prefixWord, tailWord_594996, baseEnd_594996] using wordTrace_append hprefix tailTrace_594996
  have hstable : (prefixWord ++ tailWord_594996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_594996).length < 2 ^ (prefixWord ++ tailWord_594996).sum := by decide
  have hdescent : baseEnd_594996 < baseStart_594996 := by decide
  rcases family_descends (prefixWord ++ tailWord_594996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595000 : List Nat := [2, 1, 2, 1, 5, 2, 1, 4, 2]
def baseStart_595000 : Nat := 118140960795 + 595000 * 2 ^ 59
def prefixEnd_595000 : Nat := 4983230072969 + 3 ^ 40 * 595000 * 2
def baseEnd_595000 : Nat := 271574212822468705301023

theorem tailTrace_595000 : CollatzResearch.WordTrace tailWord_595000 prefixEnd_595000 271574212822468705301023 := by
  unfold tailWord_595000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10850716422212046377447227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14467621896282728503262969 10850716422212046377447227)
  ·
    refine ⟨16276074633318069566170841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10850716422212046377447227 16276074633318069566170841)
    ·
      refine ⟨12207055974988552174628131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16276074633318069566170841 12207055974988552174628131)
      ·
        refine ⟨18310583962482828261942197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12207055974988552174628131 18310583962482828261942197)
        ·
          refine ⟨1716617246482765149557081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18310583962482828261942197 1716617246482765149557081)
          ·
            refine ⟨1287462934862073862167811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716617246482765149557081 1287462934862073862167811)
            ·
              refine ⟨1931194402293110793251717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287462934862073862167811 1931194402293110793251717)
              ·
                refine ⟨362098950429958273734697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1931194402293110793251717 362098950429958273734697)
                ·
                  refine ⟨271574212822468705301023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362098950429958273734697 271574212822468705301023)
                  ·
                    rfl

theorem cell20_595000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_595000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595000 prefixEnd_595000 := by exact prefixLift 595000
  have htrace : WordTrace (prefixWord ++ tailWord_595000) baseStart_595000 baseEnd_595000 := by
    simpa [prefixWord, tailWord_595000, baseEnd_595000] using wordTrace_append hprefix tailTrace_595000
  have hstable : (prefixWord ++ tailWord_595000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595000).length < 2 ^ (prefixWord ++ tailWord_595000).sum := by decide
  have hdescent : baseEnd_595000 < baseStart_595000 := by decide
  rcases family_descends (prefixWord ++ tailWord_595000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595021 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_595021 : Nat := 118140960795 + 595021 * 2 ^ 59
def prefixEnd_595021 : Nat := 4983230072969 + 3 ^ 40 * 595021 * 2
def baseEnd_595021 : Nat := 271583797794685965600937

theorem tailTrace_595021 : CollatzResearch.WordTrace tailWord_595021 prefixEnd_595021 271583797794685965600937 := by
  unfold tailWord_595021
  simp only [CollatzResearch.WordTrace]
  refine ⟨21702198777348013341408917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14468132518232008894272611 21702198777348013341408917)
  ·
    refine ⟨1017290567688188125378543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21702198777348013341408917 1017290567688188125378543)
    ·
      refine ⟨1525935851532282188067815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017290567688188125378543 1525935851532282188067815)
      ·
        refine ⟨2288903777298423282101723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525935851532282188067815 2288903777298423282101723)
        ·
          refine ⟨3433355665947634923152585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288903777298423282101723 3433355665947634923152585)
          ·
            refine ⟨2575016749460726192364439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3433355665947634923152585 2575016749460726192364439)
            ·
              refine ⟨3862525124191089288546659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575016749460726192364439 3862525124191089288546659)
              ·
                refine ⟨5793787686286633932819989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862525124191089288546659 5793787686286633932819989)
                ·
                  refine ⟨271583797794685965600937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5793787686286633932819989 271583797794685965600937)
                  ·
                    rfl

theorem cell20_595021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_595021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595021 prefixEnd_595021 := by exact prefixLift 595021
  have htrace : WordTrace (prefixWord ++ tailWord_595021) baseStart_595021 baseEnd_595021 := by
    simpa [prefixWord, tailWord_595021, baseEnd_595021] using wordTrace_append hprefix tailTrace_595021
  have hstable : (prefixWord ++ tailWord_595021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595021).length < 2 ^ (prefixWord ++ tailWord_595021).sum := by decide
  have hdescent : baseEnd_595021 < baseStart_595021 := by decide
  rcases family_descends (prefixWord ++ tailWord_595021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595048 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_595048 : Nat := 118140960795 + 595048 * 2 ^ 59
def prefixEnd_595048 : Nat := 4983230072969 + 3 ^ 40 * 595048 * 2
def baseEnd_595048 : Nat := 271596121330393871700827

theorem tailTrace_595048 : CollatzResearch.WordTrace tailWord_595048 prefixEnd_595048 271596121330393871700827 := by
  unfold tailWord_595048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10851591774125098476320899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14468789032166797968427865 10851591774125098476320899)
  ·
    refine ⟨16277387661187647714481349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10851591774125098476320899 16277387661187647714481349)
    ·
      refine ⟨3052010186472683946465253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16277387661187647714481349 3052010186472683946465253)
      ·
        refine ⟨572251909963628239962235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3052010186472683946465253 572251909963628239962235)
        ·
          refine ⟨858377864945442359943353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572251909963628239962235 858377864945442359943353)
          ·
            refine ⟨643783398709081769957515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858377864945442359943353 643783398709081769957515)
            ·
              refine ⟨965675098063622654936273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643783398709081769957515 965675098063622654936273)
              ·
                refine ⟨724256323547716991202205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965675098063622654936273 724256323547716991202205)
                ·
                  refine ⟨271596121330393871700827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724256323547716991202205 271596121330393871700827)
                  ·
                    rfl

theorem cell20_595048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_595048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595048 prefixEnd_595048 := by exact prefixLift 595048
  have htrace : WordTrace (prefixWord ++ tailWord_595048) baseStart_595048 baseEnd_595048 := by
    simpa [prefixWord, tailWord_595048, baseEnd_595048] using wordTrace_append hprefix tailTrace_595048
  have hstable : (prefixWord ++ tailWord_595048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595048).length < 2 ^ (prefixWord ++ tailWord_595048).sum := by decide
  have hdescent : baseEnd_595048 < baseStart_595048 := by decide
  rcases family_descends (prefixWord ++ tailWord_595048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595049 : List Nat := [1, 2, 1, 1, 1, 7, 7]
def baseStart_595049 : Nat := 118140960795 + 595049 * 2 ^ 59
def prefixEnd_595049 : Nat := 4983230072969 + 3 ^ 40 * 595049 * 2
def baseEnd_595049 : Nat := 30177397528626923629721

theorem tailTrace_595049 : CollatzResearch.WordTrace tailWord_595049 prefixEnd_595049 30177397528626923629721 := by
  unfold tailWord_595049
  simp only [CollatzResearch.WordTrace]
  refine ⟨21703220021246574123428201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14468813347497716082285467 21703220021246574123428201)
  ·
    refine ⟨16277415015934930592571151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21703220021246574123428201 16277415015934930592571151)
    ·
      refine ⟨24416122523902395888856727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16277415015934930592571151 24416122523902395888856727)
      ·
        refine ⟨36624183785853593833285091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24416122523902395888856727 36624183785853593833285091)
        ·
          refine ⟨54936275678780390749927637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36624183785853593833285091 54936275678780390749927637)
          ·
            refine ⟨1287568961221415408201429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54936275678780390749927637 1287568961221415408201429)
            ·
              refine ⟨30177397528626923629721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1287568961221415408201429 30177397528626923629721)
              ·
                rfl

theorem cell20_595049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_595049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595049 prefixEnd_595049 := by exact prefixLift 595049
  have htrace : WordTrace (prefixWord ++ tailWord_595049) baseStart_595049 baseEnd_595049 := by
    simpa [prefixWord, tailWord_595049, baseEnd_595049] using wordTrace_append hprefix tailTrace_595049
  have hstable : (prefixWord ++ tailWord_595049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595049).length < 2 ^ (prefixWord ++ tailWord_595049).sum := by decide
  have hdescent : baseEnd_595049 < baseStart_595049 := by decide
  rcases family_descends (prefixWord ++ tailWord_595049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595114 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_595114 : Nat := 118140960795 + 595114 * 2 ^ 59
def prefixEnd_595114 : Nat := 4983230072969 + 3 ^ 40 * 595114 * 2
def baseEnd_595114 : Nat := 271626245528790975500557

theorem tailTrace_595114 : CollatzResearch.WordTrace tailWord_595114 prefixEnd_595114 271626245528790975500557 := by
  unfold tailWord_595114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5426397691502772556136099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14470393844007393483029597 5426397691502772556136099)
  ·
    refine ⟨8139596537254158834204149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5426397691502772556136099 8139596537254158834204149)
    ·
      refine ⟨763087175367577390706639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8139596537254158834204149 763087175367577390706639)
      ·
        refine ⟨1144630763051366086059959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763087175367577390706639 1144630763051366086059959)
        ·
          refine ⟨1716946144577049129089939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144630763051366086059959 1716946144577049129089939)
          ·
            refine ⟨2575419216865573693634909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716946144577049129089939 2575419216865573693634909)
            ·
              refine ⟨965782206324590135113091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2575419216865573693634909 965782206324590135113091)
              ·
                refine ⟨1448673309486885202669637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965782206324590135113091 1448673309486885202669637)
                ·
                  refine ⟨271626245528790975500557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1448673309486885202669637 271626245528790975500557)
                  ·
                    rfl

theorem cell20_595114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_595114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595114 prefixEnd_595114 := by exact prefixLift 595114
  have htrace : WordTrace (prefixWord ++ tailWord_595114) baseStart_595114 baseEnd_595114 := by
    simpa [prefixWord, tailWord_595114, baseEnd_595114] using wordTrace_append hprefix tailTrace_595114
  have hstable : (prefixWord ++ tailWord_595114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595114).length < 2 ^ (prefixWord ++ tailWord_595114).sum := by decide
  have hdescent : baseEnd_595114 < baseStart_595114 := by decide
  rcases family_descends (prefixWord ++ tailWord_595114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595165 : List Nat := [1, 4, 3, 2, 3, 1, 2, 2, 2]
def baseStart_595165 : Nat := 118140960795 + 595165 * 2 ^ 59
def prefixEnd_595165 : Nat := 4983230072969 + 3 ^ 40 * 595165 * 2
def baseEnd_595165 : Nat := 271649523318461464800349

theorem tailTrace_595165 : CollatzResearch.WordTrace tailWord_595165 prefixEnd_595165 271649523318461464800349 := by
  unfold tailWord_595165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21707450888826325934650949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14471633925884217289767299 21707450888826325934650949)
  ·
    refine ⟨4070147041654936112747053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21707450888826325934650949 4070147041654936112747053)
    ·
      refine ⟨1526305140620601042280145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4070147041654936112747053 1526305140620601042280145)
      ·
        refine ⟨1144728855465450781710109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1526305140620601042280145 1144728855465450781710109)
        ·
          refine ⟨429273320799544043141291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1144728855465450781710109 429273320799544043141291)
          ·
            refine ⟨643909981199316064711937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429273320799544043141291 643909981199316064711937)
            ·
              refine ⟨482932485899487048533953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643909981199316064711937 482932485899487048533953)
              ·
                refine ⟨362199364424615286400465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482932485899487048533953 362199364424615286400465)
                ·
                  refine ⟨271649523318461464800349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362199364424615286400465 271649523318461464800349)
                  ·
                    rfl

theorem cell20_595165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_595165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595165 prefixEnd_595165 := by exact prefixLift 595165
  have htrace : WordTrace (prefixWord ++ tailWord_595165) baseStart_595165 baseEnd_595165 := by
    simpa [prefixWord, tailWord_595165, baseEnd_595165] using wordTrace_append hprefix tailTrace_595165
  have hstable : (prefixWord ++ tailWord_595165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595165).length < 2 ^ (prefixWord ++ tailWord_595165).sum := by decide
  have hdescent : baseEnd_595165 < baseStart_595165 := by decide
  rcases family_descends (prefixWord ++ tailWord_595165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595169 : List Nat := [1, 2, 3, 1, 3, 4, 2, 2, 2]
def baseStart_595169 : Nat := 118140960795 + 595169 * 2 ^ 59
def prefixEnd_595169 : Nat := 4983230072969 + 3 ^ 40 * 595169 * 2
def baseEnd_595169 : Nat := 271651349027455228666999

theorem tailTrace_595169 : CollatzResearch.WordTrace tailWord_595169 prefixEnd_595169 271651349027455228666999 := by
  unfold tailWord_595169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21707596780811834617796561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14471731187207889745197707 21707596780811834617796561)
  ·
    refine ⟨16280697585608875963347421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21707596780811834617796561 16280697585608875963347421)
    ·
      refine ⟨6105261594603328486255283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16280697585608875963347421 6105261594603328486255283)
      ·
        refine ⟨9157892391904992729382925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6105261594603328486255283 9157892391904992729382925)
        ·
          refine ⟨3434209646964372273518597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9157892391904992729382925 3434209646964372273518597)
          ·
            refine ⟨643914308805819801284737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3434209646964372273518597 643914308805819801284737)
            ·
              refine ⟨482935731604364850963553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643914308805819801284737 482935731604364850963553)
              ·
                refine ⟨362201798703273638222665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482935731604364850963553 362201798703273638222665)
                ·
                  refine ⟨271651349027455228666999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362201798703273638222665 271651349027455228666999)
                  ·
                    rfl

theorem cell20_595169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 2].length) (baseStart_595169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595169 prefixEnd_595169 := by exact prefixLift 595169
  have htrace : WordTrace (prefixWord ++ tailWord_595169) baseStart_595169 baseEnd_595169 := by
    simpa [prefixWord, tailWord_595169, baseEnd_595169] using wordTrace_append hprefix tailTrace_595169
  have hstable : (prefixWord ++ tailWord_595169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595169).length < 2 ^ (prefixWord ++ tailWord_595169).sum := by decide
  have hdescent : baseEnd_595169 < baseStart_595169 := by decide
  rcases family_descends (prefixWord ++ tailWord_595169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595180 : List Nat := [2, 2, 1, 1, 2, 6, 1, 5]
def baseStart_595180 : Nat := 118140960795 + 595180 * 2 ^ 59
def prefixEnd_595180 : Nat := 4983230072969 + 3 ^ 40 * 595180 * 2
def baseEnd_595180 : Nat := 90552123242396026433429

theorem tailTrace_595180 : CollatzResearch.WordTrace tailWord_595180 prefixEnd_595180 90552123242396026433429 := by
  unfold tailWord_595180
  simp only [CollatzResearch.WordTrace]
  refine ⟨10853998991885991748223497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14471998655847988997631329 10853998991885991748223497)
  ·
    refine ⟨8140499243914493811167623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10853998991885991748223497 8140499243914493811167623)
    ·
      refine ⟨12210748865871740716751435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8140499243914493811167623 12210748865871740716751435)
      ·
        refine ⟨18316123298807611075127153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12210748865871740716751435 18316123298807611075127153)
        ·
          refine ⟨13737092474105708306345365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18316123298807611075127153 13737092474105708306345365)
          ·
            refine ⟨643926209723705076859939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13737092474105708306345365 643926209723705076859939)
            ·
              refine ⟨965889314585557615289909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643926209723705076859939 965889314585557615289909)
              ·
                refine ⟨90552123242396026433429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 965889314585557615289909 90552123242396026433429)
                ·
                  rfl

theorem cell20_595180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_595180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595180 prefixEnd_595180 := by exact prefixLift 595180
  have htrace : WordTrace (prefixWord ++ tailWord_595180) baseStart_595180 baseEnd_595180 := by
    simpa [prefixWord, tailWord_595180, baseEnd_595180] using wordTrace_append hprefix tailTrace_595180
  have hstable : (prefixWord ++ tailWord_595180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595180).length < 2 ^ (prefixWord ++ tailWord_595180).sum := by decide
  have hdescent : baseEnd_595180 < baseStart_595180 := by decide
  rcases family_descends (prefixWord ++ tailWord_595180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595187 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 3]
def baseStart_595187 : Nat := 118140960795 + 595187 * 2 ^ 59
def prefixEnd_595187 : Nat := 4983230072969 + 3 ^ 40 * 595187 * 2
def baseEnd_595187 : Nat := 271659564717927166066925

theorem tailTrace_595187 : CollatzResearch.WordTrace tailWord_595187 prefixEnd_595187 271659564717927166066925 := by
  unfold tailWord_595187
  simp only [CollatzResearch.WordTrace]
  refine ⟨21708253294746623691951815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14472168863164415794634543 21708253294746623691951815)
  ·
    refine ⟨32562379942119935537927723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21708253294746623691951815 32562379942119935537927723)
    ·
      refine ⟨48843569913179903306891585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32562379942119935537927723 48843569913179903306891585)
      ·
        refine ⟨36632677434884927480168689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48843569913179903306891585 36632677434884927480168689)
        ·
          refine ⟨27474508076163695610126517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36632677434884927480168689 27474508076163695610126517)
          ·
            refine ⟨2575735132140346463449361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27474508076163695610126517 2575735132140346463449361)
            ·
              refine ⟨1931801349105259847587021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2575735132140346463449361 1931801349105259847587021)
              ·
                refine ⟨724425505914472442845133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1931801349105259847587021 724425505914472442845133)
                ·
                  refine ⟨271659564717927166066925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724425505914472442845133 271659564717927166066925)
                  ·
                    rfl

theorem cell20_595187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_595187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595187 prefixEnd_595187 := by exact prefixLift 595187
  have htrace : WordTrace (prefixWord ++ tailWord_595187) baseStart_595187 baseEnd_595187 := by
    simpa [prefixWord, tailWord_595187, baseEnd_595187] using wordTrace_append hprefix tailTrace_595187
  have hstable : (prefixWord ++ tailWord_595187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595187).length < 2 ^ (prefixWord ++ tailWord_595187).sum := by decide
  have hdescent : baseEnd_595187 < baseStart_595187 := by decide
  rcases family_descends (prefixWord ++ tailWord_595187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595194 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_595194 : Nat := 118140960795 + 595194 * 2 ^ 59
def prefixEnd_595194 : Nat := 4983230072969 + 3 ^ 40 * 595194 * 2
def baseEnd_595194 : Nat := 271662759708666252833563

theorem tailTrace_595194 : CollatzResearch.WordTrace tailWord_595194 prefixEnd_595194 271662759708666252833563 := by
  unfold tailWord_595194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427127151430315971864159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14472339070480842591637757 5427127151430315971864159)
  ·
    refine ⟨8140690727145473957796239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5427127151430315971864159 8140690727145473957796239)
    ·
      refine ⟨12211036090718210936694359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8140690727145473957796239 12211036090718210936694359)
      ·
        refine ⟨18316554136077316405041539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12211036090718210936694359 18316554136077316405041539)
        ·
          refine ⟨27474831204115974607562309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18316554136077316405041539 27474831204115974607562309)
          ·
            refine ⟨5151530850771745238917933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27474831204115974607562309 5151530850771745238917933)
            ·
              refine ⟨1931824069039404464594225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5151530850771745238917933 1931824069039404464594225)
              ·
                refine ⟨1448868051779553348445669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1931824069039404464594225 1448868051779553348445669)
                ·
                  refine ⟨271662759708666252833563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1448868051779553348445669 271662759708666252833563)
                  ·
                    rfl

theorem cell20_595194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_595194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595194 prefixEnd_595194 := by exact prefixLift 595194
  have htrace : WordTrace (prefixWord ++ tailWord_595194) baseStart_595194 baseEnd_595194 := by
    simpa [prefixWord, tailWord_595194, baseEnd_595194] using wordTrace_append hprefix tailTrace_595194
  have hstable : (prefixWord ++ tailWord_595194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595194).length < 2 ^ (prefixWord ++ tailWord_595194).sum := by decide
  have hdescent : baseEnd_595194 < baseStart_595194 := by decide
  rcases family_descends (prefixWord ++ tailWord_595194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
