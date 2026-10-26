import V185TrunkScan23Chunk1348

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7988742 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7988742 : Nat := 118140960795 + 7988742 * 2 ^ 59
def prefixEnd_7988742 : Nat := 4983230072969 + 3 ^ 40 * 7988742 * 2
def baseEnd_7988742 : Nat := 4102064470760488243885451

theorem tailTrace_7988742 : CollatzResearch.WordTrace tailWord_7988742 prefixEnd_7988742 4102064470760488243885451 := by
  unfold tailWord_7988742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9105417438254986792368265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194248905349439718237189653 9105417438254986792368265)
  ·
    refine ⟨6829063078691240094276199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9105417438254986792368265 6829063078691240094276199)
    ·
      refine ⟨10243594618036860141414299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829063078691240094276199 10243594618036860141414299)
      ·
        refine ⟨15365391927055290212121449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243594618036860141414299 15365391927055290212121449)
        ·
          refine ⟨11524043945291467659091087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15365391927055290212121449 11524043945291467659091087)
          ·
            refine ⟨17286065917937201488636631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524043945291467659091087 17286065917937201488636631)
            ·
              refine ⟨25929098876905802232954947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17286065917937201488636631 25929098876905802232954947)
              ·
                refine ⟨38893648315358703349432421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25929098876905802232954947 38893648315358703349432421)
                ·
                  refine ⟨7292559059129756878018579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38893648315358703349432421 7292559059129756878018579)
                  ·
                    refine ⟨10938838588694635317027869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7292559059129756878018579 10938838588694635317027869)
                    ·
                      refine ⟨4102064470760488243885451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10938838588694635317027869 4102064470760488243885451)
                      ·
                        rfl

theorem cell23_7988742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7988742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988742 prefixEnd_7988742 := by exact prefixLift 7988742
  have htrace : WordTrace (prefixWord ++ tailWord_7988742) baseStart_7988742 baseEnd_7988742 := by
    simpa [prefixWord, tailWord_7988742, baseEnd_7988742] using wordTrace_append hprefix tailTrace_7988742
  have hstable : (prefixWord ++ tailWord_7988742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988742).length < 2 ^ (prefixWord ++ tailWord_7988742).sum := by decide
  have hdescent : baseEnd_7988742 < baseStart_7988742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988748 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 4, 2, 2]
def baseStart_7988748 : Nat := 118140960795 + 7988748 * 2 ^ 59
def prefixEnd_7988748 : Nat := 4983230072969 + 3 ^ 40 * 7988748 * 2
def baseEnd_7988748 : Nat := 4102067551644415220410423

theorem tailTrace_7988748 : CollatzResearch.WordTrace tailWord_7988748 prefixEnd_7988748 4102067551644415220410423 := by
  unfold tailWord_7988748
  simp only [CollatzResearch.WordTrace]
  refine ⟨145686788431068920190251449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194249051241425226920335265 145686788431068920190251449)
  ·
    refine ⟨109265091323301690142688587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145686788431068920190251449 109265091323301690142688587)
    ·
      refine ⟨163897636984952535214032881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109265091323301690142688587 163897636984952535214032881)
      ·
        refine ⟨122923227738714401410524661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163897636984952535214032881 122923227738714401410524661)
        ·
          refine ⟨11524052600504475132236687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122923227738714401410524661 11524052600504475132236687)
          ·
            refine ⟨17286078900756712698355031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524052600504475132236687 17286078900756712698355031)
            ·
              refine ⟨25929118351135069047532547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17286078900756712698355031 25929118351135069047532547)
              ·
                refine ⟨38893677526702603571298821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25929118351135069047532547 38893677526702603571298821)
                ·
                  refine ⟨7292564536256738169618529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38893677526702603571298821 7292564536256738169618529)
                  ·
                    refine ⟨5469423402192553627213897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7292564536256738169618529 5469423402192553627213897)
                    ·
                      refine ⟨4102067551644415220410423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469423402192553627213897 4102067551644415220410423)
                      ·
                        rfl

theorem cell23_7988748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_7988748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988748 prefixEnd_7988748 := by exact prefixLift 7988748
  have htrace : WordTrace (prefixWord ++ tailWord_7988748) baseStart_7988748 baseEnd_7988748 := by
    simpa [prefixWord, tailWord_7988748, baseEnd_7988748] using wordTrace_append hprefix tailTrace_7988748
  have hstable : (prefixWord ++ tailWord_7988748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988748).length < 2 ^ (prefixWord ++ tailWord_7988748).sum := by decide
  have hdescent : baseEnd_7988748 < baseStart_7988748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988764 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7988764 : Nat := 118140960795 + 7988764 * 2 ^ 59
def prefixEnd_7988764 : Nat := 4983230072969 + 3 ^ 40 * 7988764 * 2
def baseEnd_7988764 : Nat := 4102075767334887157810349

theorem tailTrace_7988764 : CollatzResearch.WordTrace tailWord_7988764 prefixEnd_7988764 4102075767334887157810349 := by
  unfold tailWord_7988764
  simp only [CollatzResearch.WordTrace]
  refine ⟨145687080215039937556542673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194249440286719916742056897 145687080215039937556542673)
  ·
    refine ⟨109265310161279953167407005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145687080215039937556542673 109265310161279953167407005)
    ·
      refine ⟨40974491310479982437777627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109265310161279953167407005 40974491310479982437777627)
      ·
        refine ⟨61461736965719973656666441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40974491310479982437777627 61461736965719973656666441)
        ·
          refine ⟨46096302724289980242499831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61461736965719973656666441 46096302724289980242499831)
          ·
            refine ⟨69144454086434970363749747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46096302724289980242499831 69144454086434970363749747)
            ·
              refine ⟨103716681129652455545624621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69144454086434970363749747 103716681129652455545624621)
              ·
                refine ⟨38893755423619670829609233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103716681129652455545624621 38893755423619670829609233)
                ·
                  refine ⟨29170316567714753122206925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38893755423619670829609233 29170316567714753122206925)
                  ·
                    refine ⟨10938868712893032420827597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29170316567714753122206925 10938868712893032420827597)
                    ·
                      refine ⟨4102075767334887157810349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10938868712893032420827597 4102075767334887157810349)
                      ·
                        rfl

theorem cell23_7988764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7988764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988764 prefixEnd_7988764 := by exact prefixLift 7988764
  have htrace : WordTrace (prefixWord ++ tailWord_7988764) baseStart_7988764 baseEnd_7988764 := by
    simpa [prefixWord, tailWord_7988764, baseEnd_7988764] using wordTrace_append hprefix tailTrace_7988764
  have hstable : (prefixWord ++ tailWord_7988764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988764).length < 2 ^ (prefixWord ++ tailWord_7988764).sum := by decide
  have hdescent : baseEnd_7988764 < baseStart_7988764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988765 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_7988765 : Nat := 118140960795 + 7988765 * 2 ^ 59
def prefixEnd_7988765 : Nat := 4983230072969 + 3 ^ 40 * 7988765 * 2
def baseEnd_7988765 : Nat := 4102076280815541653897845

theorem tailTrace_7988765 : CollatzResearch.WordTrace tailWord_7988765 prefixEnd_7988765 4102076280815541653897845 := by
  unfold tailWord_7988765
  simp only [CollatzResearch.WordTrace]
  refine ⟨291374196903076252283871749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194249464602050834855914499 291374196903076252283871749)
  ·
    refine ⟨54632661919326797303225953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291374196903076252283871749 54632661919326797303225953)
    ·
      refine ⟨40974496439495097977419465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54632661919326797303225953 40974496439495097977419465)
      ·
        refine ⟨30730872329621323483064599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40974496439495097977419465 30730872329621323483064599)
        ·
          refine ⟨46096308494431985224596899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30730872329621323483064599 46096308494431985224596899)
          ·
            refine ⟨69144462741647977836895349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46096308494431985224596899 69144462741647977836895349)
            ·
              refine ⟨6482293382029497922208939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69144462741647977836895349 6482293382029497922208939)
              ·
                refine ⟨9723440073044246883313409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482293382029497922208939 9723440073044246883313409)
                ·
                  refine ⟨7292580054783185162485057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9723440073044246883313409 7292580054783185162485057)
                  ·
                    refine ⟨5469435041087388871863793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7292580054783185162485057 5469435041087388871863793)
                    ·
                      refine ⟨4102076280815541653897845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469435041087388871863793 4102076280815541653897845)
                      ·
                        rfl

theorem cell23_7988765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_7988765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988765 prefixEnd_7988765 := by exact prefixLift 7988765
  have htrace : WordTrace (prefixWord ++ tailWord_7988765) baseStart_7988765 baseEnd_7988765 := by
    simpa [prefixWord, tailWord_7988765, baseEnd_7988765] using wordTrace_append hprefix tailTrace_7988765
  have hstable : (prefixWord ++ tailWord_7988765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988765).length < 2 ^ (prefixWord ++ tailWord_7988765).sum := by decide
  have hdescent : baseEnd_7988765 < baseStart_7988765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988767 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 1, 7]
def baseStart_7988767 : Nat := 118140960795 + 7988767 * 2 ^ 59
def prefixEnd_7988767 : Nat := 4983230072969 + 3 ^ 40 * 7988767 * 2
def baseEnd_7988767 : Nat := 1367359102592283548690945

theorem tailTrace_7988767 : CollatzResearch.WordTrace tailWord_7988767 prefixEnd_7988767 1367359102592283548690945 := by
  unfold tailWord_7988767
  simp only [CollatzResearch.WordTrace]
  refine ⟨291374269849069006625444555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194249513232712671083629703 291374269849069006625444555)
  ·
    refine ⟨437061404773603509938166833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291374269849069006625444555 437061404773603509938166833)
    ·
      refine ⟨327796053580202632453625125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437061404773603509938166833 327796053580202632453625125)
      ·
        refine ⟨61461760046287993585054711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327796053580202632453625125 61461760046287993585054711)
        ·
          refine ⟨92192640069431990377582067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61461760046287993585054711 92192640069431990377582067)
          ·
            refine ⟨138288960104147985566373101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92192640069431990377582067 138288960104147985566373101)
            ·
              refine ⟨51858360039055494587389913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138288960104147985566373101 51858360039055494587389913)
              ·
                refine ⟨38893770029291620940542435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51858360039055494587389913 38893770029291620940542435)
                ·
                  refine ⟨58340655043937431410813653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38893770029291620940542435 58340655043937431410813653)
                  ·
                    refine ⟨1367359102592283548690945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58340655043937431410813653 1367359102592283548690945)
                    ·
                      rfl

theorem cell23_7988767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_7988767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988767 prefixEnd_7988767 := by exact prefixLift 7988767
  have htrace : WordTrace (prefixWord ++ tailWord_7988767) baseStart_7988767 baseEnd_7988767 := by
    simpa [prefixWord, tailWord_7988767, baseEnd_7988767] using wordTrace_append hprefix tailTrace_7988767
  have hstable : (prefixWord ++ tailWord_7988767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988767).length < 2 ^ (prefixWord ++ tailWord_7988767).sum := by decide
  have hdescent : baseEnd_7988767 < baseStart_7988767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988824 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_7988824 : Nat := 118140960795 + 7988824 * 2 ^ 59
def prefixEnd_7988824 : Nat := 4983230072969 + 3 ^ 40 * 7988824 * 2
def baseEnd_7988824 : Nat := 4102106576174156923060073

theorem tailTrace_7988824 : CollatzResearch.WordTrace tailWord_7988824 prefixEnd_7988824 4102106576174156923060073 := by
  unfold tailWord_7988824
  simp only [CollatzResearch.WordTrace]
  refine ⟨145688174404931252680134763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194250899206575003573513017 145688174404931252680134763)
  ·
    refine ⟨218532261607396879020202145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145688174404931252680134763 218532261607396879020202145)
    ·
      refine ⟨163899196205547659265151609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218532261607396879020202145 163899196205547659265151609)
      ·
        refine ⟨122924397154160744448863707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163899196205547659265151609 122924397154160744448863707)
        ·
          refine ⟨184386595731241116673295561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122924397154160744448863707 184386595731241116673295561)
          ·
            refine ⟨138289946798430837504971671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184386595731241116673295561 138289946798430837504971671)
            ·
              refine ⟨207434920197646256257457507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138289946798430837504971671 207434920197646256257457507)
              ·
                refine ⟨311152380296469384386186261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207434920197646256257457507 311152380296469384386186261)
                ·
                  refine ⟨14585267826397002393102481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311152380296469384386186261 14585267826397002393102481)
                  ·
                    refine ⟨10938950869797751794826861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14585267826397002393102481 10938950869797751794826861)
                    ·
                      refine ⟨4102106576174156923060073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10938950869797751794826861 4102106576174156923060073)
                      ·
                        rfl

theorem cell23_7988824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_7988824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988824 prefixEnd_7988824 := by exact prefixLift 7988824
  have htrace : WordTrace (prefixWord ++ tailWord_7988824) baseStart_7988824 baseEnd_7988824 := by
    simpa [prefixWord, tailWord_7988824, baseEnd_7988824] using wordTrace_append hprefix tailTrace_7988824
  have hstable : (prefixWord ++ tailWord_7988824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988824).length < 2 ^ (prefixWord ++ tailWord_7988824).sum := by decide
  have hdescent : baseEnd_7988824 < baseStart_7988824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988847 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_7988847 : Nat := 118140960795 + 7988847 * 2 ^ 59
def prefixEnd_7988847 : Nat := 4983230072969 + 3 ^ 40 * 7988847 * 2
def baseEnd_7988847 : Nat := 4102118386229210333072467

theorem tailTrace_7988847 : CollatzResearch.WordTrace tailWord_7988847 prefixEnd_7988847 4102118386229210333072467 := by
  unfold tailWord_7988847
  simp only [CollatzResearch.WordTrace]
  refine ⟨291377187688779180288356795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194251458459186120192237863 291377187688779180288356795)
  ·
    refine ⟨437065781533168770432535193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291377187688779180288356795 437065781533168770432535193)
    ·
      refine ⟨327799336149876577824401395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437065781533168770432535193 327799336149876577824401395)
      ·
        refine ⟨491699004224814866736602093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327799336149876577824401395 491699004224814866736602093)
        ·
          refine ⟨184387126584305575026225785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491699004224814866736602093 184387126584305575026225785)
          ·
            refine ⟨138290344938229181269669339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184387126584305575026225785 138290344938229181269669339)
            ·
              refine ⟨207435517407343771904504009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138290344938229181269669339 207435517407343771904504009)
              ·
                refine ⟨155576638055507828928378007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207435517407343771904504009 155576638055507828928378007)
                ·
                  refine ⟨233364957083261743392567011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155576638055507828928378007 233364957083261743392567011)
                  ·
                    refine ⟨350047435624892615088850517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233364957083261743392567011 350047435624892615088850517)
                    ·
                      refine ⟨4102118386229210333072467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 350047435624892615088850517 4102118386229210333072467)
                      ·
                        rfl

theorem cell23_7988847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_7988847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988847 prefixEnd_7988847 := by exact prefixLift 7988847
  have htrace : WordTrace (prefixWord ++ tailWord_7988847) baseStart_7988847 baseEnd_7988847 := by
    simpa [prefixWord, tailWord_7988847, baseEnd_7988847] using wordTrace_append hprefix tailTrace_7988847
  have hstable : (prefixWord ++ tailWord_7988847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988847).length < 2 ^ (prefixWord ++ tailWord_7988847).sum := by decide
  have hdescent : baseEnd_7988847 < baseStart_7988847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988861 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 6]
def baseStart_7988861 : Nat := 118140960795 + 7988861 * 2 ^ 59
def prefixEnd_7988861 : Nat := 4983230072969 + 3 ^ 40 * 7988861 * 2
def baseEnd_7988861 : Nat := 455791730550930364255267

theorem tailTrace_7988861 : CollatzResearch.WordTrace tailWord_7988861 prefixEnd_7988861 455791730550930364255267 := by
  unfold tailWord_7988861
  simp only [CollatzResearch.WordTrace]
  refine ⟨291377698310728460679366437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194251798873818973786244291 291377698310728460679366437)
  ·
    refine ⟨54633318433261586377381207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291377698310728460679366437 54633318433261586377381207)
    ·
      refine ⟨81949977649892379566071811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54633318433261586377381207 81949977649892379566071811)
      ·
        refine ⟨122924966474838569349107717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81949977649892379566071811 122924966474838569349107717)
        ·
          refine ⟨23048431214032231752957697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122924966474838569349107717 23048431214032231752957697)
          ·
            refine ⟨17286323410524173814718273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23048431214032231752957697 17286323410524173814718273)
            ·
              refine ⟨12964742557893130361038705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17286323410524173814718273 12964742557893130361038705)
              ·
                refine ⟨9723556918419847770779029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12964742557893130361038705 9723556918419847770779029)
                ·
                  refine ⟨455791730550930364255267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9723556918419847770779029 455791730550930364255267)
                  ·
                    rfl

theorem cell23_7988861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_7988861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988861 prefixEnd_7988861 := by exact prefixLift 7988861
  have htrace : WordTrace (prefixWord ++ tailWord_7988861) baseStart_7988861 baseEnd_7988861 := by
    simpa [prefixWord, tailWord_7988861, baseEnd_7988861] using wordTrace_append hprefix tailTrace_7988861
  have hstable : (prefixWord ++ tailWord_7988861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988861).length < 2 ^ (prefixWord ++ tailWord_7988861).sum := by decide
  have hdescent : baseEnd_7988861 < baseStart_7988861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988865 : List Nat := [1, 2, 4, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7988865 : Nat := 118140960795 + 7988865 * 2 ^ 59
def prefixEnd_7988865 : Nat := 4983230072969 + 3 ^ 40 * 7988865 * 2
def baseEnd_7988865 : Nat := 1367375876293663754215795

theorem tailTrace_7988865 : CollatzResearch.WordTrace tailWord_7988865 prefixEnd_7988865 1367375876293663754215795 := by
  unfold tailWord_7988865
  simp only [CollatzResearch.WordTrace]
  refine ⟨291377844202713969362512049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194251896135142646241674699 291377844202713969362512049)
  ·
    refine ⟨218533383152035477021884037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291377844202713969362512049 218533383152035477021884037)
    ·
      refine ⟨40975009341006651941603257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218533383152035477021884037 40975009341006651941603257)
      ·
        refine ⟨30731257005754988956202443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40975009341006651941603257 30731257005754988956202443)
        ·
          refine ⟨46096885508632483434303665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30731257005754988956202443 46096885508632483434303665)
          ·
            refine ⟨34572664131474362575727749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46096885508632483434303665 34572664131474362575727749)
            ·
              refine ⟨6482374524651442982948953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34572664131474362575727749 6482374524651442982948953)
              ·
                refine ⟨4861780893488582237211715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6482374524651442982948953 4861780893488582237211715)
                ·
                  refine ⟨7292671340232873355817573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861780893488582237211715 7292671340232873355817573)
                  ·
                    refine ⟨1367375876293663754215795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7292671340232873355817573 1367375876293663754215795)
                    ·
                      rfl

theorem cell23_7988865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7988865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988865 prefixEnd_7988865 := by exact prefixLift 7988865
  have htrace : WordTrace (prefixWord ++ tailWord_7988865) baseStart_7988865 baseEnd_7988865 := by
    simpa [prefixWord, tailWord_7988865, baseEnd_7988865] using wordTrace_append hprefix tailTrace_7988865
  have hstable : (prefixWord ++ tailWord_7988865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988865).length < 2 ^ (prefixWord ++ tailWord_7988865).sum := by decide
  have hdescent : baseEnd_7988865 < baseStart_7988865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988888 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_7988888 : Nat := 118140960795 + 7988888 * 2 ^ 59
def prefixEnd_7988888 : Nat := 4983230072969 + 3 ^ 40 * 7988888 * 2
def baseEnd_7988888 : Nat := 4102139438936044672659779

theorem tailTrace_7988888 : CollatzResearch.WordTrace tailWord_7988888 prefixEnd_7988888 4102139438936044672659779 := by
  unfold tailWord_7988888
  simp only [CollatzResearch.WordTrace]
  refine ⟨145689341540815322145299659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194252455387753762860399545 145689341540815322145299659)
  ·
    refine ⟨218534012311222983217949489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145689341540815322145299659 218534012311222983217949489)
    ·
      refine ⟨163900509233417237413462117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218534012311222983217949489 163900509233417237413462117)
      ·
        refine ⟨30731345481265732015024147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163900509233417237413462117 30731345481265732015024147)
        ·
          refine ⟨46097018221898598022536221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30731345481265732015024147 46097018221898598022536221)
          ·
            refine ⟨17286381833211974258451083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46097018221898598022536221 17286381833211974258451083)
            ·
              refine ⟨25929572749817961387676625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17286381833211974258451083 25929572749817961387676625)
              ·
                refine ⟨19447179562363471040757469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25929572749817961387676625 19447179562363471040757469)
                ·
                  refine ⟨7292692335886301640284051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19447179562363471040757469 7292692335886301640284051)
                  ·
                    refine ⟨10939038503829452460426077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7292692335886301640284051 10939038503829452460426077)
                    ·
                      refine ⟨4102139438936044672659779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10939038503829452460426077 4102139438936044672659779)
                      ·
                        rfl

theorem cell23_7988888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_7988888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988888 prefixEnd_7988888 := by exact prefixLift 7988888
  have htrace : WordTrace (prefixWord ++ tailWord_7988888) baseStart_7988888 baseEnd_7988888 := by
    simpa [prefixWord, tailWord_7988888, baseEnd_7988888] using wordTrace_append hprefix tailTrace_7988888
  have hstable : (prefixWord ++ tailWord_7988888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988888).length < 2 ^ (prefixWord ++ tailWord_7988888).sum := by decide
  have hdescent : baseEnd_7988888 < baseStart_7988888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988911 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 4]
def baseStart_7988911 : Nat := 118140960795 + 7988911 * 2 ^ 59
def prefixEnd_7988911 : Nat := 4983230072969 + 3 ^ 40 * 7988911 * 2
def baseEnd_7988911 : Nat := 4102151248991098082672173

theorem tailTrace_7988911 : CollatzResearch.WordTrace tailWord_7988911 prefixEnd_7988911 4102151248991098082672173 := by
  unfold tailWord_7988911
  simp only [CollatzResearch.WordTrace]
  refine ⟨291379521960547319218686587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194253014640364879479124391 291379521960547319218686587)
  ·
    refine ⟨437069282940820978828029881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291379521960547319218686587 437069282940820978828029881)
    ·
      refine ⟨327801962205615734121022411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437069282940820978828029881 327801962205615734121022411)
      ·
        refine ⟨491702943308423601181533617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327801962205615734121022411 491702943308423601181533617)
        ·
          refine ⟨368777207481317700886150213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491702943308423601181533617 368777207481317700886150213)
          ·
            refine ⟨69145726402747068916153165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368777207481317700886150213 69145726402747068916153165)
            ·
              refine ⟨25929647401030150843557437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69145726402747068916153165 25929647401030150843557437)
              ·
                refine ⟨9723617775386306566334039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25929647401030150843557437 9723617775386306566334039)
                ·
                  refine ⟨14585426663079459849501059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9723617775386306566334039 14585426663079459849501059)
                  ·
                    refine ⟨21878139994619189774251589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14585426663079459849501059 21878139994619189774251589)
                    ·
                      refine ⟨4102151248991098082672173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21878139994619189774251589 4102151248991098082672173)
                      ·
                        rfl

theorem cell23_7988911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_7988911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988911 prefixEnd_7988911 := by exact prefixLift 7988911
  have htrace : WordTrace (prefixWord ++ tailWord_7988911) baseStart_7988911 baseEnd_7988911 := by
    simpa [prefixWord, tailWord_7988911, baseEnd_7988911] using wordTrace_append hprefix tailTrace_7988911
  have hstable : (prefixWord ++ tailWord_7988911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988911).length < 2 ^ (prefixWord ++ tailWord_7988911).sum := by decide
  have hdescent : baseEnd_7988911 < baseStart_7988911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988938 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_7988938 : Nat := 118140960795 + 7988938 * 2 ^ 59
def prefixEnd_7988938 : Nat := 4983230072969 + 3 ^ 40 * 7988938 * 2
def baseEnd_7988938 : Nat := 1367388370989589825678183

theorem tailTrace_7988938 : CollatzResearch.WordTrace tailWord_7988938 prefixEnd_7988938 1367388370989589825678183 := by
  unfold tailWord_7988938
  simp only [CollatzResearch.WordTrace]
  refine ⟨72845126682862375707479867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194253671154299668553279645 72845126682862375707479867)
  ·
    refine ⟨109267690024293563561219801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72845126682862375707479867 109267690024293563561219801)
    ·
      refine ⟨81950767518220172670914851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109267690024293563561219801 81950767518220172670914851)
      ·
        refine ⟨122926151277330259006372277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81950767518220172670914851 122926151277330259006372277)
        ·
          refine ⟨11524326682249711781847401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122926151277330259006372277 11524326682249711781847401)
          ·
            refine ⟨8643245011687283836385551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11524326682249711781847401 8643245011687283836385551)
            ·
              refine ⟨12964867517530925754578327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8643245011687283836385551 12964867517530925754578327)
              ·
                refine ⟨19447301276296388631867491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12964867517530925754578327 19447301276296388631867491)
                ·
                  refine ⟨29170951914444582947801237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19447301276296388631867491 29170951914444582947801237)
                  ·
                    refine ⟨1367388370989589825678183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29170951914444582947801237 1367388370989589825678183)
                    ·
                      rfl

theorem cell23_7988938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_7988938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988938 prefixEnd_7988938 := by exact prefixLift 7988938
  have htrace : WordTrace (prefixWord ++ tailWord_7988938) baseStart_7988938 baseEnd_7988938 := by
    simpa [prefixWord, tailWord_7988938, baseEnd_7988938] using wordTrace_append hprefix tailTrace_7988938
  have hstable : (prefixWord ++ tailWord_7988938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988938).length < 2 ^ (prefixWord ++ tailWord_7988938).sum := by decide
  have hdescent : baseEnd_7988938 < baseStart_7988938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988956 : List Nat := [2, 2, 5, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7988956 : Nat := 118140960795 + 7988956 * 2 ^ 59
def prefixEnd_7988956 : Nat := 4983230072969 + 3 ^ 40 * 7988956 * 2
def baseEnd_7988956 : Nat := 4102174355620550406609467

theorem tailTrace_7988956 : CollatzResearch.WordTrace tailWord_7988956 prefixEnd_7988956 4102174355620550406609467 := by
  unfold tailWord_7988956
  simp only [CollatzResearch.WordTrace]
  refine ⟨145690581622692145952037361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194254108830256194602716481 145690581622692145952037361)
  ·
    refine ⟨109267936217019109464028021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145690581622692145952037361 109267936217019109464028021)
    ·
      refine ⟨10243869020345541512252627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109267936217019109464028021 10243869020345541512252627)
      ·
        refine ⟨15365803530518312268378941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243869020345541512252627 15365803530518312268378941)
        ·
          refine ⟨5762176323944367100642103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15365803530518312268378941 5762176323944367100642103)
          ·
            refine ⟨8643264485916550650963155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5762176323944367100642103 8643264485916550650963155)
            ·
              refine ⟨12964896728874825976444733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8643264485916550650963155 12964896728874825976444733)
              ·
                refine ⟨4861836273328059741166775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12964896728874825976444733 4861836273328059741166775)
                ·
                  refine ⟨7292754409992089611750163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861836273328059741166775 7292754409992089611750163)
                  ·
                    refine ⟨10939131614988134417625245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7292754409992089611750163 10939131614988134417625245)
                    ·
                      refine ⟨4102174355620550406609467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10939131614988134417625245 4102174355620550406609467)
                      ·
                        rfl

theorem cell23_7988956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7988956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988956 prefixEnd_7988956 := by exact prefixLift 7988956
  have htrace : WordTrace (prefixWord ++ tailWord_7988956) baseStart_7988956 baseEnd_7988956 := by
    simpa [prefixWord, tailWord_7988956, baseEnd_7988956] using wordTrace_append hprefix tailTrace_7988956
  have hstable : (prefixWord ++ tailWord_7988956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988956).length < 2 ^ (prefixWord ++ tailWord_7988956).sum := by decide
  have hdescent : baseEnd_7988956 < baseStart_7988956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988978 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_7988978 : Nat := 118140960795 + 7988978 * 2 ^ 59
def prefixEnd_7988978 : Nat := 4983230072969 + 3 ^ 40 * 7988978 * 2
def baseEnd_7988978 : Nat := 4102185652194949320534365

theorem tailTrace_7988978 : CollatzResearch.WordTrace tailWord_7988978 prefixEnd_7988978 4102185652194949320534365 := by
  unfold tailWord_7988978
  simp only [CollatzResearch.WordTrace]
  refine ⟨72845491412826147415343897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194254643767536393107583725 72845491412826147415343897)
  ·
    refine ⟨54634118559619610561507923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72845491412826147415343897 54634118559619610561507923)
    ·
      refine ⟨81951177839429415842261885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54634118559619610561507923 81951177839429415842261885)
      ·
        refine ⟨30731691689786030940848207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81951177839429415842261885 30731691689786030940848207)
        ·
          refine ⟨46097537534679046411272311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30731691689786030940848207 46097537534679046411272311)
          ·
            refine ⟨69146306302018569616908467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46097537534679046411272311 69146306302018569616908467)
            ·
              refine ⟨103719459453027854425362701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69146306302018569616908467 103719459453027854425362701)
              ·
                refine ⟨38894797294885445409511013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103719459453027854425362701 38894797294885445409511013)
                ·
                  refine ⟨7292774492791021014283315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38894797294885445409511013 7292774492791021014283315)
                  ·
                    refine ⟨10939161739186531521424973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7292774492791021014283315 10939161739186531521424973)
                    ·
                      refine ⟨4102185652194949320534365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10939161739186531521424973 4102185652194949320534365)
                      ·
                        rfl

theorem cell23_7988978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_7988978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988978 prefixEnd_7988978 := by exact prefixLift 7988978
  have htrace : WordTrace (prefixWord ++ tailWord_7988978) baseStart_7988978 baseEnd_7988978 := by
    simpa [prefixWord, tailWord_7988978, baseEnd_7988978] using wordTrace_append hprefix tailTrace_7988978
  have hstable : (prefixWord ++ tailWord_7988978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988978).length < 2 ^ (prefixWord ++ tailWord_7988978).sum := by decide
  have hdescent : baseEnd_7988978 < baseStart_7988978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988988 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_7988988 : Nat := 118140960795 + 7988988 * 2 ^ 59
def prefixEnd_7988988 : Nat := 4983230072969 + 3 ^ 40 * 7988988 * 2
def baseEnd_7988988 : Nat := 4102190787001494281409319

theorem tailTrace_7988988 : CollatzResearch.WordTrace tailWord_7988988 prefixEnd_7988988 4102190787001494281409319 := by
  unfold tailWord_7988988
  simp only [CollatzResearch.WordTrace]
  refine ⟨145691165190634180684619809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194254886920845574246159745 145691165190634180684619809)
  ·
    refine ⟨109268373892975635513464857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145691165190634180684619809 109268373892975635513464857)
    ·
      refine ⟨81951280419731726635098643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109268373892975635513464857 81951280419731726635098643)
      ·
        refine ⟨122926920629597589952647965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81951280419731726635098643 122926920629597589952647965)
        ·
          refine ⟨46097595236099096232242987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122926920629597589952647965 46097595236099096232242987)
          ·
            refine ⟨69146392854148644348364481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46097595236099096232242987 69146392854148644348364481)
            ·
              refine ⟨51859794640611483261273361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69146392854148644348364481 51859794640611483261273361)
              ·
                refine ⟨38894845980458612445955021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51859794640611483261273361 38894845980458612445955021)
                ·
                  refine ⟨14585567242671979667233133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38894845980458612445955021 14585567242671979667233133)
                  ·
                    refine ⟨5469587716001992375212425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14585567242671979667233133 5469587716001992375212425)
                    ·
                      refine ⟨4102190787001494281409319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469587716001992375212425 4102190787001494281409319)
                      ·
                        rfl

theorem cell23_7988988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_7988988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988988 prefixEnd_7988988 := by exact prefixLift 7988988
  have htrace : WordTrace (prefixWord ++ tailWord_7988988) baseStart_7988988 baseEnd_7988988 := by
    simpa [prefixWord, tailWord_7988988, baseEnd_7988988] using wordTrace_append hprefix tailTrace_7988988
  have hstable : (prefixWord ++ tailWord_7988988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988988).length < 2 ^ (prefixWord ++ tailWord_7988988).sum := by decide
  have hdescent : baseEnd_7988988 < baseStart_7988988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7988995 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 2, 1, 3]
def baseStart_7988995 : Nat := 118140960795 + 7988995 * 2 ^ 59
def prefixEnd_7988995 : Nat := 4983230072969 + 3 ^ 40 * 7988995 * 2
def baseEnd_7988995 : Nat := 4102194381366075754021787

theorem tailTrace_7988995 : CollatzResearch.WordTrace tailWord_7988995 prefixEnd_7988995 4102194381366075754021787 := by
  unfold tailWord_7988995
  simp only [CollatzResearch.WordTrace]
  refine ⟨291382585692243001564744439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194255057128162001043162959 291382585692243001564744439)
  ·
    refine ⟨437073878538364502347116659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291382585692243001564744439 437073878538364502347116659)
    ·
      refine ⟨655610817807546753520674989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437073878538364502347116659 655610817807546753520674989)
      ·
        refine ⟨245854056677830032570253121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655610817807546753520674989 245854056677830032570253121)
        ·
          refine ⟨184390542508372524427689841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245854056677830032570253121 184390542508372524427689841)
          ·
            refine ⟨138292906881279393320767381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184390542508372524427689841 138292906881279393320767381)
            ·
              refine ⟨6482480010059971561910971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138292906881279393320767381 6482480010059971561910971)
              ·
                refine ⟨9723720015089957342866457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482480010059971561910971 9723720015089957342866457)
                ·
                  refine ⟨7292790011317468007149843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9723720015089957342866457 7292790011317468007149843)
                  ·
                    refine ⟨10939185016976202010724765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7292790011317468007149843 10939185016976202010724765)
                    ·
                      refine ⟨4102194381366075754021787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10939185016976202010724765 4102194381366075754021787)
                      ·
                        rfl

theorem cell23_7988995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_7988995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7988995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7988995 prefixEnd_7988995 := by exact prefixLift 7988995
  have htrace : WordTrace (prefixWord ++ tailWord_7988995) baseStart_7988995 baseEnd_7988995 := by
    simpa [prefixWord, tailWord_7988995, baseEnd_7988995] using wordTrace_append hprefix tailTrace_7988995
  have hstable : (prefixWord ++ tailWord_7988995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7988995).length < 2 ^ (prefixWord ++ tailWord_7988995).sum := by decide
  have hdescent : baseEnd_7988995 < baseStart_7988995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7988995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989018 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2]
def baseStart_7989018 : Nat := 118140960795 + 7989018 * 2 ^ 59
def prefixEnd_7989018 : Nat := 4983230072969 + 3 ^ 40 * 7989018 * 2
def baseEnd_7989018 : Nat := 4102206191421129164034181

theorem tailTrace_7989018 : CollatzResearch.WordTrace tailWord_7989018 prefixEnd_7989018 4102206191421129164034181 := by
  unfold tailWord_7989018
  simp only [CollatzResearch.WordTrace]
  refine ⟨72845856142789919123207927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194255616380773117661887805 72845856142789919123207927)
  ·
    refine ⟨109268784214184878684811891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72845856142789919123207927 109268784214184878684811891)
    ·
      refine ⟨163903176321277318027217837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109268784214184878684811891 163903176321277318027217837)
      ·
        refine ⟨61463691120478994260206689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163903176321277318027217837 61463691120478994260206689)
        ·
          refine ⟨46097768340359245695155017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61463691120478994260206689 46097768340359245695155017)
          ·
            refine ⟨34573326255269434271366263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46097768340359245695155017 34573326255269434271366263)
            ·
              refine ⟨51859989382904151407049395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34573326255269434271366263 51859989382904151407049395)
              ·
                refine ⟨77789984074356227110574093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51859989382904151407049395 77789984074356227110574093)
                ·
                  refine ⟨29171244027883585166465285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77789984074356227110574093 29171244027883585166465285)
                  ·
                    refine ⟨5469608255228172218712241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29171244027883585166465285 5469608255228172218712241)
                    ·
                      refine ⟨4102206191421129164034181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469608255228172218712241 4102206191421129164034181)
                      ·
                        rfl

theorem cell23_7989018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_7989018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989018 prefixEnd_7989018 := by exact prefixLift 7989018
  have htrace : WordTrace (prefixWord ++ tailWord_7989018) baseStart_7989018 baseEnd_7989018 := by
    simpa [prefixWord, tailWord_7989018, baseEnd_7989018] using wordTrace_append hprefix tailTrace_7989018
  have hstable : (prefixWord ++ tailWord_7989018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989018).length < 2 ^ (prefixWord ++ tailWord_7989018).sum := by decide
  have hdescent : baseEnd_7989018 < baseStart_7989018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989148 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 8]
def baseStart_7989148 : Nat := 118140960795 + 7989148 * 2 ^ 59
def prefixEnd_7989148 : Nat := 4983230072969 + 3 ^ 40 * 7989148 * 2
def baseEnd_7989148 : Nat := 455808104878468183934287

theorem tailTrace_7989148 : CollatzResearch.WordTrace tailWord_7989148 prefixEnd_7989148 455808104878468183934287 := by
  unfold tailWord_7989148
  simp only [CollatzResearch.WordTrace]
  refine ⟨145694083030344354347532049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194258777373792472463376065 145694083030344354347532049)
  ·
    refine ⟨109270562272758265760649037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145694083030344354347532049 109270562272758265760649037)
    ·
      refine ⟨40976460852284349660243389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109270562272758265760649037 40976460852284349660243389)
      ·
        refine ⟨15366172819606631122591271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40976460852284349660243389 15366172819606631122591271)
        ·
          refine ⟨23049259229409946683886907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15366172819606631122591271 23049259229409946683886907)
          ·
            refine ⟨34573888844114920025830361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23049259229409946683886907 34573888844114920025830361)
            ·
              refine ⟨25930416633086190019372771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34573888844114920025830361 25930416633086190019372771)
              ·
                refine ⟨38895624949629285029059157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25930416633086190019372771 38895624949629285029059157)
                ·
                  refine ⟨455808104878468183934287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38895624949629285029059157 455808104878468183934287)
                  ·
                    rfl

theorem cell23_7989148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_7989148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989148 prefixEnd_7989148 := by exact prefixLift 7989148
  have htrace : WordTrace (prefixWord ++ tailWord_7989148) baseStart_7989148 baseEnd_7989148 := by
    simpa [prefixWord, tailWord_7989148, baseEnd_7989148] using wordTrace_append hprefix tailTrace_7989148
  have hstable : (prefixWord ++ tailWord_7989148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989148).length < 2 ^ (prefixWord ++ tailWord_7989148).sum := by decide
  have hdescent : baseEnd_7989148 < baseStart_7989148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989178 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_7989178 : Nat := 118140960795 + 7989178 * 2 ^ 59
def prefixEnd_7989178 : Nat := 4983230072969 + 3 ^ 40 * 7989178 * 2
def baseEnd_7989178 : Nat := 1367429449441949512677815

theorem tailTrace_7989178 : CollatzResearch.WordTrace tailWord_7989178 prefixEnd_7989178 1367429449441949512677815 := by
  unfold tailWord_7989178
  simp only [CollatzResearch.WordTrace]
  refine ⟨72847315062645005954664047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194259506833720015879104125 72847315062645005954664047)
  ·
    refine ⟨109270972593967508931996071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72847315062645005954664047 109270972593967508931996071)
    ·
      refine ⟨163906458890951263397994107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109270972593967508931996071 163906458890951263397994107)
      ·
        refine ⟨245859688336426895096991161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163906458890951263397994107 245859688336426895096991161)
        ·
          refine ⟨184394766252320171322743371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245859688336426895096991161 184394766252320171322743371)
          ·
            refine ⟨276592149378480256984115057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184394766252320171322743371 276592149378480256984115057)
            ·
              refine ⟨207444112033860192738086293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276592149378480256984115057 207444112033860192738086293)
              ·
                refine ⟨9723942751587196534597795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207444112033860192738086293 9723942751587196534597795)
                ·
                  refine ⟨14585914127380794801896693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9723942751587196534597795 14585914127380794801896693)
                  ·
                    refine ⟨1367429449441949512677815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14585914127380794801896693 1367429449441949512677815)
                    ·
                      rfl

theorem cell23_7989178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_7989178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989178 prefixEnd_7989178 := by exact prefixLift 7989178
  have htrace : WordTrace (prefixWord ++ tailWord_7989178) baseStart_7989178 baseEnd_7989178 := by
    simpa [prefixWord, tailWord_7989178, baseEnd_7989178] using wordTrace_append hprefix tailTrace_7989178
  have hstable : (prefixWord ++ tailWord_7989178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989178).length < 2 ^ (prefixWord ++ tailWord_7989178).sum := by decide
  have hdescent : baseEnd_7989178 < baseStart_7989178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989195 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 1, 5]
def baseStart_7989195 : Nat := 118140960795 + 7989195 * 2 ^ 59
def prefixEnd_7989195 : Nat := 4983230072969 + 3 ^ 40 * 7989195 * 2
def baseEnd_7989195 : Nat := 1367432359165658323840289

theorem tailTrace_7989195 : CollatzResearch.WordTrace tailWord_7989195 prefixEnd_7989195 1367432359165658323840289 := by
  unfold tailWord_7989195
  simp only [CollatzResearch.WordTrace]
  refine ⟨291389880291518435722025039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194259920194345623814683359 291389880291518435722025039)
  ·
    refine ⟨437084820437277653583037559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291389880291518435722025039 437084820437277653583037559)
    ·
      refine ⟨655627230655916480374556339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437084820437277653583037559 655627230655916480374556339)
      ·
        refine ⟨983440845983874720561834509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655627230655916480374556339 983440845983874720561834509)
        ·
          refine ⟨368790317243953020210687941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 983440845983874720561834509 368790317243953020210687941)
          ·
            refine ⟨69148184483241191289503989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368790317243953020210687941 69148184483241191289503989)
            ·
              refine ⟨6482642295303861683390999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69148184483241191289503989 6482642295303861683390999)
              ·
                refine ⟨9723963442955792525086499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482642295303861683390999 9723963442955792525086499)
                ·
                  refine ⟨14585945164433688787629749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9723963442955792525086499 14585945164433688787629749)
                  ·
                    refine ⟨1367432359165658323840289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14585945164433688787629749 1367432359165658323840289)
                    ·
                      rfl

theorem cell23_7989195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 5].length) (baseStart_7989195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989195 prefixEnd_7989195 := by exact prefixLift 7989195
  have htrace : WordTrace (prefixWord ++ tailWord_7989195) baseStart_7989195 baseEnd_7989195 := by
    simpa [prefixWord, tailWord_7989195, baseEnd_7989195] using wordTrace_append hprefix tailTrace_7989195
  have hstable : (prefixWord ++ tailWord_7989195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989195).length < 2 ^ (prefixWord ++ tailWord_7989195).sum := by decide
  have hdescent : baseEnd_7989195 < baseStart_7989195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989209 : List Nat := [1, 2, 1, 2, 6, 1, 1, 4, 1, 1, 3]
def baseStart_7989209 : Nat := 118140960795 + 7989209 * 2 ^ 59
def prefixEnd_7989209 : Nat := 4983230072969 + 3 ^ 40 * 7989209 * 2
def baseEnd_7989209 : Nat := 4102304266226137916745803

theorem tailTrace_7989209 : CollatzResearch.WordTrace tailWord_7989209 prefixEnd_7989209 4102304266226137916745803 := by
  unfold tailWord_7989209
  simp only [CollatzResearch.WordTrace]
  refine ⟨291390390913467716113034681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194260260608978477408689787 291390390913467716113034681)
  ·
    refine ⟨218542793185100787084776011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291390390913467716113034681 218542793185100787084776011)
    ·
      refine ⟨327814189777651180627164017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218542793185100787084776011 327814189777651180627164017)
      ·
        refine ⟨245860642333238385470373013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327814189777651180627164017 245860642333238385470373013)
        ·
          refine ⟨11524717609370549318923735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 245860642333238385470373013 11524717609370549318923735)
          ·
            refine ⟨17287076414055823978385603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524717609370549318923735 17287076414055823978385603)
            ·
              refine ⟨25930614621083735967578405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17287076414055823978385603 25930614621083735967578405)
              ·
                refine ⟨4861990241453200493920951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25930614621083735967578405 4861990241453200493920951)
                ·
                  refine ⟨7292985362179800740881427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861990241453200493920951 7292985362179800740881427)
                  ·
                    refine ⟨10939478043269701111322141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7292985362179800740881427 10939478043269701111322141)
                    ·
                      refine ⟨4102304266226137916745803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10939478043269701111322141 4102304266226137916745803)
                      ·
                        rfl

theorem cell23_7989209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_7989209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989209 prefixEnd_7989209 := by exact prefixLift 7989209
  have htrace : WordTrace (prefixWord ++ tailWord_7989209) baseStart_7989209 baseEnd_7989209 := by
    simpa [prefixWord, tailWord_7989209, baseEnd_7989209] using wordTrace_append hprefix tailTrace_7989209
  have hstable : (prefixWord ++ tailWord_7989209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989209).length < 2 ^ (prefixWord ++ tailWord_7989209).sum := by decide
  have hdescent : baseEnd_7989209 < baseStart_7989209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989248 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3]
def baseStart_7989248 : Nat := 118140960795 + 7989248 * 2 ^ 59
def prefixEnd_7989248 : Nat := 4983230072969 + 3 ^ 40 * 7989248 * 2
def baseEnd_7989248 : Nat := 4102324291971663264158123

theorem tailTrace_7989248 : CollatzResearch.WordTrace tailWord_7989248 prefixEnd_7989248 4102324291971663264158123 := by
  unfold tailWord_7989248
  simp only [CollatzResearch.WordTrace]
  refine ⟨145695906680163212886852199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194261208906884283849136265 145695906680163212886852199)
  ·
    refine ⟨218543860020244819330278299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145695906680163212886852199 218543860020244819330278299)
    ·
      refine ⟨327815790030367228995417449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218543860020244819330278299 327815790030367228995417449)
      ·
        refine ⟨245861842522775421746563087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327815790030367228995417449 245861842522775421746563087)
        ·
          refine ⟨368792763784163132619844631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245861842522775421746563087 368792763784163132619844631)
          ·
            refine ⟨553189145676244698929766947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368792763784163132619844631 553189145676244698929766947)
            ·
              refine ⟨829783718514367048394650421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553189145676244698929766947 829783718514367048394650421)
              ·
                refine ⟨77792223610721910786998477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 829783718514367048394650421 77792223610721910786998477)
                ·
                  refine ⟨29172083854020716545124429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77792223610721910786998477 29172083854020716545124429)
                  ·
                    refine ⟨10939531445257768704421661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29172083854020716545124429 10939531445257768704421661)
                    ·
                      refine ⟨4102324291971663264158123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10939531445257768704421661 4102324291971663264158123)
                      ·
                        rfl

theorem cell23_7989248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_7989248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989248 prefixEnd_7989248 := by exact prefixLift 7989248
  have htrace : WordTrace (prefixWord ++ tailWord_7989248) baseStart_7989248 baseEnd_7989248 := by
    simpa [prefixWord, tailWord_7989248, baseEnd_7989248] using wordTrace_append hprefix tailTrace_7989248
  have hstable : (prefixWord ++ tailWord_7989248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989248).length < 2 ^ (prefixWord ++ tailWord_7989248).sum := by decide
  have hdescent : baseEnd_7989248 < baseStart_7989248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989275 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 3, 3, 2]
def baseStart_7989275 : Nat := 118140960795 + 7989275 * 2 ^ 59
def prefixEnd_7989275 : Nat := 4983230072969 + 3 ^ 40 * 7989275 * 2
def baseEnd_7989275 : Nat := 4102338155949334658520499

theorem tailTrace_7989275 : CollatzResearch.WordTrace tailWord_7989275 prefixEnd_7989275 4102338155949334658520499 := by
  unfold tailWord_7989275
  simp only [CollatzResearch.WordTrace]
  refine ⟨291392798131228609384937279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194261865420819072923291519 291392798131228609384937279)
  ·
    refine ⟨437089197196842914077405919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291392798131228609384937279 437089197196842914077405919)
    ·
      refine ⟨655633795795264371116108879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437089197196842914077405919 655633795795264371116108879)
      ·
        refine ⟨983450693692896556674163319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655633795795264371116108879 983450693692896556674163319)
        ·
          refine ⟨1475176040539344835011244979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983450693692896556674163319 1475176040539344835011244979)
          ·
            refine ⟨2212764060809017252516867469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475176040539344835011244979 2212764060809017252516867469)
            ·
              refine ⟨829786522803381469693825301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2212764060809017252516867469 829786522803381469693825301)
              ·
                refine ⟨38896243256408506391898061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 829786522803381469693825301 38896243256408506391898061)
                ·
                  refine ⟨14586091221153189896961773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38896243256408506391898061 14586091221153189896961773)
                  ·
                    refine ⟨5469784207932446211360665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14586091221153189896961773 5469784207932446211360665)
                    ·
                      refine ⟨4102338155949334658520499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469784207932446211360665 4102338155949334658520499)
                      ·
                        rfl

theorem cell23_7989275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3, 2].length) (baseStart_7989275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989275 prefixEnd_7989275 := by exact prefixLift 7989275
  have htrace : WordTrace (prefixWord ++ tailWord_7989275) baseStart_7989275 baseEnd_7989275 := by
    simpa [prefixWord, tailWord_7989275, baseEnd_7989275] using wordTrace_append hprefix tailTrace_7989275
  have hstable : (prefixWord ++ tailWord_7989275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989275).length < 2 ^ (prefixWord ++ tailWord_7989275).sum := by decide
  have hdescent : baseEnd_7989275 < baseStart_7989275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989300 : List Nat := [2, 5, 1, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_7989300 : Nat := 118140960795 + 7989300 * 2 ^ 59
def prefixEnd_7989300 : Nat := 4983230072969 + 3 ^ 40 * 7989300 * 2
def baseEnd_7989300 : Nat := 4102350992965697060707885

theorem tailTrace_7989300 : CollatzResearch.WordTrace tailWord_7989300 prefixEnd_7989300 4102350992965697060707885 := by
  unfold tailWord_7989300
  simp only [CollatzResearch.WordTrace]
  refine ⟨145696854978069019327298677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194262473304092025769731569 145696854978069019327298677)
  ·
    refine ⟨13659080154193970561934251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145696854978069019327298677 13659080154193970561934251)
    ·
      refine ⟨20488620231290955842901377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13659080154193970561934251 20488620231290955842901377)
      ·
        refine ⟨15366465173468216882176033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20488620231290955842901377 15366465173468216882176033)
        ·
          refine ⟨11524848880101162661632025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15366465173468216882176033 11524848880101162661632025)
          ·
            refine ⟨8643636660075871996224019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11524848880101162661632025 8643636660075871996224019)
            ·
              refine ⟨12965454990113807994336029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8643636660075871996224019 12965454990113807994336029)
              ·
                refine ⟨4862045621292677997876011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12965454990113807994336029 4862045621292677997876011)
                ·
                  refine ⟨7293068431939016996814017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862045621292677997876011 7293068431939016996814017)
                  ·
                    refine ⟨5469801323954262747610513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7293068431939016996814017 5469801323954262747610513)
                    ·
                      refine ⟨4102350992965697060707885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469801323954262747610513 4102350992965697060707885)
                      ·
                        rfl

theorem cell23_7989300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_7989300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989300 prefixEnd_7989300 := by exact prefixLift 7989300
  have htrace : WordTrace (prefixWord ++ tailWord_7989300) baseStart_7989300 baseEnd_7989300 := by
    simpa [prefixWord, tailWord_7989300, baseEnd_7989300] using wordTrace_append hprefix tailTrace_7989300
  have hstable : (prefixWord ++ tailWord_7989300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989300).length < 2 ^ (prefixWord ++ tailWord_7989300).sum := by decide
  have hdescent : baseEnd_7989300 < baseStart_7989300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989325 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7989325 : Nat := 118140960795 + 7989325 * 2 ^ 59
def prefixEnd_7989325 : Nat := 4983230072969 + 3 ^ 40 * 7989325 * 2
def baseEnd_7989325 : Nat := 4102363829982059462895269

theorem tailTrace_7989325 : CollatzResearch.WordTrace tailWord_7989325 prefixEnd_7989325 4102363829982059462895269 := by
  unfold tailWord_7989325
  simp only [CollatzResearch.WordTrace]
  refine ⟨291394621781047467924257429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194263081187364978616171619 291394621781047467924257429)
  ·
    refine ⟨13659122895986600058949567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 291394621781047467924257429 13659122895986600058949567)
    ·
      refine ⟨20488684343979900088424351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13659122895986600058949567 20488684343979900088424351)
      ·
        refine ⟨30733026515969850132636527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20488684343979900088424351 30733026515969850132636527)
        ·
          refine ⟨46099539773954775198954791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30733026515969850132636527 46099539773954775198954791)
          ·
            refine ⟨69149309660932162798432187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46099539773954775198954791 69149309660932162798432187)
            ·
              refine ⟨103723964491398244197648281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69149309660932162798432187 103723964491398244197648281)
              ·
                refine ⟨77792973368548683148236211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103723964491398244197648281 77792973368548683148236211)
                ·
                  refine ⟨116689460052823024722354317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77792973368548683148236211 116689460052823024722354317)
                  ·
                    refine ⟨43758547519808634270882869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116689460052823024722354317 43758547519808634270882869)
                    ·
                      refine ⟨4102363829982059462895269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43758547519808634270882869 4102363829982059462895269)
                      ·
                        rfl

theorem cell23_7989325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7989325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989325 prefixEnd_7989325 := by exact prefixLift 7989325
  have htrace : WordTrace (prefixWord ++ tailWord_7989325) baseStart_7989325 baseEnd_7989325 := by
    simpa [prefixWord, tailWord_7989325, baseEnd_7989325] using wordTrace_append hprefix tailTrace_7989325
  have hstable : (prefixWord ++ tailWord_7989325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989325).length < 2 ^ (prefixWord ++ tailWord_7989325).sum := by decide
  have hdescent : baseEnd_7989325 < baseStart_7989325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989379 : List Nat := [1, 1, 1, 3, 3, 5, 2, 2, 5]
def baseStart_7989379 : Nat := 118140960795 + 7989379 * 2 ^ 59
def prefixEnd_7989379 : Nat := 4983230072969 + 3 ^ 40 * 7989379 * 2
def baseEnd_7989379 : Nat := 455821284215266916846669

theorem tailTrace_7989379 : CollatzResearch.WordTrace tailWord_7989379 prefixEnd_7989379 455821284215266916846669 := by
  unfold tailWord_7989379
  simp only [CollatzResearch.WordTrace]
  refine ⟨291396591322851835146723191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194264394215234556764482127 291396591322851835146723191)
  ·
    refine ⟨437094886984277752720084787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291396591322851835146723191 437094886984277752720084787)
    ·
      refine ⟨655642330476416629080127181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437094886984277752720084787 655642330476416629080127181)
      ·
        refine ⟨245865873928656235905047693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655642330476416629080127181 245865873928656235905047693)
        ·
          refine ⟨92199702723246088464392885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245865873928656235905047693 92199702723246088464392885)
          ·
            refine ⟨8643722130304320793536833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92199702723246088464392885 8643722130304320793536833)
            ·
              refine ⟨6482791597728240595152625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8643722130304320793536833 6482791597728240595152625)
              ·
                refine ⟨4862093698296180446364469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6482791597728240595152625 4862093698296180446364469)
                ·
                  refine ⟨455821284215266916846669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4862093698296180446364469 455821284215266916846669)
                  ·
                    rfl

theorem cell23_7989379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 5].length) (baseStart_7989379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989379 prefixEnd_7989379 := by exact prefixLift 7989379
  have htrace : WordTrace (prefixWord ++ tailWord_7989379) baseStart_7989379 baseEnd_7989379 := by
    simpa [prefixWord, tailWord_7989379, baseEnd_7989379] using wordTrace_append hprefix tailTrace_7989379
  have hstable : (prefixWord ++ tailWord_7989379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989379).length < 2 ^ (prefixWord ++ tailWord_7989379).sum := by decide
  have hdescent : baseEnd_7989379 < baseStart_7989379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989388 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_7989388 : Nat := 118140960795 + 7989388 * 2 ^ 59
def prefixEnd_7989388 : Nat := 4983230072969 + 3 ^ 40 * 7989388 * 2
def baseEnd_7989388 : Nat := 1367465393087764238802493

theorem tailTrace_7989388 : CollatzResearch.WordTrace tailWord_7989388 prefixEnd_7989388 1367465393087764238802493 := by
  unfold tailWord_7989388
  simp only [CollatzResearch.WordTrace]
  refine ⟨145698459789909614841900409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194264613053212819789200545 145698459789909614841900409)
  ·
    refine ⟨109273844842432211131425307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145698459789909614841900409 109273844842432211131425307)
    ·
      refine ⟨163910767263648316697137961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109273844842432211131425307 163910767263648316697137961)
      ·
        refine ⟨122933075447736237522853471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163910767263648316697137961 122933075447736237522853471)
        ·
          refine ⟨184399613171604356284280207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122933075447736237522853471 184399613171604356284280207)
          ·
            refine ⟨276599419757406534426420311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184399613171604356284280207 276599419757406534426420311)
            ·
              refine ⟨414899129636109801639630467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276599419757406534426420311 414899129636109801639630467)
              ·
                refine ⟨622348694454164702459445701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414899129636109801639630467 622348694454164702459445701)
                ·
                  refine ⟨116690380210155881711146069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622348694454164702459445701 116690380210155881711146069)
                  ·
                    refine ⟨1367465393087764238802493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116690380210155881711146069 1367465393087764238802493)
                    ·
                      rfl

theorem cell23_7989388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_7989388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989388 prefixEnd_7989388 := by exact prefixLift 7989388
  have htrace : WordTrace (prefixWord ++ tailWord_7989388) baseStart_7989388 baseEnd_7989388 := by
    simpa [prefixWord, tailWord_7989388, baseEnd_7989388] using wordTrace_append hprefix tailTrace_7989388
  have hstable : (prefixWord ++ tailWord_7989388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989388).length < 2 ^ (prefixWord ++ tailWord_7989388).sum := by decide
  have hdescent : baseEnd_7989388 < baseStart_7989388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989412 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_7989412 : Nat := 118140960795 + 7989412 * 2 ^ 59
def prefixEnd_7989412 : Nat := 4983230072969 + 3 ^ 40 * 7989412 * 2
def baseEnd_7989412 : Nat := 4102408502799000622507369

theorem tailTrace_7989412 : CollatzResearch.WordTrace tailWord_7989412 prefixEnd_7989412 4102408502799000622507369 := by
  unfold tailWord_7989412
  simp only [CollatzResearch.WordTrace]
  refine ⟨145698897465866140891337245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194265196621154854521782993 145698897465866140891337245)
  ·
    refine ⟨54637086549699802834251467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145698897465866140891337245 54637086549699802834251467)
    ·
      refine ⟨81955629824549704251377201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54637086549699802834251467 81955629824549704251377201)
      ·
        refine ⟨61466722368412278188532901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81955629824549704251377201 61466722368412278188532901)
        ·
          refine ⟨11525010444077302160349919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61466722368412278188532901 11525010444077302160349919)
          ·
            refine ⟨17287515666115953240524879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525010444077302160349919 17287515666115953240524879)
            ·
              refine ⟨25931273499173929860787319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17287515666115953240524879 25931273499173929860787319)
              ·
                refine ⟨38896910248760894791180979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25931273499173929860787319 38896910248760894791180979)
                ·
                  refine ⟨58345365373141342186771469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38896910248760894791180979 58345365373141342186771469)
                  ·
                    refine ⟨21879512014928003320039301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58345365373141342186771469 21879512014928003320039301)
                    ·
                      refine ⟨4102408502799000622507369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21879512014928003320039301 4102408502799000622507369)
                      ·
                        rfl

theorem cell23_7989412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_7989412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989412 prefixEnd_7989412 := by exact prefixLift 7989412
  have htrace : WordTrace (prefixWord ++ tailWord_7989412) baseStart_7989412 baseEnd_7989412 := by
    simpa [prefixWord, tailWord_7989412, baseEnd_7989412] using wordTrace_append hprefix tailTrace_7989412
  have hstable : (prefixWord ++ tailWord_7989412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989412).length < 2 ^ (prefixWord ++ tailWord_7989412).sum := by decide
  have hdescent : baseEnd_7989412 < baseStart_7989412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989465 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 3, 5]
def baseStart_7989465 : Nat := 118140960795 + 7989465 * 2 ^ 59
def prefixEnd_7989465 : Nat := 4983230072969 + 3 ^ 40 * 7989465 * 2
def baseEnd_7989465 : Nat := 1367478572424562971714875

theorem tailTrace_7989465 : CollatzResearch.WordTrace tailWord_7989465 prefixEnd_7989465 1367478572424562971714875 := by
  unfold tailWord_7989465
  simp only [CollatzResearch.WordTrace]
  refine ⟨291399728000540271834353849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194266485333693514556235899 291399728000540271834353849)
  ·
    refine ⟨218549796000405203875765387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291399728000540271834353849 218549796000405203875765387)
    ·
      refine ⟨327824694000607805813648081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218549796000405203875765387 327824694000607805813648081)
      ·
        refine ⟨245868520500455854360236061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327824694000607805813648081 245868520500455854360236061)
        ·
          refine ⟨92200695187670945385088523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245868520500455854360236061 92200695187670945385088523)
          ·
            refine ⟨138301042781506418077632785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92200695187670945385088523 138301042781506418077632785)
            ·
              refine ⟨103725782086129813558224589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138301042781506418077632785 103725782086129813558224589)
              ·
                refine ⟨38897168282298680084334221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103725782086129813558224589 38897168282298680084334221)
                ·
                  refine ⟨14586438105862005031625333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38897168282298680084334221 14586438105862005031625333)
                  ·
                    refine ⟨1367478572424562971714875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14586438105862005031625333 1367478572424562971714875)
                    ·
                      rfl

theorem cell23_7989465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_7989465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989465 prefixEnd_7989465 := by exact prefixLift 7989465
  have htrace : WordTrace (prefixWord ++ tailWord_7989465) baseStart_7989465 baseEnd_7989465 := by
    simpa [prefixWord, tailWord_7989465, baseEnd_7989465] using wordTrace_append hprefix tailTrace_7989465
  have hstable : (prefixWord ++ tailWord_7989465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989465).length < 2 ^ (prefixWord ++ tailWord_7989465).sum := by decide
  have hdescent : baseEnd_7989465 < baseStart_7989465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989472 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 1, 5, 2]
def baseStart_7989472 : Nat := 118140960795 + 7989472 * 2 ^ 59
def prefixEnd_7989472 : Nat := 4983230072969 + 3 ^ 40 * 7989472 * 2
def baseEnd_7989472 : Nat := 4102439311638270387757093

theorem tailTrace_7989472 : CollatzResearch.WordTrace tailWord_7989472 prefixEnd_7989472 4102439311638270387757093 := by
  unfold tailWord_7989472
  simp only [CollatzResearch.WordTrace]
  refine ⟨145699991655757456014929335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194266655541009941353239113 145699991655757456014929335)
  ·
    refine ⟨218549987483636184022394003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145699991655757456014929335 218549987483636184022394003)
    ·
      refine ⟨327824981225454276033591005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218549987483636184022394003 327824981225454276033591005)
      ·
        refine ⟨122934367959545353512596627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327824981225454276033591005 122934367959545353512596627)
        ·
          refine ⟨184401551939318030268894941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122934367959545353512596627 184401551939318030268894941)
          ·
            refine ⟨69150581977244261350835603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184401551939318030268894941 69150581977244261350835603)
            ·
              refine ⟨103725872965866392026253405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69150581977244261350835603 103725872965866392026253405)
              ·
                refine ⟨38897202362199897009845027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103725872965866392026253405 38897202362199897009845027)
                ·
                  refine ⟨58345803543299845514767541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38897202362199897009845027 58345803543299845514767541)
                  ·
                    refine ⟨5469919082184360517009457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58345803543299845514767541 5469919082184360517009457)
                    ·
                      refine ⟨4102439311638270387757093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469919082184360517009457 4102439311638270387757093)
                      ·
                        rfl

theorem cell23_7989472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_7989472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989472 prefixEnd_7989472 := by exact prefixLift 7989472
  have htrace : WordTrace (prefixWord ++ tailWord_7989472) baseStart_7989472 baseEnd_7989472 := by
    simpa [prefixWord, tailWord_7989472, baseEnd_7989472] using wordTrace_append hprefix tailTrace_7989472
  have hstable : (prefixWord ++ tailWord_7989472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989472).length < 2 ^ (prefixWord ++ tailWord_7989472).sum := by decide
  have hdescent : baseEnd_7989472 < baseStart_7989472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989482 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_7989482 : Nat := 118140960795 + 7989482 * 2 ^ 59
def prefixEnd_7989482 : Nat := 4983230072969 + 3 ^ 40 * 7989482 * 2
def baseEnd_7989482 : Nat := 1367481482148271782877349

theorem tailTrace_7989482 : CollatzResearch.WordTrace tailWord_7989482 prefixEnd_7989482 1367481482148271782877349 := by
  unfold tailWord_7989482
  simp only [CollatzResearch.WordTrace]
  refine ⟨72850087010369670934430675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194266898694319122491815133 72850087010369670934430675)
  ·
    refine ⟨109275130515554506401646013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72850087010369670934430675 109275130515554506401646013)
    ·
      refine ⟨40978173943332939900617255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109275130515554506401646013 40978173943332939900617255)
      ·
        refine ⟨61467260914999409850925883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40978173943332939900617255 61467260914999409850925883)
        ·
          refine ⟨92200891372499114776388825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61467260914999409850925883 92200891372499114776388825)
          ·
            refine ⟨69150668529374336082291619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92200891372499114776388825 69150668529374336082291619)
            ·
              refine ⟨103726002794061504123437429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69150668529374336082291619 103726002794061504123437429)
              ·
                refine ⟨9724312761943266011572259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103726002794061504123437429 9724312761943266011572259)
                ·
                  refine ⟨14586469142914899017358389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724312761943266011572259 14586469142914899017358389)
                  ·
                    refine ⟨1367481482148271782877349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14586469142914899017358389 1367481482148271782877349)
                    ·
                      rfl

theorem cell23_7989482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_7989482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989482 prefixEnd_7989482 := by exact prefixLift 7989482
  have htrace : WordTrace (prefixWord ++ tailWord_7989482) baseStart_7989482 baseEnd_7989482 := by
    simpa [prefixWord, tailWord_7989482, baseEnd_7989482] using wordTrace_append hprefix tailTrace_7989482
  have hstable : (prefixWord ++ tailWord_7989482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989482).length < 2 ^ (prefixWord ++ tailWord_7989482).sum := by decide
  have hdescent : baseEnd_7989482 < baseStart_7989482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989515 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6]
def baseStart_7989515 : Nat := 118140960795 + 7989515 * 2 ^ 59
def prefixEnd_7989515 : Nat := 4983230072969 + 3 ^ 40 * 7989515 * 2
def baseEnd_7989515 : Nat := 4102461391306413719519395

theorem tailTrace_7989515 : CollatzResearch.WordTrace tailWord_7989515 prefixEnd_7989515 4102461391306413719519395 := by
  unfold tailWord_7989515
  simp only [CollatzResearch.WordTrace]
  refine ⟨291401551650359130373673999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194267701100239420249115999 291401551650359130373673999)
  ·
    refine ⟨437102327475538695560510999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291401551650359130373673999 437102327475538695560510999)
    ·
      refine ⟨655653491213308043340766499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437102327475538695560510999 655653491213308043340766499)
      ·
        refine ⟨983480236819962065011149749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655653491213308043340766499 983480236819962065011149749)
        ·
          refine ⟨92201272201871443594795289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 983480236819962065011149749 92201272201871443594795289)
          ·
            refine ⟨69150954151403582696096467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92201272201871443594795289 69150954151403582696096467)
            ·
              refine ⟨103726431227105374044144701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69150954151403582696096467 103726431227105374044144701)
              ·
                refine ⟨38897411710164515266554263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103726431227105374044144701 38897411710164515266554263)
                ·
                  refine ⟨58346117565246772899831395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38897411710164515266554263 58346117565246772899831395)
                  ·
                    refine ⟨87519176347870159349747093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58346117565246772899831395 87519176347870159349747093)
                    ·
                      refine ⟨4102461391306413719519395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87519176347870159349747093 4102461391306413719519395)
                      ·
                        rfl

theorem cell23_7989515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_7989515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989515 prefixEnd_7989515 := by exact prefixLift 7989515
  have htrace : WordTrace (prefixWord ++ tailWord_7989515) baseStart_7989515 baseEnd_7989515 := by
    simpa [prefixWord, tailWord_7989515, baseEnd_7989515] using wordTrace_append hprefix tailTrace_7989515
  have hstable : (prefixWord ++ tailWord_7989515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989515).length < 2 ^ (prefixWord ++ tailWord_7989515).sum := by decide
  have hdescent : baseEnd_7989515 < baseStart_7989515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989519 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 3, 2, 2]
def baseStart_7989519 : Nat := 118140960795 + 7989519 * 2 ^ 59
def prefixEnd_7989519 : Nat := 4983230072969 + 3 ^ 40 * 7989519 * 2
def baseEnd_7989519 : Nat := 4102463445229031703869377

theorem tailTrace_7989519 : CollatzResearch.WordTrace tailWord_7989519 prefixEnd_7989519 4102463445229031703869377 := by
  unfold tailWord_7989519
  simp only [CollatzResearch.WordTrace]
  refine ⟨291401697542344639056819611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194267798361563092704546407 291401697542344639056819611)
  ·
    refine ⟨437102546313516958585229417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291401697542344639056819611 437102546313516958585229417)
    ·
      refine ⟨327826909735137718938922063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437102546313516958585229417 327826909735137718938922063)
      ·
        refine ⟨491740364602706578408383095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327826909735137718938922063 491740364602706578408383095)
        ·
          refine ⟨737610546904059867612574643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491740364602706578408383095 737610546904059867612574643)
          ·
            refine ⟨1106415820356089801418861965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737610546904059867612574643 1106415820356089801418861965)
            ·
              refine ⟨414905932633533675532073237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1106415820356089801418861965 414905932633533675532073237)
              ·
                refine ⟨19448715592196891040565933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 414905932633533675532073237 19448715592196891040565933)
                ·
                  refine ⟨7293268347073834140212225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19448715592196891040565933 7293268347073834140212225)
                  ·
                    refine ⟨5469951260305375605159169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7293268347073834140212225 5469951260305375605159169)
                    ·
                      refine ⟨4102463445229031703869377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5469951260305375605159169 4102463445229031703869377)
                      ·
                        rfl

theorem cell23_7989519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 2, 2].length) (baseStart_7989519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989519 prefixEnd_7989519 := by exact prefixLift 7989519
  have htrace : WordTrace (prefixWord ++ tailWord_7989519) baseStart_7989519 baseEnd_7989519 := by
    simpa [prefixWord, tailWord_7989519, baseEnd_7989519] using wordTrace_append hprefix tailTrace_7989519
  have hstable : (prefixWord ++ tailWord_7989519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989519).length < 2 ^ (prefixWord ++ tailWord_7989519).sum := by decide
  have hdescent : baseEnd_7989519 < baseStart_7989519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989525 : List Nat := [1, 3, 2, 1, 2, 1, 4, 9]
def baseStart_7989525 : Nat := 118140960795 + 7989525 * 2 ^ 59
def prefixEnd_7989525 : Nat := 4983230072969 + 3 ^ 40 * 7989525 * 2
def baseEnd_7989525 : Nat := 151943204670850321496087

theorem tailTrace_7989525 : CollatzResearch.WordTrace tailWord_7989525 prefixEnd_7989525 151943204670850321496087 := by
  unfold tailWord_7989525
  simp only [CollatzResearch.WordTrace]
  refine ⟨291401916380322902081538029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194267944253548601387692019 291401916380322902081538029)
  ·
    refine ⟨109275718642621088280576761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291401916380322902081538029 109275718642621088280576761)
    ·
      refine ⟨81956788981965816210432571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109275718642621088280576761 81956788981965816210432571)
      ·
        refine ⟨122935183472948724315648857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81956788981965816210432571 122935183472948724315648857)
        ·
          refine ⟨92201387604711543236736643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122935183472948724315648857 92201387604711543236736643)
          ·
            refine ⟨138302081407067314855104965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92201387604711543236736643 138302081407067314855104965)
            ·
              refine ⟨25931640263825121535332181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138302081407067314855104965 25931640263825121535332181)
              ·
                refine ⟨151943204670850321496087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25931640263825121535332181 151943204670850321496087)
                ·
                  rfl

theorem cell23_7989525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 9].length) (baseStart_7989525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989525 prefixEnd_7989525 := by exact prefixLift 7989525
  have htrace : WordTrace (prefixWord ++ tailWord_7989525) baseStart_7989525 baseEnd_7989525 := by
    simpa [prefixWord, tailWord_7989525, baseEnd_7989525] using wordTrace_append hprefix tailTrace_7989525
  have hstable : (prefixWord ++ tailWord_7989525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989525).length < 2 ^ (prefixWord ++ tailWord_7989525).sum := by decide
  have hdescent : baseEnd_7989525 < baseStart_7989525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989536 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 1, 1, 4]
def baseStart_7989536 : Nat := 118140960795 + 7989536 * 2 ^ 59
def prefixEnd_7989536 : Nat := 4983230072969 + 3 ^ 40 * 7989536 * 2
def baseEnd_7989536 : Nat := 4102472174400158137356799

theorem tailTrace_7989536 : CollatzResearch.WordTrace tailWord_7989536 prefixEnd_7989536 4102472174400158137356799 := by
  unfold tailWord_7989536
  simp only [CollatzResearch.WordTrace]
  refine ⟨145701158791641525480094231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194268211722188700640125641 145701158791641525480094231)
  ·
    refine ⟨218551738187462288220141347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145701158791641525480094231 218551738187462288220141347)
    ·
      refine ⟨327827607281193432330212021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218551738187462288220141347 327827607281193432330212021)
      ·
        refine ⟨30733838182611884280957377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327827607281193432330212021 30733838182611884280957377)
        ·
          refine ⟨23050378636958913210718033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30733838182611884280957377 23050378636958913210718033)
          ·
            refine ⟨17287783977719184908038525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23050378636958913210718033 17287783977719184908038525)
            ·
              refine ⟨6482918991644694340514447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17287783977719184908038525 6482918991644694340514447)
              ·
                refine ⟨9724378487467041510771671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482918991644694340514447 9724378487467041510771671)
                ·
                  refine ⟨14586567731200562266157507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724378487467041510771671 14586567731200562266157507)
                  ·
                    refine ⟨21879851596800843399236261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14586567731200562266157507 21879851596800843399236261)
                    ·
                      refine ⟨4102472174400158137356799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21879851596800843399236261 4102472174400158137356799)
                      ·
                        rfl

theorem cell23_7989536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_7989536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989536 prefixEnd_7989536 := by exact prefixLift 7989536
  have htrace : WordTrace (prefixWord ++ tailWord_7989536) baseStart_7989536 baseEnd_7989536 := by
    simpa [prefixWord, tailWord_7989536, baseEnd_7989536] using wordTrace_append hprefix tailTrace_7989536
  have hstable : (prefixWord ++ tailWord_7989536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989536).length < 2 ^ (prefixWord ++ tailWord_7989536).sum := by decide
  have hdescent : baseEnd_7989536 < baseStart_7989536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989555 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 9]
def baseStart_7989555 : Nat := 118140960795 + 7989555 * 2 ^ 59
def prefixEnd_7989555 : Nat := 4983230072969 + 3 ^ 40 * 7989555 * 2
def baseEnd_7989555 : Nat := 1367493976844197854339737

theorem tailTrace_7989555 : CollatzResearch.WordTrace tailWord_7989555 prefixEnd_7989555 1367493976844197854339737 := by
  unfold tailWord_7989555
  simp only [CollatzResearch.WordTrace]
  refine ⟨291403010570214217205130119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194268673713476144803420079 291403010570214217205130119)
  ·
    refine ⟨437104515855321325807695179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291403010570214217205130119 437104515855321325807695179)
    ·
      refine ⟨655656773782981988711542769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437104515855321325807695179 655656773782981988711542769)
      ·
        refine ⟨491742580337236491533657077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655656773782981988711542769 491742580337236491533657077)
        ·
          refine ⟨46100866906615921081280351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491742580337236491533657077 46100866906615921081280351)
          ·
            refine ⟨69151300359923881621920527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46100866906615921081280351 69151300359923881621920527)
            ·
              refine ⟨103726950539885822432880791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69151300359923881621920527 103726950539885822432880791)
              ·
                refine ⟨155590425809828733649321187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103726950539885822432880791 155590425809828733649321187)
                ·
                  refine ⟨233385638714743100473981781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155590425809828733649321187 233385638714743100473981781)
                  ·
                    refine ⟨1367493976844197854339737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 233385638714743100473981781 1367493976844197854339737)
                    ·
                      rfl

theorem cell23_7989555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 9].length) (baseStart_7989555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989555 prefixEnd_7989555 := by exact prefixLift 7989555
  have htrace : WordTrace (prefixWord ++ tailWord_7989555) baseStart_7989555 baseEnd_7989555 := by
    simpa [prefixWord, tailWord_7989555, baseEnd_7989555] using wordTrace_append hprefix tailTrace_7989555
  have hstable : (prefixWord ++ tailWord_7989555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989555).length < 2 ^ (prefixWord ++ tailWord_7989555).sum := by decide
  have hdescent : baseEnd_7989555 < baseStart_7989555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989669 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 2, 5, 2]
def baseStart_7989669 : Nat := 118140960795 + 7989669 * 2 ^ 59
def prefixEnd_7989669 : Nat := 4983230072969 + 3 ^ 40 * 7989669 * 2
def baseEnd_7989669 : Nat := 4102540467327206116993687

theorem tailTrace_7989669 : CollatzResearch.WordTrace tailWord_7989669 prefixEnd_7989669 4102540467327206116993687 := by
  unfold tailWord_7989669
  simp only [CollatzResearch.WordTrace]
  refine ⟨291407168491801214674780061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194271445661200809783186707 291407168491801214674780061)
  ·
    refine ⟨109277688184425455503042523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291407168491801214674780061 109277688184425455503042523)
    ·
      refine ⟨163916532276638183254563785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109277688184425455503042523 163916532276638183254563785)
      ·
        refine ⟨122937399207478637440922839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163916532276638183254563785 122937399207478637440922839)
        ·
          refine ⟨184406098811217956161384259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122937399207478637440922839 184406098811217956161384259)
          ·
            refine ⟨276609148216826934242076389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184406098811217956161384259 276609148216826934242076389)
            ·
              refine ⟨51864215290655050170389323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276609148216826934242076389 51864215290655050170389323)
              ·
                refine ⟨77796322935982575255583985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51864215290655050170389323 77796322935982575255583985)
                ·
                  refine ⟨58347242201986931441687989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77796322935982575255583985 58347242201986931441687989)
                  ·
                    refine ⟨5470053956436274822658249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58347242201986931441687989 5470053956436274822658249)
                    ·
                      refine ⟨4102540467327206116993687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470053956436274822658249 4102540467327206116993687)
                      ·
                        rfl

theorem cell23_7989669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_7989669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989669 prefixEnd_7989669 := by exact prefixLift 7989669
  have htrace : WordTrace (prefixWord ++ tailWord_7989669) baseStart_7989669 baseEnd_7989669 := by
    simpa [prefixWord, tailWord_7989669, baseEnd_7989669] using wordTrace_append hprefix tailTrace_7989669
  have hstable : (prefixWord ++ tailWord_7989669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989669).length < 2 ^ (prefixWord ++ tailWord_7989669).sum := by decide
  have hdescent : baseEnd_7989669 < baseStart_7989669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989699 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 4, 4, 2]
def baseStart_7989699 : Nat := 118140960795 + 7989699 * 2 ^ 59
def prefixEnd_7989699 : Nat := 4983230072969 + 3 ^ 40 * 7989699 * 2
def baseEnd_7989699 : Nat := 4102555871746840999618549

theorem tailTrace_7989699 : CollatzResearch.WordTrace tailWord_7989699 prefixEnd_7989699 4102555871746840999618549 := by
  unfold tailWord_7989699
  simp only [CollatzResearch.WordTrace]
  refine ⟨291408262681692529798372151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194272175121128353198914767 291408262681692529798372151)
  ·
    refine ⟨437112394022538794697558227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291408262681692529798372151 437112394022538794697558227)
    ·
      refine ⟨655668591033808192046337341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437112394022538794697558227 655668591033808192046337341)
      ·
        refine ⟨245875721637678072017376503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655668591033808192046337341 245875721637678072017376503)
        ·
          refine ⟨368813582456517108026064755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245875721637678072017376503 368813582456517108026064755)
          ·
            refine ⟨553220373684775662039097133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368813582456517108026064755 553220373684775662039097133)
            ·
              refine ⟨207457640131790873264661425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553220373684775662039097133 207457640131790873264661425)
              ·
                refine ⟨155593230098843154948496069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207457640131790873264661425 155593230098843154948496069)
                ·
                  refine ⟨29173730643533091552843013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155593230098843154948496069 29173730643533091552843013)
                  ·
                    refine ⟨5470074495662454666158065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29173730643533091552843013 5470074495662454666158065)
                    ·
                      refine ⟨4102555871746840999618549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470074495662454666158065 4102555871746840999618549)
                      ·
                        rfl

theorem cell23_7989699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_7989699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989699 prefixEnd_7989699 := by exact prefixLift 7989699
  have htrace : WordTrace (prefixWord ++ tailWord_7989699) baseStart_7989699 baseEnd_7989699 := by
    simpa [prefixWord, tailWord_7989699, baseEnd_7989699] using wordTrace_append hprefix tailTrace_7989699
  have hstable : (prefixWord ++ tailWord_7989699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989699).length < 2 ^ (prefixWord ++ tailWord_7989699).sum := by decide
  have hdescent : baseEnd_7989699 < baseStart_7989699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989716 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7989716 : Nat := 118140960795 + 7989716 * 2 ^ 59
def prefixEnd_7989716 : Nat := 4983230072969 + 3 ^ 40 * 7989716 * 2
def baseEnd_7989716 : Nat := 4102564600917967433105971

theorem tailTrace_7989716 : CollatzResearch.WordTrace tailWord_7989716 prefixEnd_7989716 4102564600917967433105971 := by
  unfold tailWord_7989716
  simp only [CollatzResearch.WordTrace]
  refine ⟨145704441361315470850870501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194272588481753961134494001 145704441361315470850870501)
  ·
    refine ⟨27319582755246650784538219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145704441361315470850870501 27319582755246650784538219)
    ·
      refine ⟨40979374132869976176807329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27319582755246650784538219 40979374132869976176807329)
      ·
        refine ⟨30734530599652482132605497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40979374132869976176807329 30734530599652482132605497)
        ·
          refine ⟨23050897949739361599454123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30734530599652482132605497 23050897949739361599454123)
          ·
            refine ⟨34576346924609042399181185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23050897949739361599454123 34576346924609042399181185)
            ·
              refine ⟨25932260193456781799385889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34576346924609042399181185 25932260193456781799385889)
              ·
                refine ⟨19449195145092586349539417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25932260193456781799385889 19449195145092586349539417)
                ·
                  refine ⟨14586896358819439762154563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19449195145092586349539417 14586896358819439762154563)
                  ·
                    refine ⟨21880344538229159643231845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14586896358819439762154563 21880344538229159643231845)
                    ·
                      refine ⟨4102564600917967433105971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21880344538229159643231845 4102564600917967433105971)
                      ·
                        rfl

theorem cell23_7989716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7989716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989716 prefixEnd_7989716 := by exact prefixLift 7989716
  have htrace : WordTrace (prefixWord ++ tailWord_7989716) baseStart_7989716 baseEnd_7989716 := by
    simpa [prefixWord, tailWord_7989716, baseEnd_7989716] using wordTrace_append hprefix tailTrace_7989716
  have hstable : (prefixWord ++ tailWord_7989716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989716).length < 2 ^ (prefixWord ++ tailWord_7989716).sum := by decide
  have hdescent : baseEnd_7989716 < baseStart_7989716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989733 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7989733 : Nat := 118140960795 + 7989733 * 2 ^ 59
def prefixEnd_7989733 : Nat := 4983230072969 + 3 ^ 40 * 7989733 * 2
def baseEnd_7989733 : Nat := 4102573330089093866593393

theorem tailTrace_7989733 : CollatzResearch.WordTrace tailWord_7989733 prefixEnd_7989733 4102573330089093866593393 := by
  unfold tailWord_7989733
  simp only [CollatzResearch.WordTrace]
  refine ⟨291409502763569353605109853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194273001842379569070073235 291409502763569353605109853)
  ·
    refine ⟨109278563536338507601916195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291409502763569353605109853 109278563536338507601916195)
    ·
      refine ⟨163917845304507761402874293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109278563536338507601916195 163917845304507761402874293)
      ·
        refine ⟨15367297997297602631519465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163917845304507761402874293 15367297997297602631519465)
        ·
          refine ⟨11525473497973201973639599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15367297997297602631519465 11525473497973201973639599)
          ·
            refine ⟨17288210246959802960459399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525473497973201973639599 17288210246959802960459399)
            ·
              refine ⟨25932315370439704440689099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17288210246959802960459399 25932315370439704440689099)
              ·
                refine ⟨38898473055659556661033649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25932315370439704440689099 38898473055659556661033649)
                ·
                  refine ⟨29173854791744667495775237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38898473055659556661033649 29173854791744667495775237)
                  ·
                    refine ⟨5470097773452125155457857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29173854791744667495775237 5470097773452125155457857)
                    ·
                      refine ⟨4102573330089093866593393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470097773452125155457857 4102573330089093866593393)
                      ·
                        rfl

theorem cell23_7989733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7989733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989733 prefixEnd_7989733 := by exact prefixLift 7989733
  have htrace : WordTrace (prefixWord ++ tailWord_7989733) baseStart_7989733 baseEnd_7989733 := by
    simpa [prefixWord, tailWord_7989733, baseEnd_7989733] using wordTrace_append hprefix tailTrace_7989733
  have hstable : (prefixWord ++ tailWord_7989733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989733).length < 2 ^ (prefixWord ++ tailWord_7989733).sum := by decide
  have hdescent : baseEnd_7989733 < baseStart_7989733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989773 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 8]
def baseStart_7989773 : Nat := 118140960795 + 7989773 * 2 ^ 59
def prefixEnd_7989773 : Nat := 4983230072969 + 3 ^ 40 * 7989773 * 2
def baseEnd_7989773 : Nat := 455843763257252634454801

theorem tailTrace_7989773 : CollatzResearch.WordTrace tailWord_7989773 prefixEnd_7989773 455843763257252634454801 := by
  unfold tailWord_7989773
  simp only [CollatzResearch.WordTrace]
  refine ⟨291410961683424440436565973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194273974455616293624377315 291410961683424440436565973)
  ·
    refine ⟨6829944414455260322732015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 291410961683424440436565973 6829944414455260322732015)
    ·
      refine ⟨10244916621682890484098023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829944414455260322732015 10244916621682890484098023)
      ·
        refine ⟨15367374932524335726147035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10244916621682890484098023 15367374932524335726147035)
        ·
          refine ⟨23051062398786503589220553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15367374932524335726147035 23051062398786503589220553)
          ·
            refine ⟨17288296799089877691915415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23051062398786503589220553 17288296799089877691915415)
            ·
              refine ⟨25932445198634816537873123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17288296799089877691915415 25932445198634816537873123)
              ·
                refine ⟨38898667797952224806809685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25932445198634816537873123 38898667797952224806809685)
                ·
                  refine ⟨455843763257252634454801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38898667797952224806809685 455843763257252634454801)
                  ·
                    rfl

theorem cell23_7989773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_7989773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989773 prefixEnd_7989773 := by exact prefixLift 7989773
  have htrace : WordTrace (prefixWord ++ tailWord_7989773) baseStart_7989773 baseEnd_7989773 := by
    simpa [prefixWord, tailWord_7989773, baseEnd_7989773] using wordTrace_append hprefix tailTrace_7989773
  have hstable : (prefixWord ++ tailWord_7989773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989773).length < 2 ^ (prefixWord ++ tailWord_7989773).sum := by decide
  have hdescent : baseEnd_7989773 < baseStart_7989773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989829 : List Nat := [1, 3, 1, 1, 1, 7, 9]
def baseStart_7989829 : Nat := 118140960795 + 7989829 * 2 ^ 59
def prefixEnd_7989829 : Nat := 4983230072969 + 3 ^ 40 * 7989829 * 2
def baseEnd_7989829 : Nat := 50649662027554635691271

theorem tailTrace_7989829 : CollatzResearch.WordTrace tailWord_7989829 prefixEnd_7989829 50649662027554635691271 := by
  unfold tailWord_7989829
  simp only [CollatzResearch.WordTrace]
  refine ⟨291413004171221562000604541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194275336114147708000403027 291413004171221562000604541)
  ·
    refine ⟨109279876564208085750226703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291413004171221562000604541 109279876564208085750226703)
    ·
      refine ⟨163919814846312128625340055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109279876564208085750226703 163919814846312128625340055)
      ·
        refine ⟨245879722269468192938010083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163919814846312128625340055 245879722269468192938010083)
        ·
          refine ⟨368819583404202289407015125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245879722269468192938010083 368819583404202289407015125)
          ·
            refine ⟨8644208986035991157976917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 368819583404202289407015125 8644208986035991157976917)
            ·
              refine ⟨50649662027554635691271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8644208986035991157976917 50649662027554635691271)
              ·
                rfl

theorem cell23_7989829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 9].length) (baseStart_7989829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989829 prefixEnd_7989829 := by exact prefixLift 7989829
  have htrace : WordTrace (prefixWord ++ tailWord_7989829) baseStart_7989829 baseEnd_7989829 := by
    simpa [prefixWord, tailWord_7989829, baseEnd_7989829] using wordTrace_append hprefix tailTrace_7989829
  have hstable : (prefixWord ++ tailWord_7989829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989829).length < 2 ^ (prefixWord ++ tailWord_7989829).sum := by decide
  have hdescent : baseEnd_7989829 < baseStart_7989829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989854 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7989854 : Nat := 118140960795 + 7989854 * 2 ^ 59
def prefixEnd_7989854 : Nat := 4983230072969 + 3 ^ 40 * 7989854 * 2
def baseEnd_7989854 : Nat := 1367545153749429297726779

theorem tailTrace_7989854 : CollatzResearch.WordTrace tailWord_7989854 prefixEnd_7989854 1367545153749429297726779 := by
  unfold tailWord_7989854
  simp only [CollatzResearch.WordTrace]
  refine ⟨36426739499516373908783077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194275943997420660846843077 36426739499516373908783077)
  ·
    refine ⟨6830013656159320107896827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36426739499516373908783077 6830013656159320107896827)
    ·
      refine ⟨10245020484238980161845241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830013656159320107896827 10245020484238980161845241)
      ·
        refine ⟨7683765363179235121383931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10245020484238980161845241 7683765363179235121383931)
        ·
          refine ⟨11525648044768852682075897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7683765363179235121383931 11525648044768852682075897)
          ·
            refine ⟨8644236033576639511556923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11525648044768852682075897 8644236033576639511556923)
            ·
              refine ⟨12966354050364959267335385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8644236033576639511556923 12966354050364959267335385)
              ·
                refine ⟨9724765537773719450501539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12966354050364959267335385 9724765537773719450501539)
                ·
                  refine ⟨14587148306660579175752309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724765537773719450501539 14587148306660579175752309)
                  ·
                    refine ⟨1367545153749429297726779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14587148306660579175752309 1367545153749429297726779)
                    ·
                      rfl

theorem cell23_7989854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7989854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989854 prefixEnd_7989854 := by exact prefixLift 7989854
  have htrace : WordTrace (prefixWord ++ tailWord_7989854) baseStart_7989854 baseEnd_7989854 := by
    simpa [prefixWord, tailWord_7989854, baseEnd_7989854] using wordTrace_append hprefix tailTrace_7989854
  have hstable : (prefixWord ++ tailWord_7989854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989854).length < 2 ^ (prefixWord ++ tailWord_7989854).sum := by decide
  have hdescent : baseEnd_7989854 < baseStart_7989854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989877 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7989877 : Nat := 118140960795 + 7989877 * 2 ^ 59
def prefixEnd_7989877 : Nat := 4983230072969 + 3 ^ 40 * 7989877 * 2
def baseEnd_7989877 : Nat := 4102647271303341303192731

theorem tailTrace_7989877 : CollatzResearch.WordTrace tailWord_7989877 prefixEnd_7989877 4102647271303341303192731 := by
  unfold tailWord_7989877
  simp only [CollatzResearch.WordTrace]
  refine ⟨291414754875047666198351885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194276503250031777465567923 291414754875047666198351885)
  ·
    refine ⟨109280533078142874824381957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291414754875047666198351885 109280533078142874824381957)
    ·
      refine ⟨20490099952151789029571617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109280533078142874824381957 20490099952151789029571617)
      ·
        refine ⟨15367574964113841772178713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20490099952151789029571617 15367574964113841772178713)
        ·
          refine ⟨11525681223085381329134035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15367574964113841772178713 11525681223085381329134035)
          ·
            refine ⟨17288521834628071993701053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525681223085381329134035 17288521834628071993701053)
            ·
              refine ⟨6483195687985526997637895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17288521834628071993701053 6483195687985526997637895)
              ·
                refine ⟨9724793531978290496456843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483195687985526997637895 9724793531978290496456843)
                ·
                  refine ⟨14587190297967435744685265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724793531978290496456843 14587190297967435744685265)
                  ·
                    refine ⟨10940392723475576808513949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14587190297967435744685265 10940392723475576808513949)
                    ·
                      refine ⟨4102647271303341303192731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10940392723475576808513949 4102647271303341303192731)
                      ·
                        rfl

theorem cell23_7989877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7989877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989877 prefixEnd_7989877 := by exact prefixLift 7989877
  have htrace : WordTrace (prefixWord ++ tailWord_7989877) baseStart_7989877 baseEnd_7989877 := by
    simpa [prefixWord, tailWord_7989877, baseEnd_7989877] using wordTrace_append hprefix tailTrace_7989877
  have hstable : (prefixWord ++ tailWord_7989877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989877).length < 2 ^ (prefixWord ++ tailWord_7989877).sum := by decide
  have hdescent : baseEnd_7989877 < baseStart_7989877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989899 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5]
def baseStart_7989899 : Nat := 118140960795 + 7989899 * 2 ^ 59
def prefixEnd_7989899 : Nat := 4983230072969 + 3 ^ 40 * 7989899 * 2
def baseEnd_7989899 : Nat := 4102658567877740217117629

theorem tailTrace_7989899 : CollatzResearch.WordTrace tailWord_7989899 prefixEnd_7989899 4102658567877740217117629 := by
  unfold tailWord_7989899
  simp only [CollatzResearch.WordTrace]
  refine ⟨291415557280967963955652751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194277038187311975970435167 291415557280967963955652751)
  ·
    refine ⟨437123335921451945933479127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291415557280967963955652751 437123335921451945933479127)
    ·
      refine ⟨655685003882177918900218691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437123335921451945933479127 655685003882177918900218691)
      ·
        refine ⟨983527505823266878350328037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655685003882177918900218691 983527505823266878350328037)
        ·
          refine ⟨184411407341862539690686507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 983527505823266878350328037 184411407341862539690686507)
          ·
            refine ⟨276617111012793809536029761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184411407341862539690686507 276617111012793809536029761)
            ·
              refine ⟨207462833259595357152022321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276617111012793809536029761 207462833259595357152022321)
              ·
                refine ⟨155597124944696517864016741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207462833259595357152022321 155597124944696517864016741)
                ·
                  refine ⟨29174460927130597099503139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155597124944696517864016741 29174460927130597099503139)
                  ·
                    refine ⟨43761691390695895649254709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29174460927130597099503139 43761691390695895649254709)
                    ·
                      refine ⟨4102658567877740217117629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43761691390695895649254709 4102658567877740217117629)
                      ·
                        rfl

theorem cell23_7989899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_7989899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989899 prefixEnd_7989899 := by exact prefixLift 7989899
  have htrace : WordTrace (prefixWord ++ tailWord_7989899) baseStart_7989899 baseEnd_7989899 := by
    simpa [prefixWord, tailWord_7989899, baseEnd_7989899] using wordTrace_append hprefix tailTrace_7989899
  have hstable : (prefixWord ++ tailWord_7989899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989899).length < 2 ^ (prefixWord ++ tailWord_7989899).sum := by decide
  have hdescent : baseEnd_7989899 < baseStart_7989899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989906 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_7989906 : Nat := 118140960795 + 7989906 * 2 ^ 59
def prefixEnd_7989906 : Nat := 4983230072969 + 3 ^ 40 * 7989906 * 2
def baseEnd_7989906 : Nat := 1367554054080773896576699

theorem tailTrace_7989906 : CollatzResearch.WordTrace tailWord_7989906 prefixEnd_7989906 1367554054080773896576699 := by
  unfold tailWord_7989906
  simp only [CollatzResearch.WordTrace]
  refine ⟨72853953147985651037789393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194277208394628402767438381 72853953147985651037789393)
  ·
    refine ⟨54640464860989238278342045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72853953147985651037789393 54640464860989238278342045)
    ·
      refine ⟨20490174322870964354378267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54640464860989238278342045 20490174322870964354378267)
      ·
        refine ⟨30735261484306446531567401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20490174322870964354378267 30735261484306446531567401)
        ·
          refine ⟨23051446113229834898675551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30735261484306446531567401 23051446113229834898675551)
          ·
            refine ⟨34577169169844752348013327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23051446113229834898675551 34577169169844752348013327)
            ·
              refine ⟨51865753754767128522019991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34577169169844752348013327 51865753754767128522019991)
              ·
                refine ⟨77798630632150692783029987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51865753754767128522019991 77798630632150692783029987)
                ·
                  refine ⟨116697945948226039174544981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77798630632150692783029987 116697945948226039174544981)
                  ·
                    refine ⟨1367554054080773896576699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116697945948226039174544981 1367554054080773896576699)
                    ·
                      rfl

theorem cell23_7989906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_7989906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989906 prefixEnd_7989906 := by exact prefixLift 7989906
  have htrace : WordTrace (prefixWord ++ tailWord_7989906) baseStart_7989906 baseEnd_7989906 := by
    simpa [prefixWord, tailWord_7989906, baseEnd_7989906] using wordTrace_append hprefix tailTrace_7989906
  have hstable : (prefixWord ++ tailWord_7989906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989906).length < 2 ^ (prefixWord ++ tailWord_7989906).sum := by decide
  have hdescent : baseEnd_7989906 < baseStart_7989906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989913 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 1, 4, 2]
def baseStart_7989913 : Nat := 118140960795 + 7989913 * 2 ^ 59
def prefixEnd_7989913 : Nat := 4983230072969 + 3 ^ 40 * 7989913 * 2
def baseEnd_7989913 : Nat := 4102665756606903162342565

theorem tailTrace_7989913 : CollatzResearch.WordTrace tailWord_7989913 prefixEnd_7989913 4102665756606903162342565 := by
  unfold tailWord_7989913
  simp only [CollatzResearch.WordTrace]
  refine ⟨291416067902917244346662393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194277378601944829564441595 291416067902917244346662393)
  ·
    refine ⟨218562050927187933259996795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291416067902917244346662393 218562050927187933259996795)
    ·
      refine ⟨327843076390781899889995193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218562050927187933259996795 327843076390781899889995193)
      ·
        refine ⟨245882307293086424917496395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327843076390781899889995193 245882307293086424917496395)
        ·
          refine ⟨368823460939629637376244593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245882307293086424917496395 368823460939629637376244593)
          ·
            refine ⟨276617595704722228032183445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368823460939629637376244593 276617595704722228032183445)
            ·
              refine ⟨12966449798658854439008599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276617595704722228032183445 12966449798658854439008599)
              ·
                refine ⟨19449674697988281658512899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12966449798658854439008599 19449674697988281658512899)
                ·
                  refine ⟨29174512046982422487769349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19449674697988281658512899 29174512046982422487769349)
                  ·
                    refine ⟨5470221008809204216456753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29174512046982422487769349 5470221008809204216456753)
                    ·
                      refine ⟨4102665756606903162342565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470221008809204216456753 4102665756606903162342565)
                      ·
                        rfl

theorem cell23_7989913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_7989913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989913 prefixEnd_7989913 := by exact prefixLift 7989913
  have htrace : WordTrace (prefixWord ++ tailWord_7989913) baseStart_7989913 baseEnd_7989913 := by
    simpa [prefixWord, tailWord_7989913, baseEnd_7989913] using wordTrace_append hprefix tailTrace_7989913
  have hstable : (prefixWord ++ tailWord_7989913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989913).length < 2 ^ (prefixWord ++ tailWord_7989913).sum := by decide
  have hdescent : baseEnd_7989913 < baseStart_7989913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989934 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7989934 : Nat := 118140960795 + 7989934 * 2 ^ 59
def prefixEnd_7989934 : Nat := 4983230072969 + 3 ^ 40 * 7989934 * 2
def baseEnd_7989934 : Nat := 4102676539700647580179969

theorem tailTrace_7989934 : CollatzResearch.WordTrace tailWord_7989934 prefixEnd_7989934 4102676539700647580179969 := by
  unfold tailWord_7989934
  simp only [CollatzResearch.WordTrace]
  refine ⟨36427104229480145616647107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194277889223894109955451237 36427104229480145616647107)
  ·
    refine ⟨54640656344220218424970661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36427104229480145616647107 54640656344220218424970661)
    ·
      refine ⟨10245123064541290954681999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54640656344220218424970661 10245123064541290954681999)
      ·
        refine ⟨15367684596811936432022999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245123064541290954681999 15367684596811936432022999)
        ·
          refine ⟨23051526895217904648034499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15367684596811936432022999 23051526895217904648034499)
          ·
            refine ⟨34577290342826856972051749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23051526895217904648034499 34577290342826856972051749)
            ·
              refine ⟨6483241939280035682259703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34577290342826856972051749 6483241939280035682259703)
              ·
                refine ⟨9724862908920053523389555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483241939280035682259703 9724862908920053523389555)
                ·
                  refine ⟨14587294363380080285084333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724862908920053523389555 14587294363380080285084333)
                  ·
                    refine ⟨5470235386267530106906625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14587294363380080285084333 5470235386267530106906625)
                    ·
                      refine ⟨4102676539700647580179969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470235386267530106906625 4102676539700647580179969)
                      ·
                        rfl

theorem cell23_7989934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7989934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989934 prefixEnd_7989934 := by exact prefixLift 7989934
  have htrace : WordTrace (prefixWord ++ tailWord_7989934) baseStart_7989934 baseEnd_7989934 := by
    simpa [prefixWord, tailWord_7989934, baseEnd_7989934] using wordTrace_append hprefix tailTrace_7989934
  have hstable : (prefixWord ++ tailWord_7989934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989934).length < 2 ^ (prefixWord ++ tailWord_7989934).sum := by decide
  have hdescent : baseEnd_7989934 < baseStart_7989934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989946 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_7989946 : Nat := 118140960795 + 7989946 * 2 ^ 59
def prefixEnd_7989946 : Nat := 4983230072969 + 3 ^ 40 * 7989946 * 2
def baseEnd_7989946 : Nat := 4102682701468501533229913

theorem tailTrace_7989946 : CollatzResearch.WordTrace tailWord_7989946 prefixEnd_7989946 4102682701468501533229913 := by
  unfold tailWord_7989946
  simp only [CollatzResearch.WordTrace]
  refine ⟨72854317877949422745653423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194278181007865127321742461 72854317877949422745653423)
  ·
    refine ⟨109281476816924134118480135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72854317877949422745653423 109281476816924134118480135)
    ·
      refine ⟨163922215225386201177720203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109281476816924134118480135 163922215225386201177720203)
      ·
        refine ⟨245883322838079301766580305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163922215225386201177720203 245883322838079301766580305)
        ·
          refine ⟨184412492128559476324935229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245883322838079301766580305 184412492128559476324935229)
          ·
            refine ⟨69154684548209803621850711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184412492128559476324935229 69154684548209803621850711)
            ·
              refine ⟨103732026822314705432776067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69154684548209803621850711 103732026822314705432776067)
              ·
                refine ⟨155598040233472058149164101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103732026822314705432776067 155598040233472058149164101)
                ·
                  refine ⟨29174632543776010902968269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155598040233472058149164101 29174632543776010902968269)
                  ·
                    refine ⟨10940487203916004088613101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29174632543776010902968269 10940487203916004088613101)
                    ·
                      refine ⟨4102682701468501533229913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10940487203916004088613101 4102682701468501533229913)
                      ·
                        rfl

theorem cell23_7989946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_7989946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989946 prefixEnd_7989946 := by exact prefixLift 7989946
  have htrace : WordTrace (prefixWord ++ tailWord_7989946) baseStart_7989946 baseEnd_7989946 := by
    simpa [prefixWord, tailWord_7989946, baseEnd_7989946] using wordTrace_append hprefix tailTrace_7989946
  have hstable : (prefixWord ++ tailWord_7989946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989946).length < 2 ^ (prefixWord ++ tailWord_7989946).sum := by decide
  have hdescent : baseEnd_7989946 < baseStart_7989946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989964 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7989964 : Nat := 118140960795 + 7989964 * 2 ^ 59
def prefixEnd_7989964 : Nat := 4983230072969 + 3 ^ 40 * 7989964 * 2
def baseEnd_7989964 : Nat := 4102691944120282462804831

theorem tailTrace_7989964 : CollatzResearch.WordTrace tailWord_7989964 prefixEnd_7989964 4102691944120282462804831 := by
  unfold tailWord_7989964
  simp only [CollatzResearch.WordTrace]
  refine ⟨145708964012866240028384473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194278618683821653371179297 145708964012866240028384473)
  ·
    refine ⟨109281723009649680021288355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145708964012866240028384473 109281723009649680021288355)
    ·
      refine ⟨163922584514474520031932533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109281723009649680021288355 163922584514474520031932533)
      ·
        refine ⟨15367742298231986252993675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163922584514474520031932533 15367742298231986252993675)
        ·
          refine ⟨23051613447347979379490513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15367742298231986252993675 23051613447347979379490513)
          ·
            refine ⟨17288710085510984534617885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23051613447347979379490513 17288710085510984534617885)
            ·
              refine ⟨6483266282066619200481707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17288710085510984534617885 6483266282066619200481707)
              ·
                refine ⟨9724899423099928800722561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483266282066619200481707 9724899423099928800722561)
                ·
                  refine ⟨7293674567324946600541921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9724899423099928800722561 7293674567324946600541921)
                  ·
                    refine ⟨5470255925493709950406441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7293674567324946600541921 5470255925493709950406441)
                    ·
                      refine ⟨4102691944120282462804831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470255925493709950406441 4102691944120282462804831)
                      ·
                        rfl

theorem cell23_7989964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7989964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989964 prefixEnd_7989964 := by exact prefixLift 7989964
  have htrace : WordTrace (prefixWord ++ tailWord_7989964) baseStart_7989964 baseEnd_7989964 := by
    simpa [prefixWord, tailWord_7989964, baseEnd_7989964] using wordTrace_append hprefix tailTrace_7989964
  have hstable : (prefixWord ++ tailWord_7989964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989964).length < 2 ^ (prefixWord ++ tailWord_7989964).sum := by decide
  have hdescent : baseEnd_7989964 < baseStart_7989964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7989966 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_7989966 : Nat := 118140960795 + 7989966 * 2 ^ 59
def prefixEnd_7989966 : Nat := 4983230072969 + 3 ^ 40 * 7989966 * 2
def baseEnd_7989966 : Nat := 1367564323693863818326607

theorem tailTrace_7989966 : CollatzResearch.WordTrace tailWord_7989966 prefixEnd_7989966 1367564323693863818326607 := by
  unfold tailWord_7989966
  simp only [CollatzResearch.WordTrace]
  refine ⟨36427250121465654299792719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194278667314483489598894501 36427250121465654299792719)
  ·
    refine ⟨54640875182198481449689079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36427250121465654299792719 54640875182198481449689079)
    ·
      refine ⟨81961312773297722174533619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54640875182198481449689079 81961312773297722174533619)
      ·
        refine ⟨122941969159946583261800429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81961312773297722174533619 122941969159946583261800429)
        ·
          refine ⟨46103238434979968723175161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122941969159946583261800429 46103238434979968723175161)
          ·
            refine ⟨34577428826234976542381371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46103238434979968723175161 34577428826234976542381371)
            ·
              refine ⟨51866143239352464813572057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34577428826234976542381371 51866143239352464813572057)
              ·
                refine ⟨38899607429514348610179043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51866143239352464813572057 38899607429514348610179043)
                ·
                  refine ⟨58349411144271522915268565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38899607429514348610179043 58349411144271522915268565)
                  ·
                    refine ⟨1367564323693863818326607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58349411144271522915268565 1367564323693863818326607)
                    ·
                      rfl

theorem cell23_7989966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_7989966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7989966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7989966 prefixEnd_7989966 := by exact prefixLift 7989966
  have htrace : WordTrace (prefixWord ++ tailWord_7989966) baseStart_7989966 baseEnd_7989966 := by
    simpa [prefixWord, tailWord_7989966, baseEnd_7989966] using wordTrace_append hprefix tailTrace_7989966
  have hstable : (prefixWord ++ tailWord_7989966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7989966).length < 2 ^ (prefixWord ++ tailWord_7989966).sum := by decide
  have hdescent : baseEnd_7989966 < baseStart_7989966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7989966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990004 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7990004 : Nat := 118140960795 + 7990004 * 2 ^ 59
def prefixEnd_7990004 : Nat := 4983230072969 + 3 ^ 40 * 7990004 * 2
def baseEnd_7990004 : Nat := 455856942594051367367183

theorem tailTrace_7990004 : CollatzResearch.WordTrace tailWord_7990004 prefixEnd_7990004 455856942594051367367183 := by
  unfold tailWord_7990004
  simp only [CollatzResearch.WordTrace]
  refine ⟨145709693472793783444112533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194279591297058377925483377 145709693472793783444112533)
  ·
    refine ⟨6830141881537208598942775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145709693472793783444112533 6830141881537208598942775)
    ·
      refine ⟨10245212822305812898414163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830141881537208598942775 10245212822305812898414163)
      ·
        refine ⟨15367819233458719347621245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245212822305812898414163 15367819233458719347621245)
        ·
          refine ⟨5762932212547019755357967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15367819233458719347621245 5762932212547019755357967)
          ·
            refine ⟨8644398318820529633036951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5762932212547019755357967 8644398318820529633036951)
            ·
              refine ⟨12966597478230794449555427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8644398318820529633036951 12966597478230794449555427)
              ·
                refine ⟨19449896217346191674333141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12966597478230794449555427 19449896217346191674333141)
                ·
                  refine ⟨455856942594051367367183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19449896217346191674333141 455856942594051367367183)
                  ·
                    rfl

theorem cell23_7990004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7990004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990004 prefixEnd_7990004 := by exact prefixLift 7990004
  have htrace : WordTrace (prefixWord ++ tailWord_7990004) baseStart_7990004 baseEnd_7990004 := by
    simpa [prefixWord, tailWord_7990004, baseEnd_7990004] using wordTrace_append hprefix tailTrace_7990004
  have hstable : (prefixWord ++ tailWord_7990004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990004).length < 2 ^ (prefixWord ++ tailWord_7990004).sum := by decide
  have hdescent : baseEnd_7990004 < baseStart_7990004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990103 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 1, 6]
def baseStart_7990103 : Nat := 118140960795 + 7990103 * 2 ^ 59
def prefixEnd_7990103 : Nat := 4983230072969 + 3 ^ 40 * 7990103 * 2
def baseEnd_7990103 : Nat := 1367587772643752472988897

theorem tailTrace_7990103 : CollatzResearch.WordTrace tailWord_7990103 prefixEnd_7990103 1367587772643752472988897 := by
  unfold tailWord_7990103
  simp only [CollatzResearch.WordTrace]
  refine ⟨291422997772228906796078963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194281998514819271197385975 291422997772228906796078963)
  ·
    refine ⟨437134496658343360194118445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291422997772228906796078963 437134496658343360194118445)
    ·
      refine ⟨163925436246878760072794417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437134496658343360194118445 163925436246878760072794417)
      ·
        refine ⟨122944077185159070054595813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163925436246878760072794417 122944077185159070054595813)
        ·
          refine ⟨23052014472217325635236715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122944077185159070054595813 23052014472217325635236715)
          ·
            refine ⟨34578021708325988452855073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23052014472217325635236715 34578021708325988452855073)
            ·
              refine ⟨25933516281244491339641305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34578021708325988452855073 25933516281244491339641305)
              ·
                refine ⟨19450137210933368504730979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25933516281244491339641305 19450137210933368504730979)
                ·
                  refine ⟨29175205816400052757096469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19450137210933368504730979 29175205816400052757096469)
                  ·
                    refine ⟨1367587772643752472988897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29175205816400052757096469 1367587772643752472988897)
                    ·
                      rfl

theorem cell23_7990103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_7990103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990103 prefixEnd_7990103 := by exact prefixLift 7990103
  have htrace : WordTrace (prefixWord ++ tailWord_7990103) baseStart_7990103 baseEnd_7990103 := by
    simpa [prefixWord, tailWord_7990103, baseEnd_7990103] using wordTrace_append hprefix tailTrace_7990103
  have hstable : (prefixWord ++ tailWord_7990103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990103).length < 2 ^ (prefixWord ++ tailWord_7990103).sum := by decide
  have hdescent : baseEnd_7990103 < baseStart_7990103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990113 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_7990113 : Nat := 118140960795 + 7990113 * 2 ^ 59
def prefixEnd_7990113 : Nat := 4983230072969 + 3 ^ 40 * 7990113 * 2
def baseEnd_7990113 : Nat := 4102768452737802379841645

theorem tailTrace_7990113 : CollatzResearch.WordTrace tailWord_7990113 prefixEnd_7990113 4102768452737802379841645 := by
  unfold tailWord_7990113
  simp only [CollatzResearch.WordTrace]
  refine ⟨291423362502192678503942993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194282241668128452335961995 291423362502192678503942993)
  ·
    refine ⟨218567521876644508877957245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291423362502192678503942993 218567521876644508877957245)
    ·
      refine ⟨81962820703741690829233967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218567521876644508877957245 81962820703741690829233967)
      ·
        refine ⟨122944231055612536243850951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81962820703741690829233967 122944231055612536243850951)
        ·
          refine ⟨184416346583418804365776427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122944231055612536243850951 184416346583418804365776427)
          ·
            refine ⟨276624519875128206548664641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184416346583418804365776427 276624519875128206548664641)
            ·
              refine ⟨207468389906346154911498481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276624519875128206548664641 207468389906346154911498481)
              ·
                refine ⟨155601292429759616183623861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207468389906346154911498481 155601292429759616183623861)
                ·
                  refine ⟨14587621165289964017214737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155601292429759616183623861 14587621165289964017214737)
                  ·
                    refine ⟨10940715873967473012911053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14587621165289964017214737 10940715873967473012911053)
                    ·
                      refine ⟨4102768452737802379841645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10940715873967473012911053 4102768452737802379841645)
                      ·
                        rfl

theorem cell23_7990113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_7990113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990113 prefixEnd_7990113 := by exact prefixLift 7990113
  have htrace : WordTrace (prefixWord ++ tailWord_7990113) baseStart_7990113 baseEnd_7990113 := by
    simpa [prefixWord, tailWord_7990113, baseEnd_7990113] using wordTrace_append hprefix tailTrace_7990113
  have hstable : (prefixWord ++ tailWord_7990113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990113).length < 2 ^ (prefixWord ++ tailWord_7990113).sum := by decide
  have hdescent : baseEnd_7990113 < baseStart_7990113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990120 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 4, 4]
def baseStart_7990120 : Nat := 118140960795 + 7990120 * 2 ^ 59
def prefixEnd_7990120 : Nat := 4983230072969 + 3 ^ 40 * 7990120 * 2
def baseEnd_7990120 : Nat := 1367590682367461284151371

theorem tailTrace_7990120 : CollatzResearch.WordTrace tailWord_7990120 prefixEnd_7990120 1367590682367461284151371 := by
  unfold tailWord_7990120
  simp only [CollatzResearch.WordTrace]
  refine ⟨145711808906583659349723907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194282411875444879132965209 145711808906583659349723907)
  ·
    refine ⟨218567713359875489024585861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145711808906583659349723907 218567713359875489024585861)
    ·
      refine ⟨40981446254976654192109849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218567713359875489024585861 40981446254976654192109849)
      ·
        refine ⟨30736084691232490644082387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40981446254976654192109849 30736084691232490644082387)
        ·
          refine ⟨46104127036848735966123581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30736084691232490644082387 46104127036848735966123581)
          ·
            refine ⟨17289047638818275987296343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46104127036848735966123581 17289047638818275987296343)
            ·
              refine ⟨25933571458227413980944515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17289047638818275987296343 25933571458227413980944515)
              ·
                refine ⟨38900357187341120971416773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25933571458227413980944515 38900357187341120971416773)
                ·
                  refine ⟨7293816972626460182140645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38900357187341120971416773 7293816972626460182140645)
                  ·
                    refine ⟨1367590682367461284151371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7293816972626460182140645 1367590682367461284151371)
                    ·
                      rfl

theorem cell23_7990120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_7990120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990120 prefixEnd_7990120 := by exact prefixLift 7990120
  have htrace : WordTrace (prefixWord ++ tailWord_7990120) baseStart_7990120 baseEnd_7990120 := by
    simpa [prefixWord, tailWord_7990120, baseEnd_7990120] using wordTrace_append hprefix tailTrace_7990120
  have hstable : (prefixWord ++ tailWord_7990120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990120).length < 2 ^ (prefixWord ++ tailWord_7990120).sum := by decide
  have hdescent : baseEnd_7990120 < baseStart_7990120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990136 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_7990136 : Nat := 118140960795 + 7990136 * 2 ^ 59
def prefixEnd_7990136 : Nat := 4983230072969 + 3 ^ 40 * 7990136 * 2
def baseEnd_7990136 : Nat := 4102780262792855789854039

theorem tailTrace_7990136 : CollatzResearch.WordTrace tailWord_7990136 prefixEnd_7990136 4102780262792855789854039 := by
  unfold tailWord_7990136
  simp only [CollatzResearch.WordTrace]
  refine ⟨145712100690554676716015131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194282800920739568954686841 145712100690554676716015131)
  ·
    refine ⟨218568151035832015074022697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145712100690554676716015131 218568151035832015074022697)
    ·
      refine ⟨163926113276874011305517023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218568151035832015074022697 163926113276874011305517023)
      ·
        refine ⟨245889169915311016958275535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163926113276874011305517023 245889169915311016958275535)
        ·
          refine ⟨368833754872966525437413303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245889169915311016958275535 368833754872966525437413303)
          ·
            refine ⟨553250632309449788156119955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368833754872966525437413303 553250632309449788156119955)
            ·
              refine ⟨829875948464174682234179933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553250632309449788156119955 829875948464174682234179933)
              ·
                refine ⟨311203480674065505837817475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829875948464174682234179933 311203480674065505837817475)
                ·
                  refine ⟨466805221011098258756726213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311203480674065505837817475 466805221011098258756726213)
                  ·
                    refine ⟨87525978939580923516886165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466805221011098258756726213 87525978939580923516886165)
                    ·
                      refine ⟨4102780262792855789854039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87525978939580923516886165 4102780262792855789854039)
                      ·
                        rfl

theorem cell23_7990136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_7990136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990136 prefixEnd_7990136 := by exact prefixLift 7990136
  have htrace : WordTrace (prefixWord ++ tailWord_7990136) baseStart_7990136 baseEnd_7990136 := by
    simpa [prefixWord, tailWord_7990136, baseEnd_7990136] using wordTrace_append hprefix tailTrace_7990136
  have hstable : (prefixWord ++ tailWord_7990136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990136).length < 2 ^ (prefixWord ++ tailWord_7990136).sum := by decide
  have hdescent : baseEnd_7990136 < baseStart_7990136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990137 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 2, 4]
def baseStart_7990137 : Nat := 118140960795 + 7990137 * 2 ^ 59
def prefixEnd_7990137 : Nat := 4983230072969 + 3 ^ 40 * 7990137 * 2
def baseEnd_7990137 : Nat := 1367593592091170095313845

theorem tailTrace_7990137 : CollatzResearch.WordTrace tailWord_7990137 prefixEnd_7990137 1367593592091170095313845 := by
  unfold tailWord_7990137
  simp only [CollatzResearch.WordTrace]
  refine ⟨291424237854105730602816665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194282825236070487068544443 291424237854105730602816665)
  ·
    refine ⟨218568178390579297952112499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291424237854105730602816665 218568178390579297952112499)
    ·
      refine ⟨327852267585868946928168749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218568178390579297952112499 327852267585868946928168749)
      ·
        refine ⟨122944600344700855098063281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327852267585868946928168749 122944600344700855098063281)
        ·
          refine ⟨92208450258525641323547461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122944600344700855098063281 92208450258525641323547461)
          ·
            refine ⟨17289084423473557748165149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92208450258525641323547461 17289084423473557748165149)
            ·
              refine ⟨6483406658802584155561931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17289084423473557748165149 6483406658802584155561931)
              ·
                refine ⟨9725109988203876233342897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483406658802584155561931 9725109988203876233342897)
                ·
                  refine ⟨7293832491152907175007173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9725109988203876233342897 7293832491152907175007173)
                  ·
                    refine ⟨1367593592091170095313845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7293832491152907175007173 1367593592091170095313845)
                    ·
                      rfl

theorem cell23_7990137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 4].length) (baseStart_7990137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990137 prefixEnd_7990137 := by exact prefixLift 7990137
  have htrace : WordTrace (prefixWord ++ tailWord_7990137) baseStart_7990137 baseEnd_7990137 := by
    simpa [prefixWord, tailWord_7990137, baseEnd_7990137] using wordTrace_append hprefix tailTrace_7990137
  have hstable : (prefixWord ++ tailWord_7990137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990137).length < 2 ^ (prefixWord ++ tailWord_7990137).sum := by decide
  have hdescent : baseEnd_7990137 < baseStart_7990137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990173 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7990173 : Nat := 118140960795 + 7990173 * 2 ^ 59
def prefixEnd_7990173 : Nat := 4983230072969 + 3 ^ 40 * 7990173 * 2
def baseEnd_7990173 : Nat := 4102799261577072145091369

theorem tailTrace_7990173 : CollatzResearch.WordTrace tailWord_7990173 prefixEnd_7990173 4102799261577072145091369 := by
  unfold tailWord_7990173
  simp only [CollatzResearch.WordTrace]
  refine ⟨291425550881975308751127173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194283700587983539167418115 291425550881975308751127173)
  ·
    refine ⟨54642290790370370390836345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291425550881975308751127173 54642290790370370390836345)
    ·
      refine ⟨40981718092777777793127259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54642290790370370390836345 40981718092777777793127259)
      ·
        refine ⟨61472577139166666689690889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40981718092777777793127259 61472577139166666689690889)
        ·
          refine ⟨46104432854375000017268167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61472577139166666689690889 46104432854375000017268167)
          ·
            refine ⟨69156649281562500025902251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46104432854375000017268167 69156649281562500025902251)
            ·
              refine ⟨103734973922343750038853377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69156649281562500025902251 103734973922343750038853377)
              ·
                refine ⟨77801230441757812529140033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103734973922343750038853377 77801230441757812529140033)
                ·
                  refine ⟨58350922831318359396855025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77801230441757812529140033 58350922831318359396855025)
                  ·
                    refine ⟨43763192123488769547641269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58350922831318359396855025 43763192123488769547641269)
                    ·
                      refine ⟨4102799261577072145091369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43763192123488769547641269 4102799261577072145091369)
                      ·
                        rfl

theorem cell23_7990173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7990173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990173 prefixEnd_7990173 := by exact prefixLift 7990173
  have htrace : WordTrace (prefixWord ++ tailWord_7990173) baseStart_7990173 baseEnd_7990173 := by
    simpa [prefixWord, tailWord_7990173, baseEnd_7990173] using wordTrace_append hprefix tailTrace_7990173
  have hstable : (prefixWord ++ tailWord_7990173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990173).length < 2 ^ (prefixWord ++ tailWord_7990173).sum := by decide
  have hdescent : baseEnd_7990173 < baseStart_7990173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990177 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7990177 : Nat := 118140960795 + 7990177 * 2 ^ 59
def prefixEnd_7990177 : Nat := 4983230072969 + 3 ^ 40 * 7990177 * 2
def baseEnd_7990177 : Nat := 4102801315499690129441351

theorem tailTrace_7990177 : CollatzResearch.WordTrace tailWord_7990177 prefixEnd_7990177 4102801315499690129441351 := by
  unfold tailWord_7990177
  simp only [CollatzResearch.WordTrace]
  refine ⟨291425696773960817434272785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194283797849307211622848523 291425696773960817434272785)
  ·
    refine ⟨218569272580470613075704589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291425696773960817434272785 218569272580470613075704589)
    ·
      refine ⟨81963477217676479903389221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218569272580470613075704589 81963477217676479903389221)
      ·
        refine ⟨15368151978314339981885479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81963477217676479903389221 15368151978314339981885479)
        ·
          refine ⟨23052227967471509972828219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15368151978314339981885479 23052227967471509972828219)
          ·
            refine ⟨34578341951207264959242329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23052227967471509972828219 34578341951207264959242329)
            ·
              refine ⟨25933756463405448719431747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34578341951207264959242329 25933756463405448719431747)
              ·
                refine ⟨38900634695108173079147621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25933756463405448719431747 38900634695108173079147621)
                ·
                  refine ⟨7293869005332782452340179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38900634695108173079147621 7293869005332782452340179)
                  ·
                    refine ⟨10940803507999173678510269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7293869005332782452340179 10940803507999173678510269)
                    ·
                      refine ⟨4102801315499690129441351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10940803507999173678510269 4102801315499690129441351)
                      ·
                        rfl

theorem cell23_7990177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7990177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990177 prefixEnd_7990177 := by exact prefixLift 7990177
  have htrace : WordTrace (prefixWord ++ tailWord_7990177) baseStart_7990177 baseEnd_7990177 := by
    simpa [prefixWord, tailWord_7990177, baseEnd_7990177] using wordTrace_append hprefix tailTrace_7990177
  have hstable : (prefixWord ++ tailWord_7990177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990177).length < 2 ^ (prefixWord ++ tailWord_7990177).sum := by decide
  have hdescent : baseEnd_7990177 < baseStart_7990177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990178 : List Nat := [3, 3, 1, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_7990178 : Nat := 118140960795 + 7990178 * 2 ^ 59
def prefixEnd_7990178 : Nat := 4983230072969 + 3 ^ 40 * 7990178 * 2
def baseEnd_7990178 : Nat := 4102801828980344625528847

theorem tailTrace_7990178 : CollatzResearch.WordTrace tailWord_7990178 prefixEnd_7990178 4102801828980344625528847 := by
  unfold tailWord_7990178
  simp only [CollatzResearch.WordTrace]
  refine ⟨72856433311739298651264797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194283822164638129736706125 72856433311739298651264797)
  ·
    refine ⟨27321162491902236994224299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72856433311739298651264797 27321162491902236994224299)
    ·
      refine ⟨40981743737853355491336449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27321162491902236994224299 40981743737853355491336449)
      ·
        refine ⟨30736307803390016618502337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40981743737853355491336449 30736307803390016618502337)
        ·
          refine ⟨23052230852542512463876753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30736307803390016618502337 23052230852542512463876753)
          ·
            refine ⟨17289173139406884347907565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23052230852542512463876753 17289173139406884347907565)
            ·
              refine ⟨6483439927277581630465337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17289173139406884347907565 6483439927277581630465337)
              ·
                refine ⟨4862579945458186222849003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483439927277581630465337 4862579945458186222849003)
                ·
                  refine ⟨7293869918187279334273505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862579945458186222849003 7293869918187279334273505)
                  ·
                    refine ⟨5470402438640459500705129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7293869918187279334273505 5470402438640459500705129)
                    ·
                      refine ⟨4102801828980344625528847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470402438640459500705129 4102801828980344625528847)
                      ·
                        rfl

theorem cell23_7990178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_7990178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990178 prefixEnd_7990178 := by exact prefixLift 7990178
  have htrace : WordTrace (prefixWord ++ tailWord_7990178) baseStart_7990178 baseEnd_7990178 := by
    simpa [prefixWord, tailWord_7990178, baseEnd_7990178] using wordTrace_append hprefix tailTrace_7990178
  have hstable : (prefixWord ++ tailWord_7990178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990178).length < 2 ^ (prefixWord ++ tailWord_7990178).sum := by decide
  have hdescent : baseEnd_7990178 < baseStart_7990178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990234 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2]
def baseStart_7990234 : Nat := 118140960795 + 7990234 * 2 ^ 59
def prefixEnd_7990234 : Nat := 4983230072969 + 3 ^ 40 * 7990234 * 2
def baseEnd_7990234 : Nat := 4102830583896996406428589

theorem tailTrace_7990234 : CollatzResearch.WordTrace tailWord_7990234 prefixEnd_7990234 4102830583896996406428589 := by
  unfold tailWord_7990234
  simp only [CollatzResearch.WordTrace]
  refine ⟨72856943933688579042274439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194285183823169544112731837 72856943933688579042274439)
  ·
    refine ⟨109285415900532868563411659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72856943933688579042274439 109285415900532868563411659)
    ·
      refine ⟨163928123850799302845117489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109285415900532868563411659 163928123850799302845117489)
      ·
        refine ⟨122946092888099477133838117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163928123850799302845117489 122946092888099477133838117)
        ·
          refine ⟨23052392416518651962594647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122946092888099477133838117 23052392416518651962594647)
          ·
            refine ⟨34578588624777977943891971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23052392416518651962594647 34578588624777977943891971)
            ·
              refine ⟨51867882937166966915837957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34578588624777977943891971 51867882937166966915837957)
              ·
                refine ⟨9725228050718806296719617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51867882937166966915837957 9725228050718806296719617)
                ·
                  refine ⟨7293921038039104722539713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9725228050718806296719617 7293921038039104722539713)
                  ·
                    refine ⟨5470440778529328541904785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7293921038039104722539713 5470440778529328541904785)
                    ·
                      refine ⟨4102830583896996406428589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470440778529328541904785 4102830583896996406428589)
                      ·
                        rfl

theorem cell23_7990234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_7990234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990234 prefixEnd_7990234 := by exact prefixLift 7990234
  have htrace : WordTrace (prefixWord ++ tailWord_7990234) baseStart_7990234 baseEnd_7990234 := by
    simpa [prefixWord, tailWord_7990234, baseEnd_7990234] using wordTrace_append hprefix tailTrace_7990234
  have hstable : (prefixWord ++ tailWord_7990234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990234).length < 2 ^ (prefixWord ++ tailWord_7990234).sum := by decide
  have hdescent : baseEnd_7990234 < baseStart_7990234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990250 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_7990250 : Nat := 118140960795 + 7990250 * 2 ^ 59
def prefixEnd_7990250 : Nat := 4983230072969 + 3 ^ 40 * 7990250 * 2
def baseEnd_7990250 : Nat := 4102838799587468343828515

theorem tailTrace_7990250 : CollatzResearch.WordTrace tailWord_7990250 prefixEnd_7990250 4102838799587468343828515 := by
  unfold tailWord_7990250
  simp only [CollatzResearch.WordTrace]
  refine ⟨72857089825674087725420051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194285572868464233934453469 72857089825674087725420051)
  ·
    refine ⟨109285634738511131588130077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72857089825674087725420051 109285634738511131588130077)
    ·
      refine ⟨40982113026941674345548779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109285634738511131588130077 40982113026941674345548779)
      ·
        refine ⟨61473169540412511518323169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40982113026941674345548779 61473169540412511518323169)
        ·
          refine ⟨46104877155309383638742377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61473169540412511518323169 46104877155309383638742377)
          ·
            refine ⟨34578657866482037729056783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46104877155309383638742377 34578657866482037729056783)
            ·
              refine ⟨51867986799723056593585175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34578657866482037729056783 51867986799723056593585175)
              ·
                refine ⟨77801980199584584890377763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51867986799723056593585175 77801980199584584890377763)
                ·
                  refine ⟨116702970299376877335566645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77801980199584584890377763 116702970299376877335566645)
                  ·
                    refine ⟨10940903465566582250209373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116702970299376877335566645 10940903465566582250209373)
                    ·
                      refine ⟨4102838799587468343828515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10940903465566582250209373 4102838799587468343828515)
                      ·
                        rfl

theorem cell23_7990250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_7990250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990250 prefixEnd_7990250 := by exact prefixLift 7990250
  have htrace : WordTrace (prefixWord ++ tailWord_7990250) baseStart_7990250 baseEnd_7990250 := by
    simpa [prefixWord, tailWord_7990250, baseEnd_7990250] using wordTrace_append hprefix tailTrace_7990250
  have hstable : (prefixWord ++ tailWord_7990250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990250).length < 2 ^ (prefixWord ++ tailWord_7990250).sum := by decide
  have hdescent : baseEnd_7990250 < baseStart_7990250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990307 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 2, 4, 2]
def baseStart_7990307 : Nat := 118140960795 + 7990307 * 2 ^ 59
def prefixEnd_7990307 : Nat := 4983230072969 + 3 ^ 40 * 7990307 * 2
def baseEnd_7990307 : Nat := 4102868067984774620815753

theorem tailTrace_7990307 : CollatzResearch.WordTrace tailWord_7990307 prefixEnd_7990307 4102868067984774620815753 := by
  unfold tailWord_7990307
  simp only [CollatzResearch.WordTrace]
  refine ⟨291430438263489849636505175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194286958842326566424336783 291430438263489849636505175)
  ·
    refine ⟨437145657395234774454757763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291430438263489849636505175 437145657395234774454757763)
    ·
      refine ⟨655718486092852161682136645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437145657395234774454757763 655718486092852161682136645)
      ·
        refine ⟨122947216142409780315400621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 655718486092852161682136645 122947216142409780315400621)
        ·
          refine ⟨46105206053403667618275233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122947216142409780315400621 46105206053403667618275233)
          ·
            refine ⟨34578904540052750713706425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46105206053403667618275233 34578904540052750713706425)
            ·
              refine ⟨25934178405039563035279819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34578904540052750713706425 25934178405039563035279819)
              ·
                refine ⟨38901267607559344552919729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25934178405039563035279819 38901267607559344552919729)
                ·
                  refine ⟨29175950705669508414689797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38901267607559344552919729 29175950705669508414689797)
                  ·
                    refine ⟨5470490757313032827754337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29175950705669508414689797 5470490757313032827754337)
                    ·
                      refine ⟨4102868067984774620815753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470490757313032827754337 4102868067984774620815753)
                      ·
                        rfl

theorem cell23_7990307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_7990307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990307 prefixEnd_7990307 := by exact prefixLift 7990307
  have htrace : WordTrace (prefixWord ++ tailWord_7990307) baseStart_7990307 baseEnd_7990307 := by
    simpa [prefixWord, tailWord_7990307, baseEnd_7990307] using wordTrace_append hprefix tailTrace_7990307
  have hstable : (prefixWord ++ tailWord_7990307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990307).length < 2 ^ (prefixWord ++ tailWord_7990307).sum := by decide
  have hdescent : baseEnd_7990307 < baseStart_7990307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990360 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 3, 5]
def baseStart_7990360 : Nat := 118140960795 + 7990360 * 2 ^ 59
def prefixEnd_7990360 : Nat := 4983230072969 + 3 ^ 40 * 7990360 * 2
def baseEnd_7990360 : Nat := 1367631760819820971151003

theorem tailTrace_7990360 : CollatzResearch.WordTrace tailWord_7990360 prefixEnd_7990360 1367631760819820971151003 := by
  unfold tailWord_7990360
  simp only [CollatzResearch.WordTrace]
  refine ⟨145716185666148919844092267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194288247554865226458789689 145716185666148919844092267)
  ·
    refine ⟨218574278499223379766138401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145716185666148919844092267 218574278499223379766138401)
    ·
      refine ⟨163930708874417534824603801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218574278499223379766138401 163930708874417534824603801)
      ·
        refine ⟨122948031655813151118452851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163930708874417534824603801 122948031655813151118452851)
        ·
          refine ⟨184422047483719726677679277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122948031655813151118452851 184422047483719726677679277)
          ·
            refine ⟨69158267806394897504129729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184422047483719726677679277 69158267806394897504129729)
            ·
              refine ⟨51868700854796173128097297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69158267806394897504129729 51868700854796173128097297)
              ·
                refine ⟨38901525641097129846072973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51868700854796173128097297 38901525641097129846072973)
                ·
                  refine ⟨14588072115411423692277365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38901525641097129846072973 14588072115411423692277365)
                  ·
                    refine ⟨1367631760819820971151003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14588072115411423692277365 1367631760819820971151003)
                    ·
                      rfl

theorem cell23_7990360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_7990360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990360 prefixEnd_7990360 := by exact prefixLift 7990360
  have htrace : WordTrace (prefixWord ++ tailWord_7990360) baseStart_7990360 baseEnd_7990360 := by
    simpa [prefixWord, tailWord_7990360, baseEnd_7990360] using wordTrace_append hprefix tailTrace_7990360
  have hstable : (prefixWord ++ tailWord_7990360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990360).length < 2 ^ (prefixWord ++ tailWord_7990360).sum := by decide
  have hdescent : baseEnd_7990360 < baseStart_7990360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990367 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 4, 3, 2]
def baseStart_7990367 : Nat := 118140960795 + 7990367 * 2 ^ 59
def prefixEnd_7990367 : Nat := 4983230072969 + 3 ^ 40 * 7990367 * 2
def baseEnd_7990367 : Nat := 4102898876824044386065477

theorem tailTrace_7990367 : CollatzResearch.WordTrace tailWord_7990367 prefixEnd_7990367 4102898876824044386065477 := by
  unfold tailWord_7990367
  simp only [CollatzResearch.WordTrace]
  refine ⟨291432626643272479883689355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194288417762181653255792903 291432626643272479883689355)
  ·
    refine ⟨437148939964908719825534033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291432626643272479883689355 437148939964908719825534033)
    ·
      refine ⟨327861704973681539869150525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437148939964908719825534033 327861704973681539869150525)
      ·
        refine ⟨122948139365130577450931447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327861704973681539869150525 122948139365130577450931447)
        ·
          refine ⟨184422209047695866176397171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122948139365130577450931447 184422209047695866176397171)
          ·
            refine ⟨276633313571543799264595757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184422209047695866176397171 276633313571543799264595757)
            ·
              refine ⟨103737492589328924724223409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276633313571543799264595757 103737492589328924724223409)
              ·
                refine ⟨77803119441996693543167557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103737492589328924724223409 77803119441996693543167557)
                ·
                  refine ⟨14588084895374380039343917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77803119441996693543167557 14588084895374380039343917)
                  ·
                    refine ⟨5470531835765392514753969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14588084895374380039343917 5470531835765392514753969)
                    ·
                      refine ⟨4102898876824044386065477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470531835765392514753969 4102898876824044386065477)
                      ·
                        rfl

theorem cell23_7990367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_7990367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990367 prefixEnd_7990367 := by exact prefixLift 7990367
  have htrace : WordTrace (prefixWord ++ tailWord_7990367) baseStart_7990367 baseEnd_7990367 := by
    simpa [prefixWord, tailWord_7990367, baseEnd_7990367] using wordTrace_append hprefix tailTrace_7990367
  have hstable : (prefixWord ++ tailWord_7990367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990367).length < 2 ^ (prefixWord ++ tailWord_7990367).sum := by decide
  have hdescent : baseEnd_7990367 < baseStart_7990367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990377 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 1, 5]
def baseStart_7990377 : Nat := 118140960795 + 7990377 * 2 ^ 59
def prefixEnd_7990377 : Nat := 4983230072969 + 3 ^ 40 * 7990377 * 2
def baseEnd_7990377 : Nat := 1367634670543529782313477

theorem tailTrace_7990377 : CollatzResearch.WordTrace tailWord_7990377 prefixEnd_7990377 1367634670543529782313477 := by
  unfold tailWord_7990377
  simp only [CollatzResearch.WordTrace]
  refine ⟨291432991373236251591553385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194288660915490834394368923 291432991373236251591553385)
  ·
    refine ⟨218574743529927188693665039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291432991373236251591553385 218574743529927188693665039)
    ·
      refine ⟨327862115294890783040497559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218574743529927188693665039 327862115294890783040497559)
      ·
        refine ⟨491793172942336174560746339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327862115294890783040497559 491793172942336174560746339)
        ·
          refine ⟨737689759413504261841119509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491793172942336174560746339 737689759413504261841119509)
          ·
            refine ⟨34579207472508012273802477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 737689759413504261841119509 34579207472508012273802477)
            ·
              refine ⟨12967202802190504602675929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34579207472508012273802477 12967202802190504602675929)
              ·
                refine ⟨9725402101642878452006947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12967202802190504602675929 9725402101642878452006947)
                ·
                  refine ⟨14588103152464317678010421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9725402101642878452006947 14588103152464317678010421)
                  ·
                    refine ⟨1367634670543529782313477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14588103152464317678010421 1367634670543529782313477)
                    ·
                      rfl

theorem cell23_7990377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_7990377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990377 prefixEnd_7990377 := by exact prefixLift 7990377
  have htrace : WordTrace (prefixWord ++ tailWord_7990377) baseStart_7990377 baseEnd_7990377 := by
    simpa [prefixWord, tailWord_7990377, baseEnd_7990377] using wordTrace_append hprefix tailTrace_7990377
  have hstable : (prefixWord ++ tailWord_7990377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990377).length < 2 ^ (prefixWord ++ tailWord_7990377).sum := by decide
  have hdescent : baseEnd_7990377 < baseStart_7990377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990384 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 2, 3, 2]
def baseStart_7990384 : Nat := 118140960795 + 7990384 * 2 ^ 59
def prefixEnd_7990384 : Nat := 4983230072969 + 3 ^ 40 * 7990384 * 2
def baseEnd_7990384 : Nat := 4102907605995170819552899

theorem tailTrace_7990384 : CollatzResearch.WordTrace tailWord_7990384 prefixEnd_7990384 4102907605995170819552899 := by
  unfold tailWord_7990384
  simp only [CollatzResearch.WordTrace]
  refine ⟨145716623342105445893529103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194288831122807261191372137 145716623342105445893529103)
  ·
    refine ⟨218574935013158168840293655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145716623342105445893529103 218574935013158168840293655)
    ·
      refine ⟨327862402519737253260440483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218574935013158168840293655 327862402519737253260440483)
      ·
        refine ⟨491793603779605879890660725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327862402519737253260440483 491793603779605879890660725)
        ·
          refine ⟨46105650354338051239749443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491793603779605879890660725 46105650354338051239749443)
          ·
            refine ⟨69158475531507076859624165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46105650354338051239749443 69158475531507076859624165)
            ·
              refine ⟨12967214162157576911179531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69158475531507076859624165 12967214162157576911179531)
              ·
                refine ⟨19450821243236365366769297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12967214162157576911179531 19450821243236365366769297)
                ·
                  refine ⟨14588115932427274025076973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19450821243236365366769297 14588115932427274025076973)
                  ·
                    refine ⟨5470543474660227759403865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14588115932427274025076973 5470543474660227759403865)
                    ·
                      refine ⟨4102907605995170819552899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470543474660227759403865 4102907605995170819552899)
                      ·
                        rfl

theorem cell23_7990384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 3, 2].length) (baseStart_7990384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990384 prefixEnd_7990384 := by exact prefixLift 7990384
  have htrace : WordTrace (prefixWord ++ tailWord_7990384) baseStart_7990384 baseEnd_7990384 := by
    simpa [prefixWord, tailWord_7990384, baseEnd_7990384] using wordTrace_append hprefix tailTrace_7990384
  have hstable : (prefixWord ++ tailWord_7990384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990384).length < 2 ^ (prefixWord ++ tailWord_7990384).sum := by decide
  have hdescent : baseEnd_7990384 < baseStart_7990384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990398 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_7990398 : Nat := 118140960795 + 7990398 * 2 ^ 59
def prefixEnd_7990398 : Nat := 4983230072969 + 3 ^ 40 * 7990398 * 2
def baseEnd_7990398 : Nat := 455879421636037084975315

theorem tailTrace_7990398 : CollatzResearch.WordTrace tailWord_7990398 prefixEnd_7990398 455879421636037084975315 := by
  unfold tailWord_7990398
  simp only [CollatzResearch.WordTrace]
  refine ⟨36429219663270021522258481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194289171537440114785378565 36429219663270021522258481)
  ·
    refine ⟨27321914747452516141693861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36429219663270021522258481 27321914747452516141693861)
    ·
      refine ⟨5122859015147346776567599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27321914747452516141693861 5122859015147346776567599)
      ·
        refine ⟨7684288522721020164851399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122859015147346776567599 7684288522721020164851399)
        ·
          refine ⟨11526432784081530247277099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684288522721020164851399 11526432784081530247277099)
          ·
            refine ⟨17289649176122295370915649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11526432784081530247277099 17289649176122295370915649)
            ·
              refine ⟨12967236882091721528186737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17289649176122295370915649 12967236882091721528186737)
              ·
                refine ⟨9725427661568791146140053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12967236882091721528186737 9725427661568791146140053)
                ·
                  refine ⟨455879421636037084975315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9725427661568791146140053 455879421636037084975315)
                  ·
                    rfl

theorem cell23_7990398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_7990398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990398 prefixEnd_7990398 := by exact prefixLift 7990398
  have htrace : WordTrace (prefixWord ++ tailWord_7990398) baseStart_7990398 baseEnd_7990398 := by
    simpa [prefixWord, tailWord_7990398, baseEnd_7990398] using wordTrace_append hprefix tailTrace_7990398
  have hstable : (prefixWord ++ tailWord_7990398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990398).length < 2 ^ (prefixWord ++ tailWord_7990398).sum := by decide
  have hdescent : baseEnd_7990398 < baseStart_7990398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990408 : List Nat := [2, 1, 3, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7990408 : Nat := 118140960795 + 7990408 * 2 ^ 59
def prefixEnd_7990408 : Nat := 4983230072969 + 3 ^ 40 * 7990408 * 2
def baseEnd_7990408 : Nat := 4102919929530878725652789

theorem tailTrace_7990408 : CollatzResearch.WordTrace tailWord_7990408 prefixEnd_7990408 4102919929530878725652789 := by
  unfold tailWord_7990408
  simp only [CollatzResearch.WordTrace]
  refine ⟨145717061018061971942965939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194289414690749295923954585 145717061018061971942965939)
  ·
    refine ⟨218575591527092957914448909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145717061018061971942965939 218575591527092957914448909)
    ·
      refine ⟨81965846822659859217918341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218575591527092957914448909 81965846822659859217918341)
      ·
        refine ⟨15368596279248723603359689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81965846822659859217918341 15368596279248723603359689)
        ·
          refine ⟨11526447209436542702519767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15368596279248723603359689 11526447209436542702519767)
          ·
            refine ⟨17289670814154814053779651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11526447209436542702519767 17289670814154814053779651)
            ·
              refine ⟨25934506221232221080669477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17289670814154814053779651 25934506221232221080669477)
              ·
                refine ⟨4862719916481041452625527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25934506221232221080669477 4862719916481041452625527)
                ·
                  refine ⟨7294079874721562178938291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862719916481041452625527 7294079874721562178938291)
                  ·
                    refine ⟨10941119812082343268407437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7294079874721562178938291 10941119812082343268407437)
                    ·
                      refine ⟨4102919929530878725652789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10941119812082343268407437 4102919929530878725652789)
                      ·
                        rfl

theorem cell23_7990408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7990408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990408 prefixEnd_7990408 := by exact prefixLift 7990408
  have htrace : WordTrace (prefixWord ++ tailWord_7990408) baseStart_7990408 baseEnd_7990408 := by
    simpa [prefixWord, tailWord_7990408, baseEnd_7990408] using wordTrace_append hprefix tailTrace_7990408
  have hstable : (prefixWord ++ tailWord_7990408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990408).length < 2 ^ (prefixWord ++ tailWord_7990408).sum := by decide
  have hdescent : baseEnd_7990408 < baseStart_7990408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990424 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 2, 4]
def baseStart_7990424 : Nat := 118140960795 + 7990424 * 2 ^ 59
def prefixEnd_7990424 : Nat := 4983230072969 + 3 ^ 40 * 7990424 * 2
def baseEnd_7990424 : Nat := 1367642715073783554350905

theorem tailTrace_7990424 : CollatzResearch.WordTrace tailWord_7990424 prefixEnd_7990424 1367642715073783554350905 := by
  unfold tailWord_7990424
  simp only [CollatzResearch.WordTrace]
  refine ⟨145717352802032989309257163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194289803736043985745676217 145717352802032989309257163)
  ·
    refine ⟨218576029203049483963885745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145717352802032989309257163 218576029203049483963885745)
    ·
      refine ⟨163932021902287112972914309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218576029203049483963885745 163932021902287112972914309)
      ·
        refine ⟨30737254106678833682421433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163932021902287112972914309 30737254106678833682421433)
        ·
          refine ⟨23052940580009125261816075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30737254106678833682421433 23052940580009125261816075)
          ·
            refine ⟨34579410870013687892724113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23052940580009125261816075 34579410870013687892724113)
            ·
              refine ⟨25934558152510265919543085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34579410870013687892724113 25934558152510265919543085)
              ·
                refine ⟨9725459307191349719828657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25934558152510265919543085 9725459307191349719828657)
                ·
                  refine ⟨7294094480393512289871493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9725459307191349719828657 7294094480393512289871493)
                  ·
                    refine ⟨1367642715073783554350905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7294094480393512289871493 1367642715073783554350905)
                    ·
                      rfl

theorem cell23_7990424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_7990424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990424 prefixEnd_7990424 := by exact prefixLift 7990424
  have htrace : WordTrace (prefixWord ++ tailWord_7990424) baseStart_7990424 baseEnd_7990424 := by
    simpa [prefixWord, tailWord_7990424, baseEnd_7990424] using wordTrace_append hprefix tailTrace_7990424
  have hstable : (prefixWord ++ tailWord_7990424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990424).length < 2 ^ (prefixWord ++ tailWord_7990424).sum := by decide
  have hdescent : baseEnd_7990424 < baseStart_7990424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990437 : List Nat := [1, 3, 1, 2, 1, 5, 3, 7]
def baseStart_7990437 : Nat := 118140960795 + 7990437 * 2 ^ 59
def prefixEnd_7990437 : Nat := 4983230072969 + 3 ^ 40 * 7990437 * 2
def baseEnd_7990437 : Nat := 151960548906291078229265

theorem tailTrace_7990437 : CollatzResearch.WordTrace tailWord_7990437 prefixEnd_7990437 151960548906291078229265 := by
  unfold tailWord_7990437
  simp only [CollatzResearch.WordTrace]
  refine ⟨291435179753018881838737565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194290119835345921225825043 291435179753018881838737565)
  ·
    refine ⟨109288192407382080689526587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291435179753018881838737565 109288192407382080689526587)
    ·
      refine ⟨163932288611073121034289881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109288192407382080689526587 163932288611073121034289881)
      ·
        refine ⟨122949216458304840775717411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163932288611073121034289881 122949216458304840775717411)
        ·
          refine ⟨184423824687457261163576117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122949216458304840775717411 184423824687457261163576117)
          ·
            refine ⟨17289733564449118234085261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184423824687457261163576117 17289733564449118234085261)
            ·
              refine ⟨6483650086668419337781973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17289733564449118234085261 6483650086668419337781973)
              ·
                refine ⟨151960548906291078229265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6483650086668419337781973 151960548906291078229265)
                ·
                  rfl

theorem cell23_7990437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 7].length) (baseStart_7990437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990437 prefixEnd_7990437 := by exact prefixLift 7990437
  have htrace : WordTrace (prefixWord ++ tailWord_7990437) baseStart_7990437 baseEnd_7990437 := by
    simpa [prefixWord, tailWord_7990437, baseEnd_7990437] using wordTrace_append hprefix tailTrace_7990437
  have hstable : (prefixWord ++ tailWord_7990437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990437).length < 2 ^ (prefixWord ++ tailWord_7990437).sum := by decide
  have hdescent : baseEnd_7990437 < baseStart_7990437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990447 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 3]
def baseStart_7990447 : Nat := 118140960795 + 7990447 * 2 ^ 59
def prefixEnd_7990447 : Nat := 4983230072969 + 3 ^ 40 * 7990447 * 2
def baseEnd_7990447 : Nat := 4102939955276404073065109

theorem tailTrace_7990447 : CollatzResearch.WordTrace tailWord_7990447 prefixEnd_7990447 4102939955276404073065109 := by
  unfold tailWord_7990447
  simp only [CollatzResearch.WordTrace]
  refine ⟨291435544482982653546601595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194290362988655102364401063 291435544482982653546601595)
  ·
    refine ⟨437153316724473980319902393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291435544482982653546601595 437153316724473980319902393)
    ·
      refine ⟨327864987543355485239926795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437153316724473980319902393 327864987543355485239926795)
      ·
        refine ⟨491797481315033227859890193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327864987543355485239926795 491797481315033227859890193)
        ·
          refine ⟨368848110986274920894917645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491797481315033227859890193 368848110986274920894917645)
          ·
            refine ⟨138318041619853095335594117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368848110986274920894917645 138318041619853095335594117)
            ·
              refine ⟨25934632803722455375423897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138318041619853095335594117 25934632803722455375423897)
              ·
                refine ⟨19450974602791841531567923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25934632803722455375423897 19450974602791841531567923)
                ·
                  refine ⟨29176461904187762297351885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19450974602791841531567923 29176461904187762297351885)
                  ·
                    refine ⟨10941173214070410861506957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29176461904187762297351885 10941173214070410861506957)
                    ·
                      refine ⟨4102939955276404073065109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10941173214070410861506957 4102939955276404073065109)
                      ·
                        rfl

theorem cell23_7990447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_7990447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990447 prefixEnd_7990447 := by exact prefixLift 7990447
  have htrace : WordTrace (prefixWord ++ tailWord_7990447) baseStart_7990447 baseEnd_7990447 := by
    simpa [prefixWord, tailWord_7990447, baseEnd_7990447] using wordTrace_append hprefix tailTrace_7990447
  have hstable : (prefixWord ++ tailWord_7990447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990447).length < 2 ^ (prefixWord ++ tailWord_7990447).sum := by decide
  have hdescent : baseEnd_7990447 < baseStart_7990447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990465 : List Nat := [1, 2, 6, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7990465 : Nat := 118140960795 + 7990465 * 2 ^ 59
def prefixEnd_7990465 : Nat := 4983230072969 + 3 ^ 40 * 7990465 * 2
def baseEnd_7990465 : Nat := 4102949197928185002640027

theorem tailTrace_7990465 : CollatzResearch.WordTrace tailWord_7990465 prefixEnd_7990465 4102949197928185002640027 := by
  unfold tailWord_7990465
  simp only [CollatzResearch.WordTrace]
  refine ⟨291436200996917442620756849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194290800664611628413837899 291436200996917442620756849)
  ·
    refine ⟨218577150747688081965567637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291436200996917442620756849 218577150747688081965567637)
    ·
      refine ⟨10245803941297878842135983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218577150747688081965567637 10245803941297878842135983)
      ·
        refine ⟨15368705911946818263203975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245803941297878842135983 15368705911946818263203975)
        ·
          refine ⟨23053058867920227394805963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15368705911946818263203975 23053058867920227394805963)
          ·
            refine ⟨34579588301880341092208945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23053058867920227394805963 34579588301880341092208945)
            ·
              refine ⟨25934691226410255819156709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34579588301880341092208945 25934691226410255819156709)
              ·
                refine ⟨4862754604951922966091883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25934691226410255819156709 4862754604951922966091883)
                ·
                  refine ⟨7294131907427884449137825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862754604951922966091883 7294131907427884449137825)
                  ·
                    refine ⟨5470598930570913336853369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7294131907427884449137825 5470598930570913336853369)
                    ·
                      refine ⟨4102949197928185002640027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470598930570913336853369 4102949197928185002640027)
                      ·
                        rfl

theorem cell23_7990465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7990465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990465 prefixEnd_7990465 := by exact prefixLift 7990465
  have htrace : WordTrace (prefixWord ++ tailWord_7990465) baseStart_7990465 baseEnd_7990465 := by
    simpa [prefixWord, tailWord_7990465, baseEnd_7990465] using wordTrace_append hprefix tailTrace_7990465
  have hstable : (prefixWord ++ tailWord_7990465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990465).length < 2 ^ (prefixWord ++ tailWord_7990465).sum := by decide
  have hdescent : baseEnd_7990465 < baseStart_7990465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990504 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_7990504 : Nat := 118140960795 + 7990504 * 2 ^ 59
def prefixEnd_7990504 : Nat := 4983230072969 + 3 ^ 40 * 7990504 * 2
def baseEnd_7990504 : Nat := 4102969223673710350052347

theorem tailTrace_7990504 : CollatzResearch.WordTrace tailWord_7990504 prefixEnd_7990504 4102969223673710350052347 := by
  unfold tailWord_7990504
  simp only [CollatzResearch.WordTrace]
  refine ⟨145718811721888076140713283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194291748962517434854284377 145718811721888076140713283)
  ·
    refine ⟨218578217582832114211069925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145718811721888076140713283 218578217582832114211069925)
    ·
      refine ⟨40983415796781021414575611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218578217582832114211069925 40983415796781021414575611)
      ·
        refine ⟨61475123695171532121863417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40983415796781021414575611 61475123695171532121863417)
        ·
          refine ⟨46106342771378649091397563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61475123695171532121863417 46106342771378649091397563)
          ·
            refine ⟨69159514157067973637096345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46106342771378649091397563 69159514157067973637096345)
            ·
              refine ⟨51869635617800980227822259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69159514157067973637096345 51869635617800980227822259)
              ·
                refine ⟨77804453426701470341733389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51869635617800980227822259 77804453426701470341733389)
                ·
                  refine ⟨29176670035013051378150021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77804453426701470341733389 29176670035013051378150021)
                  ·
                    refine ⟨5470625631564947133403129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29176670035013051378150021 5470625631564947133403129)
                    ·
                      refine ⟨4102969223673710350052347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470625631564947133403129 4102969223673710350052347)
                      ·
                        rfl

theorem cell23_7990504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_7990504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990504 prefixEnd_7990504 := by exact prefixLift 7990504
  have htrace : WordTrace (prefixWord ++ tailWord_7990504) baseStart_7990504 baseEnd_7990504 := by
    simpa [prefixWord, tailWord_7990504, baseEnd_7990504] using wordTrace_append hprefix tailTrace_7990504
  have hstable : (prefixWord ++ tailWord_7990504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990504).length < 2 ^ (prefixWord ++ tailWord_7990504).sum := by decide
  have hdescent : baseEnd_7990504 < baseStart_7990504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990507 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5]
def baseStart_7990507 : Nat := 118140960795 + 7990507 * 2 ^ 59
def prefixEnd_7990507 : Nat := 4983230072969 + 3 ^ 40 * 7990507 * 2
def baseEnd_7990507 : Nat := 4102970764115673838314833

theorem tailTrace_7990507 : CollatzResearch.WordTrace tailWord_7990507 prefixEnd_7990507 4102970764115673838314833 := by
  unfold tailWord_7990507
  simp only [CollatzResearch.WordTrace]
  refine ⟨291437732862765283793785775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194291821908510189195857183 291437732862765283793785775)
  ·
    refine ⟨437156599294147925690678663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291437732862765283793785775 437156599294147925690678663)
    ·
      refine ⟨655734898941221888536017995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437156599294147925690678663 655734898941221888536017995)
      ·
        refine ⟨983602348411832832804026993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655734898941221888536017995 983602348411832832804026993)
        ·
          refine ⟨737701761308874624603020245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983602348411832832804026993 737701761308874624603020245)
          ·
            refine ⟨17289885030676749014133287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 737701761308874624603020245 17289885030676749014133287)
            ·
              refine ⟨25934827546015123521199931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17289885030676749014133287 25934827546015123521199931)
              ·
                refine ⟨38902241319022685281799897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25934827546015123521199931 38902241319022685281799897)
                ·
                  refine ⟨29176680989267013961349923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38902241319022685281799897 29176680989267013961349923)
                  ·
                    refine ⟨43765021483900520942024885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29176680989267013961349923 43765021483900520942024885)
                    ·
                      refine ⟨4102970764115673838314833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43765021483900520942024885 4102970764115673838314833)
                      ·
                        rfl

theorem cell23_7990507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 5].length) (baseStart_7990507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990507 prefixEnd_7990507 := by exact prefixLift 7990507
  have htrace : WordTrace (prefixWord ++ tailWord_7990507) baseStart_7990507 baseEnd_7990507 := by
    simpa [prefixWord, tailWord_7990507, baseEnd_7990507] using wordTrace_append hprefix tailTrace_7990507
  have hstable : (prefixWord ++ tailWord_7990507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990507).length < 2 ^ (prefixWord ++ tailWord_7990507).sum := by decide
  have hdescent : baseEnd_7990507 < baseStart_7990507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990516 : List Nat := [2, 6, 1, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7990516 : Nat := 118140960795 + 7990516 * 2 ^ 59
def prefixEnd_7990516 : Nat := 4983230072969 + 3 ^ 40 * 7990516 * 2
def baseEnd_7990516 : Nat := 4102975385441564303102293

theorem tailTrace_7990516 : CollatzResearch.WordTrace tailWord_7990516 prefixEnd_7990516 4102975385441564303102293 := by
  unfold tailWord_7990516
  simp only [CollatzResearch.WordTrace]
  refine ⟨145719030559866339165431701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194292040746488452220575601 145719030559866339165431701)
  ·
    refine ⟨6830579557493734648379611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145719030559866339165431701 6830579557493734648379611)
    ·
      refine ⟨10245869336240601972569417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6830579557493734648379611 10245869336240601972569417)
      ·
        refine ⟨7684402002180451479427063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10245869336240601972569417 7684402002180451479427063)
        ·
          refine ⟨11526603003270677219140595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684402002180451479427063 11526603003270677219140595)
          ·
            refine ⟨17289904504906015828710893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11526603003270677219140595 17289904504906015828710893)
            ·
              refine ⟨6483714189339755935766585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17289904504906015828710893 6483714189339755935766585)
              ·
                refine ⟨4862785642004816951824939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483714189339755935766585 4862785642004816951824939)
                ·
                  refine ⟨7294178463007225427737409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862785642004816951824939 7294178463007225427737409)
                  ·
                    refine ⟨5470633847255419070803057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7294178463007225427737409 5470633847255419070803057)
                    ·
                      refine ⟨4102975385441564303102293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470633847255419070803057 4102975385441564303102293)
                      ·
                        rfl

theorem cell23_7990516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7990516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990516 prefixEnd_7990516 := by exact prefixLift 7990516
  have htrace : WordTrace (prefixWord ++ tailWord_7990516) baseStart_7990516 baseEnd_7990516 := by
    simpa [prefixWord, tailWord_7990516, baseEnd_7990516] using wordTrace_append hprefix tailTrace_7990516
  have hstable : (prefixWord ++ tailWord_7990516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990516).length < 2 ^ (prefixWord ++ tailWord_7990516).sum := by decide
  have hdescent : baseEnd_7990516 < baseStart_7990516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990521 : List Nat := [1, 2, 1, 3, 1, 1, 4, 4, 2, 2, 2]
def baseStart_7990521 : Nat := 118140960795 + 7990521 * 2 ^ 59
def prefixEnd_7990521 : Nat := 4983230072969 + 3 ^ 40 * 7990521 * 2
def baseEnd_7990521 : Nat := 4102977952844836783539769

theorem tailTrace_7990521 : CollatzResearch.WordTrace tailWord_7990521 prefixEnd_7990521 4102977952844836783539769 := by
  unfold tailWord_7990521
  simp only [CollatzResearch.WordTrace]
  refine ⟨291438243484714564184795417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194292162323143042789863611 291438243484714564184795417)
  ·
    refine ⟨218578682613535923138596563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291438243484714564184795417 218578682613535923138596563)
    ·
      refine ⟨327868023920303884707894845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218578682613535923138596563 327868023920303884707894845)
      ·
        refine ⟨122950508970113956765460567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327868023920303884707894845 122950508970113956765460567)
        ·
          refine ⟨184425763455170935148190851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122950508970113956765460567 184425763455170935148190851)
          ·
            refine ⟨276638645182756402722286277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184425763455170935148190851 276638645182756402722286277)
            ·
              refine ⟨51869745971766825510428677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276638645182756402722286277 51869745971766825510428677)
              ·
                refine ⟨9725577369706279783205377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51869745971766825510428677 9725577369706279783205377)
                ·
                  refine ⟨7294183027279709837404033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9725577369706279783205377 7294183027279709837404033)
                  ·
                    refine ⟨5470637270459782378053025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7294183027279709837404033 5470637270459782378053025)
                    ·
                      refine ⟨4102977952844836783539769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470637270459782378053025 4102977952844836783539769)
                      ·
                        rfl

theorem cell23_7990521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_7990521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990521 prefixEnd_7990521 := by exact prefixLift 7990521
  have htrace : WordTrace (prefixWord ++ tailWord_7990521) baseStart_7990521 baseEnd_7990521 := by
    simpa [prefixWord, tailWord_7990521, baseEnd_7990521] using wordTrace_append hprefix tailTrace_7990521
  have hstable : (prefixWord ++ tailWord_7990521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990521).length < 2 ^ (prefixWord ++ tailWord_7990521).sum := by decide
  have hdescent : baseEnd_7990521 < baseStart_7990521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990527 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 7]
def baseStart_7990527 : Nat := 118140960795 + 7990527 * 2 ^ 59
def prefixEnd_7990527 : Nat := 4983230072969 + 3 ^ 40 * 7990527 * 2
def baseEnd_7990527 : Nat := 455886781525418195562749

theorem tailTrace_7990527 : CollatzResearch.WordTrace tailWord_7990527 prefixEnd_7990527 455886781525418195562749 := by
  unfold tailWord_7990527
  simp only [CollatzResearch.WordTrace]
  refine ⟨291438462322692827209513835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194292308215128551473009223 291438462322692827209513835)
  ·
    refine ⟨437157693484039240814270753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291438462322692827209513835 437157693484039240814270753)
    ·
      refine ⟨327868270113029430610703065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437157693484039240814270753 327868270113029430610703065)
      ·
        refine ⟨245901202584772072958027299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327868270113029430610703065 245901202584772072958027299)
        ·
          refine ⟨368851803877158109437040949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245901202584772072958027299 368851803877158109437040949)
          ·
            refine ⟨34579856613483572759722589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368851803877158109437040949 34579856613483572759722589)
            ·
              refine ⟨12967446230056339784895971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34579856613483572759722589 12967446230056339784895971)
              ·
                refine ⟨19451169345084509677343957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12967446230056339784895971 19451169345084509677343957)
                ·
                  refine ⟨455886781525418195562749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19451169345084509677343957 455886781525418195562749)
                  ·
                    rfl

theorem cell23_7990527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 7].length) (baseStart_7990527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990527 prefixEnd_7990527 := by exact prefixLift 7990527
  have htrace : WordTrace (prefixWord ++ tailWord_7990527) baseStart_7990527 baseEnd_7990527 := by
    simpa [prefixWord, tailWord_7990527, baseEnd_7990527] using wordTrace_append hprefix tailTrace_7990527
  have hstable : (prefixWord ++ tailWord_7990527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990527).length < 2 ^ (prefixWord ++ tailWord_7990527).sum := by decide
  have hdescent : baseEnd_7990527 < baseStart_7990527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990537 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 3]
def baseStart_7990537 : Nat := 118140960795 + 7990537 * 2 ^ 59
def prefixEnd_7990537 : Nat := 4983230072969 + 3 ^ 40 * 7990537 * 2
def baseEnd_7990537 : Nat := 4102986168535308720939695

theorem tailTrace_7990537 : CollatzResearch.WordTrace tailWord_7990537 prefixEnd_7990537 4102986168535308720939695 := by
  unfold tailWord_7990537
  simp only [CollatzResearch.WordTrace]
  refine ⟨291438827052656598917377865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194292551368437732611585243 291438827052656598917377865)
  ·
    refine ⟨218579120289492449188033399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291438827052656598917377865 218579120289492449188033399)
    ·
      refine ⟨327868680434238673782050099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218579120289492449188033399 327868680434238673782050099)
      ·
        refine ⟨491803020651358010673075149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327868680434238673782050099 491803020651358010673075149)
        ·
          refine ⟨184426132744259254002403181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491803020651358010673075149 184426132744259254002403181)
          ·
            refine ⟨69159799779097220250901193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184426132744259254002403181 69159799779097220250901193)
            ·
              refine ⟨51869849834322915188175895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69159799779097220250901193 51869849834322915188175895)
              ·
                refine ⟨77804774751484372782263843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51869849834322915188175895 77804774751484372782263843)
                ·
                  refine ⟨116707162127226559173395765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77804774751484372782263843 116707162127226559173395765)
                  ·
                    refine ⟨10941296449427489922505853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116707162127226559173395765 10941296449427489922505853)
                    ·
                      refine ⟨4102986168535308720939695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10941296449427489922505853 4102986168535308720939695)
                      ·
                        rfl

theorem cell23_7990537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_7990537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990537 prefixEnd_7990537 := by exact prefixLift 7990537
  have htrace : WordTrace (prefixWord ++ tailWord_7990537) baseStart_7990537 baseEnd_7990537 := by
    simpa [prefixWord, tailWord_7990537, baseEnd_7990537] using wordTrace_append hprefix tailTrace_7990537
  have hstable : (prefixWord ++ tailWord_7990537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990537).length < 2 ^ (prefixWord ++ tailWord_7990537).sum := by decide
  have hdescent : baseEnd_7990537 < baseStart_7990537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990578 : List Nat := [3, 2, 1, 1, 4, 3, 2, 2, 5]
def baseStart_7990578 : Nat := 118140960795 + 7990578 * 2 ^ 59
def prefixEnd_7990578 : Nat := 4983230072969 + 3 ^ 40 * 7990578 * 2
def baseEnd_7990578 : Nat := 455889691249127006725223

theorem tailTrace_7990578 : CollatzResearch.WordTrace tailWord_7990578 prefixEnd_7990578 455889691249127006725223 := by
  unfold tailWord_7990578
  simp only [CollatzResearch.WordTrace]
  refine ⟨72860080611377015729905097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194293548297005375279746925 72860080611377015729905097)
  ·
    refine ⟨54645060458532761797428823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72860080611377015729905097 54645060458532761797428823)
    ·
      refine ⟨81967590687799142696143235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54645060458532761797428823 81967590687799142696143235)
      ·
        refine ⟨122951386031698714044214853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81967590687799142696143235 122951386031698714044214853)
        ·
          refine ⟨23053384880943508883290285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122951386031698714044214853 23053384880943508883290285)
          ·
            refine ⟨8645019330353815831233857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23053384880943508883290285 8645019330353815831233857)
            ·
              refine ⟨6483764497765361873425393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8645019330353815831233857 6483764497765361873425393)
              ·
                refine ⟨4862823373324021405069045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483764497765361873425393 4862823373324021405069045)
                ·
                  refine ⟨455889691249127006725223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4862823373324021405069045 455889691249127006725223)
                  ·
                    rfl

theorem cell23_7990578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_7990578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990578 prefixEnd_7990578 := by exact prefixLift 7990578
  have htrace : WordTrace (prefixWord ++ tailWord_7990578) baseStart_7990578 baseEnd_7990578 := by
    simpa [prefixWord, tailWord_7990578, baseEnd_7990578] using wordTrace_append hprefix tailTrace_7990578
  have hstable : (prefixWord ++ tailWord_7990578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990578).length < 2 ^ (prefixWord ++ tailWord_7990578).sum := by decide
  have hdescent : baseEnd_7990578 < baseStart_7990578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990604 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_7990604 : Nat := 118140960795 + 7990604 * 2 ^ 59
def prefixEnd_7990604 : Nat := 4983230072969 + 3 ^ 40 * 7990604 * 2
def baseEnd_7990604 : Nat := 1367673523913053319600629

theorem tailTrace_7990604 : CollatzResearch.WordTrace tailWord_7990604 prefixEnd_7990604 1367673523913053319600629 := by
  unfold tailWord_7990604
  simp only [CollatzResearch.WordTrace]
  refine ⟨145720635371706934680033433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194294180495609246240044577 145720635371706934680033433)
  ·
    refine ⟨109290476528780201010025075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145720635371706934680033433 109290476528780201010025075)
    ·
      refine ⟨163935714793170301515037613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109290476528780201010025075 163935714793170301515037613)
      ·
        refine ⟨61475893047438863068139105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163935714793170301515037613 61475893047438863068139105)
        ·
          refine ⟨46106919785579147301104329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61475893047438863068139105 46106919785579147301104329)
          ·
            refine ⟨34580189839184360475828247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46106919785579147301104329 34580189839184360475828247)
            ·
              refine ⟨51870284758776540713742371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34580189839184360475828247 51870284758776540713742371)
              ·
                refine ⟨77805427138164811070613557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51870284758776540713742371 77805427138164811070613557)
                ·
                  refine ⟨7294258794202951037870021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77805427138164811070613557 7294258794202951037870021)
                  ·
                    refine ⟨1367673523913053319600629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7294258794202951037870021 1367673523913053319600629)
                    ·
                      rfl

theorem cell23_7990604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_7990604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990604 prefixEnd_7990604 := by exact prefixLift 7990604
  have htrace : WordTrace (prefixWord ++ tailWord_7990604) baseStart_7990604 baseEnd_7990604 := by
    simpa [prefixWord, tailWord_7990604, baseEnd_7990604] using wordTrace_append hprefix tailTrace_7990604
  have hstable : (prefixWord ++ tailWord_7990604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990604).length < 2 ^ (prefixWord ++ tailWord_7990604).sum := by decide
  have hdescent : baseEnd_7990604 < baseStart_7990604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990661 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 3]
def baseStart_7990661 : Nat := 118140960795 + 7990661 * 2 ^ 59
def prefixEnd_7990661 : Nat := 4983230072969 + 3 ^ 40 * 7990661 * 2
def baseEnd_7990661 : Nat := 4103049840136466235789125

theorem tailTrace_7990661 : CollatzResearch.WordTrace tailWord_7990661 prefixEnd_7990661 4103049840136466235789125 := by
  unfold tailWord_7990661
  simp only [CollatzResearch.WordTrace]
  refine ⟨291443349704207368094891837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194295566469471578729927891 291443349704207368094891837)
  ·
    refine ⟨109291256139077763035584439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291443349704207368094891837 109291256139077763035584439)
    ·
      refine ⟨163936884208616644553376659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109291256139077763035584439 163936884208616644553376659)
      ·
        refine ⟨245905326312924966830064989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163936884208616644553376659 245905326312924966830064989)
        ·
          refine ⟨92214497367346862561274371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245905326312924966830064989 92214497367346862561274371)
          ·
            refine ⟨138321746051020293841911557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92214497367346862561274371 138321746051020293841911557)
            ·
              refine ⟨25935327384566305095358417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138321746051020293841911557 25935327384566305095358417)
              ·
                refine ⟨19451495538424728821518813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25935327384566305095358417 19451495538424728821518813)
                ·
                  refine ⟨7294310826909273308069555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19451495538424728821518813 7294310826909273308069555)
                  ·
                    refine ⟨10941466240363909962104333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7294310826909273308069555 10941466240363909962104333)
                    ·
                      refine ⟨4103049840136466235789125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10941466240363909962104333 4103049840136466235789125)
                      ·
                        rfl

theorem cell23_7990661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_7990661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990661 prefixEnd_7990661 := by exact prefixLift 7990661
  have htrace : WordTrace (prefixWord ++ tailWord_7990661) baseStart_7990661 baseEnd_7990661 := by
    simpa [prefixWord, tailWord_7990661, baseEnd_7990661] using wordTrace_append hprefix tailTrace_7990661
  have hstable : (prefixWord ++ tailWord_7990661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990661).length < 2 ^ (prefixWord ++ tailWord_7990661).sum := by decide
  have hdescent : baseEnd_7990661 < baseStart_7990661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990711 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 2, 4]
def baseStart_7990711 : Nat := 118140960795 + 7990711 * 2 ^ 59
def prefixEnd_7990711 : Nat := 4983230072969 + 3 ^ 40 * 7990711 * 2
def baseEnd_7990711 : Nat := 1367691838056397013387965

theorem tailTrace_7990711 : CollatzResearch.WordTrace tailWord_7990711 prefixEnd_7990711 1367691838056397013387965 := by
  unfold tailWord_7990711
  simp only [CollatzResearch.WordTrace]
  refine ⟨291445173354026226634211987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194296782236017484422807991 291445173354026226634211987)
  ·
    refine ⟨437167760031039339951317981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291445173354026226634211987 437167760031039339951317981)
    ·
      refine ⟨163937910011639752481744243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437167760031039339951317981 163937910011639752481744243)
      ·
        refine ⟨245906865017459628722616365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163937910011639752481744243 245906865017459628722616365)
        ·
          refine ⟨92215074381547360770981137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245906865017459628722616365 92215074381547360770981137)
          ·
            refine ⟨69161305786160520578235853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92215074381547360770981137 69161305786160520578235853)
            ·
              refine ⟨25935489669810195216838445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69161305786160520578235853 25935489669810195216838445)
              ·
                refine ⟨9725808626178823206314417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25935489669810195216838445 9725808626178823206314417)
                ·
                  refine ⟨7294356469634117404735813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9725808626178823206314417 7294356469634117404735813)
                  ·
                    refine ⟨1367691838056397013387965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7294356469634117404735813 1367691838056397013387965)
                    ·
                      rfl

theorem cell23_7990711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_7990711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990711 prefixEnd_7990711 := by exact prefixLift 7990711
  have htrace : WordTrace (prefixWord ++ tailWord_7990711) baseStart_7990711 baseEnd_7990711 := by
    simpa [prefixWord, tailWord_7990711, baseEnd_7990711] using wordTrace_append hprefix tailTrace_7990711
  have hstable : (prefixWord ++ tailWord_7990711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990711).length < 2 ^ (prefixWord ++ tailWord_7990711).sum := by decide
  have hdescent : baseEnd_7990711 < baseStart_7990711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990718 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_7990718 : Nat := 118140960795 + 7990718 * 2 ^ 59
def prefixEnd_7990718 : Nat := 4983230072969 + 3 ^ 40 * 7990718 * 2
def baseEnd_7990718 : Nat := 4103079108533772512776363

theorem tailTrace_7990718 : CollatzResearch.WordTrace tailWord_7990718 prefixEnd_7990718 4103079108533772512776363 := by
  unfold tailWord_7990718
  simp only [CollatzResearch.WordTrace]
  refine ⟨36430678583125108353714601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194296952443333911219811205 36430678583125108353714601)
  ·
    refine ⟨27323008937343831265285951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36430678583125108353714601 27323008937343831265285951)
    ·
      refine ⟨40984513406015746897928927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27323008937343831265285951 40984513406015746897928927)
      ·
        refine ⟨61476770109023620346893391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40984513406015746897928927 61476770109023620346893391)
        ·
          refine ⟨92215155163535430520340087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61476770109023620346893391 92215155163535430520340087)
          ·
            refine ⟨138322732745303145780510131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92215155163535430520340087 138322732745303145780510131)
            ·
              refine ⟨207484099117954718670765197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138322732745303145780510131 207484099117954718670765197)
              ·
                refine ⟨77806537169233019501536949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207484099117954718670765197 77806537169233019501536949)
                ·
                  refine ⟨7294362859615595578269089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77806537169233019501536949 7294362859615595578269089)
                  ·
                    refine ⟨5470772144711696683701817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7294362859615595578269089 5470772144711696683701817)
                    ·
                      refine ⟨4103079108533772512776363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470772144711696683701817 4103079108533772512776363)
                      ·
                        rfl

theorem cell23_7990718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_7990718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990718 prefixEnd_7990718 := by exact prefixLift 7990718
  have htrace : WordTrace (prefixWord ++ tailWord_7990718) baseStart_7990718 baseEnd_7990718 := by
    simpa [prefixWord, tailWord_7990718, baseEnd_7990718] using wordTrace_append hprefix tailTrace_7990718
  have hstable : (prefixWord ++ tailWord_7990718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990718).length < 2 ^ (prefixWord ++ tailWord_7990718).sum := by decide
  have hdescent : baseEnd_7990718 < baseStart_7990718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990768 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 2, 1, 3]
def baseStart_7990768 : Nat := 118140960795 + 7990768 * 2 ^ 59
def prefixEnd_7990768 : Nat := 4983230072969 + 3 ^ 40 * 7990768 * 2
def baseEnd_7990768 : Nat := 4103104782566497317151133

theorem tailTrace_7990768 : CollatzResearch.WordTrace tailWord_7990768 prefixEnd_7990768 4103104782566497317151133 := by
  unfold tailWord_7990768
  simp only [CollatzResearch.WordTrace]
  refine ⟨145723626157409862684518479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194298168209879816912691305 145723626157409862684518479)
  ·
    refine ⟨218585439236114794026777719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145723626157409862684518479 218585439236114794026777719)
    ·
      refine ⟨327878158854172191040166579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218585439236114794026777719 327878158854172191040166579)
      ·
        refine ⟨491817238281258286560249869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327878158854172191040166579 491817238281258286560249869)
        ·
          refine ⟨184431464355471857460093701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491817238281258286560249869 184431464355471857460093701)
          ·
            refine ⟨34580899566650973273767569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184431464355471857460093701 34580899566650973273767569)
            ·
              refine ⟨25935674674988229955325677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34580899566650973273767569 25935674674988229955325677)
              ·
                refine ⟨9725878003120586233247129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25935674674988229955325677 9725878003120586233247129)
                ·
                  refine ⟨7294408502340439674935347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9725878003120586233247129 7294408502340439674935347)
                  ·
                    refine ⟨10941612753510659512403021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7294408502340439674935347 10941612753510659512403021)
                    ·
                      refine ⟨4103104782566497317151133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10941612753510659512403021 4103104782566497317151133)
                      ·
                        rfl

theorem cell23_7990768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 1, 3].length) (baseStart_7990768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990768 prefixEnd_7990768 := by exact prefixLift 7990768
  have htrace : WordTrace (prefixWord ++ tailWord_7990768) baseStart_7990768 baseEnd_7990768 := by
    simpa [prefixWord, tailWord_7990768, baseEnd_7990768] using wordTrace_append hprefix tailTrace_7990768
  have hstable : (prefixWord ++ tailWord_7990768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990768).length < 2 ^ (prefixWord ++ tailWord_7990768).sum := by decide
  have hdescent : baseEnd_7990768 < baseStart_7990768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990778 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2]
def baseStart_7990778 : Nat := 118140960795 + 7990778 * 2 ^ 59
def prefixEnd_7990778 : Nat := 4983230072969 + 3 ^ 40 * 7990778 * 2
def baseEnd_7990778 : Nat := 4103109917373042278026087

theorem tailTrace_7990778 : CollatzResearch.WordTrace tailWord_7990778 prefixEnd_7990778 4103109917373042278026087 := by
  unfold tailWord_7990778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72861904261195874269225247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194298411363188998051267325 72861904261195874269225247)
  ·
    refine ⟨109292856391793811403837871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72861904261195874269225247 109292856391793811403837871)
    ·
      refine ⟨163939284587690717105756807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109292856391793811403837871 163939284587690717105756807)
      ·
        refine ⟨245908926881536075658635211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163939284587690717105756807 245908926881536075658635211)
        ·
          refine ⟨368863390322304113487952817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245908926881536075658635211 368863390322304113487952817)
          ·
            refine ⟨276647542741728085115964613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368863390322304113487952817 276647542741728085115964613)
            ·
              refine ⟨51871414264074015959243365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276647542741728085115964613 51871414264074015959243365)
              ·
                refine ⟨9725890174513877992358131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51871414264074015959243365 9725890174513877992358131)
                ·
                  refine ⟨14588835261770816988537197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9725890174513877992358131 14588835261770816988537197)
                  ·
                    refine ⟨5470813223164056370701449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14588835261770816988537197 5470813223164056370701449)
                    ·
                      refine ⟨4103109917373042278026087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470813223164056370701449 4103109917373042278026087)
                      ·
                        rfl

theorem cell23_7990778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_7990778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990778 prefixEnd_7990778 := by exact prefixLift 7990778
  have htrace : WordTrace (prefixWord ++ tailWord_7990778) baseStart_7990778 baseEnd_7990778 := by
    simpa [prefixWord, tailWord_7990778, baseEnd_7990778] using wordTrace_append hprefix tailTrace_7990778
  have hstable : (prefixWord ++ tailWord_7990778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990778).length < 2 ^ (prefixWord ++ tailWord_7990778).sum := by decide
  have hdescent : baseEnd_7990778 < baseStart_7990778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990795 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 1, 3, 2]
def baseStart_7990795 : Nat := 118140960795 + 7990795 * 2 ^ 59
def prefixEnd_7990795 : Nat := 4983230072969 + 3 ^ 40 * 7990795 * 2
def baseEnd_7990795 : Nat := 4103118646544168711513509

theorem tailTrace_7990795 : CollatzResearch.WordTrace tailWord_7990795 prefixEnd_7990795 4103118646544168711513509 := by
  unfold tailWord_7990795
  simp only [CollatzResearch.WordTrace]
  refine ⟨291448237085721908980269839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194298824723814605986846559 291448237085721908980269839)
  ·
    refine ⟨437172355628582863470404759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291448237085721908980269839 437172355628582863470404759)
    ·
      refine ⟨655758533442874295205607139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437172355628582863470404759 655758533442874295205607139)
      ·
        refine ⟨983637800164311442808410709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655758533442874295205607139 983637800164311442808410709)
        ·
          refine ⟨11527005470675524720411063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 983637800164311442808410709 11527005470675524720411063)
          ·
            refine ⟨17290508206013287080616595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527005470675524720411063 17290508206013287080616595)
            ·
              refine ⟨25935762309019930620924893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17290508206013287080616595 25935762309019930620924893)
              ·
                refine ⟨9725910865882473982846835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25935762309019930620924893 9725910865882473982846835)
                ·
                  refine ⟨14588866298823710974270253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9725910865882473982846835 14588866298823710974270253)
                  ·
                    refine ⟨5470824862058891615351345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14588866298823710974270253 5470824862058891615351345)
                    ·
                      refine ⟨4103118646544168711513509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470824862058891615351345 4103118646544168711513509)
                      ·
                        rfl

theorem cell23_7990795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 3, 2].length) (baseStart_7990795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990795 prefixEnd_7990795 := by exact prefixLift 7990795
  have htrace : WordTrace (prefixWord ++ tailWord_7990795) baseStart_7990795 baseEnd_7990795 := by
    simpa [prefixWord, tailWord_7990795, baseEnd_7990795] using wordTrace_append hprefix tailTrace_7990795
  have hstable : (prefixWord ++ tailWord_7990795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990795).length < 2 ^ (prefixWord ++ tailWord_7990795).sum := by decide
  have hdescent : baseEnd_7990795 < baseStart_7990795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990851 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 7, 2]
def baseStart_7990851 : Nat := 118140960795 + 7990851 * 2 ^ 59
def prefixEnd_7990851 : Nat := 4983230072969 + 3 ^ 40 * 7990851 * 2
def baseEnd_7990851 : Nat := 4103147401460820492413251

theorem tailTrace_7990851 : CollatzResearch.WordTrace tailWord_7990851 prefixEnd_7990851 4103147401460820492413251 := by
  unfold tailWord_7990851
  simp only [CollatzResearch.WordTrace]
  refine ⟨291450279573519030544308407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194300186382346020362872271 291450279573519030544308407)
  ·
    refine ⟨437175419360278545816462611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291450279573519030544308407 437175419360278545816462611)
    ·
      refine ⟨655763129040417818724693917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437175419360278545816462611 655763129040417818724693917)
      ·
        refine ⟨245911173390156682021760219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655763129040417818724693917 245911173390156682021760219)
        ·
          refine ⟨368866760085235023032640329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245911173390156682021760219 368866760085235023032640329)
          ·
            refine ⟨276650070063926267274480247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368866760085235023032640329 276650070063926267274480247)
            ·
              refine ⟨414975105095889400911720371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276650070063926267274480247 414975105095889400911720371)
              ·
                refine ⟨622462657643834101367580557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414975105095889400911720371 622462657643834101367580557)
                ·
                  refine ⟨233423496616437788012842709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622462657643834101367580557 233423496616437788012842709)
                  ·
                    refine ⟨5470863201947760656551001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 233423496616437788012842709 5470863201947760656551001)
                    ·
                      refine ⟨4103147401460820492413251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470863201947760656551001 4103147401460820492413251)
                      ·
                        rfl

theorem cell23_7990851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7, 2].length) (baseStart_7990851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990851 prefixEnd_7990851 := by exact prefixLift 7990851
  have htrace : WordTrace (prefixWord ++ tailWord_7990851) baseStart_7990851 baseEnd_7990851 := by
    simpa [prefixWord, tailWord_7990851, baseEnd_7990851] using wordTrace_append hprefix tailTrace_7990851
  have hstable : (prefixWord ++ tailWord_7990851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990851).length < 2 ^ (prefixWord ++ tailWord_7990851).sum := by decide
  have hdescent : baseEnd_7990851 < baseStart_7990851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990868 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_7990868 : Nat := 118140960795 + 7990868 * 2 ^ 59
def prefixEnd_7990868 : Nat := 4983230072969 + 3 ^ 40 * 7990868 * 2
def baseEnd_7990868 : Nat := 4103156130631946925900673

theorem tailTrace_7990868 : CollatzResearch.WordTrace tailWord_7990868 prefixEnd_7990868 4103156130631946925900673 := by
  unfold tailWord_7990868
  simp only [CollatzResearch.WordTrace]
  refine ⟨145725449807228721223838629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194300599742971628298451505 145725449807228721223838629)
  ·
    refine ⟨27323521838855385229469743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145725449807228721223838629 27323521838855385229469743)
    ·
      refine ⟨40985282758283077844204615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27323521838855385229469743 40985282758283077844204615)
      ·
        refine ⟨61477924137424616766306923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40985282758283077844204615 61477924137424616766306923)
        ·
          refine ⟨92216886206136925149460385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61477924137424616766306923 92216886206136925149460385)
          ·
            refine ⟨69162664654602693862095289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92216886206136925149460385 69162664654602693862095289)
            ·
              refine ⟨51871998490952020396571467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69162664654602693862095289 51871998490952020396571467)
              ·
                refine ⟨77807997736428030594857201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51871998490952020396571467 77807997736428030594857201)
                ·
                  refine ⟨58355998302321022946142901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77807997736428030594857201 58355998302321022946142901)
                  ·
                    refine ⟨5470874840842595901200897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58355998302321022946142901 5470874840842595901200897)
                    ·
                      refine ⟨4103156130631946925900673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470874840842595901200897 4103156130631946925900673)
                      ·
                        rfl

theorem cell23_7990868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_7990868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990868 prefixEnd_7990868 := by exact prefixLift 7990868
  have htrace : WordTrace (prefixWord ++ tailWord_7990868) baseStart_7990868 baseEnd_7990868 := by
    simpa [prefixWord, tailWord_7990868, baseEnd_7990868] using wordTrace_append hprefix tailTrace_7990868
  have hstable : (prefixWord ++ tailWord_7990868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990868).length < 2 ^ (prefixWord ++ tailWord_7990868).sum := by decide
  have hdescent : baseEnd_7990868 < baseStart_7990868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990871 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_7990871 : Nat := 118140960795 + 7990871 * 2 ^ 59
def prefixEnd_7990871 : Nat := 4983230072969 + 3 ^ 40 * 7990871 * 2
def baseEnd_7990871 : Nat := 4103157671073910414163159

theorem tailTrace_7990871 : CollatzResearch.WordTrace tailWord_7990871 prefixEnd_7990871 4103157671073910414163159 := by
  unfold tailWord_7990871
  simp only [CollatzResearch.WordTrace]
  refine ⟨291451009033446573960036467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194300672688964382640024311 291451009033446573960036467)
  ·
    refine ⟨437176513550169860940054701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291451009033446573960036467 437176513550169860940054701)
    ·
      refine ⟨163941192581313697852520513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437176513550169860940054701 163941192581313697852520513)
      ·
        refine ⟨122955894435985273389390385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163941192581313697852520513 122955894435985273389390385)
        ·
          refine ⟨92216920826988955042042789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122955894435985273389390385 92216920826988955042042789)
          ·
            refine ⟨17290672655060429070383023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92216920826988955042042789 17290672655060429070383023)
            ·
              refine ⟨25936008982590643605574535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17290672655060429070383023 25936008982590643605574535)
              ·
                refine ⟨38904013473885965408361803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25936008982590643605574535 38904013473885965408361803)
                ·
                  refine ⟨58356020210828948112542705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38904013473885965408361803 58356020210828948112542705)
                  ·
                    refine ⟨43767015158121711084407029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58356020210828948112542705 43767015158121711084407029)
                    ·
                      refine ⟨4103157671073910414163159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43767015158121711084407029 4103157671073910414163159)
                      ·
                        rfl

theorem cell23_7990871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_7990871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990871 prefixEnd_7990871 := by exact prefixLift 7990871
  have htrace : WordTrace (prefixWord ++ tailWord_7990871) baseStart_7990871 baseEnd_7990871 := by
    simpa [prefixWord, tailWord_7990871, baseEnd_7990871] using wordTrace_append hprefix tailTrace_7990871
  have hstable : (prefixWord ++ tailWord_7990871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990871).length < 2 ^ (prefixWord ++ tailWord_7990871).sum := by decide
  have hdescent : baseEnd_7990871 < baseStart_7990871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990881 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_7990881 : Nat := 118140960795 + 7990881 * 2 ^ 59
def prefixEnd_7990881 : Nat := 4983230072969 + 3 ^ 40 * 7990881 * 2
def baseEnd_7990881 : Nat := 4103162805880455375038113

theorem tailTrace_7990881 : CollatzResearch.WordTrace tailWord_7990881 prefixEnd_7990881 4103162805880455375038113 := by
  unfold tailWord_7990881
  simp only [CollatzResearch.WordTrace]
  refine ⟨291451373763410345667900497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194300915842273563778600331 291451373763410345667900497)
  ·
    refine ⟨218588530322557759250925373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291451373763410345667900497 218588530322557759250925373)
    ·
      refine ⟨81970698870959159719097015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218588530322557759250925373 81970698870959159719097015)
      ·
        refine ⟨122956048306438739578645523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81970698870959159719097015 122956048306438739578645523)
        ·
          refine ⟨184434072459658109367968285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122956048306438739578645523 184434072459658109367968285)
          ·
            refine ⟨69162777172371791012988107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184434072459658109367968285 69162777172371791012988107)
            ·
              refine ⟨103744165758557686519482161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69162777172371791012988107 103744165758557686519482161)
              ·
                refine ⟨77808124318918264889611621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103744165758557686519482161 77808124318918264889611621)
                ·
                  refine ⟨14589023309797174666802179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77808124318918264889611621 14589023309797174666802179)
                  ·
                    refine ⟨21883534964695762000203269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14589023309797174666802179 21883534964695762000203269)
                    ·
                      refine ⟨4103162805880455375038113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21883534964695762000203269 4103162805880455375038113)
                      ·
                        rfl

theorem cell23_7990881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_7990881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990881 prefixEnd_7990881 := by exact prefixLift 7990881
  have htrace : WordTrace (prefixWord ++ tailWord_7990881) baseStart_7990881 baseEnd_7990881 := by
    simpa [prefixWord, tailWord_7990881, baseEnd_7990881] using wordTrace_append hprefix tailTrace_7990881
  have hstable : (prefixWord ++ tailWord_7990881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990881).length < 2 ^ (prefixWord ++ tailWord_7990881).sum := by decide
  have hdescent : baseEnd_7990881 < baseStart_7990881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990898 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_7990898 : Nat := 118140960795 + 7990898 * 2 ^ 59
def prefixEnd_7990898 : Nat := 4983230072969 + 3 ^ 40 * 7990898 * 2
def baseEnd_7990898 : Nat := 4103171535051581808525535

theorem tailTrace_7990898 : CollatzResearch.WordTrace tailWord_7990898 prefixEnd_7990898 4103171535051581808525535 := by
  unfold tailWord_7990898
  simp only [CollatzResearch.WordTrace]
  refine ⟨72862998451087189392817337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194301329202899171714179565 72862998451087189392817337)
  ·
    refine ⟨54647248838315392044613003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72862998451087189392817337 54647248838315392044613003)
    ·
      refine ⟨81970873257473088066919505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54647248838315392044613003 81970873257473088066919505)
      ·
        refine ⟨61478154943104816050189629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81970873257473088066919505 61478154943104816050189629)
        ·
          refine ⟨23054308103664306018821111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61478154943104816050189629 23054308103664306018821111)
          ·
            refine ⟨34581462155496459028231667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23054308103664306018821111 34581462155496459028231667)
            ·
              refine ⟨51872193233244688542347501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34581462155496459028231667 51872193233244688542347501)
              ·
                refine ⟨19452072462466758203380313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51872193233244688542347501 19452072462466758203380313)
                ·
                  refine ⟨14589054346850068652535235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19452072462466758203380313 14589054346850068652535235)
                  ·
                    refine ⟨21883581520275102978802853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14589054346850068652535235 21883581520275102978802853)
                    ·
                      refine ⟨4103171535051581808525535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21883581520275102978802853 4103171535051581808525535)
                      ·
                        rfl

theorem cell23_7990898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_7990898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990898 prefixEnd_7990898 := by exact prefixLift 7990898
  have htrace : WordTrace (prefixWord ++ tailWord_7990898) baseStart_7990898 baseEnd_7990898 := by
    simpa [prefixWord, tailWord_7990898, baseEnd_7990898] using wordTrace_append hprefix tailTrace_7990898
  have hstable : (prefixWord ++ tailWord_7990898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990898).length < 2 ^ (prefixWord ++ tailWord_7990898).sum := by decide
  have hdescent : baseEnd_7990898 < baseStart_7990898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990921 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 6]
def baseStart_7990921 : Nat := 118140960795 + 7990921 * 2 ^ 59
def prefixEnd_7990921 : Nat := 4983230072969 + 3 ^ 40 * 7990921 * 2
def baseEnd_7990921 : Nat := 455909260567403913170881

theorem tailTrace_7990921 : CollatzResearch.WordTrace tailWord_7990921 prefixEnd_7990921 455909260567403913170881 := by
  unfold tailWord_7990921
  simp only [CollatzResearch.WordTrace]
  refine ⟨291452832683265432499356617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194301888455510288332904411 291452832683265432499356617)
  ·
    refine ⟨218589624512449074374517463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291452832683265432499356617 218589624512449074374517463)
    ·
      refine ⟨327884436768673611561776195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218589624512449074374517463 327884436768673611561776195)
      ·
        refine ⟨491826655153010417342664293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327884436768673611561776195 491826655153010417342664293)
        ·
          refine ⟨92217497841189453251749555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 491826655153010417342664293 92217497841189453251749555)
          ·
            refine ⟨138326246761784179877624333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92217497841189453251749555 138326246761784179877624333)
            ·
              refine ⟨51872342535669067454109125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138326246761784179877624333 51872342535669067454109125)
              ·
                refine ⟨9726064225437950147645461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51872342535669067454109125 9726064225437950147645461)
                ·
                  refine ⟨455909260567403913170881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9726064225437950147645461 455909260567403913170881)
                  ·
                    rfl

theorem cell23_7990921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 6].length) (baseStart_7990921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990921 prefixEnd_7990921 := by exact prefixLift 7990921
  have htrace : WordTrace (prefixWord ++ tailWord_7990921) baseStart_7990921 baseEnd_7990921 := by
    simpa [prefixWord, tailWord_7990921, baseEnd_7990921] using wordTrace_append hprefix tailTrace_7990921
  have hstable : (prefixWord ++ tailWord_7990921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990921).length < 2 ^ (prefixWord ++ tailWord_7990921).sum := by decide
  have hdescent : baseEnd_7990921 < baseStart_7990921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7990932 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7990932 : Nat := 118140960795 + 7990932 * 2 ^ 59
def prefixEnd_7990932 : Nat := 4983230072969 + 3 ^ 40 * 7990932 * 2
def baseEnd_7990932 : Nat := 4103188993393834675500379

theorem tailTrace_7990932 : CollatzResearch.WordTrace tailWord_7990932 prefixEnd_7990932 4103188993393834675500379 := by
  unfold tailWord_7990932
  simp only [CollatzResearch.WordTrace]
  refine ⟨145726616943112790689003525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194302155924150387585338033 145726616943112790689003525)
  ·
    refine ⟨27323740676833648254188161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145726616943112790689003525 27323740676833648254188161)
    ·
      refine ⟨20492805507625236190641121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27323740676833648254188161 20492805507625236190641121)
      ·
        refine ⟨15369604130718927142980841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20492805507625236190641121 15369604130718927142980841)
        ·
          refine ⟨11527203098039195357235631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15369604130718927142980841 11527203098039195357235631)
          ·
            refine ⟨17290804647058793035853447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527203098039195357235631 17290804647058793035853447)
            ·
              refine ⟨25936206970588189553780171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17290804647058793035853447 25936206970588189553780171)
              ·
                refine ⟨38904310455882284330670257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25936206970588189553780171 38904310455882284330670257)
                ·
                  refine ⟨29178232841911713248002693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38904310455882284330670257 29178232841911713248002693)
                  ·
                    refine ⟨5470918657858446234000505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29178232841911713248002693 5470918657858446234000505)
                    ·
                      refine ⟨4103188993393834675500379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5470918657858446234000505 4103188993393834675500379)
                      ·
                        rfl

theorem cell23_7990932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7990932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7990932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7990932 prefixEnd_7990932 := by exact prefixLift 7990932
  have htrace : WordTrace (prefixWord ++ tailWord_7990932) baseStart_7990932 baseEnd_7990932 := by
    simpa [prefixWord, tailWord_7990932, baseEnd_7990932] using wordTrace_append hprefix tailTrace_7990932
  have hstable : (prefixWord ++ tailWord_7990932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7990932).length < 2 ^ (prefixWord ++ tailWord_7990932).sum := by decide
  have hdescent : baseEnd_7990932 < baseStart_7990932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7990932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991008 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3]
def baseStart_7991008 : Nat := 118140960795 + 7991008 * 2 ^ 59
def prefixEnd_7991008 : Nat := 4983230072969 + 3 ^ 40 * 7991008 * 2
def baseEnd_7991008 : Nat := 4103228017923576378150029

theorem tailTrace_7991008 : CollatzResearch.WordTrace tailWord_7991008 prefixEnd_7991008 4103228017923576378150029 := by
  unfold tailWord_7991008
  simp only [CollatzResearch.WordTrace]
  refine ⟨145728002916975123178886839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194304003889300164238515785 145728002916975123178886839)
  ·
    refine ⟨218592004375462684768330259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145728002916975123178886839 218592004375462684768330259)
    ·
      refine ⟨327888006563194027152495389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218592004375462684768330259 327888006563194027152495389)
      ·
        refine ⟨122958002461197760182185771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327888006563194027152495389 122958002461197760182185771)
        ·
          refine ⟨184437003691796640273278657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122958002461197760182185771 184437003691796640273278657)
          ·
            refine ⟨138327752768847480204958993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184437003691796640273278657 138327752768847480204958993)
            ·
              refine ⟨103745814576635610153719245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138327752768847480204958993 103745814576635610153719245)
              ·
                refine ⟨38904680466238353807644717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103745814576635610153719245 38904680466238353807644717)
                ·
                  refine ⟨14589255174839382677866769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38904680466238353807644717 14589255174839382677866769)
                  ·
                    refine ⟨10941941381129537008400077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14589255174839382677866769 10941941381129537008400077)
                    ·
                      refine ⟨4103228017923576378150029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10941941381129537008400077 4103228017923576378150029)
                      ·
                        rfl

theorem cell23_7991008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_7991008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991008 prefixEnd_7991008 := by exact prefixLift 7991008
  have htrace : WordTrace (prefixWord ++ tailWord_7991008) baseStart_7991008 baseEnd_7991008 := by
    simpa [prefixWord, tailWord_7991008, baseEnd_7991008] using wordTrace_append hprefix tailTrace_7991008
  have hstable : (prefixWord ++ tailWord_7991008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991008).length < 2 ^ (prefixWord ++ tailWord_7991008).sum := by decide
  have hdescent : baseEnd_7991008 < baseStart_7991008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991018 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_7991018 : Nat := 118140960795 + 7991018 * 2 ^ 59
def prefixEnd_7991018 : Nat := 4983230072969 + 3 ^ 40 * 7991018 * 2
def baseEnd_7991018 : Nat := 4103233152730121339024983

theorem tailTrace_7991018 : CollatzResearch.WordTrace tailWord_7991018 prefixEnd_7991018 4103233152730121339024983 := by
  unfold tailWord_7991018
  simp only [CollatzResearch.WordTrace]
  refine ⟨72864092640978504516409427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194304247042609345377091805 72864092640978504516409427)
  ·
    refine ⟨109296138961467756774614141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72864092640978504516409427 109296138961467756774614141)
    ·
      refine ⟨40986052110550408790480303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109296138961467756774614141 40986052110550408790480303)
      ·
        refine ⟨61479078165825613185720455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40986052110550408790480303 61479078165825613185720455)
        ·
          refine ⟨92218617248738419778580683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61479078165825613185720455 92218617248738419778580683)
          ·
            refine ⟨138327925873107629667871025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92218617248738419778580683 138327925873107629667871025)
            ·
              refine ⟨103745944404830722250903269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138327925873107629667871025 103745944404830722250903269)
              ·
                refine ⟨19452364575905760422044363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103745944404830722250903269 19452364575905760422044363)
                ·
                  refine ⟨29178546863858640633066545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19452364575905760422044363 29178546863858640633066545)
                  ·
                    refine ⟨21883910147893980474799909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29178546863858640633066545 21883910147893980474799909)
                    ·
                      refine ⟨4103233152730121339024983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21883910147893980474799909 4103233152730121339024983)
                      ·
                        rfl

theorem cell23_7991018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_7991018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991018 prefixEnd_7991018 := by exact prefixLift 7991018
  have htrace : WordTrace (prefixWord ++ tailWord_7991018) baseStart_7991018 baseEnd_7991018 := by
    simpa [prefixWord, tailWord_7991018, baseEnd_7991018] using wordTrace_append hprefix tailTrace_7991018
  have hstable : (prefixWord ++ tailWord_7991018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991018).length < 2 ^ (prefixWord ++ tailWord_7991018).sum := by decide
  have hdescent : baseEnd_7991018 < baseStart_7991018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991025 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_7991025 : Nat := 118140960795 + 7991025 * 2 ^ 59
def prefixEnd_7991025 : Nat := 4983230072969 + 3 ^ 40 * 7991025 * 2
def baseEnd_7991025 : Nat := 4103236747094702811637451

theorem tailTrace_7991025 : CollatzResearch.WordTrace tailWord_7991025 prefixEnd_7991025 4103236747094702811637451 := by
  unfold tailWord_7991025
  simp only [CollatzResearch.WordTrace]
  refine ⟨291456625874888658261142529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194304417249925772174095019 291456625874888658261142529)
  ·
    refine ⟨218592469406166493695856897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291456625874888658261142529 218592469406166493695856897)
    ·
      refine ⟨163944352054624870271892673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218592469406166493695856897 163944352054624870271892673)
      ·
        refine ⟨122958264040968652703919505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163944352054624870271892673 122958264040968652703919505)
        ·
          refine ⟨92218698030726489527939629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122958264040968652703919505 92218698030726489527939629)
          ·
            refine ⟨34582011761522433572977361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92218698030726489527939629 34582011761522433572977361)
            ·
              refine ⟨25936508821141825179733021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34582011761522433572977361 25936508821141825179733021)
              ·
                refine ⟨9726190807928184442399883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25936508821141825179733021 9726190807928184442399883)
                ·
                  refine ⟨14589286211892276663599825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726190807928184442399883 14589286211892276663599825)
                  ·
                    refine ⟨10941964658919207497699869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14589286211892276663599825 10941964658919207497699869)
                    ·
                      refine ⟨4103236747094702811637451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10941964658919207497699869 4103236747094702811637451)
                      ·
                        rfl

theorem cell23_7991025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_7991025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991025 prefixEnd_7991025 := by exact prefixLift 7991025
  have htrace : WordTrace (prefixWord ++ tailWord_7991025) baseStart_7991025 baseEnd_7991025 := by
    simpa [prefixWord, tailWord_7991025, baseEnd_7991025] using wordTrace_append hprefix tailTrace_7991025
  have hstable : (prefixWord ++ tailWord_7991025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991025).length < 2 ^ (prefixWord ++ tailWord_7991025).sum := by decide
  have hdescent : baseEnd_7991025 < baseStart_7991025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991053 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7991053 : Nat := 118140960795 + 7991053 * 2 ^ 59
def prefixEnd_7991053 : Nat := 4983230072969 + 3 ^ 40 * 7991053 * 2
def baseEnd_7991053 : Nat := 1367750374851009567362441

theorem tailTrace_7991053 : CollatzResearch.WordTrace tailWord_7991053 prefixEnd_7991053 1367750374851009567362441 := by
  unfold tailWord_7991053
  simp only [CollatzResearch.WordTrace]
  refine ⟨291457647118787219043161813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194305098079191479362107875 291457647118787219043161813)
  ·
    refine ⟨6831038604346575446324105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 291457647118787219043161813 6831038604346575446324105)
    ·
      refine ⟨5123278953259931584743079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6831038604346575446324105 5123278953259931584743079)
      ·
        refine ⟨7684918429889897377114619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123278953259931584743079 7684918429889897377114619)
        ·
          refine ⟨11527377644834846065671929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684918429889897377114619 11527377644834846065671929)
          ·
            refine ⟨8645533233626134549253947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11527377644834846065671929 8645533233626134549253947)
            ·
              refine ⟨12968299850439201823880921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645533233626134549253947 12968299850439201823880921)
              ·
                refine ⟨9726224887829401367910691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12968299850439201823880921 9726224887829401367910691)
                ·
                  refine ⟨14589337331744102051866037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726224887829401367910691 14589337331744102051866037)
                  ·
                    refine ⟨1367750374851009567362441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14589337331744102051866037 1367750374851009567362441)
                    ·
                      rfl

theorem cell23_7991053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7991053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991053 prefixEnd_7991053 := by exact prefixLift 7991053
  have htrace : WordTrace (prefixWord ++ tailWord_7991053) baseStart_7991053 baseEnd_7991053 := by
    simpa [prefixWord, tailWord_7991053, baseEnd_7991053] using wordTrace_append hprefix tailTrace_7991053
  have hstable : (prefixWord ++ tailWord_7991053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991053).length < 2 ^ (prefixWord ++ tailWord_7991053).sum := by decide
  have hdescent : baseEnd_7991053 < baseStart_7991053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991112 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_7991112 : Nat := 118140960795 + 7991112 * 2 ^ 59
def prefixEnd_7991112 : Nat := 4983230072969 + 3 ^ 40 * 7991112 * 2
def baseEnd_7991112 : Nat := 4103281419911643971249551

theorem tailTrace_7991112 : CollatzResearch.WordTrace tailWord_7991112 prefixEnd_7991112 4103281419911643971249551 := by
  unfold tailWord_7991112
  simp only [CollatzResearch.WordTrace]
  refine ⟨145729899512786736059779795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194306532683715648079706393 145729899512786736059779795)
  ·
    refine ⟨218594849269180104089669693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145729899512786736059779795 218594849269180104089669693)
    ·
      refine ⟨81973068475942539033626135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218594849269180104089669693 81973068475942539033626135)
      ·
        refine ⟨122959602713913808550439203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81973068475942539033626135 122959602713913808550439203)
        ·
          refine ⟨184439404070870712825658805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122959602713913808550439203 184439404070870712825658805)
          ·
            refine ⟨17291194131644129327405513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184439404070870712825658805 17291194131644129327405513)
            ·
              refine ⟨12968395598733096995554135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17291194131644129327405513 12968395598733096995554135)
              ·
                refine ⟨19452593398099645493331203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12968395598733096995554135 19452593398099645493331203)
                ·
                  refine ⟨29178890097149468239996805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19452593398099645493331203 29178890097149468239996805)
                  ·
                    refine ⟨5471041893215525294999401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29178890097149468239996805 5471041893215525294999401)
                    ·
                      refine ⟨4103281419911643971249551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471041893215525294999401 4103281419911643971249551)
                      ·
                        rfl

theorem cell23_7991112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_7991112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991112 prefixEnd_7991112 := by exact prefixLift 7991112
  have htrace : WordTrace (prefixWord ++ tailWord_7991112) baseStart_7991112 baseEnd_7991112 := by
    simpa [prefixWord, tailWord_7991112, baseEnd_7991112] using wordTrace_append hprefix tailTrace_7991112
  have hstable : (prefixWord ++ tailWord_7991112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991112).length < 2 ^ (prefixWord ++ tailWord_7991112).sum := by decide
  have hdescent : baseEnd_7991112 < baseStart_7991112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991135 : List Nat := [1, 1, 2, 3, 1, 4, 1, 5, 5]
def baseStart_7991135 : Nat := 118140960795 + 7991135 * 2 ^ 59
def prefixEnd_7991135 : Nat := 4983230072969 + 3 ^ 40 * 7991135 * 2
def baseEnd_7991135 : Nat := 455921469996299709029105

theorem tailTrace_7991135 : CollatzResearch.WordTrace tailWord_7991135 prefixEnd_7991135 455921469996299709029105 := by
  unfold tailWord_7991135
  simp only [CollatzResearch.WordTrace]
  refine ⟨291460637904490147047646859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194307091936326764698431239 291460637904490147047646859)
  ·
    refine ⟨437190956856735220571470289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291460637904490147047646859 437190956856735220571470289)
    ·
      refine ⟨327893217642551415428602717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437190956856735220571470289 327893217642551415428602717)
      ·
        refine ⟨122959956615956780785726019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327893217642551415428602717 122959956615956780785726019)
        ·
          refine ⟨184439934923935171178589029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122959956615956780785726019 184439934923935171178589029)
          ·
            refine ⟨34582487798237844595985443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184439934923935171178589029 34582487798237844595985443)
            ·
              refine ⟨51873731697356766893978165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34582487798237844595985443 51873731697356766893978165)
              ·
                refine ⟨4863162346627196896310453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51873731697356766893978165 4863162346627196896310453)
                ·
                  refine ⟨455921469996299709029105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4863162346627196896310453 455921469996299709029105)
                  ·
                    rfl

theorem cell23_7991135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 5].length) (baseStart_7991135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991135 prefixEnd_7991135 := by exact prefixLift 7991135
  have htrace : WordTrace (prefixWord ++ tailWord_7991135) baseStart_7991135 baseEnd_7991135 := by
    simpa [prefixWord, tailWord_7991135, baseEnd_7991135] using wordTrace_append hprefix tailTrace_7991135
  have hstable : (prefixWord ++ tailWord_7991135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991135).length < 2 ^ (prefixWord ++ tailWord_7991135).sum := by decide
  have hdescent : baseEnd_7991135 < baseStart_7991135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991146 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7991146 : Nat := 118140960795 + 7991146 * 2 ^ 59
def prefixEnd_7991146 : Nat := 4983230072969 + 3 ^ 40 * 7991146 * 2
def baseEnd_7991146 : Nat := 4103298878253896838224395

theorem tailTrace_7991146 : CollatzResearch.WordTrace tailWord_7991146 prefixEnd_7991146 4103298878253896838224395 := by
  unfold tailWord_7991146
  simp only [CollatzResearch.WordTrace]
  refine ⟨72865259776862573981574323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194307359404966863950864861 72865259776862573981574323)
  ·
    refine ⟨109297889665293860972361485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72865259776862573981574323 109297889665293860972361485)
    ·
      refine ⟨40986708624485197864635557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109297889665293860972361485 40986708624485197864635557)
      ·
        refine ⟨7685007867090974599619167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40986708624485197864635557 7685007867090974599619167)
        ·
          refine ⟨11527511800636461899428751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7685007867090974599619167 11527511800636461899428751)
          ·
            refine ⟨17291267700954692849143127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527511800636461899428751 17291267700954692849143127)
            ·
              refine ⟨25936901551432039273714691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17291267700954692849143127 25936901551432039273714691)
              ·
                refine ⟨38905352327148058910572037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25936901551432039273714691 38905352327148058910572037)
                ·
                  refine ⟨7294753561340261045732257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38905352327148058910572037 7294753561340261045732257)
                  ·
                    refine ⟨5471065171005195784299193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7294753561340261045732257 5471065171005195784299193)
                    ·
                      refine ⟨4103298878253896838224395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471065171005195784299193 4103298878253896838224395)
                      ·
                        rfl

theorem cell23_7991146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7991146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991146 prefixEnd_7991146 := by exact prefixLift 7991146
  have htrace : WordTrace (prefixWord ++ tailWord_7991146) baseStart_7991146 baseEnd_7991146 := by
    simpa [prefixWord, tailWord_7991146, baseEnd_7991146] using wordTrace_append hprefix tailTrace_7991146
  have hstable : (prefixWord ++ tailWord_7991146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991146).length < 2 ^ (prefixWord ++ tailWord_7991146).sum := by decide
  have hdescent : baseEnd_7991146 < baseStart_7991146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991168 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_7991168 : Nat := 118140960795 + 7991168 * 2 ^ 59
def prefixEnd_7991168 : Nat := 4983230072969 + 3 ^ 40 * 7991168 * 2
def baseEnd_7991168 : Nat := 4103310174828295752149293

theorem tailTrace_7991168 : CollatzResearch.WordTrace tailWord_7991168 prefixEnd_7991168 4103310174828295752149293 := by
  unfold tailWord_7991168
  simp only [CollatzResearch.WordTrace]
  refine ⟨145730920756685296841799079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194307894342247062455732105 145730920756685296841799079)
  ·
    refine ⟨218596381135027945262698619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145730920756685296841799079 218596381135027945262698619)
    ·
      refine ⟨327894571702541917894047929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218596381135027945262698619 327894571702541917894047929)
      ·
        refine ⟨245920928776906438420535947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327894571702541917894047929 245920928776906438420535947)
        ·
          refine ⟨368881393165359657630803921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245920928776906438420535947 368881393165359657630803921)
          ·
            refine ⟨276661044874019743223102941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368881393165359657630803921 276661044874019743223102941)
            ·
              refine ⟨103747891827757403708663603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276661044874019743223102941 103747891827757403708663603)
              ·
                refine ⟨155621837741636105562995405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103747891827757403708663603 155621837741636105562995405)
                ·
                  refine ⟨58358189153113539586123277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155621837741636105562995405 58358189153113539586123277)
                  ·
                    refine ⟨21884320932417577344796229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58358189153113539586123277 21884320932417577344796229)
                    ·
                      refine ⟨4103310174828295752149293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21884320932417577344796229 4103310174828295752149293)
                      ·
                        rfl

theorem cell23_7991168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_7991168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991168 prefixEnd_7991168 := by exact prefixLift 7991168
  have htrace : WordTrace (prefixWord ++ tailWord_7991168) baseStart_7991168 baseEnd_7991168 := by
    simpa [prefixWord, tailWord_7991168, baseEnd_7991168] using wordTrace_append hprefix tailTrace_7991168
  have hstable : (prefixWord ++ tailWord_7991168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991168).length < 2 ^ (prefixWord ++ tailWord_7991168).sum := by decide
  have hdescent : baseEnd_7991168 < baseStart_7991168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991185 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 1, 6, 2]
def baseStart_7991185 : Nat := 118140960795 + 7991185 * 2 ^ 59
def prefixEnd_7991185 : Nat := 4983230072969 + 3 ^ 40 * 7991185 * 2
def baseEnd_7991185 : Nat := 4103318903999422185636715

theorem tailTrace_7991185 : CollatzResearch.WordTrace tailWord_7991185 prefixEnd_7991185 4103318903999422185636715 := by
  unfold tailWord_7991185
  simp only [CollatzResearch.WordTrace]
  refine ⟨291462461554309005586967009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194308307702872670391311339 291462461554309005586967009)
  ·
    refine ⟨218596846165731754190225257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291462461554309005586967009 218596846165731754190225257)
    ·
      refine ⟨163947634624298815642668943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218596846165731754190225257 163947634624298815642668943)
      ·
        refine ⟨245921451936448223464003415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163947634624298815642668943 245921451936448223464003415)
        ·
          refine ⟨368882177904672335196005123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245921451936448223464003415 368882177904672335196005123)
          ·
            refine ⟨553323266857008502794007685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368882177904672335196005123 553323266857008502794007685)
            ·
              refine ⟨103748112535689094273876441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 553323266857008502794007685 103748112535689094273876441)
              ·
                refine ⟨77811084401766820705407331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103748112535689094273876441 77811084401766820705407331)
                ·
                  refine ⟨116716626602650231058110997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77811084401766820705407331 116716626602650231058110997)
                  ·
                    refine ⟨5471091871999229580848953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116716626602650231058110997 5471091871999229580848953)
                    ·
                      refine ⟨4103318903999422185636715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471091871999229580848953 4103318903999422185636715)
                      ·
                        rfl

theorem cell23_7991185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_7991185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991185 prefixEnd_7991185 := by exact prefixLift 7991185
  have htrace : WordTrace (prefixWord ++ tailWord_7991185) baseStart_7991185 baseEnd_7991185 := by
    simpa [prefixWord, tailWord_7991185, baseEnd_7991185] using wordTrace_append hprefix tailTrace_7991185
  have hstable : (prefixWord ++ tailWord_7991185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991185).length < 2 ^ (prefixWord ++ tailWord_7991185).sum := by decide
  have hdescent : baseEnd_7991185 < baseStart_7991185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991214 : List Nat := [4, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7991214 : Nat := 118140960795 + 7991214 * 2 ^ 59
def prefixEnd_7991214 : Nat := 4983230072969 + 3 ^ 40 * 7991214 * 2
def baseEnd_7991214 : Nat := 4103333794938402572174083

theorem tailTrace_7991214 : CollatzResearch.WordTrace tailWord_7991214 prefixEnd_7991214 4103333794938402572174083 := by
  unfold tailWord_7991214
  simp only [CollatzResearch.WordTrace]
  refine ⟨36432939908900492942471587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194309012847469295693181797 36432939908900492942471587)
  ·
    refine ⟨54649409863350739413707381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36432939908900492942471587 54649409863350739413707381)
    ·
      refine ⟨5123382174689131820035067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54649409863350739413707381 5123382174689131820035067)
      ·
        refine ⟨7685073262033697730052601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123382174689131820035067 7685073262033697730052601)
        ·
          refine ⟨5763804946525273297539451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7685073262033697730052601 5763804946525273297539451)
          ·
            refine ⟨8645707419787909946309177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5763804946525273297539451 8645707419787909946309177)
            ·
              refine ⟨6484280564840932459731883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8645707419787909946309177 6484280564840932459731883)
              ·
                refine ⟨9726420847261398689597825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484280564840932459731883 9726420847261398689597825)
                ·
                  refine ⟨7294815635446049017198369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9726420847261398689597825 7294815635446049017198369)
                  ·
                    refine ⟨5471111726584536762898777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7294815635446049017198369 5471111726584536762898777)
                    ·
                      refine ⟨4103333794938402572174083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471111726584536762898777 4103333794938402572174083)
                      ·
                        rfl

theorem cell23_7991214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7991214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991214 prefixEnd_7991214 := by exact prefixLift 7991214
  have htrace : WordTrace (prefixWord ++ tailWord_7991214) baseStart_7991214 baseEnd_7991214 := by
    simpa [prefixWord, tailWord_7991214, baseEnd_7991214] using wordTrace_append hprefix tailTrace_7991214
  have hstable : (prefixWord ++ tailWord_7991214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991214).length < 2 ^ (prefixWord ++ tailWord_7991214).sum := by decide
  have hdescent : baseEnd_7991214 < baseStart_7991214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991225 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 6]
def baseStart_7991225 : Nat := 118140960795 + 7991225 * 2 ^ 59
def prefixEnd_7991225 : Nat := 4983230072969 + 3 ^ 40 * 7991225 * 2
def baseEnd_7991225 : Nat := 455926604802844669904059

theorem tailTrace_7991225 : CollatzResearch.WordTrace tailWord_7991225 prefixEnd_7991225 455926604802844669904059 := by
  unfold tailWord_7991225
  simp only [CollatzResearch.WordTrace]
  refine ⟨291463920474164092418423129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194309280316109394945615419 291463920474164092418423129)
  ·
    refine ⟨218597940355623069313817347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291463920474164092418423129 218597940355623069313817347)
    ·
      refine ⟨327896910533434603970726021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218597940355623069313817347 327896910533434603970726021)
      ·
        refine ⟨61480670725018988244511129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327896910533434603970726021 61480670725018988244511129)
        ·
          refine ⟨46110503043764241183383347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61480670725018988244511129 46110503043764241183383347)
          ·
            refine ⟨69165754565646361775075021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46110503043764241183383347 69165754565646361775075021)
            ·
              refine ⟨25937157962117385665653133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69165754565646361775075021 25937157962117385665653133)
              ·
                refine ⟨9726434235794019624619925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25937157962117385665653133 9726434235794019624619925)
                ·
                  refine ⟨455926604802844669904059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9726434235794019624619925 455926604802844669904059)
                  ·
                    rfl

theorem cell23_7991225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 6].length) (baseStart_7991225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991225 prefixEnd_7991225 := by exact prefixLift 7991225
  have htrace : WordTrace (prefixWord ++ tailWord_7991225) baseStart_7991225 baseEnd_7991225 := by
    simpa [prefixWord, tailWord_7991225, baseEnd_7991225] using wordTrace_append hprefix tailTrace_7991225
  have hstable : (prefixWord ++ tailWord_7991225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991225).length < 2 ^ (prefixWord ++ tailWord_7991225).sum := by decide
  have hdescent : baseEnd_7991225 < baseStart_7991225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991286 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_7991286 : Nat := 118140960795 + 7991286 * 2 ^ 59
def prefixEnd_7991286 : Nat := 4983230072969 + 3 ^ 40 * 7991286 * 2
def baseEnd_7991286 : Nat := 4103370765545526290473751

theorem tailTrace_7991286 : CollatzResearch.WordTrace tailWord_7991286 prefixEnd_7991286 4103370765545526290473751 := by
  unfold tailWord_7991286
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216634082933943739774607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194310763551295399890929141 18216634082933943739774607)
  ·
    refine ⟨27324951124400915609661911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18216634082933943739774607 27324951124400915609661911)
    ·
      refine ⟨40987426686601373414492867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27324951124400915609661911 40987426686601373414492867)
      ·
        refine ⟨61481140029902060121739301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40987426686601373414492867 61481140029902060121739301)
        ·
          refine ⟨11527713755606636272826119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61481140029902060121739301 11527713755606636272826119)
          ·
            refine ⟨17291570633409954409239179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527713755606636272826119 17291570633409954409239179)
            ·
              refine ⟨25937355950114931613858769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17291570633409954409239179 25937355950114931613858769)
              ·
                refine ⟨19453016962586198710394077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25937355950114931613858769 19453016962586198710394077)
                ·
                  refine ⟨7294881360969824516397779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19453016962586198710394077 7294881360969824516397779)
                  ·
                    refine ⟨10942322041454736774596669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7294881360969824516397779 10942322041454736774596669)
                    ·
                      refine ⟨4103370765545526290473751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10942322041454736774596669 4103370765545526290473751)
                      ·
                        rfl

theorem cell23_7991286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_7991286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991286 prefixEnd_7991286 := by exact prefixLift 7991286
  have htrace : WordTrace (prefixWord ++ tailWord_7991286) baseStart_7991286 baseEnd_7991286 := by
    simpa [prefixWord, tailWord_7991286, baseEnd_7991286] using wordTrace_append hprefix tailTrace_7991286
  have hstable : (prefixWord ++ tailWord_7991286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991286).length < 2 ^ (prefixWord ++ tailWord_7991286).sum := by decide
  have hdescent : baseEnd_7991286 < baseStart_7991286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991292 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_7991292 : Nat := 118140960795 + 7991292 * 2 ^ 59
def prefixEnd_7991292 : Nat := 4983230072969 + 3 ^ 40 * 7991292 * 2
def baseEnd_7991292 : Nat := 4103373846429453266998723

theorem tailTrace_7991292 : CollatzResearch.WordTrace tailWord_7991292 prefixEnd_7991292 4103373846429453266998723 := by
  unfold tailWord_7991292
  simp only [CollatzResearch.WordTrace]
  refine ⟨145733182082460681430556065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194310909443280908574074753 145733182082460681430556065)
  ·
    refine ⟨109299886561845511072917049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145733182082460681430556065 109299886561845511072917049)
    ·
      refine ⟨81974914921384133304687787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109299886561845511072917049 81974914921384133304687787)
      ·
        refine ⟨122962372382076199957031681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81974914921384133304687787 122962372382076199957031681)
        ·
          refine ⟨92221779286557149967773761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122962372382076199957031681 92221779286557149967773761)
          ·
            refine ⟨69166334464917862475830321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92221779286557149967773761 69166334464917862475830321)
            ·
              refine ⟨51874750848688396856872741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69166334464917862475830321 51874750848688396856872741)
              ·
                refine ⟨9726515784129074410663639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51874750848688396856872741 9726515784129074410663639)
                ·
                  refine ⟨14589773676193611615995459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726515784129074410663639 14589773676193611615995459)
                  ·
                    refine ⟨21884660514290417423993189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14589773676193611615995459 21884660514290417423993189)
                    ·
                      refine ⟨4103373846429453266998723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21884660514290417423993189 4103373846429453266998723)
                      ·
                        rfl

theorem cell23_7991292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_7991292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991292 prefixEnd_7991292 := by exact prefixLift 7991292
  have htrace : WordTrace (prefixWord ++ tailWord_7991292) baseStart_7991292 baseEnd_7991292 := by
    simpa [prefixWord, tailWord_7991292, baseEnd_7991292] using wordTrace_append hprefix tailTrace_7991292
  have hstable : (prefixWord ++ tailWord_7991292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991292).length < 2 ^ (prefixWord ++ tailWord_7991292).sum := by decide
  have hdescent : baseEnd_7991292 < baseStart_7991292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991306 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_7991306 : Nat := 118140960795 + 7991306 * 2 ^ 59
def prefixEnd_7991306 : Nat := 4983230072969 + 3 ^ 40 * 7991306 * 2
def baseEnd_7991306 : Nat := 1367793678386205404074553

theorem tailTrace_7991306 : CollatzResearch.WordTrace tailWord_7991306 prefixEnd_7991306 1367793678386205404074553 := by
  unfold tailWord_7991306
  simp only [CollatzResearch.WordTrace]
  refine ⟨72866718696717660813030443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194311249857913762168081181 72866718696717660813030443)
  ·
    refine ⟨109300078045076491219545665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72866718696717660813030443 109300078045076491219545665)
    ·
      refine ⟨81975058533807368414659249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109300078045076491219545665 81975058533807368414659249)
      ·
        refine ⟨61481293900355526310994437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81975058533807368414659249 61481293900355526310994437)
        ·
          refine ⟨11527742606316661183311457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61481293900355526310994437 11527742606316661183311457)
          ·
            refine ⟨8645806954737495887483593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11527742606316661183311457 8645806954737495887483593)
            ·
              refine ⟨6484355216053121915612695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8645806954737495887483593 6484355216053121915612695)
              ·
                refine ⟨9726532824079682873419043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484355216053121915612695 9726532824079682873419043)
                ·
                  refine ⟨14589799236119524310128565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726532824079682873419043 14589799236119524310128565)
                  ·
                    refine ⟨1367793678386205404074553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14589799236119524310128565 1367793678386205404074553)
                    ·
                      rfl

theorem cell23_7991306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_7991306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991306 prefixEnd_7991306 := by exact prefixLift 7991306
  have htrace : WordTrace (prefixWord ++ tailWord_7991306) baseStart_7991306 baseEnd_7991306 := by
    simpa [prefixWord, tailWord_7991306, baseEnd_7991306] using wordTrace_append hprefix tailTrace_7991306
  have hstable : (prefixWord ++ tailWord_7991306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991306).length < 2 ^ (prefixWord ++ tailWord_7991306).sum := by decide
  have hdescent : baseEnd_7991306 < baseStart_7991306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991312 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3]
def baseStart_7991312 : Nat := 118140960795 + 7991312 * 2 ^ 59
def prefixEnd_7991312 : Nat := 4983230072969 + 3 ^ 40 * 7991312 * 2
def baseEnd_7991312 : Nat := 4103384116042543188748631

theorem tailTrace_7991312 : CollatzResearch.WordTrace tailWord_7991312 prefixEnd_7991312 4103384116042543188748631 := by
  unfold tailWord_7991312
  simp only [CollatzResearch.WordTrace]
  refine ⟨145733546812424453138420095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194311395749899270851226793 145733546812424453138420095)
  ·
    refine ⟨218600320218636679707630143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145733546812424453138420095 218600320218636679707630143)
    ·
      refine ⟨327900480327955019561445215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218600320218636679707630143 327900480327955019561445215)
      ·
        refine ⟨491850720491932529342167823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327900480327955019561445215 491850720491932529342167823)
        ·
          refine ⟨737776080737898794013251735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491850720491932529342167823 737776080737898794013251735)
          ·
            refine ⟨1106664121106848191019877603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737776080737898794013251735 1106664121106848191019877603)
            ·
              refine ⟨1659996181660272286529816405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1106664121106848191019877603 1659996181660272286529816405)
              ·
                refine ⟨9726540126915657928885643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1659996181660272286529816405 9726540126915657928885643)
                ·
                  refine ⟨14589810190373486893328465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726540126915657928885643 14589810190373486893328465)
                  ·
                    refine ⟨10942357642780115169996349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14589810190373486893328465 10942357642780115169996349)
                    ·
                      refine ⟨4103384116042543188748631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10942357642780115169996349 4103384116042543188748631)
                      ·
                        rfl

theorem cell23_7991312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_7991312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991312 prefixEnd_7991312 := by exact prefixLift 7991312
  have htrace : WordTrace (prefixWord ++ tailWord_7991312) baseStart_7991312 baseEnd_7991312 := by
    simpa [prefixWord, tailWord_7991312, baseEnd_7991312] using wordTrace_append hprefix tailTrace_7991312
  have hstable : (prefixWord ++ tailWord_7991312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991312).length < 2 ^ (prefixWord ++ tailWord_7991312).sum := by decide
  have hdescent : baseEnd_7991312 < baseStart_7991312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991319 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 4, 4]
def baseStart_7991319 : Nat := 118140960795 + 7991319 * 2 ^ 59
def prefixEnd_7991319 : Nat := 4983230072969 + 3 ^ 40 * 7991319 * 2
def baseEnd_7991319 : Nat := 1367795903469041553787033

theorem tailTrace_7991319 : CollatzResearch.WordTrace tailWord_7991319 prefixEnd_7991319 1367795903469041553787033 := by
  unfold tailWord_7991319
  simp only [CollatzResearch.WordTrace]
  refine ⟨291467348935823546472345011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194311565957215697648230007 291467348935823546472345011)
  ·
    refine ⟨437201023403735319708517517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291467348935823546472345011 437201023403735319708517517)
    ·
      refine ⟨163950383776400744890694069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437201023403735319708517517 163950383776400744890694069)
      ·
        refine ⟨15370348479037569833502569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163950383776400744890694069 15370348479037569833502569)
        ·
          refine ⟨11527761359278177375126927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15370348479037569833502569 11527761359278177375126927)
          ·
            refine ⟨17291642038917266062690391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527761359278177375126927 17291642038917266062690391)
            ·
              refine ⟨25937463058375899094035587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17291642038917266062690391 25937463058375899094035587)
              ·
                refine ⟨38906194587563848641053381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25937463058375899094035587 38906194587563848641053381)
                ·
                  refine ⟨7294911485168221620197509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38906194587563848641053381 7294911485168221620197509)
                  ·
                    refine ⟨1367795903469041553787033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7294911485168221620197509 1367795903469041553787033)
                    ·
                      rfl

theorem cell23_7991319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_7991319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991319 prefixEnd_7991319 := by exact prefixLift 7991319
  have htrace : WordTrace (prefixWord ++ tailWord_7991319) baseStart_7991319 baseEnd_7991319 := by
    simpa [prefixWord, tailWord_7991319, baseEnd_7991319] using wordTrace_append hprefix tailTrace_7991319
  have hstable : (prefixWord ++ tailWord_7991319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991319).length < 2 ^ (prefixWord ++ tailWord_7991319).sum := by decide
  have hdescent : baseEnd_7991319 < baseStart_7991319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991336 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7991336 : Nat := 118140960795 + 7991336 * 2 ^ 59
def prefixEnd_7991336 : Nat := 4983230072969 + 3 ^ 40 * 7991336 * 2
def baseEnd_7991336 : Nat := 1367798813192750364949507

theorem tailTrace_7991336 : CollatzResearch.WordTrace tailWord_7991336 prefixEnd_7991336 1367798813192750364949507 := by
  unfold tailWord_7991336
  simp only [CollatzResearch.WordTrace]
  refine ⟨145733984488380979187856931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194311979317841305583809241 145733984488380979187856931)
  ·
    refine ⟨218600976732571468781785397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145733984488380979187856931 218600976732571468781785397)
    ·
      refine ⟨20493841568678575198292381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218600976732571468781785397 20493841568678575198292381)
      ·
        refine ⟨7685190588254465699359643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20493841568678575198292381 7685190588254465699359643)
        ·
          refine ⟨11527785882381698549039465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7685190588254465699359643 11527785882381698549039465)
          ·
            refine ⟨8645839411786273911779599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11527785882381698549039465 8645839411786273911779599)
            ·
              refine ⟨12968759117679410867669399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645839411786273911779599 12968759117679410867669399)
              ·
                refine ⟨19453138676519116301504099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12968759117679410867669399 19453138676519116301504099)
                ·
                  refine ⟨29179708014778674452256149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19453138676519116301504099 29179708014778674452256149)
                  ·
                    refine ⟨1367798813192750364949507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29179708014778674452256149 1367798813192750364949507)
                    ·
                      rfl

theorem cell23_7991336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7991336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991336 prefixEnd_7991336 := by exact prefixLift 7991336
  have htrace : WordTrace (prefixWord ++ tailWord_7991336) baseStart_7991336 baseEnd_7991336 := by
    simpa [prefixWord, tailWord_7991336, baseEnd_7991336] using wordTrace_append hprefix tailTrace_7991336
  have hstable : (prefixWord ++ tailWord_7991336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991336).length < 2 ^ (prefixWord ++ tailWord_7991336).sum := by decide
  have hdescent : baseEnd_7991336 < baseStart_7991336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991365 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_7991365 : Nat := 118140960795 + 7991365 * 2 ^ 59
def prefixEnd_7991365 : Nat := 4983230072969 + 3 ^ 40 * 7991365 * 2
def baseEnd_7991365 : Nat := 4103411330517231481385887

theorem tailTrace_7991365 : CollatzResearch.WordTrace tailWord_7991365 prefixEnd_7991365 4103411330517231481385887 := by
  unfold tailWord_7991365
  simp only [CollatzResearch.WordTrace]
  refine ⟨291469026693656896328519549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194312684462437930885679699 291469026693656896328519549)
  ·
    refine ⟨109300885010121336123194831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291469026693656896328519549 109300885010121336123194831)
    ·
      refine ⟨163951327515182004184792247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109300885010121336123194831 163951327515182004184792247)
      ·
        refine ⟨245926991272773006277188371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163951327515182004184792247 245926991272773006277188371)
        ·
          refine ⟨368890486909159509415782557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245926991272773006277188371 368890486909159509415782557)
          ·
            refine ⟨138333932590934816030918459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368890486909159509415782557 138333932590934816030918459)
            ·
              refine ⟨207500898886402224046377689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138333932590934816030918459 207500898886402224046377689)
              ·
                refine ⟨155625674164801668034783267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207500898886402224046377689 155625674164801668034783267)
                ·
                  refine ⟨233438511247202502052174901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155625674164801668034783267 233438511247202502052174901)
                  ·
                    refine ⟨21884860429425234567391397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233438511247202502052174901 21884860429425234567391397)
                    ·
                      refine ⟨4103411330517231481385887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21884860429425234567391397 4103411330517231481385887)
                      ·
                        rfl

theorem cell23_7991365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_7991365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991365 prefixEnd_7991365 := by exact prefixLift 7991365
  have htrace : WordTrace (prefixWord ++ tailWord_7991365) baseStart_7991365 baseEnd_7991365 := by
    simpa [prefixWord, tailWord_7991365, baseEnd_7991365] using wordTrace_append hprefix tailTrace_7991365
  have hstable : (prefixWord ++ tailWord_7991365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991365).length < 2 ^ (prefixWord ++ tailWord_7991365).sum := by decide
  have hdescent : baseEnd_7991365 < baseStart_7991365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991369 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 1, 3, 2]
def baseStart_7991369 : Nat := 118140960795 + 7991369 * 2 ^ 59
def prefixEnd_7991369 : Nat := 4983230072969 + 3 ^ 40 * 7991369 * 2
def baseEnd_7991369 : Nat := 4103413384439849465735869

theorem tailTrace_7991369 : CollatzResearch.WordTrace tailWord_7991369 prefixEnd_7991369 4103413384439849465735869 := by
  unfold tailWord_7991369
  simp only [CollatzResearch.WordTrace]
  refine ⟨291469172585642405011665161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194312781723761603341110107 291469172585642405011665161)
  ·
    refine ⟨218601879439231803758748871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291469172585642405011665161 218601879439231803758748871)
    ·
      refine ⟨327902819158847705638123307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218601879439231803758748871 327902819158847705638123307)
      ·
        refine ⟨491854228738271558457184961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327902819158847705638123307 491854228738271558457184961)
        ·
          refine ⟨368890671553703668842888721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491854228738271558457184961 368890671553703668842888721)
          ·
            refine ⟨276668003665277751632166541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368890671553703668842888721 276668003665277751632166541)
            ·
              refine ⟨103750501374479156862062453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276668003665277751632166541 103750501374479156862062453)
              ·
                refine ⟨9726609503857420955818355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103750501374479156862062453 9726609503857420955818355)
                ·
                  refine ⟨14589914255786131433727533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726609503857420955818355 14589914255786131433727533)
                  ·
                    refine ⟨5471217845919799287647825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14589914255786131433727533 5471217845919799287647825)
                    ·
                      refine ⟨4103413384439849465735869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471217845919799287647825 4103413384439849465735869)
                      ·
                        rfl

theorem cell23_7991369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 3, 2].length) (baseStart_7991369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991369 prefixEnd_7991369 := by exact prefixLift 7991369
  have htrace : WordTrace (prefixWord ++ tailWord_7991369) baseStart_7991369 baseEnd_7991369 := by
    simpa [prefixWord, tailWord_7991369, baseEnd_7991369] using wordTrace_append hprefix tailTrace_7991369
  have hstable : (prefixWord ++ tailWord_7991369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991369).length < 2 ^ (prefixWord ++ tailWord_7991369).sum := by decide
  have hdescent : baseEnd_7991369 < baseStart_7991369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991385 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_7991385 : Nat := 118140960795 + 7991385 * 2 ^ 59
def prefixEnd_7991385 : Nat := 4983230072969 + 3 ^ 40 * 7991385 * 2
def baseEnd_7991385 : Nat := 4103421600130321403135795

theorem tailTrace_7991385 : CollatzResearch.WordTrace tailWord_7991385 prefixEnd_7991385 4103421600130321403135795 := by
  unfold tailWord_7991385
  simp only [CollatzResearch.WordTrace]
  refine ⟨291469756153584439744247609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194313170769056293162831739 291469756153584439744247609)
  ·
    refine ⟨218602317115188329808185707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291469756153584439744247609 218602317115188329808185707)
    ·
      refine ⟨327903475672782494712278561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218602317115188329808185707 327903475672782494712278561)
      ·
        refine ⟨245927606754586871034208921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327903475672782494712278561 245927606754586871034208921)
        ·
          refine ⟨184445705065940153275656691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245927606754586871034208921 184445705065940153275656691)
          ·
            refine ⟨276668557598910229913485037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184445705065940153275656691 276668557598910229913485037)
            ·
              refine ⟨103750709099591336217556889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276668557598910229913485037 103750709099591336217556889)
              ·
                refine ⟨77813031824693502163167667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103750709099591336217556889 77813031824693502163167667)
                ·
                  refine ⟨116719547737040253244751501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77813031824693502163167667 116719547737040253244751501)
                  ·
                    refine ⟨43769830401390094966781813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116719547737040253244751501 43769830401390094966781813)
                    ·
                      refine ⟨4103421600130321403135795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43769830401390094966781813 4103421600130321403135795)
                      ·
                        rfl

theorem cell23_7991385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_7991385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991385 prefixEnd_7991385 := by exact prefixLift 7991385
  have htrace : WordTrace (prefixWord ++ tailWord_7991385) baseStart_7991385 baseEnd_7991385 := by
    simpa [prefixWord, tailWord_7991385, baseEnd_7991385] using wordTrace_append hprefix tailTrace_7991385
  have hstable : (prefixWord ++ tailWord_7991385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991385).length < 2 ^ (prefixWord ++ tailWord_7991385).sum := by decide
  have hdescent : baseEnd_7991385 < baseStart_7991385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991399 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_7991399 : Nat := 118140960795 + 7991399 * 2 ^ 59
def prefixEnd_7991399 : Nat := 4983230072969 + 3 ^ 40 * 7991399 * 2
def baseEnd_7991399 : Nat := 4103428788859484348360731

theorem tailTrace_7991399 : CollatzResearch.WordTrace tailWord_7991399 prefixEnd_7991399 4103428788859484348360731 := by
  unfold tailWord_7991399
  simp only [CollatzResearch.WordTrace]
  refine ⟨291470266775533720135257251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194313511183689146756838167 291470266775533720135257251)
  ·
    refine ⟨437205400163300580202885877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291470266775533720135257251 437205400163300580202885877)
    ·
      refine ⟨40988006265309429394020551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 437205400163300580202885877 40988006265309429394020551)
      ·
        refine ⟨61482009397964144091030827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40988006265309429394020551 61482009397964144091030827)
        ·
          refine ⟨92223014096946216136546241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61482009397964144091030827 92223014096946216136546241)
          ·
            refine ⟨69167260572709662102409681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92223014096946216136546241 69167260572709662102409681)
            ·
              refine ⟨51875445429532246576807261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69167260572709662102409681 51875445429532246576807261)
              ·
                refine ⟨19453292036074592466302723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51875445429532246576807261 19453292036074592466302723)
                ·
                  refine ⟨29179938054111888699454085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19453292036074592466302723 29179938054111888699454085)
                  ·
                    refine ⟨5471238385145979131147641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29179938054111888699454085 5471238385145979131147641)
                    ·
                      refine ⟨4103428788859484348360731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471238385145979131147641 4103428788859484348360731)
                      ·
                        rfl

theorem cell23_7991399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_7991399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991399 prefixEnd_7991399 := by exact prefixLift 7991399
  have htrace : WordTrace (prefixWord ++ tailWord_7991399) baseStart_7991399 baseEnd_7991399 := by
    simpa [prefixWord, tailWord_7991399, baseEnd_7991399] using wordTrace_append hprefix tailTrace_7991399
  have hstable : (prefixWord ++ tailWord_7991399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991399).length < 2 ^ (prefixWord ++ tailWord_7991399).sum := by decide
  have hdescent : baseEnd_7991399 < baseStart_7991399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991435 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 5, 7]
def baseStart_7991435 : Nat := 118140960795 + 7991435 * 2 ^ 59
def prefixEnd_7991435 : Nat := 4983230072969 + 3 ^ 40 * 7991435 * 2
def baseEnd_7991435 : Nat := 1367815758054348735836855

theorem tailTrace_7991435 : CollatzResearch.WordTrace tailWord_7991435 prefixEnd_7991435 1367815758054348735836855 := by
  unfold tailWord_7991435
  simp only [CollatzResearch.WordTrace]
  refine ⟨291471579803403298283567759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194314386535602198855711839 291471579803403298283567759)
  ·
    refine ⟨437207369705104947425351639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291471579803403298283567759 437207369705104947425351639)
    ·
      refine ⟨655811054557657421138027459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437207369705104947425351639 655811054557657421138027459)
      ·
        refine ⟨983716581836486131707041189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655811054557657421138027459 983716581836486131707041189)
        ·
          refine ⟨184446859094341149695070223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 983716581836486131707041189 184446859094341149695070223)
          ·
            refine ⟨276670288641511724542605335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184446859094341149695070223 276670288641511724542605335)
            ·
              refine ⟨415005432962267586813908003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276670288641511724542605335 415005432962267586813908003)
              ·
                refine ⟨622508149443401380220862005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415005432962267586813908003 622508149443401380220862005)
                ·
                  refine ⟨58360139010318879395705813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622508149443401380220862005 58360139010318879395705813)
                  ·
                    refine ⟨1367815758054348735836855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58360139010318879395705813 1367815758054348735836855)
                    ·
                      rfl

theorem cell23_7991435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_7991435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991435 prefixEnd_7991435 := by exact prefixLift 7991435
  have htrace : WordTrace (prefixWord ++ tailWord_7991435) baseStart_7991435 baseEnd_7991435 := by
    simpa [prefixWord, tailWord_7991435, baseEnd_7991435] using wordTrace_append hprefix tailTrace_7991435
  have hstable : (prefixWord ++ tailWord_7991435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991435).length < 2 ^ (prefixWord ++ tailWord_7991435).sum := by decide
  have hdescent : baseEnd_7991435 < baseStart_7991435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991452 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_7991452 : Nat := 118140960795 + 7991452 * 2 ^ 59
def prefixEnd_7991452 : Nat := 4983230072969 + 3 ^ 40 * 7991452 * 2
def baseEnd_7991452 : Nat := 1367818667778057546999329

theorem tailTrace_7991452 : CollatzResearch.WordTrace tailWord_7991452 prefixEnd_7991452 1367818667778057546999329 := by
  unfold tailWord_7991452
  simp only [CollatzResearch.WordTrace]
  refine ⟨145736099922170855093468305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194314799896227806791291073 145736099922170855093468305)
  ·
    refine ⟨109302074941628141320101229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145736099922170855093468305 109302074941628141320101229)
    ·
      refine ⟨40988278103110552995037961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109302074941628141320101229 40988278103110552995037961)
      ·
        refine ⟨30741208577332914746278471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40988278103110552995037961 30741208577332914746278471)
        ·
          refine ⟨46111812865999372119417707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30741208577332914746278471 46111812865999372119417707)
          ·
            refine ⟨69167719298999058179126561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46111812865999372119417707 69167719298999058179126561)
            ·
              refine ⟨51875789474249293634344921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69167719298999058179126561 51875789474249293634344921)
              ·
                refine ⟨38906842105686970225758691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51875789474249293634344921 38906842105686970225758691)
                ·
                  refine ⟨58360263158530455338638037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38906842105686970225758691 58360263158530455338638037)
                  ·
                    refine ⟨1367818667778057546999329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58360263158530455338638037 1367818667778057546999329)
                    ·
                      rfl

theorem cell23_7991452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_7991452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991452 prefixEnd_7991452 := by exact prefixLift 7991452
  have htrace : WordTrace (prefixWord ++ tailWord_7991452) baseStart_7991452 baseEnd_7991452 := by
    simpa [prefixWord, tailWord_7991452, baseEnd_7991452] using wordTrace_append hprefix tailTrace_7991452
  have hstable : (prefixWord ++ tailWord_7991452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991452).length < 2 ^ (prefixWord ++ tailWord_7991452).sum := by decide
  have hdescent : baseEnd_7991452 < baseStart_7991452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991469 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_7991469 : Nat := 118140960795 + 7991469 * 2 ^ 59
def prefixEnd_7991469 : Nat := 4983230072969 + 3 ^ 40 * 7991469 * 2
def baseEnd_7991469 : Nat := 1367821577501766358161803

theorem tailTrace_7991469 : CollatzResearch.WordTrace tailWord_7991469 prefixEnd_7991469 1367821577501766358161803 := by
  unfold tailWord_7991469
  simp only [CollatzResearch.WordTrace]
  refine ⟨291472819885280122090305461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194315213256853414726870307 291472819885280122090305461)
  ·
    refine ⟨27325576864245011445966137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291472819885280122090305461 27325576864245011445966137)
    ·
      refine ⟨20494182648183758584474603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27325576864245011445966137 20494182648183758584474603)
      ·
        refine ⟨30741273972275637876711905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20494182648183758584474603 30741273972275637876711905)
        ·
          refine ⟨23055955479206728407533929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30741273972275637876711905 23055955479206728407533929)
          ·
            refine ⟨17291966609405046305650447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23055955479206728407533929 17291966609405046305650447)
            ·
              refine ⟨25937949914107569458475671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17291966609405046305650447 25937949914107569458475671)
              ·
                refine ⟨38906924871161354187713507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25937949914107569458475671 38906924871161354187713507)
                ·
                  refine ⟨58360387306742031281570261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38906924871161354187713507 58360387306742031281570261)
                  ·
                    refine ⟨1367821577501766358161803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58360387306742031281570261 1367821577501766358161803)
                    ·
                      rfl

theorem cell23_7991469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_7991469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991469 prefixEnd_7991469 := by exact prefixLift 7991469
  have htrace : WordTrace (prefixWord ++ tailWord_7991469) baseStart_7991469 baseEnd_7991469 := by
    simpa [prefixWord, tailWord_7991469, baseEnd_7991469] using wordTrace_append hprefix tailTrace_7991469
  have hstable : (prefixWord ++ tailWord_7991469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991469).length < 2 ^ (prefixWord ++ tailWord_7991469).sum := by decide
  have hdescent : baseEnd_7991469 < baseStart_7991469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991499 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 3, 4]
def baseStart_7991499 : Nat := 118140960795 + 7991499 * 2 ^ 59
def prefixEnd_7991499 : Nat := 4983230072969 + 3 ^ 40 * 7991499 * 2
def baseEnd_7991499 : Nat := 1367826712308311319036757

theorem tailTrace_7991499 : CollatzResearch.WordTrace tailWord_7991499 prefixEnd_7991499 1367826712308311319036757 := by
  unfold tailWord_7991499
  simp only [CollatzResearch.WordTrace]
  refine ⟨291473914075171437213897551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194315942716780958142598367 291473914075171437213897551)
  ·
    refine ⟨437210871112757155820846327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291473914075171437213897551 437210871112757155820846327)
    ·
      refine ⟨655816306669135733731269491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437210871112757155820846327 655816306669135733731269491)
      ·
        refine ⟨983724460003703600596904237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655816306669135733731269491 983724460003703600596904237)
        ·
          refine ⟨368896672501388850223839089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 983724460003703600596904237 368896672501388850223839089)
          ·
            refine ⟨276672504376041637667879317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368896672501388850223839089 276672504376041637667879317)
            ·
              refine ⟨12969023642626951765681843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 276672504376041637667879317 12969023642626951765681843)
              ·
                refine ⟨19453535463940427648522765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12969023642626951765681843 19453535463940427648522765)
                ·
                  refine ⟨7295075798977660368196037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19453535463940427648522765 7295075798977660368196037)
                  ·
                    refine ⟨1367826712308311319036757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295075798977660368196037 1367826712308311319036757)
                    ·
                      rfl

theorem cell23_7991499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 4].length) (baseStart_7991499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991499 prefixEnd_7991499 := by exact prefixLift 7991499
  have htrace : WordTrace (prefixWord ++ tailWord_7991499) baseStart_7991499 baseEnd_7991499 := by
    simpa [prefixWord, tailWord_7991499, baseEnd_7991499] using wordTrace_append hprefix tailTrace_7991499
  have hstable : (prefixWord ++ tailWord_7991499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991499).length < 2 ^ (prefixWord ++ tailWord_7991499).sum := by decide
  have hdescent : baseEnd_7991499 < baseStart_7991499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991506 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_7991506 : Nat := 118140960795 + 7991506 * 2 ^ 59
def prefixEnd_7991506 : Nat := 4983230072969 + 3 ^ 40 * 7991506 * 2
def baseEnd_7991506 : Nat := 4103483731289515429722739

theorem tailTrace_7991506 : CollatzResearch.WordTrace tailWord_7991506 prefixEnd_7991506 4103483731289515429722739 := by
  unfold tailWord_7991506
  simp only [CollatzResearch.WordTrace]
  refine ⟨72868542346536519352350593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194316112924097384939601581 72868542346536519352350593)
  ·
    refine ⟨54651406759902389514262945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72868542346536519352350593 54651406759902389514262945)
    ·
      refine ⟨40988555069926792135697209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54651406759902389514262945 40988555069926792135697209)
      ·
        refine ⟨30741416302445094101772907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40988555069926792135697209 30741416302445094101772907)
        ·
          refine ⟨46112124453667641152659361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30741416302445094101772907 46112124453667641152659361)
          ·
            refine ⟨34584093340250730864494521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46112124453667641152659361 34584093340250730864494521)
            ·
              refine ⟨25938070005188048148370891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34584093340250730864494521 25938070005188048148370891)
              ·
                refine ⟨38907105007782072222556337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25938070005188048148370891 38907105007782072222556337)
                ·
                  refine ⟨29180328755836554166917253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38907105007782072222556337 29180328755836554166917253)
                  ·
                    refine ⟨5471311641719353906296985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29180328755836554166917253 5471311641719353906296985)
                    ·
                      refine ⟨4103483731289515429722739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471311641719353906296985 4103483731289515429722739)
                      ·
                        rfl

theorem cell23_7991506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_7991506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991506 prefixEnd_7991506 := by exact prefixLift 7991506
  have htrace : WordTrace (prefixWord ++ tailWord_7991506) baseStart_7991506 baseEnd_7991506 := by
    simpa [prefixWord, tailWord_7991506, baseEnd_7991506] using wordTrace_append hprefix tailTrace_7991506
  have hstable : (prefixWord ++ tailWord_7991506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991506).length < 2 ^ (prefixWord ++ tailWord_7991506).sum := by decide
  have hdescent : baseEnd_7991506 < baseStart_7991506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991550 : List Nat := [4, 2, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_7991550 : Nat := 118140960795 + 7991550 * 2 ^ 59
def prefixEnd_7991550 : Nat := 4983230072969 + 3 ^ 40 * 7991550 * 2
def baseEnd_7991550 : Nat := 1367835441479437752524179

theorem tailTrace_7991550 : CollatzResearch.WordTrace tailWord_7991550 prefixEnd_7991550 1367835441479437752524179 := by
  unfold tailWord_7991550
  simp only [CollatzResearch.WordTrace]
  refine ⟨36434471774748334115500513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194317182798657781949336069 36434471774748334115500513)
  ·
    refine ⟨27325853831061250586625385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36434471774748334115500513 27325853831061250586625385)
    ·
      refine ⟨20494390373295937939969039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27325853831061250586625385 20494390373295937939969039)
      ·
        refine ⟨30741585559943906909953559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20494390373295937939969039 30741585559943906909953559)
        ·
          refine ⟨46112378339915860364930339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30741585559943906909953559 46112378339915860364930339)
          ·
            refine ⟨69168567509873790547395509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46112378339915860364930339 69168567509873790547395509)
            ·
              refine ⟨6484553204050667863818329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69168567509873790547395509 6484553204050667863818329)
              ·
                refine ⟨4863414903038000897863747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6484553204050667863818329 4863414903038000897863747)
                ·
                  refine ⟨7295122354557001346795621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863414903038000897863747 7295122354557001346795621)
                  ·
                    refine ⟨1367835441479437752524179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295122354557001346795621 1367835441479437752524179)
                    ·
                      rfl

theorem cell23_7991550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_7991550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991550 prefixEnd_7991550 := by exact prefixLift 7991550
  have htrace : WordTrace (prefixWord ++ tailWord_7991550) baseStart_7991550 baseEnd_7991550 := by
    simpa [prefixWord, tailWord_7991550, baseEnd_7991550] using wordTrace_append hprefix tailTrace_7991550
  have hstable : (prefixWord ++ tailWord_7991550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991550).length < 2 ^ (prefixWord ++ tailWord_7991550).sum := by decide
  have hdescent : baseEnd_7991550 < baseStart_7991550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991566 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_7991566 : Nat := 118140960795 + 7991566 * 2 ^ 59
def prefixEnd_7991566 : Nat := 4983230072969 + 3 ^ 40 * 7991566 * 2
def baseEnd_7991566 : Nat := 4103514540128785194972463

theorem tailTrace_7991566 : CollatzResearch.WordTrace tailWord_7991566 prefixEnd_7991566 4103514540128785194972463 := by
  unfold tailWord_7991566
  simp only [CollatzResearch.WordTrace]
  refine ⟨36434544720741088457073319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194317571843952471771057701 36434544720741088457073319)
  ·
    refine ⟨54651817081111632685609979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36434544720741088457073319 54651817081111632685609979)
    ·
      refine ⟨81977725621667449028414969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54651817081111632685609979 81977725621667449028414969)
      ·
        refine ⟨61483294216250586771311227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81977725621667449028414969 61483294216250586771311227)
        ·
          refine ⟨92224941324375880156966841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61483294216250586771311227 92224941324375880156966841)
          ·
            refine ⟨69168705993281910117725131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92224941324375880156966841 69168705993281910117725131)
            ·
              refine ⟨103753058989922865176587697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69168705993281910117725131 103753058989922865176587697)
              ·
                refine ⟨77814794242442148882440773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103753058989922865176587697 77814794242442148882440773)
                ·
                  refine ⟨14590273920457902915457645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77814794242442148882440773 14590273920457902915457645)
                  ·
                    refine ⟨5471352720171713593296617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14590273920457902915457645 5471352720171713593296617)
                    ·
                      refine ⟨4103514540128785194972463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471352720171713593296617 4103514540128785194972463)
                      ·
                        rfl

theorem cell23_7991566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_7991566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991566 prefixEnd_7991566 := by exact prefixLift 7991566
  have htrace : WordTrace (prefixWord ++ tailWord_7991566) baseStart_7991566 baseEnd_7991566 := by
    simpa [prefixWord, tailWord_7991566, baseEnd_7991566] using wordTrace_append hprefix tailTrace_7991566
  have hstable : (prefixWord ++ tailWord_7991566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991566).length < 2 ^ (prefixWord ++ tailWord_7991566).sum := by decide
  have hdescent : baseEnd_7991566 < baseStart_7991566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991579 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 2, 6, 2]
def baseStart_7991579 : Nat := 118140960795 + 7991579 * 2 ^ 59
def prefixEnd_7991579 : Nat := 4983230072969 + 3 ^ 40 * 7991579 * 2
def baseEnd_7991579 : Nat := 4103521215377293644109903

theorem tailTrace_7991579 : CollatzResearch.WordTrace tailWord_7991579 prefixEnd_7991579 4103521215377293644109903 := by
  unfold tailWord_7991579
  simp only [CollatzResearch.WordTrace]
  refine ⟨291476831914881610876809791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194317887943254407251206527 291476831914881610876809791)
  ·
    refine ⟨437215247872322416315214687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291476831914881610876809791 437215247872322416315214687)
    ·
      refine ⟨655822871808483624472822031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437215247872322416315214687 655822871808483624472822031)
      ·
        refine ⟨983734307712725436709233047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655822871808483624472822031 983734307712725436709233047)
        ·
          refine ⟨1475601461569088155063849571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983734307712725436709233047 1475601461569088155063849571)
          ·
            refine ⟨2213402192353632232595774357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475601461569088155063849571 2213402192353632232595774357)
            ·
              refine ⟨103753227766576510902926923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2213402192353632232595774357 103753227766576510902926923)
              ·
                refine ⟨155629841649864766354390385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103753227766576510902926923 155629841649864766354390385)
                ·
                  refine ⟨116722381237398574765792789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155629841649864766354390385 116722381237398574765792789)
                  ·
                    refine ⟨5471361620503058192146537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116722381237398574765792789 5471361620503058192146537)
                    ·
                      refine ⟨4103521215377293644109903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471361620503058192146537 4103521215377293644109903)
                      ·
                        rfl

theorem cell23_7991579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6, 2].length) (baseStart_7991579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991579 prefixEnd_7991579 := by exact prefixLift 7991579
  have htrace : WordTrace (prefixWord ++ tailWord_7991579) baseStart_7991579 baseEnd_7991579 := by
    simpa [prefixWord, tailWord_7991579, baseEnd_7991579] using wordTrace_append hprefix tailTrace_7991579
  have hstable : (prefixWord ++ tailWord_7991579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991579).length < 2 ^ (prefixWord ++ tailWord_7991579).sum := by decide
  have hdescent : baseEnd_7991579 < baseStart_7991579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991583 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 2, 3, 2]
def baseStart_7991583 : Nat := 118140960795 + 7991583 * 2 ^ 59
def prefixEnd_7991583 : Nat := 4983230072969 + 3 ^ 40 * 7991583 * 2
def baseEnd_7991583 : Nat := 4103523269299911628459885

theorem tailTrace_7991583 : CollatzResearch.WordTrace tailWord_7991583 prefixEnd_7991583 4103523269299911628459885 := by
  unfold tailWord_7991583
  simp only [CollatzResearch.WordTrace]
  refine ⟨291476977806867119559955403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194317985204578079706636935 291476977806867119559955403)
  ·
    refine ⟨437215466710300679339933105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291476977806867119559955403 437215466710300679339933105)
    ·
      refine ⟨327911600032725509504949829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437215466710300679339933105 327911600032725509504949829)
      ·
        refine ⟨61483425006136033032178093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327911600032725509504949829 61483425006136033032178093)
        ·
          refine ⟨23056284377301012387066785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61483425006136033032178093 23056284377301012387066785)
          ·
            refine ⟨17292213282975759290300089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23056284377301012387066785 17292213282975759290300089)
            ·
              refine ⟨12969159962231819467725067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17292213282975759290300089 12969159962231819467725067)
              ·
                refine ⟨19453739943347729201587601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12969159962231819467725067 19453739943347729201587601)
                ·
                  refine ⟨14590304957510796901190701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19453739943347729201587601 14590304957510796901190701)
                  ·
                    refine ⟨5471364359066548837946513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14590304957510796901190701 5471364359066548837946513)
                    ·
                      refine ⟨4103523269299911628459885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471364359066548837946513 4103523269299911628459885)
                      ·
                        rfl

theorem cell23_7991583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_7991583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991583 prefixEnd_7991583 := by exact prefixLift 7991583
  have htrace : WordTrace (prefixWord ++ tailWord_7991583) baseStart_7991583 baseEnd_7991583 := by
    simpa [prefixWord, tailWord_7991583, baseEnd_7991583] using wordTrace_append hprefix tailTrace_7991583
  have hstable : (prefixWord ++ tailWord_7991583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991583).length < 2 ^ (prefixWord ++ tailWord_7991583).sum := by decide
  have hdescent : baseEnd_7991583 < baseStart_7991583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991599 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 5]
def baseStart_7991599 : Nat := 118140960795 + 7991599 * 2 ^ 59
def prefixEnd_7991599 : Nat := 4983230072969 + 3 ^ 40 * 7991599 * 2
def baseEnd_7991599 : Nat := 4103531484990383565859811

theorem tailTrace_7991599 : CollatzResearch.WordTrace tailWord_7991599 prefixEnd_7991599 4103531484990383565859811 := by
  unfold tailWord_7991599
  simp only [CollatzResearch.WordTrace]
  refine ⟨291477561374809154292537851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194318374249872769528358567 291477561374809154292537851)
  ·
    refine ⟨437216342062213731438806777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291477561374809154292537851 437216342062213731438806777)
    ·
      refine ⟨327912256546660298579105083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437216342062213731438806777 327912256546660298579105083)
      ·
        refine ⟨491868384819990447868657625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327912256546660298579105083 491868384819990447868657625)
        ·
          refine ⟨368901288614992835901493219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491868384819990447868657625 368901288614992835901493219)
          ·
            refine ⟨553351932922489253852239829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368901288614992835901493219 553351932922489253852239829)
            ·
              refine ⟨12969185927870841887161871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 553351932922489253852239829 12969185927870841887161871)
              ·
                refine ⟨19453778891806262830742807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12969185927870841887161871 19453778891806262830742807)
                ·
                  refine ⟨29180668337709394246114211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19453778891806262830742807 29180668337709394246114211)
                  ·
                    refine ⟨43771002506564091369171317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29180668337709394246114211 43771002506564091369171317)
                    ·
                      refine ⟨4103531484990383565859811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43771002506564091369171317 4103531484990383565859811)
                      ·
                        rfl

theorem cell23_7991599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_7991599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991599 prefixEnd_7991599 := by exact prefixLift 7991599
  have htrace : WordTrace (prefixWord ++ tailWord_7991599) baseStart_7991599 baseEnd_7991599 := by
    simpa [prefixWord, tailWord_7991599, baseEnd_7991599] using wordTrace_append hprefix tailTrace_7991599
  have hstable : (prefixWord ++ tailWord_7991599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991599).length < 2 ^ (prefixWord ++ tailWord_7991599).sum := by decide
  have hdescent : baseEnd_7991599 < baseStart_7991599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991602 : List Nat := [3, 2, 1, 1, 16]
def baseStart_7991602 : Nat := 118140960795 + 7991602 * 2 ^ 59
def prefixEnd_7991602 : Nat := 4983230072969 + 3 ^ 40 * 7991602 * 2
def baseEnd_7991602 : Nat := 5628989060949721610593

theorem tailTrace_7991602 : CollatzResearch.WordTrace tailWord_7991602 prefixEnd_7991602 5628989060949721610593 := by
  unfold tailWord_7991602
  simp only [CollatzResearch.WordTrace]
  refine ⟨72869417698449571451224265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194318447195865523869931373 72869417698449571451224265)
  ·
    refine ⟨54652063273837178588418199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72869417698449571451224265 54652063273837178588418199)
    ·
      refine ⟨81978094910755767882627299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54652063273837178588418199 81978094910755767882627299)
      ·
        refine ⟨122967142366133651823940949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81978094910755767882627299 122967142366133651823940949)
        ·
          refine ⟨5628989060949721610593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 122967142366133651823940949 5628989060949721610593)
          ·
            rfl

theorem cell23_7991602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 16].length) (baseStart_7991602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991602 prefixEnd_7991602 := by exact prefixLift 7991602
  have htrace : WordTrace (prefixWord ++ tailWord_7991602) baseStart_7991602 baseEnd_7991602 := by
    simpa [prefixWord, tailWord_7991602, baseEnd_7991602] using wordTrace_append hprefix tailTrace_7991602
  have hstable : (prefixWord ++ tailWord_7991602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991602).length < 2 ^ (prefixWord ++ tailWord_7991602).sum := by decide
  have hdescent : baseEnd_7991602 < baseStart_7991602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991636 : List Nat := [2, 4, 1, 1, 2, 3, 3, 7]
def baseStart_7991636 : Nat := 118140960795 + 7991636 * 2 ^ 59
def prefixEnd_7991636 : Nat := 4983230072969 + 3 ^ 40 * 7991636 * 2
def baseEnd_7991636 : Nat := 151983351250911108188783

theorem tailTrace_7991636 : CollatzResearch.WordTrace tailWord_7991636 prefixEnd_7991636 151983351250911108188783 := by
  unfold tailWord_7991636
  simp only [CollatzResearch.WordTrace]
  refine ⟨145739455437837554805817381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194319273917116739741089841 145739455437837554805817381)
  ·
    refine ⟨27326147894594541526090759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145739455437837554805817381 27326147894594541526090759)
    ·
      refine ⟨40989221841891812289136139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27326147894594541526090759 40989221841891812289136139)
      ·
        refine ⟨61483832762837718433704209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40989221841891812289136139 61483832762837718433704209)
        ·
          refine ⟨46112874572128288825278157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61483832762837718433704209 46112874572128288825278157)
          ·
            refine ⟨17292327964548108309479309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46112874572128288825278157 17292327964548108309479309)
            ·
              refine ⟨6484622986705540616054741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17292327964548108309479309 6484622986705540616054741)
              ·
                refine ⟨151983351250911108188783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6484622986705540616054741 151983351250911108188783)
                ·
                  rfl

theorem cell23_7991636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 7].length) (baseStart_7991636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991636 prefixEnd_7991636 := by exact prefixLift 7991636
  have htrace : WordTrace (prefixWord ++ tailWord_7991636) baseStart_7991636 baseEnd_7991636 := by
    simpa [prefixWord, tailWord_7991636, baseEnd_7991636] using wordTrace_append hprefix tailTrace_7991636
  have hstable : (prefixWord ++ tailWord_7991636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991636).length < 2 ^ (prefixWord ++ tailWord_7991636).sum := by decide
  have hdescent : baseEnd_7991636 < baseStart_7991636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991650 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_7991650 : Nat := 118140960795 + 7991650 * 2 ^ 59
def prefixEnd_7991650 : Nat := 4983230072969 + 3 ^ 40 * 7991650 * 2
def baseEnd_7991650 : Nat := 4103557672503762866322077

theorem tailTrace_7991650 : CollatzResearch.WordTrace tailWord_7991650 prefixEnd_7991650 4103557672503762866322077 := by
  unfold tailWord_7991650
  simp only [CollatzResearch.WordTrace]
  refine ⟨72869855374406097500661101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194319614331749593335096269 72869855374406097500661101)
  ·
    refine ⟨27326195765402286562747913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72869855374406097500661101 27326195765402286562747913)
    ·
      refine ⟨20494646824051714922060935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27326195765402286562747913 20494646824051714922060935)
      ·
        refine ⟨30741970236077572383091403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20494646824051714922060935 30741970236077572383091403)
        ·
          refine ⟨46112955354116358574637105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30741970236077572383091403 46112955354116358574637105)
          ·
            refine ⟨34584716515587268930977829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46112955354116358574637105 34584716515587268930977829)
            ·
              refine ⟨6484634346672612924558343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34584716515587268930977829 6484634346672612924558343)
              ·
                refine ⟨9726951520008919386837515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484634346672612924558343 9726951520008919386837515)
                ·
                  refine ⟨14590427280013379080256273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726951520008919386837515 14590427280013379080256273)
                  ·
                    refine ⟨10942820460010034310192205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14590427280013379080256273 10942820460010034310192205)
                    ·
                      refine ⟨4103557672503762866322077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10942820460010034310192205 4103557672503762866322077)
                      ·
                        rfl

theorem cell23_7991650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_7991650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991650 prefixEnd_7991650 := by exact prefixLift 7991650
  have htrace : WordTrace (prefixWord ++ tailWord_7991650) baseStart_7991650 baseEnd_7991650 := by
    simpa [prefixWord, tailWord_7991650, baseEnd_7991650] using wordTrace_append hprefix tailTrace_7991650
  have hstable : (prefixWord ++ tailWord_7991650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991650).length < 2 ^ (prefixWord ++ tailWord_7991650).sum := by decide
  have hdescent : baseEnd_7991650 < baseStart_7991650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991703 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 4, 2, 2]
def baseStart_7991703 : Nat := 118140960795 + 7991703 * 2 ^ 59
def prefixEnd_7991703 : Nat := 4983230072969 + 3 ^ 40 * 7991703 * 2
def baseEnd_7991703 : Nat := 4103584886978451158959333

theorem tailTrace_7991703 : CollatzResearch.WordTrace tailWord_7991703 prefixEnd_7991703 4103584886978451158959333 := by
  unfold tailWord_7991703
  simp only [CollatzResearch.WordTrace]
  refine ⟨291481354566432380054323763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194320903044288253369549175 291481354566432380054323763)
  ·
    refine ⟨437222031849648570081485645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291481354566432380054323763 437222031849648570081485645)
    ·
      refine ⟨163958261943618213780557117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437222031849648570081485645 163958261943618213780557117)
      ·
        refine ⟨61484348228856830167708919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163958261943618213780557117 61484348228856830167708919)
        ·
          refine ⟨92226522343285245251563379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61484348228856830167708919 92226522343285245251563379)
          ·
            refine ⟨138339783514927867877345069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92226522343285245251563379 138339783514927867877345069)
            ·
              refine ⟨51877418818097950454004401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138339783514927867877345069 51877418818097950454004401)
              ·
                refine ⟨38908064113573462840503301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51877418818097950454004401 38908064113573462840503301)
                ·
                  refine ⟨7295262021295024282594369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38908064113573462840503301 7295262021295024282594369)
                  ·
                    refine ⟨5471446515971268211945777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7295262021295024282594369 5471446515971268211945777)
                    ·
                      refine ⟨4103584886978451158959333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471446515971268211945777 4103584886978451158959333)
                      ·
                        rfl

theorem cell23_7991703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_7991703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991703 prefixEnd_7991703 := by exact prefixLift 7991703
  have htrace : WordTrace (prefixWord ++ tailWord_7991703) baseStart_7991703 baseEnd_7991703 := by
    simpa [prefixWord, tailWord_7991703, baseEnd_7991703] using wordTrace_append hprefix tailTrace_7991703
  have hstable : (prefixWord ++ tailWord_7991703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991703).length < 2 ^ (prefixWord ++ tailWord_7991703).sum := by decide
  have hdescent : baseEnd_7991703 < baseStart_7991703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991706 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7991706 : Nat := 118140960795 + 7991706 * 2 ^ 59
def prefixEnd_7991706 : Nat := 4983230072969 + 3 ^ 40 * 7991706 * 2
def baseEnd_7991706 : Nat := 4103586427420414647221819

theorem tailTrace_7991706 : CollatzResearch.WordTrace tailWord_7991706 prefixEnd_7991706 4103586427420414647221819 := by
  unfold tailWord_7991706
  simp only [CollatzResearch.WordTrace]
  refine ⟨72870365996355377891670743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194320975990281007711121981 72870365996355377891670743)
  ·
    refine ⟨109305548994533066837506115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72870365996355377891670743 109305548994533066837506115)
    ·
      refine ⟨163958323491799600256259173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109305548994533066837506115 163958323491799600256259173)
      ·
        refine ⟨30742185654712425048048595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163958323491799600256259173 30742185654712425048048595)
        ·
          refine ⟨46113278482068637572072893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30742185654712425048048595 46113278482068637572072893)
          ·
            refine ⟨17292479430775739089527335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46113278482068637572072893 17292479430775739089527335)
            ·
              refine ⟨25938719146163608634291003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17292479430775739089527335 25938719146163608634291003)
              ·
                refine ⟨38908078719245412951436505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25938719146163608634291003 38908078719245412951436505)
                ·
                  refine ⟨29181059039434059713577379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38908078719245412951436505 29181059039434059713577379)
                  ·
                    refine ⟨43771588559151089570366069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29181059039434059713577379 43771588559151089570366069)
                    ·
                      refine ⟨4103586427420414647221819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43771588559151089570366069 4103586427420414647221819)
                      ·
                        rfl

theorem cell23_7991706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7991706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991706 prefixEnd_7991706 := by exact prefixLift 7991706
  have htrace : WordTrace (prefixWord ++ tailWord_7991706) baseStart_7991706 baseEnd_7991706 := by
    simpa [prefixWord, tailWord_7991706, baseEnd_7991706] using wordTrace_append hprefix tailTrace_7991706
  have hstable : (prefixWord ++ tailWord_7991706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991706).length < 2 ^ (prefixWord ++ tailWord_7991706).sum := by decide
  have hdescent : baseEnd_7991706 < baseStart_7991706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991737 : List Nat := [1, 2, 1, 4, 3, 1, 4, 1, 2, 2, 2]
def baseStart_7991737 : Nat := 118140960795 + 7991737 * 2 ^ 59
def prefixEnd_7991737 : Nat := 4983230072969 + 3 ^ 40 * 7991737 * 2
def baseEnd_7991737 : Nat := 4103602345320704025934177

theorem tailTrace_7991737 : CollatzResearch.WordTrace tailWord_7991737 prefixEnd_7991737 4103602345320704025934177 := by
  unfold tailWord_7991737
  simp only [CollatzResearch.WordTrace]
  refine ⟨291482594648309203861061465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194321729765539469240707643 291482594648309203861061465)
  ·
    refine ⟨218611945986231902895796099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291482594648309203861061465 218611945986231902895796099)
    ·
      refine ⟨327917918979347854343694149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218611945986231902895796099 327917918979347854343694149)
      ·
        refine ⟨61484609808627722689442653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327917918979347854343694149 61484609808627722689442653)
        ·
          refine ⟨23056728678235396008540995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61484609808627722689442653 23056728678235396008540995)
          ·
            refine ⟨34585093017353094012811493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23056728678235396008540995 34585093017353094012811493)
            ·
              refine ⟨6484704940753705127402155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34585093017353094012811493 6484704940753705127402155)
              ·
                refine ⟨9727057411130557691103233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484704940753705127402155 9727057411130557691103233)
                ·
                  refine ⟨7295293058347918268327425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9727057411130557691103233 7295293058347918268327425)
                  ·
                    refine ⟨5471469793760938701245569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7295293058347918268327425 5471469793760938701245569)
                    ·
                      refine ⟨4103602345320704025934177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471469793760938701245569 4103602345320704025934177)
                      ·
                        rfl

theorem cell23_7991737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_7991737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991737 prefixEnd_7991737 := by exact prefixLift 7991737
  have htrace : WordTrace (prefixWord ++ tailWord_7991737) baseStart_7991737 baseEnd_7991737 := by
    simpa [prefixWord, tailWord_7991737, baseEnd_7991737] using wordTrace_append hprefix tailTrace_7991737
  have hstable : (prefixWord ++ tailWord_7991737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991737).length < 2 ^ (prefixWord ++ tailWord_7991737).sum := by decide
  have hdescent : baseEnd_7991737 < baseStart_7991737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991776 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_7991776 : Nat := 118140960795 + 7991776 * 2 ^ 59
def prefixEnd_7991776 : Nat := 4983230072969 + 3 ^ 40 * 7991776 * 2
def baseEnd_7991776 : Nat := 4103622371066229373346497

theorem tailTrace_7991776 : CollatzResearch.WordTrace tailWord_7991776 prefixEnd_7991776 4103622371066229373346497 := by
  unfold tailWord_7991776
  simp only [CollatzResearch.WordTrace]
  refine ⟨145742008547583956760865591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194322678063445275681154121 145742008547583956760865591)
  ·
    refine ⟨218613012821375935141298387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145742008547583956760865591 218613012821375935141298387)
    ·
      refine ⟨327919519232063902711947581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218613012821375935141298387 327919519232063902711947581)
      ·
        refine ⟨122969819712023963516980343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327919519232063902711947581 122969819712023963516980343)
        ·
          refine ⟨184454729568035945275470515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122969819712023963516980343 184454729568035945275470515)
          ·
            refine ⟨276682094352053917913205773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184454729568035945275470515 276682094352053917913205773)
            ·
              refine ⟨103755785382020219217452165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276682094352053917913205773 103755785382020219217452165)
              ·
                refine ⟨19454209759128791103272281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103755785382020219217452165 19454209759128791103272281)
                ·
                  refine ⟨14590657319346593327454211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19454209759128791103272281 14590657319346593327454211)
                  ·
                    refine ⟨21885985979019889991181317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14590657319346593327454211 21885985979019889991181317)
                    ·
                      refine ⟨4103622371066229373346497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21885985979019889991181317 4103622371066229373346497)
                      ·
                        rfl

theorem cell23_7991776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_7991776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991776 prefixEnd_7991776 := by exact prefixLift 7991776
  have htrace : WordTrace (prefixWord ++ tailWord_7991776) baseStart_7991776 baseEnd_7991776 := by
    simpa [prefixWord, tailWord_7991776, baseEnd_7991776] using wordTrace_append hprefix tailTrace_7991776
  have hstable : (prefixWord ++ tailWord_7991776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991776).length < 2 ^ (prefixWord ++ tailWord_7991776).sum := by decide
  have hdescent : baseEnd_7991776 < baseStart_7991776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991793 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 2, 4, 2]
def baseStart_7991793 : Nat := 118140960795 + 7991793 * 2 ^ 59
def prefixEnd_7991793 : Nat := 4983230072969 + 3 ^ 40 * 7991793 * 2
def baseEnd_7991793 : Nat := 4103631100237355806833919

theorem tailTrace_7991793 : CollatzResearch.WordTrace tailWord_7991793 prefixEnd_7991793 4103631100237355806833919 := by
  unfold tailWord_7991793
  simp only [CollatzResearch.WordTrace]
  refine ⟨291484637136106325425100033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194323091424070883616733355 291484637136106325425100033)
  ·
    refine ⟨218613477852079744068825025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291484637136106325425100033 218613477852079744068825025)
    ·
      refine ⟨163960108389059808051618769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218613477852079744068825025 163960108389059808051618769)
      ·
        refine ⟨122970081291794856038714077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163960108389059808051618769 122970081291794856038714077)
        ·
          refine ⟨46113780484423071014517779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122970081291794856038714077 46113780484423071014517779)
          ·
            refine ⟨69170670726634606521776669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46113780484423071014517779 69170670726634606521776669)
            ·
              refine ⟨25939001522487977445666251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69170670726634606521776669 25939001522487977445666251)
              ·
                refine ⟨38908502283731966168499377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25939001522487977445666251 38908502283731966168499377)
                ·
                  refine ⟨29181376712798974626374533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38908502283731966168499377 29181376712798974626374533)
                  ·
                    refine ⟨5471508133649807742445225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29181376712798974626374533 5471508133649807742445225)
                    ·
                      refine ⟨4103631100237355806833919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471508133649807742445225 4103631100237355806833919)
                      ·
                        rfl

theorem cell23_7991793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_7991793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991793 prefixEnd_7991793 := by exact prefixLift 7991793
  have htrace : WordTrace (prefixWord ++ tailWord_7991793) baseStart_7991793 baseEnd_7991793 := by
    simpa [prefixWord, tailWord_7991793, baseEnd_7991793] using wordTrace_append hprefix tailTrace_7991793
  have hstable : (prefixWord ++ tailWord_7991793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991793).length < 2 ^ (prefixWord ++ tailWord_7991793).sum := by decide
  have hdescent : baseEnd_7991793 < baseStart_7991793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991810 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_7991810 : Nat := 118140960795 + 7991810 * 2 ^ 59
def prefixEnd_7991810 : Nat := 4983230072969 + 3 ^ 40 * 7991810 * 2
def baseEnd_7991810 : Nat := 4103639829408482240321341

theorem tailTrace_7991810 : CollatzResearch.WordTrace tailWord_7991810 prefixEnd_7991810 4103639829408482240321341 := by
  unfold tailWord_7991810
  simp only [CollatzResearch.WordTrace]
  refine ⟨72871314294261184332117221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194323504784696491552312589 72871314294261184332117221)
  ·
    refine ⟨13663371430173972062271979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72871314294261184332117221 13663371430173972062271979)
    ·
      refine ⟨20495057145260958093407969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13663371430173972062271979 20495057145260958093407969)
      ·
        refine ⟨15371292858945718570055977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20495057145260958093407969 15371292858945718570055977)
        ·
          refine ⟨11528469644209288927541983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15371292858945718570055977 11528469644209288927541983)
          ·
            refine ⟨17292704466313933391312975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11528469644209288927541983 17292704466313933391312975)
            ·
              refine ⟨25939056699470900086969463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17292704466313933391312975 25939056699470900086969463)
              ·
                refine ⟨38908585049206350130454195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25939056699470900086969463 38908585049206350130454195)
                ·
                  refine ⟨58362877573809525195681293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38908585049206350130454195 58362877573809525195681293)
                  ·
                    refine ⟨21886079090178571948380485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58362877573809525195681293 21886079090178571948380485)
                    ·
                      refine ⟨4103639829408482240321341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21886079090178571948380485 4103639829408482240321341)
                      ·
                        rfl

theorem cell23_7991810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_7991810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991810 prefixEnd_7991810 := by exact prefixLift 7991810
  have htrace : WordTrace (prefixWord ++ tailWord_7991810) baseStart_7991810 baseEnd_7991810 := by
    simpa [prefixWord, tailWord_7991810, baseEnd_7991810] using wordTrace_append hprefix tailTrace_7991810
  have hstable : (prefixWord ++ tailWord_7991810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991810).length < 2 ^ (prefixWord ++ tailWord_7991810).sum := by decide
  have hdescent : baseEnd_7991810 < baseStart_7991810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991813 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_7991813 : Nat := 118140960795 + 7991813 * 2 ^ 59
def prefixEnd_7991813 : Nat := 4983230072969 + 3 ^ 40 * 7991813 * 2
def baseEnd_7991813 : Nat := 4103641369850445728583827

theorem tailTrace_7991813 : CollatzResearch.WordTrace tailWord_7991813 prefixEnd_7991813 4103641369850445728583827 := by
  unfold tailWord_7991813
  simp only [CollatzResearch.WordTrace]
  refine ⟨291485366596033868840828093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194323577730689245893885395 291485366596033868840828093)
  ·
    refine ⟨109307012473512700815310535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291485366596033868840828093 109307012473512700815310535)
    ·
      refine ⟨163960518710269051222965803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109307012473512700815310535 163960518710269051222965803)
      ·
        refine ⟨245940778065403576834448705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163960518710269051222965803 245940778065403576834448705)
        ·
          refine ⟨184455583549052682625836529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245940778065403576834448705 184455583549052682625836529)
          ·
            refine ⟨138341687661789511969377397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184455583549052682625836529 138341687661789511969377397)
            ·
              refine ⟨12969533218292766747129131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138341687661789511969377397 12969533218292766747129131)
              ·
                refine ⟨19454299827439150120693697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12969533218292766747129131 19454299827439150120693697)
                ·
                  refine ⟨14590724870579362590520273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19454299827439150120693697 14590724870579362590520273)
                  ·
                    refine ⟨10943043652934521942890205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14590724870579362590520273 10943043652934521942890205)
                    ·
                      refine ⟨4103641369850445728583827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943043652934521942890205 4103641369850445728583827)
                      ·
                        rfl

theorem cell23_7991813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_7991813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991813 prefixEnd_7991813 := by exact prefixLift 7991813
  have htrace : WordTrace (prefixWord ++ tailWord_7991813) baseStart_7991813 baseEnd_7991813 := by
    simpa [prefixWord, tailWord_7991813, baseEnd_7991813] using wordTrace_append hprefix tailTrace_7991813
  have hstable : (prefixWord ++ tailWord_7991813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991813).length < 2 ^ (prefixWord ++ tailWord_7991813).sum := by decide
  have hdescent : baseEnd_7991813 < baseStart_7991813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991820 : List Nat := [2, 2, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_7991820 : Nat := 118140960795 + 7991820 * 2 ^ 59
def prefixEnd_7991820 : Nat := 4983230072969 + 3 ^ 40 * 7991820 * 2
def baseEnd_7991820 : Nat := 1367881654738342400398765

theorem tailTrace_7991820 : CollatzResearch.WordTrace tailWord_7991820 prefixEnd_7991820 1367881654738342400398765 := by
  unfold tailWord_7991820
  simp only [CollatzResearch.WordTrace]
  refine ⟨145742810953504254518166457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194323747938005672690888609 145742810953504254518166457)
  ·
    refine ⟨109307108215128190888624843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145742810953504254518166457 109307108215128190888624843)
    ·
      refine ⟨163960662322692286332937265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109307108215128190888624843 163960662322692286332937265)
      ·
        refine ⟨122970496742019214749702949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163960662322692286332937265 122970496742019214749702949)
        ·
          refine ⟨23056968139128602765569303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122970496742019214749702949 23056968139128602765569303)
          ·
            refine ⟨34585452208692904148353955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23056968139128602765569303 34585452208692904148353955)
            ·
              refine ⟨51878178313039356222530933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34585452208692904148353955 51878178313039356222530933)
              ·
                refine ⟨4863579216847439645862275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51878178313039356222530933 4863579216847439645862275)
                ·
                  refine ⟨7295368825271159468793413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863579216847439645862275 7295368825271159468793413)
                  ·
                    refine ⟨1367881654738342400398765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295368825271159468793413 1367881654738342400398765)
                    ·
                      rfl

theorem cell23_7991820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_7991820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991820 prefixEnd_7991820 := by exact prefixLift 7991820
  have htrace : WordTrace (prefixWord ++ tailWord_7991820) baseStart_7991820 baseEnd_7991820 := by
    simpa [prefixWord, tailWord_7991820, baseEnd_7991820] using wordTrace_append hprefix tailTrace_7991820
  have hstable : (prefixWord ++ tailWord_7991820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991820).length < 2 ^ (prefixWord ++ tailWord_7991820).sum := by decide
  have hdescent : baseEnd_7991820 < baseStart_7991820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991836 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7991836 : Nat := 118140960795 + 7991836 * 2 ^ 59
def prefixEnd_7991836 : Nat := 4983230072969 + 3 ^ 40 * 7991836 * 2
def baseEnd_7991836 : Nat := 4103653179905499138596221

theorem tailTrace_7991836 : CollatzResearch.WordTrace tailWord_7991836 prefixEnd_7991836 4103653179905499138596221 := by
  unfold tailWord_7991836
  simp only [CollatzResearch.WordTrace]
  refine ⟨145743102737475271884457681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194324136983300362512610241 145743102737475271884457681)
  ·
    refine ⟨109307327053106453913343261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145743102737475271884457681 109307327053106453913343261)
    ·
      refine ⟨40990247644914920217503723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109307327053106453913343261 40990247644914920217503723)
      ·
        refine ⟨61485371467372380326255585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40990247644914920217503723 61485371467372380326255585)
        ·
          refine ⟨46114028600529285244691689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61485371467372380326255585 46114028600529285244691689)
          ·
            refine ⟨34585521450396963933518767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46114028600529285244691689 34585521450396963933518767)
            ·
              refine ⟨51878282175595445900278151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34585521450396963933518767 51878282175595445900278151)
              ·
                refine ⟨77817423263393168850417227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51878282175595445900278151 77817423263393168850417227)
                ·
                  refine ⟨116726134895089753275625841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77817423263393168850417227 116726134895089753275625841)
                  ·
                    refine ⟨87544601171317314956719381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116726134895089753275625841 87544601171317314956719381)
                    ·
                      refine ⟨4103653179905499138596221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87544601171317314956719381 4103653179905499138596221)
                      ·
                        rfl

theorem cell23_7991836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7991836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991836 prefixEnd_7991836 := by exact prefixLift 7991836
  have htrace : WordTrace (prefixWord ++ tailWord_7991836) baseStart_7991836 baseEnd_7991836 := by
    simpa [prefixWord, tailWord_7991836, baseEnd_7991836] using wordTrace_append hprefix tailTrace_7991836
  have hstable : (prefixWord ++ tailWord_7991836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991836).length < 2 ^ (prefixWord ++ tailWord_7991836).sum := by decide
  have hdescent : baseEnd_7991836 < baseStart_7991836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991850 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 6]
def baseStart_7991850 : Nat := 118140960795 + 7991850 * 2 ^ 59
def prefixEnd_7991850 : Nat := 4983230072969 + 3 ^ 40 * 7991850 * 2
def baseEnd_7991850 : Nat := 455962263181629120424573

theorem tailTrace_7991850 : CollatzResearch.WordTrace tailWord_7991850 prefixEnd_7991850 455962263181629120424573 := by
  unfold tailWord_7991850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72871679024224956039981251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194324477397933216106616669 72871679024224956039981251)
  ·
    refine ⟨109307518536337434059971877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72871679024224956039981251 109307518536337434059971877)
    ·
      refine ⟨20495159725563268886244727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109307518536337434059971877 20495159725563268886244727)
      ·
        refine ⟨30742739588344903329367091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20495159725563268886244727 30742739588344903329367091)
        ·
          refine ⟨46114109382517354994050637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30742739588344903329367091 46114109382517354994050637)
          ·
            refine ⟨17292791018444008122768989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46114109382517354994050637 17292791018444008122768989)
            ·
              refine ⟨6484796631916503046038371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17292791018444008122768989 6484796631916503046038371)
              ·
                refine ⟨9727194947874754569057557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484796631916503046038371 9727194947874754569057557)
                ·
                  refine ⟨455962263181629120424573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9727194947874754569057557 455962263181629120424573)
                  ·
                    rfl

theorem cell23_7991850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_7991850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991850 prefixEnd_7991850 := by exact prefixLift 7991850
  have htrace : WordTrace (prefixWord ++ tailWord_7991850) baseStart_7991850 baseEnd_7991850 := by
    simpa [prefixWord, tailWord_7991850, baseEnd_7991850] using wordTrace_append hprefix tailTrace_7991850
  have hstable : (prefixWord ++ tailWord_7991850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991850).length < 2 ^ (prefixWord ++ tailWord_7991850).sum := by decide
  have hdescent : baseEnd_7991850 < baseStart_7991850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991863 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 1, 5]
def baseStart_7991863 : Nat := 118140960795 + 7991863 * 2 ^ 59
def prefixEnd_7991863 : Nat := 4983230072969 + 3 ^ 40 * 7991863 * 2
def baseEnd_7991863 : Nat := 1367889014627723510986199

theorem tailTrace_7991863 : CollatzResearch.WordTrace tailWord_7991863 prefixEnd_7991863 1367889014627723510986199 := by
  unfold tailWord_7991863
  simp only [CollatzResearch.WordTrace]
  refine ⟨291487190245852727380148243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194324793497235151586765495 291487190245852727380148243)
  ·
    refine ⟨437230785368779091070222365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291487190245852727380148243 437230785368779091070222365)
    ·
      refine ⟨163961544513292159151333387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437230785368779091070222365 163961544513292159151333387)
      ·
        refine ⟨245942316769938238727000081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163961544513292159151333387 245942316769938238727000081)
        ·
          refine ⟨184456737577453679045250061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245942316769938238727000081 184456737577453679045250061)
          ·
            refine ⟨69171276591545129641968773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184456737577453679045250061 69171276591545129641968773)
            ·
              refine ⟨12969614360914711807869145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69171276591545129641968773 12969614360914711807869145)
              ·
                refine ⟨9727210770686033855901859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12969614360914711807869145 9727210770686033855901859)
                ·
                  refine ⟨14590816156029050783852789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9727210770686033855901859 14590816156029050783852789)
                  ·
                    refine ⟨1367889014627723510986199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14590816156029050783852789 1367889014627723510986199)
                    ·
                      rfl

theorem cell23_7991863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_7991863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991863 prefixEnd_7991863 := by exact prefixLift 7991863
  have htrace : WordTrace (prefixWord ++ tailWord_7991863) baseStart_7991863 baseEnd_7991863 := by
    simpa [prefixWord, tailWord_7991863, baseEnd_7991863] using wordTrace_append hprefix tailTrace_7991863
  have hstable : (prefixWord ++ tailWord_7991863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991863).length < 2 ^ (prefixWord ++ tailWord_7991863).sum := by decide
  have hdescent : baseEnd_7991863 < baseStart_7991863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991877 : List Nat := [1, 3, 1, 1, 1, 5, 3, 3, 1, 1, 3]
def baseStart_7991877 : Nat := 118140960795 + 7991877 * 2 ^ 59
def prefixEnd_7991877 : Nat := 4983230072969 + 3 ^ 40 * 7991877 * 2
def baseEnd_7991877 : Nat := 4103674232612333478183533

theorem tailTrace_7991877 : CollatzResearch.WordTrace tailWord_7991877 prefixEnd_7991877 4103674232612333478183533 := by
  unfold tailWord_7991877
  simp only [CollatzResearch.WordTrace]
  refine ⟨291487700867802007771157885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194325133911868005180771923 291487700867802007771157885)
  ·
    refine ⟨109307887825425752914184207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291487700867802007771157885 109307887825425752914184207)
    ·
      refine ⟨163961831738138629371276311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109307887825425752914184207 163961831738138629371276311)
      ·
        refine ⟨245942747607207944056914467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163961831738138629371276311 245942747607207944056914467)
        ·
          refine ⟨368914121410811916085371701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245942747607207944056914467 368914121410811916085371701)
          ·
            refine ⟨34585698882263617133003597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368914121410811916085371701 34585698882263617133003597)
            ·
              refine ⟨12969637080848856424876349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34585698882263617133003597 12969637080848856424876349)
              ·
                refine ⟨4863613905318321159328631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12969637080848856424876349 4863613905318321159328631)
                ·
                  refine ⟨7295420857977481738992947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863613905318321159328631 7295420857977481738992947)
                  ·
                    refine ⟨10943131286966222608489421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7295420857977481738992947 10943131286966222608489421)
                    ·
                      refine ⟨4103674232612333478183533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943131286966222608489421 4103674232612333478183533)
                      ·
                        rfl

theorem cell23_7991877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_7991877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991877 prefixEnd_7991877 := by exact prefixLift 7991877
  have htrace : WordTrace (prefixWord ++ tailWord_7991877) baseStart_7991877 baseEnd_7991877 := by
    simpa [prefixWord, tailWord_7991877, baseEnd_7991877] using wordTrace_append hprefix tailTrace_7991877
  have hstable : (prefixWord ++ tailWord_7991877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991877).length < 2 ^ (prefixWord ++ tailWord_7991877).sum := by decide
  have hdescent : baseEnd_7991877 < baseStart_7991877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991883 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 4]
def baseStart_7991883 : Nat := 118140960795 + 7991883 * 2 ^ 59
def prefixEnd_7991883 : Nat := 4983230072969 + 3 ^ 40 * 7991883 * 2
def baseEnd_7991883 : Nat := 4103677313496260454708505

theorem tailTrace_7991883 : CollatzResearch.WordTrace tailWord_7991883 prefixEnd_7991883 4103677313496260454708505 := by
  unfold tailWord_7991883
  simp only [CollatzResearch.WordTrace]
  refine ⟨291487919705780270795876303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194325279803853513863917535 291487919705780270795876303)
  ·
    refine ⟨437231879558670406193814455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291487919705780270795876303 437231879558670406193814455)
    ·
      refine ⟨655847819338005609290721683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437231879558670406193814455 655847819338005609290721683)
      ·
        refine ⟨983771729007008413936082525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655847819338005609290721683 983771729007008413936082525)
        ·
          refine ⟨368914398377628155226030947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 983771729007008413936082525 368914398377628155226030947)
          ·
            refine ⟨553371597566442232839046421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368914398377628155226030947 553371597566442232839046421)
            ·
              refine ⟨25939293635926979664330301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 553371597566442232839046421 25939293635926979664330301)
              ·
                refine ⟨9727235113472617374123863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25939293635926979664330301 9727235113472617374123863)
                ·
                  refine ⟨14590852670208926061185795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9727235113472617374123863 14590852670208926061185795)
                  ·
                    refine ⟨21886279005313389091778693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14590852670208926061185795 21886279005313389091778693)
                    ·
                      refine ⟨4103677313496260454708505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21886279005313389091778693 4103677313496260454708505)
                      ·
                        rfl

theorem cell23_7991883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 4].length) (baseStart_7991883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991883 prefixEnd_7991883 := by exact prefixLift 7991883
  have htrace : WordTrace (prefixWord ++ tailWord_7991883) baseStart_7991883 baseEnd_7991883 := by
    simpa [prefixWord, tailWord_7991883, baseEnd_7991883] using wordTrace_append hprefix tailTrace_7991883
  have hstable : (prefixWord ++ tailWord_7991883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991883).length < 2 ^ (prefixWord ++ tailWord_7991883).sum := by decide
  have hdescent : baseEnd_7991883 < baseStart_7991883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991893 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_7991893 : Nat := 118140960795 + 7991893 * 2 ^ 59
def prefixEnd_7991893 : Nat := 4983230072969 + 3 ^ 40 * 7991893 * 2
def baseEnd_7991893 : Nat := 1367894149434268471861153

theorem tailTrace_7991893 : CollatzResearch.WordTrace tailWord_7991893 prefixEnd_7991893 1367894149434268471861153 := by
  unfold tailWord_7991893
  simp only [CollatzResearch.WordTrace]
  refine ⟨291488284435744042503740333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194325522957162695002493555 291488284435744042503740333)
  ·
    refine ⟨109308106663404015938902625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291488284435744042503740333 109308106663404015938902625)
    ·
      refine ⟨81981079997553011954176969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109308106663404015938902625 81981079997553011954176969)
      ·
        refine ⟨61485809998164758965632727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81981079997553011954176969 61485809998164758965632727)
        ·
          refine ⟨92228714997247138448449091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61485809998164758965632727 92228714997247138448449091)
          ·
            refine ⟨138343072495870707672673637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92228714997247138448449091 138343072495870707672673637)
            ·
              refine ⟨25939326092975757688626307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138343072495870707672673637 25939326092975757688626307)
              ·
                refine ⟨38908989139463636532939461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25939326092975757688626307 38908989139463636532939461)
                ·
                  refine ⟨7295435463649431849926149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38908989139463636532939461 7295435463649431849926149)
                  ·
                    refine ⟨1367894149434268471861153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295435463649431849926149 1367894149434268471861153)
                    ·
                      rfl

theorem cell23_7991893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_7991893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991893 prefixEnd_7991893 := by exact prefixLift 7991893
  have htrace : WordTrace (prefixWord ++ tailWord_7991893) baseStart_7991893 baseEnd_7991893 := by
    simpa [prefixWord, tailWord_7991893, baseEnd_7991893] using wordTrace_append hprefix tailTrace_7991893
  have hstable : (prefixWord ++ tailWord_7991893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991893).length < 2 ^ (prefixWord ++ tailWord_7991893).sum := by decide
  have hdescent : baseEnd_7991893 < baseStart_7991893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991896 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_7991896 : Nat := 118140960795 + 7991896 * 2 ^ 59
def prefixEnd_7991896 : Nat := 4983230072969 + 3 ^ 40 * 7991896 * 2
def baseEnd_7991896 : Nat := 4103683988744768903845945

theorem tailTrace_7991896 : CollatzResearch.WordTrace tailWord_7991896 prefixEnd_7991896 4103683988744768903845945 := by
  unfold tailWord_7991896
  simp only [CollatzResearch.WordTrace]
  refine ⟨145744196927366587008049771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194325595903155449344066361 145744196927366587008049771)
  ·
    refine ⟨218616295391049880512074657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145744196927366587008049771 218616295391049880512074657)
    ·
      refine ⟨163962221543287410384055993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218616295391049880512074657 163962221543287410384055993)
      ·
        refine ⟨122971666157465557788041995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163962221543287410384055993 122971666157465557788041995)
        ·
          refine ⟨184457499236198336682062993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122971666157465557788041995 184457499236198336682062993)
          ·
            refine ⟨138343124427148752511547245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184457499236198336682062993 138343124427148752511547245)
            ·
              refine ⟨51878671660180782191830217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138343124427148752511547245 51878671660180782191830217)
              ·
                refine ⟨38909003745135586643872663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51878671660180782191830217 38909003745135586643872663)
                ·
                  refine ⟨58363505617703379965808995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38909003745135586643872663 58363505617703379965808995)
                  ·
                    refine ⟨87545258426555069948713493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58363505617703379965808995 87545258426555069948713493)
                    ·
                      refine ⟨4103683988744768903845945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87545258426555069948713493 4103683988744768903845945)
                      ·
                        rfl

theorem cell23_7991896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_7991896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991896 prefixEnd_7991896 := by exact prefixLift 7991896
  have htrace : WordTrace (prefixWord ++ tailWord_7991896) baseStart_7991896 baseEnd_7991896 := by
    simpa [prefixWord, tailWord_7991896, baseEnd_7991896] using wordTrace_append hprefix tailTrace_7991896
  have hstable : (prefixWord ++ tailWord_7991896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991896).length < 2 ^ (prefixWord ++ tailWord_7991896).sum := by decide
  have hdescent : baseEnd_7991896 < baseStart_7991896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991917 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_7991917 : Nat := 118140960795 + 7991917 * 2 ^ 59
def prefixEnd_7991917 : Nat := 4983230072969 + 3 ^ 40 * 7991917 * 2
def baseEnd_7991917 : Nat := 4103694771838513321683349

theorem tailTrace_7991917 : CollatzResearch.WordTrace tailWord_7991917 prefixEnd_7991917 4103694771838513321683349 := by
  unfold tailWord_7991917
  simp only [CollatzResearch.WordTrace]
  refine ⟨291489159787657094602614005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194326106525104729735076003 291489159787657094602614005)
  ·
    refine ⟨27327108730092852618995063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291489159787657094602614005 27327108730092852618995063)
    ·
      refine ⟨40990663095139278928492595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27327108730092852618995063 40990663095139278928492595)
      ·
        refine ⟨61485994642708918392738893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40990663095139278928492595 61485994642708918392738893)
        ·
          refine ⟨23057247991015844397277085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61485994642708918392738893 23057247991015844397277085)
          ·
            refine ⟨8646467996630941648978907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23057247991015844397277085 8646467996630941648978907)
            ·
              refine ⟨12969701994946412473468361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646467996630941648978907 12969701994946412473468361)
              ·
                refine ⟨9727276496209809355101271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12969701994946412473468361 9727276496209809355101271)
                ·
                  refine ⟨14590914744314714032651907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9727276496209809355101271 14590914744314714032651907)
                  ·
                    refine ⟨21886372116472071048977861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14590914744314714032651907 21886372116472071048977861)
                    ·
                      refine ⟨4103694771838513321683349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21886372116472071048977861 4103694771838513321683349)
                      ·
                        rfl

theorem cell23_7991917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_7991917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991917 prefixEnd_7991917 := by exact prefixLift 7991917
  have htrace : WordTrace (prefixWord ++ tailWord_7991917) baseStart_7991917 baseEnd_7991917 := by
    simpa [prefixWord, tailWord_7991917, baseEnd_7991917] using wordTrace_append hprefix tailTrace_7991917
  have hstable : (prefixWord ++ tailWord_7991917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991917).length < 2 ^ (prefixWord ++ tailWord_7991917).sum := by decide
  have hdescent : baseEnd_7991917 < baseStart_7991917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991920 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3]
def baseStart_7991920 : Nat := 118140960795 + 7991920 * 2 ^ 59
def prefixEnd_7991920 : Nat := 4983230072969 + 3 ^ 40 * 7991920 * 2
def baseEnd_7991920 : Nat := 4103696312280476809945835

theorem tailTrace_7991920 : CollatzResearch.WordTrace tailWord_7991920 prefixEnd_7991920 4103696312280476809945835 := by
  unfold tailWord_7991920
  simp only [CollatzResearch.WordTrace]
  refine ⟨145744634603323113057486607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194326179471097484076648809 145744634603323113057486607)
  ·
    refine ⟨218616951904984669586229911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145744634603323113057486607 218616951904984669586229911)
    ·
      refine ⟨327925427857477004379344867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218616951904984669586229911 327925427857477004379344867)
      ·
        refine ⟨491888141786215506569017301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327925427857477004379344867 491888141786215506569017301)
        ·
          refine ⟨11528628323114425935211343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 491888141786215506569017301 11528628323114425935211343)
          ·
            refine ⟨17292942484671638902817015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11528628323114425935211343 17292942484671638902817015)
            ·
              refine ⟨25939413727007458354225523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17292942484671638902817015 25939413727007458354225523)
              ·
                refine ⟨38909120590511187531338285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25939413727007458354225523 38909120590511187531338285)
                ·
                  refine ⟨14590920221441695324251857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38909120590511187531338285 14590920221441695324251857)
                  ·
                    refine ⟨10943190166081271493188893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14590920221441695324251857 10943190166081271493188893)
                    ·
                      refine ⟨4103696312280476809945835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943190166081271493188893 4103696312280476809945835)
                      ·
                        rfl

theorem cell23_7991920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_7991920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991920 prefixEnd_7991920 := by exact prefixLift 7991920
  have htrace : WordTrace (prefixWord ++ tailWord_7991920) baseStart_7991920 baseEnd_7991920 := by
    simpa [prefixWord, tailWord_7991920, baseEnd_7991920] using wordTrace_append hprefix tailTrace_7991920
  have hstable : (prefixWord ++ tailWord_7991920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991920).length < 2 ^ (prefixWord ++ tailWord_7991920).sum := by decide
  have hdescent : baseEnd_7991920 < baseStart_7991920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991937 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7991937 : Nat := 118140960795 + 7991937 * 2 ^ 59
def prefixEnd_7991937 : Nat := 4983230072969 + 3 ^ 40 * 7991937 * 2
def baseEnd_7991937 : Nat := 4103705041451603243433257

theorem tailTrace_7991937 : CollatzResearch.WordTrace tailWord_7991937 prefixEnd_7991937 4103705041451603243433257 := by
  unfold tailWord_7991937
  simp only [CollatzResearch.WordTrace]
  refine ⟨291489889247584638018342065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194326592831723092012228043 291489889247584638018342065)
  ·
    refine ⟨218617416935688478513756549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291489889247584638018342065 218617416935688478513756549)
    ·
      refine ⟨40990765675441589721329353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218617416935688478513756549 40990765675441589721329353)
      ·
        refine ⟨30743074256581192290997015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40990765675441589721329353 30743074256581192290997015)
        ·
          refine ⟨46114611384871788436495523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30743074256581192290997015 46114611384871788436495523)
          ·
            refine ⟨69171917077307682654743285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46114611384871788436495523 69171917077307682654743285)
            ·
              refine ⟨6484867225997595248882183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69171917077307682654743285 6484867225997595248882183)
              ·
                refine ⟨9727300838996392873323275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484867225997595248882183 9727300838996392873323275)
                ·
                  refine ⟨14590951258494589309984913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9727300838996392873323275 14590951258494589309984913)
                  ·
                    refine ⟨10943213443870941982488685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14590951258494589309984913 10943213443870941982488685)
                    ·
                      refine ⟨4103705041451603243433257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943213443870941982488685 4103705041451603243433257)
                      ·
                        rfl

theorem cell23_7991937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7991937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991937 prefixEnd_7991937 := by exact prefixLift 7991937
  have htrace : WordTrace (prefixWord ++ tailWord_7991937) baseStart_7991937 baseEnd_7991937 := by
    simpa [prefixWord, tailWord_7991937, baseEnd_7991937] using wordTrace_append hprefix tailTrace_7991937
  have hstable : (prefixWord ++ tailWord_7991937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991937).length < 2 ^ (prefixWord ++ tailWord_7991937).sum := by decide
  have hdescent : baseEnd_7991937 < baseStart_7991937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7991960 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 5, 3, 2]
def baseStart_7991960 : Nat := 118140960795 + 7991960 * 2 ^ 59
def prefixEnd_7991960 : Nat := 4983230072969 + 3 ^ 40 * 7991960 * 2
def baseEnd_7991960 : Nat := 4103716851506656653445651

theorem tailTrace_7991960 : CollatzResearch.WordTrace tailWord_7991960 prefixEnd_7991960 4103716851506656653445651 := by
  unfold tailWord_7991960
  simp only [CollatzResearch.WordTrace]
  refine ⟨145745364063250656473214667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194327152084334208630952889 145745364063250656473214667)
  ·
    refine ⟨218618046094875984709822001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145745364063250656473214667 218618046094875984709822001)
    ·
      refine ⟨163963534571156988532366501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218618046094875984709822001 163963534571156988532366501)
      ·
        refine ⟨30743162732091935349818719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163963534571156988532366501 30743162732091935349818719)
        ·
          refine ⟨46114744098137903024728079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30743162732091935349818719 46114744098137903024728079)
          ·
            refine ⟨69172116147206854537092119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46114744098137903024728079 69172116147206854537092119)
            ·
              refine ⟨103758174220810281805638179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69172116147206854537092119 103758174220810281805638179)
              ·
                refine ⟨155637261331215422708457269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103758174220810281805638179 155637261331215422708457269)
                ·
                  refine ⟨14590993249801445878917869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155637261331215422708457269 14590993249801445878917869)
                  ·
                    refine ⟨5471622468675542204594201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14590993249801445878917869 5471622468675542204594201)
                    ·
                      refine ⟨4103716851506656653445651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471622468675542204594201 4103716851506656653445651)
                      ·
                        rfl

theorem cell23_7991960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_7991960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7991960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7991960 prefixEnd_7991960 := by exact prefixLift 7991960
  have htrace : WordTrace (prefixWord ++ tailWord_7991960) baseStart_7991960 baseEnd_7991960 := by
    simpa [prefixWord, tailWord_7991960, baseEnd_7991960] using wordTrace_append hprefix tailTrace_7991960
  have hstable : (prefixWord ++ tailWord_7991960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7991960).length < 2 ^ (prefixWord ++ tailWord_7991960).sum := by decide
  have hdescent : baseEnd_7991960 < baseStart_7991960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7991960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992007 : List Nat := [1, 1, 4, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_7992007 : Nat := 118140960795 + 7992007 * 2 ^ 59
def prefixEnd_7992007 : Nat := 4983230072969 + 3 ^ 40 * 7992007 * 2
def baseEnd_7992007 : Nat := 4103740985097417969557935

theorem tailTrace_7992007 : CollatzResearch.WordTrace tailWord_7992007 prefixEnd_7992007 4103740985097417969557935 := by
  unfold tailWord_7992007
  simp only [CollatzResearch.WordTrace]
  refine ⟨291492442357331039973390275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194328294904887359982260183 291492442357331039973390275)
  ·
    refine ⟨437238663535996559960085413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291492442357331039973390275 437238663535996559960085413)
    ·
      refine ⟨81982249412999354992516015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437238663535996559960085413 81982249412999354992516015)
      ·
        refine ⟨122973374119499032488774023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81982249412999354992516015 122973374119499032488774023)
        ·
          refine ⟨184460061179248548733161035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122973374119499032488774023 184460061179248548733161035)
          ·
            refine ⟨276690091768872823099741553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184460061179248548733161035 276690091768872823099741553)
            ·
              refine ⟨207517568826654617324806165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276690091768872823099741553 207517568826654617324806165)
              ·
                refine ⟨9727386038749435187100289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207517568826654617324806165 9727386038749435187100289)
                ·
                  refine ⟨7295539529062076390325217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9727386038749435187100289 7295539529062076390325217)
                  ·
                    refine ⟨5471654646796557292743913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7295539529062076390325217 5471654646796557292743913)
                    ·
                      refine ⟨4103740985097417969557935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471654646796557292743913 4103740985097417969557935)
                      ·
                        rfl

theorem cell23_7992007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_7992007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992007 prefixEnd_7992007 := by exact prefixLift 7992007
  have htrace : WordTrace (prefixWord ++ tailWord_7992007) baseStart_7992007 baseEnd_7992007 := by
    simpa [prefixWord, tailWord_7992007, baseEnd_7992007] using wordTrace_append hprefix tailTrace_7992007
  have hstable : (prefixWord ++ tailWord_7992007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992007).length < 2 ^ (prefixWord ++ tailWord_7992007).sum := by decide
  have hdescent : baseEnd_7992007 < baseStart_7992007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992043 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 2, 5]
def baseStart_7992043 : Nat := 118140960795 + 7992043 * 2 ^ 59
def prefixEnd_7992043 : Nat := 4983230072969 + 3 ^ 40 * 7992043 * 2
def baseEnd_7992043 : Nat := 1367919823466993276235923

theorem tailTrace_7992043 : CollatzResearch.WordTrace tailWord_7992043 prefixEnd_7992043 1367919823466993276235923 := by
  unfold tailWord_7992043
  simp only [CollatzResearch.WordTrace]
  refine ⟨291493755385200618121700783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194329170256800412081133855 291493755385200618121700783)
  ·
    refine ⟨437240633077800927182551175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291493755385200618121700783 437240633077800927182551175)
    ·
      refine ⟨655860949616701390773826763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437240633077800927182551175 655860949616701390773826763)
      ·
        refine ⟨983791424425052086160740145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655860949616701390773826763 983791424425052086160740145)
        ·
          refine ⟨737843568318789064620555109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983791424425052086160740145 737843568318789064620555109)
          ·
            refine ⟨138345669059772949616354083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 737843568318789064620555109 138345669059772949616354083)
            ·
              refine ⟨207518503589659424424531125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138345669059772949616354083 207518503589659424424531125)
              ·
                refine ⟨19454859711530571039799793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207518503589659424424531125 19454859711530571039799793)
                ·
                  refine ⟨14591144783647928279849845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19454859711530571039799793 14591144783647928279849845)
                  ·
                    refine ⟨1367919823466993276235923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14591144783647928279849845 1367919823466993276235923)
                    ·
                      rfl

theorem cell23_7992043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 5].length) (baseStart_7992043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992043 prefixEnd_7992043 := by exact prefixLift 7992043
  have htrace : WordTrace (prefixWord ++ tailWord_7992043) baseStart_7992043 baseEnd_7992043 := by
    simpa [prefixWord, tailWord_7992043, baseEnd_7992043] using wordTrace_append hprefix tailTrace_7992043
  have hstable : (prefixWord ++ tailWord_7992043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992043).length < 2 ^ (prefixWord ++ tailWord_7992043).sum := by decide
  have hdescent : baseEnd_7992043 < baseStart_7992043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992047 : List Nat := [1, 1, 2, 1, 5, 4, 1, 3, 5]
def baseStart_7992047 : Nat := 118140960795 + 7992047 * 2 ^ 59
def prefixEnd_7992047 : Nat := 4983230072969 + 3 ^ 40 * 7992047 * 2
def baseEnd_7992047 : Nat := 455973502702621979228639

theorem tailTrace_7992047 : CollatzResearch.WordTrace tailWord_7992047 prefixEnd_7992047 455973502702621979228639 := by
  unfold tailWord_7992047
  simp only [CollatzResearch.WordTrace]
  refine ⟨291493901277186126804846395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194329267518124084536564263 291493901277186126804846395)
  ·
    refine ⟨437240851915779190207269593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291493901277186126804846395 437240851915779190207269593)
    ·
      refine ⟨327930638936834392655452195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437240851915779190207269593 327930638936834392655452195)
      ·
        refine ⟨491895958405251588983178293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327930638936834392655452195 491895958405251588983178293)
        ·
          refine ⟨46115246100492336467172965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491895958405251588983178293 46115246100492336467172965)
          ·
            refine ⟨8646608643842313087594931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46115246100492336467172965 8646608643842313087594931)
            ·
              refine ⟨12969912965763469631392397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646608643842313087594931 12969912965763469631392397)
              ·
                refine ⟨4863717362161301111772149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12969912965763469631392397 4863717362161301111772149)
                ·
                  refine ⟨455973502702621979228639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4863717362161301111772149 455973502702621979228639)
                  ·
                    rfl

theorem cell23_7992047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 5].length) (baseStart_7992047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992047 prefixEnd_7992047 := by exact prefixLift 7992047
  have htrace : WordTrace (prefixWord ++ tailWord_7992047) baseStart_7992047 baseEnd_7992047 := by
    simpa [prefixWord, tailWord_7992047, baseEnd_7992047] using wordTrace_append hprefix tailTrace_7992047
  have hstable : (prefixWord ++ tailWord_7992047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992047).length < 2 ^ (prefixWord ++ tailWord_7992047).sum := by decide
  have hdescent : baseEnd_7992047 < baseStart_7992047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992060 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_7992060 : Nat := 118140960795 + 7992060 * 2 ^ 59
def prefixEnd_7992060 : Nat := 4983230072969 + 3 ^ 40 * 7992060 * 2
def baseEnd_7992060 : Nat := 1367922733190702087398397

theorem tailTrace_7992060 : CollatzResearch.WordTrace tailWord_7992060 prefixEnd_7992060 1367922733190702087398397 := by
  unfold tailWord_7992060
  simp only [CollatzResearch.WordTrace]
  refine ⟨145747187713069515012534817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194329583617426020016713089 145747187713069515012534817)
  ·
    refine ⟨109310390784802136259401113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145747187713069515012534817 109310390784802136259401113)
    ·
      refine ⟨81982793088601602194550835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109310390784802136259401113 81982793088601602194550835)
      ·
        refine ⟨122974189632902403291826253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81982793088601602194550835 122974189632902403291826253)
        ·
          refine ⟨46115321112338401234434845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122974189632902403291826253 46115321112338401234434845)
          ·
            refine ⟨17293245417126900462913067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46115321112338401234434845 17293245417126900462913067)
            ·
              refine ⟨25939868125690350694369601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17293245417126900462913067 25939868125690350694369601)
              ·
                refine ⟨19454901094267763020777201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25939868125690350694369601 19454901094267763020777201)
                ·
                  refine ⟨14591175820700822265582901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19454901094267763020777201 14591175820700822265582901)
                  ·
                    refine ⟨1367922733190702087398397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14591175820700822265582901 1367922733190702087398397)
                    ·
                      rfl

theorem cell23_7992060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_7992060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992060 prefixEnd_7992060 := by exact prefixLift 7992060
  have htrace : WordTrace (prefixWord ++ tailWord_7992060) baseStart_7992060 baseEnd_7992060 := by
    simpa [prefixWord, tailWord_7992060, baseEnd_7992060] using wordTrace_append hprefix tailTrace_7992060
  have hstable : (prefixWord ++ tailWord_7992060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992060).length < 2 ^ (prefixWord ++ tailWord_7992060).sum := by decide
  have hdescent : baseEnd_7992060 < baseStart_7992060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992090 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_7992090 : Nat := 118140960795 + 7992090 * 2 ^ 59
def prefixEnd_7992090 : Nat := 4983230072969 + 3 ^ 40 * 7992090 * 2
def baseEnd_7992090 : Nat := 1367927867997247048273351

theorem tailTrace_7992090 : CollatzResearch.WordTrace tailWord_7992090 prefixEnd_7992090 1367927867997247048273351 := by
  unfold tailWord_7992090
  simp only [CollatzResearch.WordTrace]
  refine ⟨72873867404007586287165431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194330313077353563432441149 72873867404007586287165431)
  ·
    refine ⟨109310801106011379430748147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72873867404007586287165431 109310801106011379430748147)
    ·
      refine ⟨163966201659017069146122221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109310801106011379430748147 163966201659017069146122221)
      ·
        refine ⟨61487325622131400929795833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163966201659017069146122221 61487325622131400929795833)
        ·
          refine ⟨46115494216598550697346875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61487325622131400929795833 46115494216598550697346875)
          ·
            refine ⟨69173241324897826046020313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46115494216598550697346875 69173241324897826046020313)
            ·
              refine ⟨51879930993673369534515235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69173241324897826046020313 51879930993673369534515235)
              ·
                refine ⟨77819896490510054301772853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51879930993673369534515235 77819896490510054301772853)
                ·
                  refine ⟨7295615295985317590791205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77819896490510054301772853 7295615295985317590791205)
                  ·
                    refine ⟨1367927867997247048273351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7295615295985317590791205 1367927867997247048273351)
                    ·
                      rfl

theorem cell23_7992090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_7992090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992090 prefixEnd_7992090 := by exact prefixLift 7992090
  have htrace : WordTrace (prefixWord ++ tailWord_7992090) baseStart_7992090 baseEnd_7992090 := by
    simpa [prefixWord, tailWord_7992090, baseEnd_7992090] using wordTrace_append hprefix tailTrace_7992090
  have hstable : (prefixWord ++ tailWord_7992090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992090).length < 2 ^ (prefixWord ++ tailWord_7992090).sum := by decide
  have hdescent : baseEnd_7992090 < baseStart_7992090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992117 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_7992117 : Nat := 118140960795 + 7992117 * 2 ^ 59
def prefixEnd_7992117 : Nat := 4983230072969 + 3 ^ 40 * 7992117 * 2
def baseEnd_7992117 : Nat := 4103797467969412539182429

theorem tailTrace_7992117 : CollatzResearch.WordTrace tailWord_7992117 prefixEnd_7992117 4103797467969412539182429 := by
  unfold tailWord_7992117
  simp only [CollatzResearch.WordTrace]
  refine ⟨291496454386932528759894605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194330969591288352506596403 291496454386932528759894605)
  ·
    refine ⟨109311170395099698284960477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291496454386932528759894605 109311170395099698284960477)
    ·
      refine ⟨40991688898162386856860179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109311170395099698284960477 40991688898162386856860179)
      ·
        refine ⟨61487533347243580285290269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40991688898162386856860179 61487533347243580285290269)
        ·
          refine ⟨23057825005216342606983851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61487533347243580285290269 23057825005216342606983851)
          ·
            refine ⟨34586737507824513910475777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23057825005216342606983851 34586737507824513910475777)
            ·
              refine ⟨25940053130868385432856833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34586737507824513910475777 25940053130868385432856833)
              ·
                refine ⟨19455039848151289074642625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25940053130868385432856833 19455039848151289074642625)
                ·
                  refine ⟨14591279886113466805981969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19455039848151289074642625 14591279886113466805981969)
                  ·
                    refine ⟨10943459914585100104486477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14591279886113466805981969 10943459914585100104486477)
                    ·
                      refine ⟨4103797467969412539182429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943459914585100104486477 4103797467969412539182429)
                      ·
                        rfl

theorem cell23_7992117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_7992117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992117 prefixEnd_7992117 := by exact prefixLift 7992117
  have htrace : WordTrace (prefixWord ++ tailWord_7992117) baseStart_7992117 baseEnd_7992117 := by
    simpa [prefixWord, tailWord_7992117, baseEnd_7992117] using wordTrace_append hprefix tailTrace_7992117
  have hstable : (prefixWord ++ tailWord_7992117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992117).length < 2 ^ (prefixWord ++ tailWord_7992117).sum := by decide
  have hdescent : baseEnd_7992117 < baseStart_7992117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992120 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 6]
def baseStart_7992120 : Nat := 118140960795 + 7992120 * 2 ^ 59
def prefixEnd_7992120 : Nat := 4983230072969 + 3 ^ 40 * 7992120 * 2
def baseEnd_7992120 : Nat := 455977667601264003049435

theorem tailTrace_7992120 : CollatzResearch.WordTrace tailWord_7992120 prefixEnd_7992120 455977667601264003049435 := by
  unfold tailWord_7992120
  simp only [CollatzResearch.WordTrace]
  refine ⟨145748281902960830136126907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194331042537281106848169209 145748281902960830136126907)
  ·
    refine ⟨218622422854441245204190361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145748281902960830136126907 218622422854441245204190361)
    ·
      refine ⟨163966817140830933903142771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218622422854441245204190361 163966817140830933903142771)
      ·
        refine ⟨245950225711246400854714157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163966817140830933903142771 245950225711246400854714157)
        ·
          refine ⟨92231334641717400320517809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245950225711246400854714157 92231334641717400320517809)
          ·
            refine ⟨69173500981288050240388357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92231334641717400320517809 69173500981288050240388357)
            ·
              refine ⟨12970031433991509420072817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69173500981288050240388357 12970031433991509420072817)
              ·
                refine ⟨9727523575493632065054613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12970031433991509420072817 9727523575493632065054613)
                ·
                  refine ⟨455977667601264003049435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9727523575493632065054613 455977667601264003049435)
                  ·
                    rfl

theorem cell23_7992120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 6].length) (baseStart_7992120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992120 prefixEnd_7992120 := by exact prefixLift 7992120
  have htrace : WordTrace (prefixWord ++ tailWord_7992120) baseStart_7992120 baseEnd_7992120 := by
    simpa [prefixWord, tailWord_7992120, baseEnd_7992120] using wordTrace_append hprefix tailTrace_7992120
  have hstable : (prefixWord ++ tailWord_7992120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992120).length < 2 ^ (prefixWord ++ tailWord_7992120).sum := by decide
  have hdescent : baseEnd_7992120 < baseStart_7992120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992167 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 1, 5]
def baseStart_7992167 : Nat := 118140960795 + 7992167 * 2 ^ 59
def prefixEnd_7992167 : Nat := 4983230072969 + 3 ^ 40 * 7992167 * 2
def baseEnd_7992167 : Nat := 1367941047334045781185733

theorem tailTrace_7992167 : CollatzResearch.WordTrace tailWord_7992167 prefixEnd_7992167 1367941047334045781185733 := by
  unfold tailWord_7992167
  simp only [CollatzResearch.WordTrace]
  refine ⟨291498278036751387299214755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194332185357834258199476503 291498278036751387299214755)
  ·
    refine ⟨437247417055127080948822133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291498278036751387299214755 437247417055127080948822133)
    ·
      refine ⟨40991945348918163838952075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 437247417055127080948822133 40991945348918163838952075)
      ·
        refine ⟨61487918023377245758428113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40991945348918163838952075 61487918023377245758428113)
        ·
          refine ⟨46115938517532934318821085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61487918023377245758428113 46115938517532934318821085)
          ·
            refine ⟨17293476944074850369557907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46115938517532934318821085 17293476944074850369557907)
            ·
              refine ⟨25940215416112275554336861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17293476944074850369557907 25940215416112275554336861)
              ·
                refine ⟨9727580781042103332876323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25940215416112275554336861 9727580781042103332876323)
                ·
                  refine ⟨14591371171563154999314485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9727580781042103332876323 14591371171563154999314485)
                  ·
                    refine ⟨1367941047334045781185733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14591371171563154999314485 1367941047334045781185733)
                    ·
                      rfl

theorem cell23_7992167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_7992167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992167 prefixEnd_7992167 := by exact prefixLift 7992167
  have htrace : WordTrace (prefixWord ++ tailWord_7992167) baseStart_7992167 baseEnd_7992167 := by
    simpa [prefixWord, tailWord_7992167, baseEnd_7992167] using wordTrace_append hprefix tailTrace_7992167
  have hstable : (prefixWord ++ tailWord_7992167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992167).length < 2 ^ (prefixWord ++ tailWord_7992167).sum := by decide
  have hdescent : baseEnd_7992167 < baseStart_7992167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992181 : List Nat := [1, 3, 4, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_7992181 : Nat := 118140960795 + 7992181 * 2 ^ 59
def prefixEnd_7992181 : Nat := 4983230072969 + 3 ^ 40 * 7992181 * 2
def baseEnd_7992181 : Nat := 4103830330731300288782135

theorem tailTrace_7992181 : CollatzResearch.WordTrace tailWord_7992181 prefixEnd_7992181 4103830330731300288782135 := by
  unfold tailWord_7992181
  simp only [CollatzResearch.WordTrace]
  refine ⟨291498788658700667690224397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194332525772467111793482931 291498788658700667690224397)
  ·
    refine ⟨109312045747012750383834149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291498788658700667690224397 109312045747012750383834149)
    ·
      refine ⟨20496008577564890696968903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109312045747012750383834149 20496008577564890696968903)
      ·
        refine ⟨30744012866347336045453355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20496008577564890696968903 30744012866347336045453355)
        ·
          refine ⟨46116019299521004068180033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30744012866347336045453355 46116019299521004068180033)
          ·
            refine ⟨34587014474640753051135025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46116019299521004068180033 34587014474640753051135025)
            ·
              refine ⟨25940260855980564788351269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34587014474640753051135025 25940260855980564788351269)
              ·
                refine ⟨4863798910496355897815863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25940260855980564788351269 4863798910496355897815863)
                ·
                  refine ⟨7295698365744533846723795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863798910496355897815863 7295698365744533846723795)
                  ·
                    refine ⟨10943547548616800770085693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7295698365744533846723795 10943547548616800770085693)
                    ·
                      refine ⟨4103830330731300288782135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943547548616800770085693 4103830330731300288782135)
                      ·
                        rfl

theorem cell23_7992181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_7992181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992181 prefixEnd_7992181 := by exact prefixLift 7992181
  have htrace : WordTrace (prefixWord ++ tailWord_7992181) baseStart_7992181 baseEnd_7992181 := by
    simpa [prefixWord, tailWord_7992181, baseEnd_7992181] using wordTrace_append hprefix tailTrace_7992181
  have hstable : (prefixWord ++ tailWord_7992181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992181).length < 2 ^ (prefixWord ++ tailWord_7992181).sum := by decide
  have hdescent : baseEnd_7992181 < baseStart_7992181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992197 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_7992197 : Nat := 118140960795 + 7992197 * 2 ^ 59
def prefixEnd_7992197 : Nat := 4983230072969 + 3 ^ 40 * 7992197 * 2
def baseEnd_7992197 : Nat := 1367946182140590742060687

theorem tailTrace_7992197 : CollatzResearch.WordTrace tailWord_7992197 prefixEnd_7992197 1367946182140590742060687 := by
  unfold tailWord_7992197
  simp only [CollatzResearch.WordTrace]
  refine ⟨291499372226642702422806845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194332914817761801615204563 291499372226642702422806845)
  ·
    refine ⟨109312264584991013408552567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291499372226642702422806845 109312264584991013408552567)
    ·
      refine ⟨163968396877486520112828851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109312264584991013408552567 163968396877486520112828851)
      ·
        refine ⟨245952595316229780169243277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163968396877486520112828851 245952595316229780169243277)
        ·
          refine ⟨92232223243586167563466229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245952595316229780169243277 92232223243586167563466229)
          ·
            refine ⟨8646770929086203209074959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92232223243586167563466229 8646770929086203209074959)
            ·
              refine ⟨12970156393629304813612439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646770929086203209074959 12970156393629304813612439)
              ·
                refine ⟨19455234590443957220418659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12970156393629304813612439 19455234590443957220418659)
                ·
                  refine ⟨29182851885665935830627989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19455234590443957220418659 29182851885665935830627989)
                  ·
                    refine ⟨1367946182140590742060687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29182851885665935830627989 1367946182140590742060687)
                    ·
                      rfl

theorem cell23_7992197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_7992197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992197 prefixEnd_7992197 := by exact prefixLift 7992197
  have htrace : WordTrace (prefixWord ++ tailWord_7992197) baseStart_7992197 baseEnd_7992197 := by
    simpa [prefixWord, tailWord_7992197, baseEnd_7992197] using wordTrace_append hprefix tailTrace_7992197
  have hstable : (prefixWord ++ tailWord_7992197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992197).length < 2 ^ (prefixWord ++ tailWord_7992197).sum := by decide
  have hdescent : baseEnd_7992197 < baseStart_7992197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992204 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 3, 2, 2]
def baseStart_7992204 : Nat := 118140960795 + 7992204 * 2 ^ 59
def prefixEnd_7992204 : Nat := 4983230072969 + 3 ^ 40 * 7992204 * 2
def baseEnd_7992204 : Nat := 4103842140786353698794529

theorem tailTrace_7992204 : CollatzResearch.WordTrace tailWord_7992204 prefixEnd_7992204 4103842140786353698794529 := by
  unfold tailWord_7992204
  simp only [CollatzResearch.WordTrace]
  refine ⟨145749813768808671309155833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194333085025078228412207777 145749813768808671309155833)
  ·
    refine ⟨109312360326606503481866875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145749813768808671309155833 109312360326606503481866875)
    ·
      refine ⟨163968540489909755222800313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109312360326606503481866875 163968540489909755222800313)
      ·
        refine ⟨122976405367432316417100235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163968540489909755222800313 122976405367432316417100235)
        ·
          refine ⟨184464608051148474625650353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122976405367432316417100235 184464608051148474625650353)
          ·
            refine ⟨138348456038361355969237765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184464608051148474625650353 138348456038361355969237765)
            ·
              refine ⟨25940335507192754244232081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138348456038361355969237765 25940335507192754244232081)
              ·
                refine ⟨19455251630394565683174061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25940335507192754244232081 19455251630394565683174061)
                ·
                  refine ⟨7295719361397962131190273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19455251630394565683174061 7295719361397962131190273)
                  ·
                    refine ⟨5471789521048471598392705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7295719361397962131190273 5471789521048471598392705)
                    ·
                      refine ⟨4103842140786353698794529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5471789521048471598392705 4103842140786353698794529)
                      ·
                        rfl

theorem cell23_7992204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_7992204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992204 prefixEnd_7992204 := by exact prefixLift 7992204
  have htrace : WordTrace (prefixWord ++ tailWord_7992204) baseStart_7992204 baseEnd_7992204 := by
    simpa [prefixWord, tailWord_7992204, baseEnd_7992204] using wordTrace_append hprefix tailTrace_7992204
  have hstable : (prefixWord ++ tailWord_7992204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992204).length < 2 ^ (prefixWord ++ tailWord_7992204).sum := by decide
  have hdescent : baseEnd_7992204 < baseStart_7992204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992244 : List Nat := [2, 5, 2, 1, 1, 2, 2, 8]
def baseStart_7992244 : Nat := 118140960795 + 7992244 * 2 ^ 59
def prefixEnd_7992244 : Nat := 4983230072969 + 3 ^ 40 * 7992244 * 2
def baseEnd_7992244 : Nat := 151994914074538279344235

theorem tailTrace_7992244 : CollatzResearch.WordTrace tailWord_7992244 prefixEnd_7992244 151994914074538279344235 := by
  unfold tailWord_7992244
  simp only [CollatzResearch.WordTrace]
  refine ⟨145750543228736214724883893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194334057638314952966511857 145750543228736214724883893)
  ·
    refine ⟨13664113427694020130457865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145750543228736214724883893 13664113427694020130457865)
    ·
      refine ⟨10248085070770515097843399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13664113427694020130457865 10248085070770515097843399)
      ·
        refine ⟨15372127606155772646765099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10248085070770515097843399 15372127606155772646765099)
        ·
          refine ⟨23058191409233658970147649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15372127606155772646765099 23058191409233658970147649)
          ·
            refine ⟨17293643556925244227610737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23058191409233658970147649 17293643556925244227610737)
            ·
              refine ⟨12970232667693933170708053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17293643556925244227610737 12970232667693933170708053)
              ·
                refine ⟨151994914074538279344235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12970232667693933170708053 151994914074538279344235)
                ·
                  rfl

theorem cell23_7992244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 8].length) (baseStart_7992244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992244 prefixEnd_7992244 := by exact prefixLift 7992244
  have htrace : WordTrace (prefixWord ++ tailWord_7992244) baseStart_7992244 baseEnd_7992244 := by
    simpa [prefixWord, tailWord_7992244, baseEnd_7992244] using wordTrace_append hprefix tailTrace_7992244
  have hstable : (prefixWord ++ tailWord_7992244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992244).length < 2 ^ (prefixWord ++ tailWord_7992244).sum := by decide
  have hdescent : baseEnd_7992244 < baseStart_7992244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992327 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_7992327 : Nat := 118140960795 + 7992327 * 2 ^ 59
def prefixEnd_7992327 : Nat := 4983230072969 + 3 ^ 40 * 7992327 * 2
def baseEnd_7992327 : Nat := 4103905298906856717556463

theorem tailTrace_7992327 : CollatzResearch.WordTrace tailWord_7992327 prefixEnd_7992327 4103905298906856717556463 := by
  unfold tailWord_7992327
  simp only [CollatzResearch.WordTrace]
  refine ⟨291504113716171734625039235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194336075810781156416692823 291504113716171734625039235)
  ·
    refine ⟨437256170574257601937558853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291504113716171734625039235 437256170574257601937558853)
    ·
      refine ⟨81985531982673300363292285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437256170574257601937558853 81985531982673300363292285)
      ·
        refine ⟨30744574493502487636234607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81985531982673300363292285 30744574493502487636234607)
        ·
          refine ⟨46116861740253731454351911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30744574493502487636234607 46116861740253731454351911)
          ·
            refine ⟨69175292610380597181527867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46116861740253731454351911 69175292610380597181527867)
            ·
              refine ⟨103762938915570895772291801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69175292610380597181527867 103762938915570895772291801)
              ·
                refine ⟨77822204186678171829218851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103762938915570895772291801 77822204186678171829218851)
                ·
                  refine ⟨116733306280017257743828277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77822204186678171829218851 116733306280017257743828277)
                  ·
                    refine ⟨10943747463751617913483901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116733306280017257743828277 10943747463751617913483901)
                    ·
                      refine ⟨4103905298906856717556463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943747463751617913483901 4103905298906856717556463)
                      ·
                        rfl

theorem cell23_7992327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_7992327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992327 prefixEnd_7992327 := by exact prefixLift 7992327
  have htrace : WordTrace (prefixWord ++ tailWord_7992327) baseStart_7992327 baseEnd_7992327 := by
    simpa [prefixWord, tailWord_7992327, baseEnd_7992327] using wordTrace_append hprefix tailTrace_7992327
  have hstable : (prefixWord ++ tailWord_7992327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992327).length < 2 ^ (prefixWord ++ tailWord_7992327).sum := by decide
  have hdescent : baseEnd_7992327 < baseStart_7992327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992334 : List Nat := [4, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_7992334 : Nat := 118140960795 + 7992334 * 2 ^ 59
def prefixEnd_7992334 : Nat := 4983230072969 + 3 ^ 40 * 7992334 * 2
def baseEnd_7992334 : Nat := 455989877030159798907659

theorem tailTrace_7992334 : CollatzResearch.WordTrace tailWord_7992334 prefixEnd_7992334 455989877030159798907659 := by
  unfold tailWord_7992334
  simp only [CollatzResearch.WordTrace]
  refine ⟨36438046128393296852568007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194336246018097583213696037 36438046128393296852568007)
  ·
    refine ⟨54657069192589945278852011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36438046128393296852568007 54657069192589945278852011)
    ·
      refine ⟨81985603788884917918278017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54657069192589945278852011 81985603788884917918278017)
      ·
        refine ⟨61489202841663688438708513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81985603788884917918278017 61489202841663688438708513)
        ·
          refine ⟨46116902131247766329031385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61489202841663688438708513 46116902131247766329031385)
          ·
            refine ⟨34587676598435824746773539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46116902131247766329031385 34587676598435824746773539)
            ·
              refine ⟨51881514897653737120160309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34587676598435824746773539 51881514897653737120160309)
              ·
                refine ⟨4863892021655037855015029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51881514897653737120160309 4863892021655037855015029)
                ·
                  refine ⟨455989877030159798907659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4863892021655037855015029 455989877030159798907659)
                  ·
                    rfl

theorem cell23_7992334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_7992334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992334 prefixEnd_7992334 := by exact prefixLift 7992334
  have htrace : WordTrace (prefixWord ++ tailWord_7992334) baseStart_7992334 baseEnd_7992334 := by
    simpa [prefixWord, tailWord_7992334, baseEnd_7992334] using wordTrace_append hprefix tailTrace_7992334
  have hstable : (prefixWord ++ tailWord_7992334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992334).length < 2 ^ (prefixWord ++ tailWord_7992334).sum := by decide
  have hdescent : baseEnd_7992334 < baseStart_7992334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992387 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 3]
def baseStart_7992387 : Nat := 118140960795 + 7992387 * 2 ^ 59
def prefixEnd_7992387 : Nat := 4983230072969 + 3 ^ 40 * 7992387 * 2
def baseEnd_7992387 : Nat := 4103936107746126482806187

theorem tailTrace_7992387 : CollatzResearch.WordTrace tailWord_7992387 prefixEnd_7992387 4103936107746126482806187 := by
  unfold tailWord_7992387
  simp only [CollatzResearch.WordTrace]
  refine ⟨291506302095954364872223415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194337534730636243248148943 291506302095954364872223415)
  ·
    refine ⟨437259453143931547308335123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291506302095954364872223415 437259453143931547308335123)
    ·
      refine ⟨655889179715897320962502685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437259453143931547308335123 655889179715897320962502685)
      ·
        refine ⟨245958442393461495360938507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655889179715897320962502685 245958442393461495360938507)
        ·
          refine ⟨368937663590192243041407761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245958442393461495360938507 368937663590192243041407761)
          ·
            refine ⟨276703247692644182281055821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368937663590192243041407761 276703247692644182281055821)
            ·
              refine ⟨103763717884741568355395933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276703247692644182281055821 103763717884741568355395933)
              ·
                refine ⟨38911394206778088133273475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103763717884741568355395933 38911394206778088133273475)
                ·
                  refine ⟨58367091310167132199910213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38911394206778088133273475 58367091310167132199910213)
                  ·
                    refine ⟨10943829620656337287483165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58367091310167132199910213 10943829620656337287483165)
                    ·
                      refine ⟨4103936107746126482806187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943829620656337287483165 4103936107746126482806187)
                      ·
                        rfl

theorem cell23_7992387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_7992387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992387 prefixEnd_7992387 := by exact prefixLift 7992387
  have htrace : WordTrace (prefixWord ++ tailWord_7992387) baseStart_7992387 baseEnd_7992387 := by
    simpa [prefixWord, tailWord_7992387, baseEnd_7992387] using wordTrace_append hprefix tailTrace_7992387
  have hstable : (prefixWord ++ tailWord_7992387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992387).length < 2 ^ (prefixWord ++ tailWord_7992387).sum := by decide
  have hdescent : baseEnd_7992387 < baseStart_7992387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992404 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_7992404 : Nat := 118140960795 + 7992404 * 2 ^ 59
def prefixEnd_7992404 : Nat := 4983230072969 + 3 ^ 40 * 7992404 * 2
def baseEnd_7992404 : Nat := 4103944836917252916293609

theorem tailTrace_7992404 : CollatzResearch.WordTrace tailWord_7992404 prefixEnd_7992404 4103944836917252916293609 := by
  unfold tailWord_7992404
  simp only [CollatzResearch.WordTrace]
  refine ⟨145753461068446388387796133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194337948091261851183728177 145753461068446388387796133)
  ·
    refine ⟨27328773950333697822711775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145753461068446388387796133 27328773950333697822711775)
    ·
      refine ⟨40993160925500546734067663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27328773950333697822711775 40993160925500546734067663)
      ·
        refine ⟨61489741388250820101101495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40993160925500546734067663 61489741388250820101101495)
        ·
          refine ⟨92234612082376230151652243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61489741388250820101101495 92234612082376230151652243)
          ·
            refine ⟨138351918123564345227478365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92234612082376230151652243 138351918123564345227478365)
            ·
              refine ⟨51881969296336629460304387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138351918123564345227478365 51881969296336629460304387)
              ·
                refine ⟨77822953944504944190456581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51881969296336629460304387 77822953944504944190456581)
                ·
                  refine ⟨14591803864594677035710609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77822953944504944190456581 14591803864594677035710609)
                  ·
                    refine ⟨10943852898446007776782957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14591803864594677035710609 10943852898446007776782957)
                    ·
                      refine ⟨4103944836917252916293609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10943852898446007776782957 4103944836917252916293609)
                      ·
                        rfl

theorem cell23_7992404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_7992404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992404 prefixEnd_7992404 := by exact prefixLift 7992404
  have htrace : WordTrace (prefixWord ++ tailWord_7992404) baseStart_7992404 baseEnd_7992404 := by
    simpa [prefixWord, tailWord_7992404, baseEnd_7992404] using wordTrace_append hprefix tailTrace_7992404
  have hstable : (prefixWord ++ tailWord_7992404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992404).length < 2 ^ (prefixWord ++ tailWord_7992404).sum := by decide
  have hdescent : baseEnd_7992404 < baseStart_7992404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992407 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 6]
def baseStart_7992407 : Nat := 118140960795 + 7992407 * 2 ^ 59
def prefixEnd_7992407 : Nat := 4983230072969 + 3 ^ 40 * 7992407 * 2
def baseEnd_7992407 : Nat := 455994041928801822728455

theorem tailTrace_7992407 : CollatzResearch.WordTrace tailWord_7992407 prefixEnd_7992407 455994041928801822728455 := by
  unfold tailWord_7992407
  simp only [CollatzResearch.WordTrace]
  refine ⟨291507031555881908287951475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194338021037254605525300983 291507031555881908287951475)
  ·
    refine ⟨437260547333822862431927213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291507031555881908287951475 437260547333822862431927213)
    ·
      refine ⟨163972705250183573411972705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437260547333822862431927213 163972705250183573411972705)
      ·
        refine ⟨122979528937637680058979529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163972705250183573411972705 122979528937637680058979529)
        ·
          refine ⟨92234646703228260044234647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122979528937637680058979529 92234646703228260044234647)
          ·
            refine ⟨138351970054842390066351971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92234646703228260044234647 138351970054842390066351971)
            ·
              refine ⟨207527955082263585099527957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138351970054842390066351971 207527955082263585099527957)
              ·
                refine ⟨9727872894481105551540373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207527955082263585099527957 9727872894481105551540373)
                ·
                  refine ⟨455994041928801822728455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9727872894481105551540373 455994041928801822728455)
                  ·
                    rfl

theorem cell23_7992407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 6].length) (baseStart_7992407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992407 prefixEnd_7992407 := by exact prefixLift 7992407
  have htrace : WordTrace (prefixWord ++ tailWord_7992407) baseStart_7992407 baseEnd_7992407 := by
    simpa [prefixWord, tailWord_7992407, baseEnd_7992407] using wordTrace_append hprefix tailTrace_7992407
  have hstable : (prefixWord ++ tailWord_7992407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992407).length < 2 ^ (prefixWord ++ tailWord_7992407).sum := by decide
  have hdescent : baseEnd_7992407 < baseStart_7992407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992484 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_7992484 : Nat := 118140960795 + 7992484 * 2 ^ 59
def prefixEnd_7992484 : Nat := 4983230072969 + 3 ^ 40 * 7992484 * 2
def baseEnd_7992484 : Nat := 1367995305123204201097747

theorem tailTrace_7992484 : CollatzResearch.WordTrace tailWord_7992484 prefixEnd_7992484 1367995305123204201097747 := by
  unfold tailWord_7992484
  simp only [CollatzResearch.WordTrace]
  refine ⟨145754919988301475219252253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194339893317735300292336337 145754919988301475219252253)
  ·
    refine ⟨54658094995613053207219595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145754919988301475219252253 54658094995613053207219595)
    ·
      refine ⟨81987142493419579810829393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54658094995613053207219595 81987142493419579810829393)
      ·
        refine ⟨61490356870064684858122045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81987142493419579810829393 61490356870064684858122045)
        ·
          refine ⟨23058883826274256821795767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61490356870064684858122045 23058883826274256821795767)
          ·
            refine ⟨34588325739411385232693651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23058883826274256821795767 34588325739411385232693651)
            ·
              refine ⟨51882488609117077849040477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34588325739411385232693651 51882488609117077849040477)
              ·
                refine ⟨19455933228418904193390179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51882488609117077849040477 19455933228418904193390179)
                ·
                  refine ⟨29183899842628356290085269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19455933228418904193390179 29183899842628356290085269)
                  ·
                    refine ⟨1367995305123204201097747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29183899842628356290085269 1367995305123204201097747)
                    ·
                      rfl

theorem cell23_7992484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_7992484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992484 prefixEnd_7992484 := by exact prefixLift 7992484
  have htrace : WordTrace (prefixWord ++ tailWord_7992484) baseStart_7992484 baseEnd_7992484 := by
    simpa [prefixWord, tailWord_7992484, baseEnd_7992484] using wordTrace_append hprefix tailTrace_7992484
  have hstable : (prefixWord ++ tailWord_7992484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992484).length < 2 ^ (prefixWord ++ tailWord_7992484).sum := by decide
  have hdescent : baseEnd_7992484 < baseStart_7992484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992508 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7992508 : Nat := 118140960795 + 7992508 * 2 ^ 59
def prefixEnd_7992508 : Nat := 4983230072969 + 3 ^ 40 * 7992508 * 2
def baseEnd_7992508 : Nat := 4103998238905320509393131

theorem tailTrace_7992508 : CollatzResearch.WordTrace tailWord_7992508 prefixEnd_7992508 4103998238905320509393131 := by
  unfold tailWord_7992508
  simp only [CollatzResearch.WordTrace]
  refine ⟨145755357664258001268689089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194340476885677335024918785 145755357664258001268689089)
  ·
    refine ⟨109316518248193500951516817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145755357664258001268689089 109316518248193500951516817)
    ·
      refine ⟨81987388686145125713637613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109316518248193500951516817 81987388686145125713637613)
      ·
        refine ⟨30745270757304422142614105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81987388686145125713637613 30745270757304422142614105)
        ·
          refine ⟨23058953067978316606960579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30745270757304422142614105 23058953067978316606960579)
          ·
            refine ⟨34588429601967474910440869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23058953067978316606960579 34588429601967474910440869)
            ·
              refine ⟨6485330550368901545707663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34588429601967474910440869 6485330550368901545707663)
              ·
                refine ⟨9727995825553352318561495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485330550368901545707663 9727995825553352318561495)
                ·
                  refine ⟨14591993738330028477842243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9727995825553352318561495 14591993738330028477842243)
                  ·
                    refine ⟨21887990607495042716763365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14591993738330028477842243 21887990607495042716763365)
                    ·
                      refine ⟨4103998238905320509393131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21887990607495042716763365 4103998238905320509393131)
                      ·
                        rfl

theorem cell23_7992508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7992508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992508 prefixEnd_7992508 := by exact prefixLift 7992508
  have htrace : WordTrace (prefixWord ++ tailWord_7992508) baseStart_7992508 baseEnd_7992508 := by
    simpa [prefixWord, tailWord_7992508, baseEnd_7992508] using wordTrace_append hprefix tailTrace_7992508
  have hstable : (prefixWord ++ tailWord_7992508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992508).length < 2 ^ (prefixWord ++ tailWord_7992508).sum := by decide
  have hdescent : baseEnd_7992508 < baseStart_7992508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992517 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_7992517 : Nat := 118140960795 + 7992517 * 2 ^ 59
def prefixEnd_7992517 : Nat := 4983230072969 + 3 ^ 40 * 7992517 * 2
def baseEnd_7992517 : Nat := 4104002860231210974180589

theorem tailTrace_7992517 : CollatzResearch.WordTrace tailWord_7992517 prefixEnd_7992517 4104002860231210974180589 := by
  unfold tailWord_7992517
  simp only [CollatzResearch.WordTrace]
  refine ⟨291511043585483397074455805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194340695723655598049637203 291511043585483397074455805)
  ·
    refine ⟨109316641344556273902920927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291511043585483397074455805 109316641344556273902920927)
    ·
      refine ⟨163974962016834410854381391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109316641344556273902920927 163974962016834410854381391)
      ·
        refine ⟨245962443025251616281572087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163974962016834410854381391 245962443025251616281572087)
        ·
          refine ⟨368943664537877424422358131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245962443025251616281572087 368943664537877424422358131)
          ·
            refine ⟨553415496806816136633537197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368943664537877424422358131 553415496806816136633537197)
            ·
              refine ⟨207530811302556051237576449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553415496806816136633537197 207530811302556051237576449)
              ·
                refine ⟨155648108476917038428182337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207530811302556051237576449 155648108476917038428182337)
                ·
                  refine ⟨116736081357687778821136753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155648108476917038428182337 116736081357687778821136753)
                  ·
                    refine ⟨87552061018265834115852565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116736081357687778821136753 87552061018265834115852565)
                    ·
                      refine ⟨4104002860231210974180589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87552061018265834115852565 4104002860231210974180589)
                      ·
                        rfl

theorem cell23_7992517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_7992517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992517 prefixEnd_7992517 := by exact prefixLift 7992517
  have htrace : WordTrace (prefixWord ++ tailWord_7992517) baseStart_7992517 baseEnd_7992517 := by
    simpa [prefixWord, tailWord_7992517, baseEnd_7992517] using wordTrace_append hprefix tailTrace_7992517
  have hstable : (prefixWord ++ tailWord_7992517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992517).length < 2 ^ (prefixWord ++ tailWord_7992517).sum := by decide
  have hdescent : baseEnd_7992517 < baseStart_7992517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992527 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 2, 7]
def baseStart_7992527 : Nat := 118140960795 + 7992527 * 2 ^ 59
def prefixEnd_7992527 : Nat := 4983230072969 + 3 ^ 40 * 7992527 * 2
def baseEnd_7992527 : Nat := 1368002665012585311685181

theorem tailTrace_7992527 : CollatzResearch.WordTrace tailWord_7992527 prefixEnd_7992527 1368002665012585311685181 := by
  unfold tailWord_7992527
  simp only [CollatzResearch.WordTrace]
  refine ⟨291511408315447168782319835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194340938876964779188213223 291511408315447168782319835)
  ·
    refine ⟨437267112473170753173479753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291511408315447168782319835 437267112473170753173479753)
    ·
      refine ⟨327950334354878064880109815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437267112473170753173479753 327950334354878064880109815)
      ·
        refine ⟨491925501532317097320164723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327950334354878064880109815 491925501532317097320164723)
        ·
          refine ⟨737888252298475645980247085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491925501532317097320164723 737888252298475645980247085)
          ·
            refine ⟨276708094611928367242592657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 737888252298475645980247085 276708094611928367242592657)
            ·
              refine ⟨207531070958946275431944493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276708094611928367242592657 207531070958946275431944493)
              ·
                refine ⟨77824151609604853286979185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207531070958946275431944493 77824151609604853286979185)
                ·
                  refine ⟨58368113707203639965234389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77824151609604853286979185 58368113707203639965234389)
                  ·
                    refine ⟨1368002665012585311685181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58368113707203639965234389 1368002665012585311685181)
                    ·
                      rfl

theorem cell23_7992527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_7992527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992527 prefixEnd_7992527 := by exact prefixLift 7992527
  have htrace : WordTrace (prefixWord ++ tailWord_7992527) baseStart_7992527 baseEnd_7992527 := by
    simpa [prefixWord, tailWord_7992527, baseEnd_7992527] using wordTrace_append hprefix tailTrace_7992527
  have hstable : (prefixWord ++ tailWord_7992527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992527).length < 2 ^ (prefixWord ++ tailWord_7992527).sum := by decide
  have hdescent : baseEnd_7992527 < baseStart_7992527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992554 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_7992554 : Nat := 118140960795 + 7992554 * 2 ^ 59
def prefixEnd_7992554 : Nat := 4983230072969 + 3 ^ 40 * 7992554 * 2
def baseEnd_7992554 : Nat := 4104021859015427329417919

theorem tailTrace_7992554 : CollatzResearch.WordTrace tailWord_7992554 prefixEnd_7992554 4104021859015427329417919 := by
  unfold tailWord_7992554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72878098271587338098388179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194341595390899568262368477 72878098271587338098388179)
  ·
    refine ⟨109317147407381007147582269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72878098271587338098388179 109317147407381007147582269)
    ·
      refine ⟨40993930277767877680343351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109317147407381007147582269 40993930277767877680343351)
      ·
        refine ⟨61490895416651816520515027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40993930277767877680343351 61490895416651816520515027)
        ·
          refine ⟨92236343124977724780772541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61490895416651816520515027 92236343124977724780772541)
          ·
            refine ⟨34588628671866646792789703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92236343124977724780772541 34588628671866646792789703)
            ·
              refine ⟨51882943007799970189184555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34588628671866646792789703 51882943007799970189184555)
              ·
                refine ⟨77824414511699955283776833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51882943007799970189184555 77824414511699955283776833)
                ·
                  refine ⟨58368310883774966462832625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77824414511699955283776833 58368310883774966462832625)
                  ·
                    refine ⟨43776233162831224847124469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58368310883774966462832625 43776233162831224847124469)
                    ·
                      refine ⟨4104021859015427329417919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43776233162831224847124469 4104021859015427329417919)
                      ·
                        rfl

theorem cell23_7992554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_7992554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992554 prefixEnd_7992554 := by exact prefixLift 7992554
  have htrace : WordTrace (prefixWord ++ tailWord_7992554) baseStart_7992554 baseEnd_7992554 := by
    simpa [prefixWord, tailWord_7992554, baseEnd_7992554] using wordTrace_append hprefix tailTrace_7992554
  have hstable : (prefixWord ++ tailWord_7992554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992554).length < 2 ^ (prefixWord ++ tailWord_7992554).sum := by decide
  have hdescent : baseEnd_7992554 < baseStart_7992554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992559 : List Nat := [1, 1, 2, 1, 8, 1, 1, 3, 1, 2, 2]
def baseStart_7992559 : Nat := 118140960795 + 7992559 * 2 ^ 59
def prefixEnd_7992559 : Nat := 4983230072969 + 3 ^ 40 * 7992559 * 2
def baseEnd_7992559 : Nat := 4104024426418699809855397

theorem tailTrace_7992559 : CollatzResearch.WordTrace tailWord_7992559 prefixEnd_7992559 4104024426418699809855397 := by
  unfold tailWord_7992559
  simp only [CollatzResearch.WordTrace]
  refine ⟨291512575451331238247484731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194341716967554158831656487 291512575451331238247484731)
  ·
    refine ⟨437268863176996857371227097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291512575451331238247484731 437268863176996857371227097)
    ·
      refine ⟨327951647382747643028420323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437268863176996857371227097 327951647382747643028420323)
      ·
        refine ⟨491927471074121464542630485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327951647382747643028420323 491927471074121464542630485)
        ·
          refine ⟨5764775051649860912608951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 491927471074121464542630485 5764775051649860912608951)
          ·
            refine ⟨8647162577474791368913427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764775051649860912608951 8647162577474791368913427)
            ·
              refine ⟨12970743866212187053370141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8647162577474791368913427 12970743866212187053370141)
              ·
                refine ⟨4864028949829570145013803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12970743866212187053370141 4864028949829570145013803)
                ·
                  refine ⟨7296043424744355217520705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864028949829570145013803 7296043424744355217520705)
                  ·
                    refine ⟨5472032568558266413140529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296043424744355217520705 5472032568558266413140529)
                    ·
                      refine ⟨4104024426418699809855397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472032568558266413140529 4104024426418699809855397)
                      ·
                        rfl

theorem cell23_7992559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 2, 2].length) (baseStart_7992559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992559 prefixEnd_7992559 := by exact prefixLift 7992559
  have htrace : WordTrace (prefixWord ++ tailWord_7992559) baseStart_7992559 baseEnd_7992559 := by
    simpa [prefixWord, tailWord_7992559, baseEnd_7992559] using wordTrace_append hprefix tailTrace_7992559
  have hstable : (prefixWord ++ tailWord_7992559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992559).length < 2 ^ (prefixWord ++ tailWord_7992559).sum := by decide
  have hdescent : baseEnd_7992559 < baseStart_7992559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992604 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 7]
def baseStart_7992604 : Nat := 118140960795 + 7992604 * 2 ^ 59
def prefixEnd_7992604 : Nat := 4983230072969 + 3 ^ 40 * 7992604 * 2
def baseEnd_7992604 : Nat := 456005281449794681532521

theorem tailTrace_7992604 : CollatzResearch.WordTrace tailWord_7992604 prefixEnd_7992604 456005281449794681532521 := by
  unfold tailWord_7992604
  simp only [CollatzResearch.WordTrace]
  refine ⟨145757108368084105466436433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194342811157445473955248577 145757108368084105466436433)
  ·
    refine ⟨109317831276063079099827325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145757108368084105466436433 109317831276063079099827325)
    ·
      refine ⟨40994186728523654662435247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109317831276063079099827325 40994186728523654662435247)
      ·
        refine ⟨61491280092785481993652871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40994186728523654662435247 61491280092785481993652871)
        ·
          refine ⟨92236920139178222990479307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61491280092785481993652871 92236920139178222990479307)
          ·
            refine ⟨138355380208767334485718961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92236920139178222990479307 138355380208767334485718961)
            ·
              refine ⟨103766535156575500864289221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138355380208767334485718961 103766535156575500864289221)
              ·
                refine ⟨19456225341857906412054229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103766535156575500864289221 19456225341857906412054229)
                ·
                  refine ⟨456005281449794681532521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19456225341857906412054229 456005281449794681532521)
                  ·
                    rfl

theorem cell23_7992604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_7992604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992604 prefixEnd_7992604 := by exact prefixLift 7992604
  have htrace : WordTrace (prefixWord ++ tailWord_7992604) baseStart_7992604 baseEnd_7992604 := by
    simpa [prefixWord, tailWord_7992604, baseEnd_7992604] using wordTrace_append hprefix tailTrace_7992604
  have hstable : (prefixWord ++ tailWord_7992604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992604).length < 2 ^ (prefixWord ++ tailWord_7992604).sum := by decide
  have hdescent : baseEnd_7992604 < baseStart_7992604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992638 : List Nat := [4, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_7992638 : Nat := 118140960795 + 7992638 * 2 ^ 59
def prefixEnd_7992638 : Nat := 4983230072969 + 3 ^ 40 * 7992638 * 2
def baseEnd_7992638 : Nat := 456007221265600555640837

theorem tailTrace_7992638 : CollatzResearch.WordTrace tailWord_7992638 prefixEnd_7992638 456007221265600555640837 := by
  unfold tailWord_7992638
  simp only [CollatzResearch.WordTrace]
  refine ⟨36439432102255629342451321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194343637878696689826407045 36439432102255629342451321)
  ·
    refine ⟨27329574076691722006838491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36439432102255629342451321 27329574076691722006838491)
    ·
      refine ⟨40994361115037583010257737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27329574076691722006838491 40994361115037583010257737)
      ·
        refine ⟨30745770836278187257693303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40994361115037583010257737 30745770836278187257693303)
        ·
          refine ⟨46118656254417280886539955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30745770836278187257693303 46118656254417280886539955)
          ·
            refine ⟨69177984381625921329809933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46118656254417280886539955 69177984381625921329809933)
            ·
              refine ⟨25941744143109720498678725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69177984381625921329809933 25941744143109720498678725)
              ·
                refine ⟨4864077026833072593502261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25941744143109720498678725 4864077026833072593502261)
                ·
                  refine ⟨456007221265600555640837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4864077026833072593502261 456007221265600555640837)
                  ·
                    rfl

theorem cell23_7992638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_7992638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992638 prefixEnd_7992638 := by exact prefixLift 7992638
  have htrace : WordTrace (prefixWord ++ tailWord_7992638) baseStart_7992638 baseEnd_7992638 := by
    simpa [prefixWord, tailWord_7992638, baseEnd_7992638] using wordTrace_append hprefix tailTrace_7992638
  have hstable : (prefixWord ++ tailWord_7992638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992638).length < 2 ^ (prefixWord ++ tailWord_7992638).sum := by decide
  have hdescent : baseEnd_7992638 < baseStart_7992638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992671 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 3, 6, 2]
def baseStart_7992671 : Nat := 118140960795 + 7992671 * 2 ^ 59
def prefixEnd_7992671 : Nat := 4983230072969 + 3 ^ 40 * 7992671 * 2
def baseEnd_7992671 : Nat := 4104081936252003371654881

theorem tailTrace_7992671 : CollatzResearch.WordTrace tailWord_7992671 prefixEnd_7992671 4104081936252003371654881 := by
  unfold tailWord_7992671
  simp only [CollatzResearch.WordTrace]
  refine ⟨291516660426925481375561867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194344440284616987583707911 291516660426925481375561867)
  ·
    refine ⟨437274990640388222063342801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291516660426925481375561867 437274990640388222063342801)
    ·
      refine ⟨327956242980291166547507101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437274990640388222063342801 327956242980291166547507101)
      ·
        refine ⟨122983591117609187455315163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327956242980291166547507101 122983591117609187455315163)
        ·
          refine ⟨184475386676413781182972745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122983591117609187455315163 184475386676413781182972745)
          ·
            refine ⟨138356540007310335887229559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184475386676413781182972745 138356540007310335887229559)
            ·
              refine ⟨207534810010965503830844339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138356540007310335887229559 207534810010965503830844339)
              ·
                refine ⟨311302215016448255746266509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207534810010965503830844339 311302215016448255746266509)
                ·
                  refine ⟨116738330631168095904849941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311302215016448255746266509 116738330631168095904849941)
                  ·
                    refine ⟨5472109248336004495539841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116738330631168095904849941 5472109248336004495539841)
                    ·
                      refine ⟨4104081936252003371654881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472109248336004495539841 4104081936252003371654881)
                      ·
                        rfl

theorem cell23_7992671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_7992671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992671 prefixEnd_7992671 := by exact prefixLift 7992671
  have htrace : WordTrace (prefixWord ++ tailWord_7992671) baseStart_7992671 baseEnd_7992671 := by
    simpa [prefixWord, tailWord_7992671, baseEnd_7992671] using wordTrace_append hprefix tailTrace_7992671
  have hstable : (prefixWord ++ tailWord_7992671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992671).length < 2 ^ (prefixWord ++ tailWord_7992671).sum := by decide
  have hdescent : baseEnd_7992671 < baseStart_7992671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992748 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 4, 3, 2]
def baseStart_7992748 : Nat := 118140960795 + 7992748 * 2 ^ 59
def prefixEnd_7992748 : Nat := 4983230072969 + 3 ^ 40 * 7992748 * 2
def baseEnd_7992748 : Nat := 4104121474262399570392027

theorem tailTrace_7992748 : CollatzResearch.WordTrace tailWord_7992748 prefixEnd_7992748 4104121474262399570392027 := by
  unfold tailWord_7992748
  simp only [CollatzResearch.WordTrace]
  refine ⟨145759734423823261763057449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194346312565097682350743265 145759734423823261763057449)
  ·
    refine ⟨109319800817867446322293087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145759734423823261763057449 109319800817867446322293087)
    ·
      refine ⟨163979701226801169483439631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109319800817867446322293087 163979701226801169483439631)
      ·
        refine ⟨245969551840201754225159447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163979701226801169483439631 245969551840201754225159447)
        ·
          refine ⟨368954327760302631337739171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245969551840201754225159447 368954327760302631337739171)
          ·
            refine ⟨553431491640453947006608757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368954327760302631337739171 553431491640453947006608757)
            ·
              refine ⟨51884202341292557531869571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 553431491640453947006608757 51884202341292557531869571)
              ·
                refine ⟨77826303511938836297804357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51884202341292557531869571 77826303511938836297804357)
                ·
                  refine ⟨14592431908488531805838317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77826303511938836297804357 14592431908488531805838317)
                  ·
                    refine ⟨5472161965683199427189369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14592431908488531805838317 5472161965683199427189369)
                    ·
                      refine ⟨4104121474262399570392027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472161965683199427189369 4104121474262399570392027)
                      ·
                        rfl

theorem cell23_7992748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_7992748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992748 prefixEnd_7992748 := by exact prefixLift 7992748
  have htrace : WordTrace (prefixWord ++ tailWord_7992748) baseStart_7992748 baseEnd_7992748 := by
    simpa [prefixWord, tailWord_7992748, baseEnd_7992748] using wordTrace_append hprefix tailTrace_7992748
  have hstable : (prefixWord ++ tailWord_7992748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992748).length < 2 ^ (prefixWord ++ tailWord_7992748).sum := by decide
  have hdescent : baseEnd_7992748 < baseStart_7992748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992749 : List Nat := [1, 5, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_7992749 : Nat := 118140960795 + 7992749 * 2 ^ 59
def prefixEnd_7992749 : Nat := 4983230072969 + 3 ^ 40 * 7992749 * 2
def baseEnd_7992749 : Nat := 1368040662581018022159841

theorem tailTrace_7992749 : CollatzResearch.WordTrace tailWord_7992749 prefixEnd_7992749 1368040662581018022159841 := by
  unfold tailWord_7992749
  simp only [CollatzResearch.WordTrace]
  refine ⟨291519505320642900696901301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194346336880428600464600867 291519505320642900696901301)
  ·
    refine ⟨27329953623810271940334497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291519505320642900696901301 27329953623810271940334497)
    ·
      refine ⟨20497465217857703955250873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27329953623810271940334497 20497465217857703955250873)
      ·
        refine ⟨15373098913393277966438155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20497465217857703955250873 15373098913393277966438155)
        ·
          refine ⟨23059648370089916949657233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15373098913393277966438155 23059648370089916949657233)
          ·
            refine ⟨17294736277567437712242925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23059648370089916949657233 17294736277567437712242925)
            ·
              refine ⟨6485526104087789142091097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17294736277567437712242925 6485526104087789142091097)
              ·
                refine ⟨4864144578065841856568323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485526104087789142091097 4864144578065841856568323)
                ·
                  refine ⟨7296216867098762784852485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864144578065841856568323 7296216867098762784852485)
                  ·
                    refine ⟨1368040662581018022159841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296216867098762784852485 1368040662581018022159841)
                    ·
                      rfl

theorem cell23_7992749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_7992749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992749 prefixEnd_7992749 := by exact prefixLift 7992749
  have htrace : WordTrace (prefixWord ++ tailWord_7992749) baseStart_7992749 baseEnd_7992749 := by
    simpa [prefixWord, tailWord_7992749, baseEnd_7992749] using wordTrace_append hprefix tailTrace_7992749
  have hstable : (prefixWord ++ tailWord_7992749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992749).length < 2 ^ (prefixWord ++ tailWord_7992749).sum := by decide
  have hdescent : baseEnd_7992749 < baseStart_7992749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992755 : List Nat := [1, 1, 1, 2, 3, 1, 1, 8, 1, 1, 3]
def baseStart_7992755 : Nat := 118140960795 + 7992755 * 2 ^ 59
def prefixEnd_7992755 : Nat := 4983230072969 + 3 ^ 40 * 7992755 * 2
def baseEnd_7992755 : Nat := 4104125068626981043004495

theorem tailTrace_7992755 : CollatzResearch.WordTrace tailWord_7992755 prefixEnd_7992755 4104125068626981043004495 := by
  unfold tailWord_7992755
  simp only [CollatzResearch.WordTrace]
  refine ⟨291519724158621163721619719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194346482772414109147746479 291519724158621163721619719)
  ·
    refine ⟨437279586237931745582429579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291519724158621163721619719 437279586237931745582429579)
    ·
      refine ⟨655919379356897618373644369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437279586237931745582429579 655919379356897618373644369)
      ·
        refine ⟨491939534517673213780233277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655919379356897618373644369 491939534517673213780233277)
        ·
          refine ⟨184477325444127455167587479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491939534517673213780233277 184477325444127455167587479)
          ·
            refine ⟨276715988166191182751381219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184477325444127455167587479 276715988166191182751381219)
            ·
              refine ⟨415073982249286774127071829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276715988166191182751381219 415073982249286774127071829)
              ·
                refine ⟨4864148229483829384301623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 415073982249286774127071829 4864148229483829384301623)
                ·
                  refine ⟨7296222344225744076452435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864148229483829384301623 7296222344225744076452435)
                  ·
                    refine ⟨10944333516338616114678653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7296222344225744076452435 10944333516338616114678653)
                    ·
                      refine ⟨4104125068626981043004495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10944333516338616114678653 4104125068626981043004495)
                      ·
                        rfl

theorem cell23_7992755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 1, 3].length) (baseStart_7992755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992755 prefixEnd_7992755 := by exact prefixLift 7992755
  have htrace : WordTrace (prefixWord ++ tailWord_7992755) baseStart_7992755 baseEnd_7992755 := by
    simpa [prefixWord, tailWord_7992755, baseEnd_7992755] using wordTrace_append hprefix tailTrace_7992755
  have hstable : (prefixWord ++ tailWord_7992755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992755).length < 2 ^ (prefixWord ++ tailWord_7992755).sum := by decide
  have hdescent : baseEnd_7992755 < baseStart_7992755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992778 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_7992778 : Nat := 118140960795 + 7992778 * 2 ^ 59
def prefixEnd_7992778 : Nat := 4983230072969 + 3 ^ 40 * 7992778 * 2
def baseEnd_7992778 : Nat := 4104136878682034453016889

theorem tailTrace_7992778 : CollatzResearch.WordTrace tailWord_7992778 prefixEnd_7992778 4104136878682034453016889 := by
  unfold tailWord_7992778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72880140759384459662426747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194347042025025225766471325 72880140759384459662426747)
  ·
    refine ⟨109320211139076689493640121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72880140759384459662426747 109320211139076689493640121)
    ·
      refine ⟨81990158354307517120230091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109320211139076689493640121 81990158354307517120230091)
      ·
        refine ⟨122985237531461275680345137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81990158354307517120230091 122985237531461275680345137)
        ·
          refine ⟨92238928148595956760258853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122985237531461275680345137 92238928148595956760258853)
          ·
            refine ⟨17294799027861741892548535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92238928148595956760258853 17294799027861741892548535)
            ·
              refine ⟨25942198541792612838822803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17294799027861741892548535 25942198541792612838822803)
              ·
                refine ⟨38913297812688919258234205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25942198541792612838822803 38913297812688919258234205)
                ·
                  refine ⟨14592486679758344721837827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38913297812688919258234205 14592486679758344721837827)
                  ·
                    refine ⟨21888730019637517082756741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14592486679758344721837827 21888730019637517082756741)
                    ·
                      refine ⟨4104136878682034453016889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21888730019637517082756741 4104136878682034453016889)
                      ·
                        rfl

theorem cell23_7992778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_7992778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992778 prefixEnd_7992778 := by exact prefixLift 7992778
  have htrace : WordTrace (prefixWord ++ tailWord_7992778) baseStart_7992778 baseEnd_7992778 := by
    simpa [prefixWord, tailWord_7992778, baseEnd_7992778] using wordTrace_append hprefix tailTrace_7992778
  have hstable : (prefixWord ++ tailWord_7992778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992778).length < 2 ^ (prefixWord ++ tailWord_7992778).sum := by decide
  have hdescent : baseEnd_7992778 < baseStart_7992778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992805 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_7992805 : Nat := 118140960795 + 7992805 * 2 ^ 59
def prefixEnd_7992805 : Nat := 4983230072969 + 3 ^ 40 * 7992805 * 2
def baseEnd_7992805 : Nat := 1368050247553235282459755

theorem tailTrace_7992805 : CollatzResearch.WordTrace tailWord_7992805 prefixEnd_7992805 1368050247553235282459755 := by
  unfold tailWord_7992805
  simp only [CollatzResearch.WordTrace]
  refine ⟨291521547808440022260939869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194347698538960014840626579 291521547808440022260939869)
  ·
    refine ⟨109320580428165008347852451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291521547808440022260939869 109320580428165008347852451)
    ·
      refine ⟨163980870642247512521778677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109320580428165008347852451 163980870642247512521778677)
      ·
        refine ⟨15373206622710704298916751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163980870642247512521778677 15373206622710704298916751)
        ·
          refine ⟨23059809934066056448375127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15373206622710704298916751 23059809934066056448375127)
          ·
            refine ⟨34589714901099084672562691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23059809934066056448375127 34589714901099084672562691)
            ·
              refine ⟨51884572351648627008844037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34589714901099084672562691 51884572351648627008844037)
              ·
                refine ⟨9728357315934117564158257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51884572351648627008844037 9728357315934117564158257)
                ·
                  refine ⟨7296267986950588173118693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9728357315934117564158257 7296267986950588173118693)
                  ·
                    refine ⟨1368050247553235282459755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296267986950588173118693 1368050247553235282459755)
                    ·
                      rfl

theorem cell23_7992805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_7992805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992805 prefixEnd_7992805 := by exact prefixLift 7992805
  have htrace : WordTrace (prefixWord ++ tailWord_7992805) baseStart_7992805 baseEnd_7992805 := by
    simpa [prefixWord, tailWord_7992805, baseEnd_7992805] using wordTrace_append hprefix tailTrace_7992805
  have hstable : (prefixWord ++ tailWord_7992805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992805).length < 2 ^ (prefixWord ++ tailWord_7992805).sum := by decide
  have hdescent : baseEnd_7992805 < baseStart_7992805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992818 : List Nat := [3, 2, 1, 4, 1, 1, 3, 8]
def baseStart_7992818 : Nat := 118140960795 + 7992818 * 2 ^ 59
def prefixEnd_7992818 : Nat := 4983230072969 + 3 ^ 40 * 7992818 * 2
def baseEnd_7992818 : Nat := 152005830292896825796915

theorem tailTrace_7992818 : CollatzResearch.WordTrace tailWord_7992818 prefixEnd_7992818 152005830292896825796915 := by
  unfold tailWord_7992818
  simp only [CollatzResearch.WordTrace]
  refine ⟨72880505489348231370290777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194348014638261950320775405 72880505489348231370290777)
  ·
    refine ⟨54660379117011173527718083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72880505489348231370290777 54660379117011173527718083)
    ·
      refine ⟨81990568675516760291577125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54660379117011173527718083 81990568675516760291577125)
      ·
        refine ⟨15373231626659392554670711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81990568675516760291577125 15373231626659392554670711)
        ·
          refine ⟨23059847439989088832006067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15373231626659392554670711 23059847439989088832006067)
          ·
            refine ⟨34589771159983633248009101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23059847439989088832006067 34589771159983633248009101)
            ·
              refine ⟨12971164184993862468003413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34589771159983633248009101 12971164184993862468003413)
              ·
                refine ⟨152005830292896825796915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12971164184993862468003413 152005830292896825796915)
                ·
                  rfl

theorem cell23_7992818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 8].length) (baseStart_7992818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992818 prefixEnd_7992818 := by exact prefixLift 7992818
  have htrace : WordTrace (prefixWord ++ tailWord_7992818) baseStart_7992818 baseEnd_7992818 := by
    simpa [prefixWord, tailWord_7992818, baseEnd_7992818] using wordTrace_append hprefix tailTrace_7992818
  have hstable : (prefixWord ++ tailWord_7992818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992818).length < 2 ^ (prefixWord ++ tailWord_7992818).sum := by decide
  have hdescent : baseEnd_7992818 < baseStart_7992818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992828 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_7992828 : Nat := 118140960795 + 7992828 * 2 ^ 59
def prefixEnd_7992828 : Nat := 4983230072969 + 3 ^ 40 * 7992828 * 2
def baseEnd_7992828 : Nat := 4104162552714759257391659

theorem tailTrace_7992828 : CollatzResearch.WordTrace tailWord_7992828 prefixEnd_7992828 4104162552714759257391659 := by
  unfold tailWord_7992828
  simp only [CollatzResearch.WordTrace]
  refine ⟨145761193343678348594513569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194348257791571131459351425 145761193343678348594513569)
  ·
    refine ⟨109320895007758761445885177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145761193343678348594513569 109320895007758761445885177)
    ·
      refine ⟨81990671255819071084413883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109320895007758761445885177 81990671255819071084413883)
      ·
        refine ⟨122986006883728606626620825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81990671255819071084413883 122986006883728606626620825)
        ·
          refine ⟨92239505162796454969965619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122986006883728606626620825 92239505162796454969965619)
          ·
            refine ⟨138359257744194682454948429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92239505162796454969965619 138359257744194682454948429)
            ·
              refine ⟨51884721654073005920605661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138359257744194682454948429 51884721654073005920605661)
              ·
                refine ⟨19456770620277377220227123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51884721654073005920605661 19456770620277377220227123)
                ·
                  refine ⟨29185155930416065830340685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19456770620277377220227123 29185155930416065830340685)
                  ·
                    refine ⟨10944433473906024686377757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29185155930416065830340685 10944433473906024686377757)
                    ·
                      refine ⟨4104162552714759257391659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10944433473906024686377757 4104162552714759257391659)
                      ·
                        rfl

theorem cell23_7992828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_7992828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992828 prefixEnd_7992828 := by exact prefixLift 7992828
  have htrace : WordTrace (prefixWord ++ tailWord_7992828) baseStart_7992828 baseEnd_7992828 := by
    simpa [prefixWord, tailWord_7992828, baseEnd_7992828] using wordTrace_append hprefix tailTrace_7992828
  have hstable : (prefixWord ++ tailWord_7992828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992828).length < 2 ^ (prefixWord ++ tailWord_7992828).sum := by decide
  have hdescent : baseEnd_7992828 < baseStart_7992828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992841 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_7992841 : Nat := 118140960795 + 7992841 * 2 ^ 59
def prefixEnd_7992841 : Nat := 4983230072969 + 3 ^ 40 * 7992841 * 2
def baseEnd_7992841 : Nat := 4104169227963267706529099

theorem tailTrace_7992841 : CollatzResearch.WordTrace tailWord_7992841 prefixEnd_7992841 4104169227963267706529099 := by
  unfold tailWord_7992841
  simp only [CollatzResearch.WordTrace]
  refine ⟨291522860836309600409250377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194348573890873066939500251 291522860836309600409250377)
  ·
    refine ⟨218642145627232200306937783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291522860836309600409250377 218642145627232200306937783)
    ·
      refine ⟨327963218440848300460406675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218642145627232200306937783 327963218440848300460406675)
      ·
        refine ⟨491944827661272450690610013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327963218440848300460406675 491944827661272450690610013)
        ·
          refine ⟨184479310372977169008978755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491944827661272450690610013 184479310372977169008978755)
          ·
            refine ⟨276718965559465753513468133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184479310372977169008978755 276718965559465753513468133)
            ·
              refine ⟨51884806042399828783775275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276718965559465753513468133 51884806042399828783775275)
              ·
                refine ⟨77827209063599743175662913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51884806042399828783775275 77827209063599743175662913)
                ·
                  refine ⟨58370406797699807381747185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77827209063599743175662913 58370406797699807381747185)
                  ·
                    refine ⟨43777805098274855536310389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58370406797699807381747185 43777805098274855536310389)
                    ·
                      refine ⟨4104169227963267706529099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43777805098274855536310389 4104169227963267706529099)
                      ·
                        rfl

theorem cell23_7992841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_7992841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992841 prefixEnd_7992841 := by exact prefixLift 7992841
  have htrace : WordTrace (prefixWord ++ tailWord_7992841) baseStart_7992841 baseEnd_7992841 := by
    simpa [prefixWord, tailWord_7992841, baseEnd_7992841] using wordTrace_append hprefix tailTrace_7992841
  have hstable : (prefixWord ++ tailWord_7992841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992841).length < 2 ^ (prefixWord ++ tailWord_7992841).sum := by decide
  have hdescent : baseEnd_7992841 < baseStart_7992841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992846 : List Nat := [4, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_7992846 : Nat := 118140960795 + 7992846 * 2 ^ 59
def prefixEnd_7992846 : Nat := 4983230072969 + 3 ^ 40 * 7992846 * 2
def baseEnd_7992846 : Nat := 4104171795366540186966577

theorem tailTrace_7992846 : CollatzResearch.WordTrace tailWord_7992846 prefixEnd_7992846 4104171795366540186966577 := by
  unfold tailWord_7992846
  simp only [CollatzResearch.WordTrace]
  refine ⟨36440380400161435782897799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194348695467527657508788261 36440380400161435782897799)
  ·
    refine ⟨54660570600242153674346699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36440380400161435782897799 54660570600242153674346699)
    ·
      refine ⟨81990855900363230511520049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54660570600242153674346699 81990855900363230511520049)
      ·
        refine ⟨61493141925272422883640037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81990855900363230511520049 61493141925272422883640037)
        ·
          refine ⟨11529964110988579290682507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61493141925272422883640037 11529964110988579290682507)
          ·
            refine ⟨17294946166482868936023761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529964110988579290682507 17294946166482868936023761)
            ·
              refine ⟨12971209624862151702017821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17294946166482868936023761 12971209624862151702017821)
              ·
                refine ⟨4864203609323306888256683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12971209624862151702017821 4864203609323306888256683)
                ·
                  refine ⟨7296305413984960332385025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864203609323306888256683 7296305413984960332385025)
                  ·
                    refine ⟨5472229060488720249288769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296305413984960332385025 5472229060488720249288769)
                    ·
                      refine ⟨4104171795366540186966577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472229060488720249288769 4104171795366540186966577)
                      ·
                        rfl

theorem cell23_7992846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_7992846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992846 prefixEnd_7992846 := by exact prefixLift 7992846
  have htrace : WordTrace (prefixWord ++ tailWord_7992846) baseStart_7992846 baseEnd_7992846 := by
    simpa [prefixWord, tailWord_7992846, baseEnd_7992846] using wordTrace_append hprefix tailTrace_7992846
  have hstable : (prefixWord ++ tailWord_7992846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992846).length < 2 ^ (prefixWord ++ tailWord_7992846).sum := by decide
  have hdescent : baseEnd_7992846 < baseStart_7992846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992936 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7992936 : Nat := 118140960795 + 7992936 * 2 ^ 59
def prefixEnd_7992936 : Nat := 4983230072969 + 3 ^ 40 * 7992936 * 2
def baseEnd_7992936 : Nat := 4104218008625444834841163

theorem tailTrace_7992936 : CollatzResearch.WordTrace tailWord_7992936 prefixEnd_7992936 4104218008625444834841163 := by
  unfold tailWord_7992936
  simp only [CollatzResearch.WordTrace]
  refine ⟨145763162885482715816979331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194350883847310287755972441 145763162885482715816979331)
  ·
    refine ⟨218644744328224073725468997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145763162885482715816979331 218644744328224073725468997)
    ·
      refine ⟨40995889561542013823525437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218644744328224073725468997 40995889561542013823525437)
      ·
        refine ⟨15373458585578255183822039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40995889561542013823525437 15373458585578255183822039)
        ·
          refine ⟨23060187878367382775733059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15373458585578255183822039 23060187878367382775733059)
          ·
            refine ⟨34590281817551074163599589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23060187878367382775733059 34590281817551074163599589)
            ·
              refine ⟨6485677840790826405674923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34590281817551074163599589 6485677840790826405674923)
              ·
                refine ⟨9728516761186239608512385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485677840790826405674923 9728516761186239608512385)
                ·
                  refine ⟨7296387570889679706384289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9728516761186239608512385 7296387570889679706384289)
                  ·
                    refine ⟨5472290678167259779788217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296387570889679706384289 5472290678167259779788217)
                    ·
                      refine ⟨4104218008625444834841163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472290678167259779788217 4104218008625444834841163)
                      ·
                        rfl

theorem cell23_7992936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7992936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992936 prefixEnd_7992936 := by exact prefixLift 7992936
  have htrace : WordTrace (prefixWord ++ tailWord_7992936) baseStart_7992936 baseEnd_7992936 := by
    simpa [prefixWord, tailWord_7992936, baseEnd_7992936] using wordTrace_append hprefix tailTrace_7992936
  have hstable : (prefixWord ++ tailWord_7992936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992936).length < 2 ^ (prefixWord ++ tailWord_7992936).sum := by decide
  have hdescent : baseEnd_7992936 < baseStart_7992936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7992992 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 2, 4, 2]
def baseStart_7992992 : Nat := 118140960795 + 7992992 * 2 ^ 59
def prefixEnd_7992992 : Nat := 4983230072969 + 3 ^ 40 * 7992992 * 2
def baseEnd_7992992 : Nat := 4104246763542096615740905

theorem tailTrace_7992992 : CollatzResearch.WordTrace tailWord_7992992 prefixEnd_7992992 4104246763542096615740905 := by
  unfold tailWord_7992992
  simp only [CollatzResearch.WordTrace]
  refine ⟨145764184129381276598998615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194352245505841702131998153 145764184129381276598998615)
  ·
    refine ⟨218646276194071914898497923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145764184129381276598998615 218646276194071914898497923)
    ·
      refine ⟨327969414291107872347746885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218646276194071914898497923 327969414291107872347746885)
      ·
        refine ⟨61494265179582726065202541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327969414291107872347746885 61494265179582726065202541)
        ·
          refine ⟨23060349442343522274450953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61494265179582726065202541 23060349442343522274450953)
          ·
            refine ⟨17295262081757641705838215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23060349442343522274450953 17295262081757641705838215)
            ·
              refine ⟨25942893122636462558757323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17295262081757641705838215 25942893122636462558757323)
              ·
                refine ⟨38914339683954693838135985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25942893122636462558757323 38914339683954693838135985)
                ·
                  refine ⟨29185754762966020378601989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38914339683954693838135985 29185754762966020378601989)
                  ·
                    refine ⟨5472329018056128820987873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29185754762966020378601989 5472329018056128820987873)
                    ·
                      refine ⟨4104246763542096615740905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472329018056128820987873 4104246763542096615740905)
                      ·
                        rfl

theorem cell23_7992992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_7992992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7992992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7992992 prefixEnd_7992992 := by exact prefixLift 7992992
  have htrace : WordTrace (prefixWord ++ tailWord_7992992) baseStart_7992992 baseEnd_7992992 := by
    simpa [prefixWord, tailWord_7992992, baseEnd_7992992] using wordTrace_append hprefix tailTrace_7992992
  have hstable : (prefixWord ++ tailWord_7992992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7992992).length < 2 ^ (prefixWord ++ tailWord_7992992).sum := by decide
  have hdescent : baseEnd_7992992 < baseStart_7992992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7992992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993006 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7993006 : Nat := 118140960795 + 7993006 * 2 ^ 59
def prefixEnd_7993006 : Nat := 4983230072969 + 3 ^ 40 * 7993006 * 2
def baseEnd_7993006 : Nat := 1368084650757086520321947

theorem tailTrace_7993006 : CollatzResearch.WordTrace tailWord_7993006 prefixEnd_7993006 1368084650757086520321947 := by
  unfold tailWord_7993006
  simp only [CollatzResearch.WordTrace]
  refine ⟨36441109860088979198625859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194352585920474555726004581 36441109860088979198625859)
  ·
    refine ⟨54661664790133468797938789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36441109860088979198625859 54661664790133468797938789)
    ·
      refine ⟨10249062148150025399613523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54661664790133468797938789 10249062148150025399613523)
      ·
        refine ⟨15373593222225038099420285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10249062148150025399613523 15373593222225038099420285)
        ·
          refine ⟨5765097458334389287282607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15373593222225038099420285 5765097458334389287282607)
          ·
            refine ⟨8647646187501583930923911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765097458334389287282607 8647646187501583930923911)
            ·
              refine ⟨12971469281252375896385867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8647646187501583930923911 12971469281252375896385867)
              ·
                refine ⟨19457203921878563844578801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12971469281252375896385867 19457203921878563844578801)
                ·
                  refine ⟨14592902941408922883434101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19457203921878563844578801 14592902941408922883434101)
                  ·
                    refine ⟨1368084650757086520321947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14592902941408922883434101 1368084650757086520321947)
                    ·
                      rfl

theorem cell23_7993006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7993006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993006 prefixEnd_7993006 := by exact prefixLift 7993006
  have htrace : WordTrace (prefixWord ++ tailWord_7993006) baseStart_7993006 baseEnd_7993006 := by
    simpa [prefixWord, tailWord_7993006, baseEnd_7993006] using wordTrace_append hprefix tailTrace_7993006
  have hstable : (prefixWord ++ tailWord_7993006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993006).length < 2 ^ (prefixWord ++ tailWord_7993006).sum := by decide
  have hdescent : baseEnd_7993006 < baseStart_7993006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993065 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 8, 2]
def baseStart_7993065 : Nat := 118140960795 + 7993065 * 2 ^ 59
def prefixEnd_7993065 : Nat := 4983230072969 + 3 ^ 40 * 7993065 * 2
def baseEnd_7993065 : Nat := 4104284247629874830128069

theorem tailTrace_7993065 : CollatzResearch.WordTrace tailWord_7993065 prefixEnd_7993065 4104284247629874830128069 := by
  unfold tailWord_7993065
  simp only [CollatzResearch.WordTrace]
  refine ⟨291531030787498086665404649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194354020524998724443603099 291531030787498086665404649)
  ·
    refine ⟨218648273090623564999053487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291531030787498086665404649 218648273090623564999053487)
    ·
      refine ⟨327972409635935347498580231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218648273090623564999053487 327972409635935347498580231)
      ·
        refine ⟨491958614453903021247870347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327972409635935347498580231 491958614453903021247870347)
        ·
          refine ⟨737937921680854531871805521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491958614453903021247870347 737937921680854531871805521)
          ·
            refine ⟨553453441260640898903854141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737937921680854531871805521 553453441260640898903854141)
            ·
              refine ⟨207545040472740337088945303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553453441260640898903854141 207545040472740337088945303)
              ·
                refine ⟨311317560709110505633417955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207545040472740337088945303 311317560709110505633417955)
                ·
                  refine ⟨466976341063665758450126933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311317560709110505633417955 466976341063665758450126933)
                  ·
                    refine ⟨5472378996839833106837425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 466976341063665758450126933 5472378996839833106837425)
                    ·
                      refine ⟨4104284247629874830128069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472378996839833106837425 4104284247629874830128069)
                      ·
                        rfl

theorem cell23_7993065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 8, 2].length) (baseStart_7993065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993065 prefixEnd_7993065 := by exact prefixLift 7993065
  have htrace : WordTrace (prefixWord ++ tailWord_7993065) baseStart_7993065 baseEnd_7993065 := by
    simpa [prefixWord, tailWord_7993065, baseEnd_7993065] using wordTrace_append hprefix tailTrace_7993065
  have hstable : (prefixWord ++ tailWord_7993065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993065).length < 2 ^ (prefixWord ++ tailWord_7993065).sum := by decide
  have hdescent : baseEnd_7993065 < baseStart_7993065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993075 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 4, 4]
def baseStart_7993075 : Nat := 118140960795 + 7993075 * 2 ^ 59
def prefixEnd_7993075 : Nat := 4983230072969 + 3 ^ 40 * 7993075 * 2
def baseEnd_7993075 : Nat := 1368096460812139930334341

theorem tailTrace_7993075 : CollatzResearch.WordTrace tailWord_7993075 prefixEnd_7993075 1368096460812139930334341 := by
  unfold tailWord_7993075
  simp only [CollatzResearch.WordTrace]
  refine ⟨291531395517461858373268679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194354263678307905582179119 291531395517461858373268679)
  ·
    refine ⟨437297093276192787559903019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291531395517461858373268679 437297093276192787559903019)
    ·
      refine ⟨655945639914289181339854529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437297093276192787559903019 655945639914289181339854529)
      ·
        refine ⟨491959229935716886004890897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655945639914289181339854529 491959229935716886004890897)
        ·
          refine ⟨368969422451787664503668173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491959229935716886004890897 368969422451787664503668173)
          ·
            refine ⟨138363533419420374188875565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368969422451787664503668173 138363533419420374188875565)
            ·
              refine ⟨51886325032282640320828337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138363533419420374188875565 51886325032282640320828337)
              ·
                refine ⟨38914743774211980240621253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51886325032282640320828337 38914743774211980240621253)
                ·
                  refine ⟨7296514457664746295116485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38914743774211980240621253 7296514457664746295116485)
                  ·
                    refine ⟨1368096460812139930334341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296514457664746295116485 1368096460812139930334341)
                    ·
                      rfl

theorem cell23_7993075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 4].length) (baseStart_7993075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993075 prefixEnd_7993075 := by exact prefixLift 7993075
  have htrace : WordTrace (prefixWord ++ tailWord_7993075) baseStart_7993075 baseEnd_7993075 := by
    simpa [prefixWord, tailWord_7993075, baseEnd_7993075] using wordTrace_append hprefix tailTrace_7993075
  have hstable : (prefixWord ++ tailWord_7993075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993075).length < 2 ^ (prefixWord ++ tailWord_7993075).sum := by decide
  have hdescent : baseEnd_7993075 < baseStart_7993075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993086 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7993086 : Nat := 118140960795 + 7993086 * 2 ^ 59
def prefixEnd_7993086 : Nat := 4983230072969 + 3 ^ 40 * 7993086 * 2
def baseEnd_7993086 : Nat := 4104295030723619247965473

theorem tailTrace_7993086 : CollatzResearch.WordTrace tailWord_7993086 prefixEnd_7993086 4104295030723619247965473 := by
  unfold tailWord_7993086
  simp only [CollatzResearch.WordTrace]
  refine ⟨36441474590052750906489889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194354531146948004834612741 36441474590052750906489889)
  ·
    refine ⟨27331105942539563179867417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36441474590052750906489889 27331105942539563179867417)
    ·
      refine ⟨20498329456904672384900563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27331105942539563179867417 20498329456904672384900563)
      ·
        refine ⟨30747494185357008577350845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20498329456904672384900563 30747494185357008577350845)
        ·
          refine ⟨11530310319508878216506567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30747494185357008577350845 11530310319508878216506567)
          ·
            refine ⟨17295465479263317324759851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11530310319508878216506567 17295465479263317324759851)
            ·
              refine ⟨25943198218894975987139777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17295465479263317324759851 25943198218894975987139777)
              ·
                refine ⟨19457398664171231990354833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25943198218894975987139777 19457398664171231990354833)
                ·
                  refine ⟨14593048998128423992766125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19457398664171231990354833 14593048998128423992766125)
                  ·
                    refine ⟨5472393374298158997287297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14593048998128423992766125 5472393374298158997287297)
                    ·
                      refine ⟨4104295030723619247965473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472393374298158997287297 4104295030723619247965473)
                      ·
                        rfl

theorem cell23_7993086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7993086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993086 prefixEnd_7993086 := by exact prefixLift 7993086
  have htrace : WordTrace (prefixWord ++ tailWord_7993086) baseStart_7993086 baseEnd_7993086 := by
    simpa [prefixWord, tailWord_7993086, baseEnd_7993086] using wordTrace_append hprefix tailTrace_7993086
  have hstable : (prefixWord ++ tailWord_7993086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993086).length < 2 ^ (prefixWord ++ tailWord_7993086).sum := by decide
  have hdescent : baseEnd_7993086 < baseStart_7993086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993092 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_7993092 : Nat := 118140960795 + 7993092 * 2 ^ 59
def prefixEnd_7993092 : Nat := 4983230072969 + 3 ^ 40 * 7993092 * 2
def baseEnd_7993092 : Nat := 1368099370535848741496815

theorem tailTrace_7993092 : CollatzResearch.WordTrace tailWord_7993092 prefixEnd_7993092 1368099370535848741496815 := by
  unfold tailWord_7993092
  simp only [CollatzResearch.WordTrace]
  refine ⟨145766007779200135138318765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194354677038933513517758353 145766007779200135138318765)
  ·
    refine ⟨54662252917200050676869537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145766007779200135138318765 54662252917200050676869537)
    ·
      refine ⟨40996689687900038007652153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54662252917200050676869537 40996689687900038007652153)
      ·
        refine ⟨30747517265925028505739115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40996689687900038007652153 30747517265925028505739115)
        ·
          refine ⟨46121275898887542758608673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30747517265925028505739115 46121275898887542758608673)
          ·
            refine ⟨34590956924165657068956505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46121275898887542758608673 34590956924165657068956505)
            ·
              refine ⟨25943217693124242801717379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34590956924165657068956505 25943217693124242801717379)
              ·
                refine ⟨38914826539686364202576069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25943217693124242801717379 38914826539686364202576069)
                ·
                  refine ⟨7296529976191193287983013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38914826539686364202576069 7296529976191193287983013)
                  ·
                    refine ⟨1368099370535848741496815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296529976191193287983013 1368099370535848741496815)
                    ·
                      rfl

theorem cell23_7993092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_7993092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993092 prefixEnd_7993092 := by exact prefixLift 7993092
  have htrace : WordTrace (prefixWord ++ tailWord_7993092) baseStart_7993092 baseEnd_7993092 := by
    simpa [prefixWord, tailWord_7993092, baseEnd_7993092] using wordTrace_append hprefix tailTrace_7993092
  have hstable : (prefixWord ++ tailWord_7993092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993092).length < 2 ^ (prefixWord ++ tailWord_7993092).sum := by decide
  have hdescent : baseEnd_7993092 < baseStart_7993092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993099 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 3, 2, 2]
def baseStart_7993099 : Nat := 118140960795 + 7993099 * 2 ^ 59
def prefixEnd_7993099 : Nat := 4983230072969 + 3 ^ 40 * 7993099 * 2
def baseEnd_7993099 : Nat := 4104301705972127697102913

theorem tailTrace_7993099 : CollatzResearch.WordTrace tailWord_7993099 prefixEnd_7993099 4104301705972127697102913 := by
  unfold tailWord_7993099
  simp only [CollatzResearch.WordTrace]
  refine ⟨291532270869374910472142351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194354847246249940314761567 291532270869374910472142351)
  ·
    refine ⟨437298406304062365708213527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291532270869374910472142351 437298406304062365708213527)
    ·
      refine ⟨655947609456093548562320291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437298406304062365708213527 655947609456093548562320291)
      ·
        refine ⟨983921414184140322843480437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655947609456093548562320291 983921414184140322843480437)
        ·
          refine ⟨92242632579763155266576291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 983921414184140322843480437 92242632579763155266576291)
          ·
            refine ⟨138363948869644732899864437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92242632579763155266576291 138363948869644732899864437)
            ·
              refine ⟨12971620206529193709362291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138363948869644732899864437 12971620206529193709362291)
              ·
                refine ⟨19457430309793790564043437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12971620206529193709362291 19457430309793790564043437)
                ·
                  refine ⟨7296536366172671461516289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19457430309793790564043437 7296536366172671461516289)
                  ·
                    refine ⟨5472402274629503596137217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296536366172671461516289 5472402274629503596137217)
                    ·
                      refine ⟨4104301705972127697102913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472402274629503596137217 4104301705972127697102913)
                      ·
                        rfl

theorem cell23_7993099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 2, 2].length) (baseStart_7993099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993099 prefixEnd_7993099 := by exact prefixLift 7993099
  have htrace : WordTrace (prefixWord ++ tailWord_7993099) baseStart_7993099 baseEnd_7993099 := by
    simpa [prefixWord, tailWord_7993099, baseEnd_7993099] using wordTrace_append hprefix tailTrace_7993099
  have hstable : (prefixWord ++ tailWord_7993099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993099).length < 2 ^ (prefixWord ++ tailWord_7993099).sum := by decide
  have hdescent : baseEnd_7993099 < baseStart_7993099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993109 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_7993109 : Nat := 118140960795 + 7993109 * 2 ^ 59
def prefixEnd_7993109 : Nat := 4983230072969 + 3 ^ 40 * 7993109 * 2
def baseEnd_7993109 : Nat := 1368102280259557552659289

theorem tailTrace_7993109 : CollatzResearch.WordTrace tailWord_7993109 prefixEnd_7993109 1368102280259557552659289 := by
  unfold tailWord_7993109
  simp only [CollatzResearch.WordTrace]
  refine ⟨291532635599338682180006381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194355090399559121453337587 291532635599338682180006381)
  ·
    refine ⟨109324738349752005817502393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291532635599338682180006381 109324738349752005817502393)
    ·
      refine ⟨81993553762314004363126795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109324738349752005817502393 81993553762314004363126795)
      ·
        refine ⟨122990330643471006544690193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81993553762314004363126795 122990330643471006544690193)
        ·
          refine ⟨92242747982603254908517645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122990330643471006544690193 92242747982603254908517645)
          ·
            refine ⟨34591030493476220590694117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92242747982603254908517645 34591030493476220590694117)
            ·
              refine ⟨6485818217526791360755147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34591030493476220590694117 6485818217526791360755147)
              ·
                refine ⟨9728727326290187041132721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485818217526791360755147 9728727326290187041132721)
                ·
                  refine ⟨7296545494717640280849541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9728727326290187041132721 7296545494717640280849541)
                  ·
                    refine ⟨1368102280259557552659289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296545494717640280849541 1368102280259557552659289)
                    ·
                      rfl

theorem cell23_7993109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_7993109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993109 prefixEnd_7993109 := by exact prefixLift 7993109
  have htrace : WordTrace (prefixWord ++ tailWord_7993109) baseStart_7993109 baseEnd_7993109 := by
    simpa [prefixWord, tailWord_7993109, baseEnd_7993109] using wordTrace_append hprefix tailTrace_7993109
  have hstable : (prefixWord ++ tailWord_7993109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993109).length < 2 ^ (prefixWord ++ tailWord_7993109).sum := by decide
  have hdescent : baseEnd_7993109 < baseStart_7993109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993132 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_7993132 : Nat := 118140960795 + 7993132 * 2 ^ 59
def prefixEnd_7993132 : Nat := 4983230072969 + 3 ^ 40 * 7993132 * 2
def baseEnd_7993132 : Nat := 4104318650833726067990261

theorem tailTrace_7993132 : CollatzResearch.WordTrace tailWord_7993132 prefixEnd_7993132 4104318650833726067990261 := by
  unfold tailWord_7993132
  simp only [CollatzResearch.WordTrace]
  refine ⟨145766737239127678554046825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194355649652170238072062433 145766737239127678554046825)
  ·
    refine ⟨109325052929345758915535119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145766737239127678554046825 109325052929345758915535119)
    ·
      refine ⟨163987579394018638373302679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109325052929345758915535119 163987579394018638373302679)
      ·
        refine ⟨245981369091027957559954019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163987579394018638373302679 245981369091027957559954019)
        ·
          refine ⟨368972053636541936339931029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245981369091027957559954019 368972053636541936339931029)
          ·
            refine ⟨17295565014212903265934267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 368972053636541936339931029 17295565014212903265934267)
            ·
              refine ⟨25943347521319354898901401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17295565014212903265934267 25943347521319354898901401)
              ·
                refine ⟨19457510640989516174176051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25943347521319354898901401 19457510640989516174176051)
                ·
                  refine ⟨29186265961484274261264077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19457510640989516174176051 29186265961484274261264077)
                  ·
                    refine ⟨10944849735556602847974029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29186265961484274261264077 10944849735556602847974029)
                    ·
                      refine ⟨4104318650833726067990261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10944849735556602847974029 4104318650833726067990261)
                      ·
                        rfl

theorem cell23_7993132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_7993132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993132 prefixEnd_7993132 := by exact prefixLift 7993132
  have htrace : WordTrace (prefixWord ++ tailWord_7993132) baseStart_7993132 baseEnd_7993132 := by
    simpa [prefixWord, tailWord_7993132, baseEnd_7993132] using wordTrace_append hprefix tailTrace_7993132
  have hstable : (prefixWord ++ tailWord_7993132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993132).length < 2 ^ (prefixWord ++ tailWord_7993132).sum := by decide
  have hdescent : baseEnd_7993132 < baseStart_7993132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993150 : List Nat := [4, 2, 1, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_7993150 : Nat := 118140960795 + 7993150 * 2 ^ 59
def prefixEnd_7993150 : Nat := 4983230072969 + 3 ^ 40 * 7993150 * 2
def baseEnd_7993150 : Nat := 4104327893485506997565179

theorem tailTrace_7993150 : CollatzResearch.WordTrace tailWord_7993150 prefixEnd_7993150 4104327893485506997565179 := by
  unfold tailWord_7993150
  simp only [CollatzResearch.WordTrace]
  refine ⟨36441766374023768272781113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194356087328126764121499269 36441766374023768272781113)
  ·
    refine ⟨27331324780517826204585835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36441766374023768272781113 27331324780517826204585835)
    ·
      refine ⟨40996987170776739306878753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27331324780517826204585835 40996987170776739306878753)
      ·
        refine ⟨30747740378082554480159065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40996987170776739306878753 30747740378082554480159065)
        ·
          refine ⟨23060805283561915860119299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30747740378082554480159065 23060805283561915860119299)
          ·
            refine ⟨34591207925342873790178949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23060805283561915860119299 34591207925342873790178949)
            ·
              refine ⟨6485851486001788835658553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34591207925342873790178949 6485851486001788835658553)
              ·
                refine ⟨4864388614501341626743915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485851486001788835658553 4864388614501341626743915)
                ·
                  refine ⟨7296582921752012440115873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864388614501341626743915 7296582921752012440115873)
                  ·
                    refine ⟨5472437191314009330086905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296582921752012440115873 5472437191314009330086905)
                    ·
                      refine ⟨4104327893485506997565179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472437191314009330086905 4104327893485506997565179)
                      ·
                        rfl

theorem cell23_7993150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_7993150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993150 prefixEnd_7993150 := by exact prefixLift 7993150
  have htrace : WordTrace (prefixWord ++ tailWord_7993150) baseStart_7993150 baseEnd_7993150 := by
    simpa [prefixWord, tailWord_7993150, baseEnd_7993150] using wordTrace_append hprefix tailTrace_7993150
  have hstable : (prefixWord ++ tailWord_7993150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993150).length < 2 ^ (prefixWord ++ tailWord_7993150).sum := by decide
  have hdescent : baseEnd_7993150 < baseStart_7993150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993155 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4]
def baseStart_7993155 : Nat := 118140960795 + 7993155 * 2 ^ 59
def prefixEnd_7993155 : Nat := 4983230072969 + 3 ^ 40 * 7993155 * 2
def baseEnd_7993155 : Nat := 4104330460888779478002655

theorem tailTrace_7993155 : CollatzResearch.WordTrace tailWord_7993155 prefixEnd_7993155 4104330460888779478002655 := by
  unfold tailWord_7993155
  simp only [CollatzResearch.WordTrace]
  refine ⟨291534313357172032036180919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194356208904781354690787279 291534313357172032036180919)
  ·
    refine ⟨437301470035758048054271379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291534313357172032036180919 437301470035758048054271379)
    ·
      refine ⟨655952205053637072081407069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437301470035758048054271379 655952205053637072081407069)
      ·
        refine ⟨245982076895113902030527651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655952205053637072081407069 245982076895113902030527651)
        ·
          refine ⟨368973115342670853045791477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245982076895113902030527651 368973115342670853045791477)
          ·
            refine ⟨34591229563375392473042951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368973115342670853045791477 34591229563375392473042951)
            ·
              refine ⟨51886844345063088709564427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34591229563375392473042951 51886844345063088709564427)
              ·
                refine ⟨77830266517594633064346641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51886844345063088709564427 77830266517594633064346641)
                ·
                  refine ⟨58372699888195974798259981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77830266517594633064346641 58372699888195974798259981)
                  ·
                    refine ⟨21889762458073490549347493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58372699888195974798259981 21889762458073490549347493)
                    ·
                      refine ⟨4104330460888779478002655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21889762458073490549347493 4104330460888779478002655)
                      ·
                        rfl

theorem cell23_7993155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_7993155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993155 prefixEnd_7993155 := by exact prefixLift 7993155
  have htrace : WordTrace (prefixWord ++ tailWord_7993155) baseStart_7993155 baseEnd_7993155 := by
    simpa [prefixWord, tailWord_7993155, baseEnd_7993155] using wordTrace_append hprefix tailTrace_7993155
  have hstable : (prefixWord ++ tailWord_7993155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993155).length < 2 ^ (prefixWord ++ tailWord_7993155).sum := by decide
  have hdescent : baseEnd_7993155 < baseStart_7993155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993185 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_7993185 : Nat := 118140960795 + 7993185 * 2 ^ 59
def prefixEnd_7993185 : Nat := 4983230072969 + 3 ^ 40 * 7993185 * 2
def baseEnd_7993185 : Nat := 4104345865308414360627517

theorem tailTrace_7993185 : CollatzResearch.WordTrace tailWord_7993185 prefixEnd_7993185 4104345865308414360627517 := by
  unfold tailWord_7993185
  simp only [CollatzResearch.WordTrace]
  refine ⟨291535407547063347159773009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194356938364708898106515339 291535407547063347159773009)
  ·
    refine ⟨218651555660297510369829757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291535407547063347159773009 218651555660297510369829757)
    ·
      refine ⟨81994333372611566388686159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218651555660297510369829757 81994333372611566388686159)
      ·
        refine ⟨122991500058917349583029239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81994333372611566388686159 122991500058917349583029239)
        ·
          refine ⟨184487250088376024374543859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122991500058917349583029239 184487250088376024374543859)
          ·
            refine ⟨276730875132564036561815789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184487250088376024374543859 276730875132564036561815789)
            ·
              refine ⟨103774078174711513710680921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276730875132564036561815789 103774078174711513710680921)
              ·
                refine ⟨77830558631033635283010691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103774078174711513710680921 77830558631033635283010691)
                ·
                  refine ⟨116745837946550452924516037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77830558631033635283010691 116745837946550452924516037)
                  ·
                    refine ⟨21889844614978209923346757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116745837946550452924516037 21889844614978209923346757)
                    ·
                      refine ⟨4104345865308414360627517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21889844614978209923346757 4104345865308414360627517)
                      ·
                        rfl

theorem cell23_7993185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_7993185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993185 prefixEnd_7993185 := by exact prefixLift 7993185
  have htrace : WordTrace (prefixWord ++ tailWord_7993185) baseStart_7993185 baseEnd_7993185 := by
    simpa [prefixWord, tailWord_7993185, baseEnd_7993185] using wordTrace_append hprefix tailTrace_7993185
  have hstable : (prefixWord ++ tailWord_7993185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993185).length < 2 ^ (prefixWord ++ tailWord_7993185).sum := by decide
  have hdescent : baseEnd_7993185 < baseStart_7993185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993189 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 4, 2, 2]
def baseStart_7993189 : Nat := 118140960795 + 7993189 * 2 ^ 59
def prefixEnd_7993189 : Nat := 4983230072969 + 3 ^ 40 * 7993189 * 2
def baseEnd_7993189 : Nat := 4104347919231032344977499

theorem tailTrace_7993189 : CollatzResearch.WordTrace tailWord_7993189 prefixEnd_7993189 4104347919231032344977499 := by
  unfold tailWord_7993189
  simp only [CollatzResearch.WordTrace]
  refine ⟨291535553439048855842918621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194357035626032570561945747 291535553439048855842918621)
  ·
    refine ⟨109325832539643320941094483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291535553439048855842918621 109325832539643320941094483)
    ·
      refine ⟨163988748809464981411641725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109325832539643320941094483 163988748809464981411641725)
      ·
        refine ⟨61495780803549368029365647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163988748809464981411641725 61495780803549368029365647)
        ·
          refine ⟨92243671205324052044048471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61495780803549368029365647 92243671205324052044048471)
          ·
            refine ⟨138365506807986078066072707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92243671205324052044048471 138365506807986078066072707)
            ·
              refine ⟨207548260211979117099109061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138365506807986078066072707 207548260211979117099109061)
              ·
                refine ⟨38915298789746084456082949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207548260211979117099109061 38915298789746084456082949)
                ·
                  refine ⟨7296618523077390835515553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38915298789746084456082949 7296618523077390835515553)
                  ·
                    refine ⟨5472463892308043126636665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296618523077390835515553 5472463892308043126636665)
                    ·
                      refine ⟨4104347919231032344977499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472463892308043126636665 4104347919231032344977499)
                      ·
                        rfl

theorem cell23_7993189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_7993189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993189 prefixEnd_7993189 := by exact prefixLift 7993189
  have htrace : WordTrace (prefixWord ++ tailWord_7993189) baseStart_7993189 baseEnd_7993189 := by
    simpa [prefixWord, tailWord_7993189, baseEnd_7993189] using wordTrace_append hprefix tailTrace_7993189
  have hstable : (prefixWord ++ tailWord_7993189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993189).length < 2 ^ (prefixWord ++ tailWord_7993189).sum := by decide
  have hdescent : baseEnd_7993189 < baseStart_7993189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993223 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_7993223 : Nat := 118140960795 + 7993223 * 2 ^ 59
def prefixEnd_7993223 : Nat := 4983230072969 + 3 ^ 40 * 7993223 * 2
def baseEnd_7993223 : Nat := 4104365377573285211952343

theorem tailTrace_7993223 : CollatzResearch.WordTrace tailWord_7993223 prefixEnd_7993223 4104365377573285211952343 := by
  unfold tailWord_7993223
  simp only [CollatzResearch.WordTrace]
  refine ⟨291536793520925679649656323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194357862347283786433104215 291536793520925679649656323)
  ·
    refine ⟨437305190281388519474484485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291536793520925679649656323 437305190281388519474484485)
    ·
      refine ⟨81994723177760347401465841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437305190281388519474484485 81994723177760347401465841)
      ·
        refine ⟨61496042383320260551099381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81994723177760347401465841 61496042383320260551099381)
        ·
          refine ⟨5765253973436274426665567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61496042383320260551099381 5765253973436274426665567)
          ·
            refine ⟨8647880960154411639998351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765253973436274426665567 8647880960154411639998351)
            ·
              refine ⟨12971821440231617459997527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8647880960154411639998351 12971821440231617459997527)
              ·
                refine ⟨19457732160347426189996291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12971821440231617459997527 19457732160347426189996291)
                ·
                  refine ⟨29186598240521139284994437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19457732160347426189996291 29186598240521139284994437)
                  ·
                    refine ⟨5472487170097713615936457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29186598240521139284994437 5472487170097713615936457)
                    ·
                      refine ⟨4104365377573285211952343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472487170097713615936457 4104365377573285211952343)
                      ·
                        rfl

theorem cell23_7993223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_7993223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993223 prefixEnd_7993223 := by exact prefixLift 7993223
  have htrace : WordTrace (prefixWord ++ tailWord_7993223) baseStart_7993223 baseEnd_7993223 := by
    simpa [prefixWord, tailWord_7993223, baseEnd_7993223] using wordTrace_append hprefix tailTrace_7993223
  have hstable : (prefixWord ++ tailWord_7993223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993223).length < 2 ^ (prefixWord ++ tailWord_7993223).sum := by decide
  have hdescent : baseEnd_7993223 < baseStart_7993223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993225 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 3, 7]
def baseStart_7993225 : Nat := 118140960795 + 7993225 * 2 ^ 59
def prefixEnd_7993225 : Nat := 4983230072969 + 3 ^ 40 * 7993225 * 2
def baseEnd_7993225 : Nat := 1368122134844864734709111

theorem tailTrace_7993225 : CollatzResearch.WordTrace tailWord_7993225 prefixEnd_7993225 1368122134844864734709111 := by
  unfold tailWord_7993225
  simp only [CollatzResearch.WordTrace]
  refine ⟨291536866466918433991229129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194357910977945622660819419 291536866466918433991229129)
  ·
    refine ⟨218652649850188825493421847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291536866466918433991229129 218652649850188825493421847)
    ·
      refine ⟨327978974775283238240132771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218652649850188825493421847 327978974775283238240132771)
      ·
        refine ⟨491968462162924857360199157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327978974775283238240132771 491968462162924857360199157)
        ·
          refine ⟨46122043327774205377518671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491968462162924857360199157 46122043327774205377518671)
          ·
            refine ⟨69183064991661308066278007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46122043327774205377518671 69183064991661308066278007)
            ·
              refine ⟨103774597487491962099417011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69183064991661308066278007 103774597487491962099417011)
              ·
                refine ⟨155661896231237943149125517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103774597487491962099417011 155661896231237943149125517)
                ·
                  refine ⟨58373211086714228680922069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155661896231237943149125517 58373211086714228680922069)
                  ·
                    refine ⟨1368122134844864734709111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58373211086714228680922069 1368122134844864734709111)
                    ·
                      rfl

theorem cell23_7993225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_7993225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993225 prefixEnd_7993225 := by exact prefixLift 7993225
  have htrace : WordTrace (prefixWord ++ tailWord_7993225) baseStart_7993225 baseEnd_7993225 := by
    simpa [prefixWord, tailWord_7993225, baseEnd_7993225] using wordTrace_append hprefix tailTrace_7993225
  have hstable : (prefixWord ++ tailWord_7993225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993225).length < 2 ^ (prefixWord ++ tailWord_7993225).sum := by decide
  have hdescent : baseEnd_7993225 < baseStart_7993225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993232 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 4, 5, 2]
def baseStart_7993232 : Nat := 118140960795 + 7993232 * 2 ^ 59
def prefixEnd_7993232 : Nat := 4983230072969 + 3 ^ 40 * 7993232 * 2
def baseEnd_7993232 : Nat := 4104369998899175676739801

theorem tailTrace_7993232 : CollatzResearch.WordTrace tailWord_7993232 prefixEnd_7993232 4104369998899175676739801 := by
  unfold tailWord_7993232
  simp only [CollatzResearch.WordTrace]
  refine ⟨145768560888946537093366975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194358081185262049457822633 145768560888946537093366975)
  ·
    refine ⟨218652841333419805640050463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145768560888946537093366975 218652841333419805640050463)
    ·
      refine ⟨327979262000129708460075695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218652841333419805640050463 327979262000129708460075695)
      ·
        refine ⟨491968893000194562690113543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327979262000129708460075695 491968893000194562690113543)
        ·
          refine ⟨737953339500291844035170315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491968893000194562690113543 737953339500291844035170315)
          ·
            refine ⟨1106930009250437766052755473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737953339500291844035170315 1106930009250437766052755473)
            ·
              refine ⟨830197506937828324539566605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106930009250437766052755473 830197506937828324539566605)
              ·
                refine ⟨311324065101685621702337477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830197506937828324539566605 311324065101685621702337477)
                ·
                  refine ⟨58373262206566054069188277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311324065101685621702337477 58373262206566054069188277)
                  ·
                    refine ⟨5472493331865567568986401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58373262206566054069188277 5472493331865567568986401)
                    ·
                      refine ⟨4104369998899175676739801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472493331865567568986401 4104369998899175676739801)
                      ·
                        rfl

theorem cell23_7993232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 5, 2].length) (baseStart_7993232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993232 prefixEnd_7993232 := by exact prefixLift 7993232
  have htrace : WordTrace (prefixWord ++ tailWord_7993232) baseStart_7993232 baseEnd_7993232 := by
    simpa [prefixWord, tailWord_7993232, baseEnd_7993232] using wordTrace_append hprefix tailTrace_7993232
  have hstable : (prefixWord ++ tailWord_7993232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993232).length < 2 ^ (prefixWord ++ tailWord_7993232).sum := by decide
  have hdescent : baseEnd_7993232 < baseStart_7993232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993242 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_7993242 : Nat := 118140960795 + 7993242 * 2 ^ 59
def prefixEnd_7993242 : Nat := 4983230072969 + 3 ^ 40 * 7993242 * 2
def baseEnd_7993242 : Nat := 1368125044568573545871585

theorem tailTrace_7993242 : CollatzResearch.WordTrace tailWord_7993242 prefixEnd_7993242 1368125044568573545871585 := by
  unfold tailWord_7993242
  simp only [CollatzResearch.WordTrace]
  refine ⟨72884371626964211473649495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194358324338571230596398653 72884371626964211473649495)
  ·
    refine ⟨109326557440446317210474243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72884371626964211473649495 109326557440446317210474243)
    ·
      refine ⟨163989836160669475815711365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109326557440446317210474243 163989836160669475815711365)
      ·
        refine ⟨30748094280125526715445881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163989836160669475815711365 30748094280125526715445881)
        ·
          refine ⟨23061070710094145036584411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30748094280125526715445881 23061070710094145036584411)
          ·
            refine ⟨34591606065141217554876617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23061070710094145036584411 34591606065141217554876617)
            ·
              refine ⟨25943704548855913166157463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34591606065141217554876617 25943704548855913166157463)
              ·
                refine ⟨38915556823283869749236195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25943704548855913166157463 38915556823283869749236195)
                ·
                  refine ⟨58373335234925804623854293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38915556823283869749236195 58373335234925804623854293)
                  ·
                    refine ⟨1368125044568573545871585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58373335234925804623854293 1368125044568573545871585)
                    ·
                      rfl

theorem cell23_7993242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_7993242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993242 prefixEnd_7993242 := by exact prefixLift 7993242
  have htrace : WordTrace (prefixWord ++ tailWord_7993242) baseStart_7993242 baseEnd_7993242 := by
    simpa [prefixWord, tailWord_7993242, baseEnd_7993242] using wordTrace_append hprefix tailTrace_7993242
  have hstable : (prefixWord ++ tailWord_7993242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993242).length < 2 ^ (prefixWord ++ tailWord_7993242).sum := by decide
  have hdescent : baseEnd_7993242 < baseStart_7993242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993275 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6]
def baseStart_7993275 : Nat := 118140960795 + 7993275 * 2 ^ 59
def prefixEnd_7993275 : Nat := 4983230072969 + 3 ^ 40 * 7993275 * 2
def baseEnd_7993275 : Nat := 4104392078567319008502103

theorem tailTrace_7993275 : CollatzResearch.WordTrace tailWord_7993275 prefixEnd_7993275 4104392078567319008502103 := by
  unfold tailWord_7993275
  simp only [CollatzResearch.WordTrace]
  refine ⟨291538690116737292530549279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194359126744491528353699519 291538690116737292530549279)
  ·
    refine ⟨437308035175105938795823919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291538690116737292530549279 437308035175105938795823919)
    ·
      refine ⟨655962052762658908193735879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437308035175105938795823919 655962052762658908193735879)
      ·
        refine ⟨983943079143988362290603819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655962052762658908193735879 983943079143988362290603819)
        ·
          refine ⟨1475914618715982543435905729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983943079143988362290603819 1475914618715982543435905729)
          ·
            refine ⟨1106935964036986907576929297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475914618715982543435905729 1106935964036986907576929297)
            ·
              refine ⟨830201973027740180682696973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106935964036986907576929297 830201973027740180682696973)
              ·
                refine ⟨311325739885402567756011365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830201973027740180682696973 311325739885402567756011365)
                ·
                  refine ⟨58373576228512981454252131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311325739885402567756011365 58373576228512981454252131)
                  ·
                    refine ⟨87560364342769472181378197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58373576228512981454252131 87560364342769472181378197)
                    ·
                      refine ⟨4104392078567319008502103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87560364342769472181378197 4104392078567319008502103)
                      ·
                        rfl

theorem cell23_7993275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_7993275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993275 prefixEnd_7993275 := by exact prefixLift 7993275
  have htrace : WordTrace (prefixWord ++ tailWord_7993275) baseStart_7993275 baseEnd_7993275 := by
    simpa [prefixWord, tailWord_7993275, baseEnd_7993275] using wordTrace_append hprefix tailTrace_7993275
  have hstable : (prefixWord ++ tailWord_7993275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993275).length < 2 ^ (prefixWord ++ tailWord_7993275).sum := by decide
  have hdescent : baseEnd_7993275 < baseStart_7993275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993285 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 10]
def baseStart_7993285 : Nat := 118140960795 + 7993285 * 2 ^ 59
def prefixEnd_7993285 : Nat := 4983230072969 + 3 ^ 40 * 7993285 * 2
def baseEnd_7993285 : Nat := 456044134819318218819673

theorem tailTrace_7993285 : CollatzResearch.WordTrace tailWord_7993285 prefixEnd_7993285 456044134819318218819673 := by
  unfold tailWord_7993285
  simp only [CollatzResearch.WordTrace]
  refine ⟨291539054846701064238413309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194359369897800709492275539 291539054846701064238413309)
  ·
    refine ⟨109327145567512899089404991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291539054846701064238413309 109327145567512899089404991)
    ·
      refine ⟨163990718351269348634107487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109327145567512899089404991 163990718351269348634107487)
      ·
        refine ⟨245986077526904022951161231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163990718351269348634107487 245986077526904022951161231)
        ·
          refine ⟨368979116290356034426741847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245986077526904022951161231 368979116290356034426741847)
          ·
            refine ⟨553468674435534051640112771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368979116290356034426741847 553468674435534051640112771)
            ·
              refine ⟨830203011653301077460169157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553468674435534051640112771 830203011653301077460169157)
              ·
                refine ⟨155663064684993952023781717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 830203011653301077460169157 155663064684993952023781717)
                ·
                  refine ⟨456044134819318218819673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155663064684993952023781717 456044134819318218819673)
                  ·
                    rfl

theorem cell23_7993285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_7993285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993285 prefixEnd_7993285 := by exact prefixLift 7993285
  have htrace : WordTrace (prefixWord ++ tailWord_7993285) baseStart_7993285 baseEnd_7993285 := by
    simpa [prefixWord, tailWord_7993285, baseEnd_7993285] using wordTrace_append hprefix tailTrace_7993285
  have hstable : (prefixWord ++ tailWord_7993285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993285).length < 2 ^ (prefixWord ++ tailWord_7993285).sum := by decide
  have hdescent : baseEnd_7993285 < baseStart_7993285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993322 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_7993322 : Nat := 118140960795 + 7993322 * 2 ^ 59
def prefixEnd_7993322 : Nat := 4983230072969 + 3 ^ 40 * 7993322 * 2
def baseEnd_7993322 : Nat := 4104416212158080324614387

theorem tailTrace_7993322 : CollatzResearch.WordTrace tailWord_7993322 prefixEnd_7993322 4104416212158080324614387 := by
  unfold tailWord_7993322
  simp only [CollatzResearch.WordTrace]
  refine ⟨72885101086891754889377555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194360269565044679705006813 72885101086891754889377555)
  ·
    refine ⟨109327651630337632334066333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72885101086891754889377555 109327651630337632334066333)
    ·
      refine ⟨40997869361376612125274875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109327651630337632334066333 40997869361376612125274875)
      ·
        refine ⟨61496804042064918187912313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40997869361376612125274875 61496804042064918187912313)
        ·
          refine ⟨46122603031548688640934235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61496804042064918187912313 46122603031548688640934235)
          ·
            refine ⟨69183904547323032961401353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46122603031548688640934235 69183904547323032961401353)
            ·
              refine ⟨51887928410492274721051015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69183904547323032961401353 51887928410492274721051015)
              ·
                refine ⟨77831892615738412081576523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51887928410492274721051015 77831892615738412081576523)
                ·
                  refine ⟨116747838923607618122364785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77831892615738412081576523 116747838923607618122364785)
                  ·
                    refine ⟨87560879192705713591773589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116747838923607618122364785 87560879192705713591773589)
                    ·
                      refine ⟨4104416212158080324614387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87560879192705713591773589 4104416212158080324614387)
                      ·
                        rfl

theorem cell23_7993322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_7993322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993322 prefixEnd_7993322 := by exact prefixLift 7993322
  have htrace : WordTrace (prefixWord ++ tailWord_7993322) baseStart_7993322 baseEnd_7993322 := by
    simpa [prefixWord, tailWord_7993322, baseEnd_7993322] using wordTrace_append hprefix tailTrace_7993322
  have hstable : (prefixWord ++ tailWord_7993322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993322).length < 2 ^ (prefixWord ++ tailWord_7993322).sum := by decide
  have hdescent : baseEnd_7993322 < baseStart_7993322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993339 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 4, 3, 2]
def baseStart_7993339 : Nat := 118140960795 + 7993339 * 2 ^ 59
def prefixEnd_7993339 : Nat := 4983230072969 + 3 ^ 40 * 7993339 * 2
def baseEnd_7993339 : Nat := 4104424941329206758101809

theorem tailTrace_7993339 : CollatzResearch.WordTrace tailWord_7993339 prefixEnd_7993339 4104424941329206758101809 := by
  unfold tailWord_7993339
  simp only [CollatzResearch.WordTrace]
  refine ⟨291541024388505431460879071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194360682925670287640586047 291541024388505431460879071)
  ·
    refine ⟨437311536582758147191318607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291541024388505431460879071 437311536582758147191318607)
    ·
      refine ⟨655967304874137220786977911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437311536582758147191318607 655967304874137220786977911)
      ·
        refine ⟨983950957311205831180466867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655967304874137220786977911 983950957311205831180466867)
        ·
          refine ⟨1475926435966808746770700301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983950957311205831180466867 1475926435966808746770700301)
          ·
            refine ⟨553472413487553280039012613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1475926435966808746770700301 553472413487553280039012613)
            ·
              refine ⟨103776077528916240007314865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 553472413487553280039012613 103776077528916240007314865)
              ·
                refine ⟨77832058146687180005486149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103776077528916240007314865 77832058146687180005486149)
                ·
                  refine ⟨14593510902503846251028653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77832058146687180005486149 14593510902503846251028653)
                  ·
                    refine ⟨5472566588438942344135745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14593510902503846251028653 5472566588438942344135745)
                    ·
                      refine ⟨4104424941329206758101809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472566588438942344135745 4104424941329206758101809)
                      ·
                        rfl

theorem cell23_7993339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3, 2].length) (baseStart_7993339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993339 prefixEnd_7993339 := by exact prefixLift 7993339
  have htrace : WordTrace (prefixWord ++ tailWord_7993339) baseStart_7993339 baseEnd_7993339 := by
    simpa [prefixWord, tailWord_7993339, baseEnd_7993339] using wordTrace_append hprefix tailTrace_7993339
  have hstable : (prefixWord ++ tailWord_7993339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993339).length < 2 ^ (prefixWord ++ tailWord_7993339).sum := by decide
  have hdescent : baseEnd_7993339 < baseStart_7993339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993379 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 4, 4]
def baseStart_7993379 : Nat := 118140960795 + 7993379 * 2 ^ 59
def prefixEnd_7993379 : Nat := 4983230072969 + 3 ^ 40 * 7993379 * 2
def baseEnd_7993379 : Nat := 1368148493518462200533875

theorem tailTrace_7993379 : CollatzResearch.WordTrace tailWord_7993379 prefixEnd_7993379 1368148493518462200533875 := by
  unfold tailWord_7993379
  simp only [CollatzResearch.WordTrace]
  refine ⟨291542483308360518292335191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194361655538907012194890127 291542483308360518292335191)
  ·
    refine ⟨437313724962540777438502787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291542483308360518292335191 437313724962540777438502787)
    ·
      refine ⟨655970587443811166157754181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437313724962540777438502787 655970587443811166157754181)
      ·
        refine ⟨122994485145714593654578909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 655970587443811166157754181 122994485145714593654578909)
        ·
          refine ⟨46122931929642972620467091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122994485145714593654578909 46122931929642972620467091)
          ·
            refine ⟨69184397894464458930700637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46122931929642972620467091 69184397894464458930700637)
            ·
              refine ⟨25944149210424172099012739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69184397894464458930700637 25944149210424172099012739)
              ·
                refine ⟨38916223815636258148519109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25944149210424172099012739 38916223815636258148519109)
                ·
                  refine ⟨7296791965431798402847333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38916223815636258148519109 7296791965431798402847333)
                  ·
                    refine ⟨1368148493518462200533875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296791965431798402847333 1368148493518462200533875)
                    ·
                      rfl

theorem cell23_7993379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 4].length) (baseStart_7993379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993379 prefixEnd_7993379 := by exact prefixLift 7993379
  have htrace : WordTrace (prefixWord ++ tailWord_7993379) baseStart_7993379 baseEnd_7993379 := by
    simpa [prefixWord, tailWord_7993379, baseEnd_7993379] using wordTrace_append hprefix tailTrace_7993379
  have hstable : (prefixWord ++ tailWord_7993379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993379).length < 2 ^ (prefixWord ++ tailWord_7993379).sum := by decide
  have hdescent : baseEnd_7993379 < baseStart_7993379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993399 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_7993399 : Nat := 118140960795 + 7993399 * 2 ^ 59
def prefixEnd_7993399 : Nat := 4983230072969 + 3 ^ 40 * 7993399 * 2
def baseEnd_7993399 : Nat := 4104455750168476523351533

theorem tailTrace_7993399 : CollatzResearch.WordTrace tailWord_7993399 prefixEnd_7993399 4104455750168476523351533 := by
  unfold tailWord_7993399
  simp only [CollatzResearch.WordTrace]
  refine ⟨291543212768288061708063251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194362141845525374472042167 291543212768288061708063251)
  ·
    refine ⟨437314819152432092562094877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291543212768288061708063251 437314819152432092562094877)
    ·
      refine ⟨163993057182162034710785579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437314819152432092562094877 163993057182162034710785579)
      ·
        refine ⟨245989585773243052066178369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163993057182162034710785579 245989585773243052066178369)
        ·
          refine ⟨184492189329932289049633777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245989585773243052066178369 184492189329932289049633777)
          ·
            refine ⟨138369141997449216787225333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184492189329932289049633777 138369141997449216787225333)
            ·
              refine ⟨12972107062260864073802375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138369141997449216787225333 12972107062260864073802375)
              ·
                refine ⟨19458160593391296110703563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12972107062260864073802375 19458160593391296110703563)
                ·
                  refine ⟨29187240890086944166055345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19458160593391296110703563 29187240890086944166055345)
                  ·
                    refine ⟨21890430667565208124541509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29187240890086944166055345 21890430667565208124541509)
                    ·
                      refine ⟨4104455750168476523351533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21890430667565208124541509 4104455750168476523351533)
                      ·
                        rfl

theorem cell23_7993399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_7993399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993399 prefixEnd_7993399 := by exact prefixLift 7993399
  have htrace : WordTrace (prefixWord ++ tailWord_7993399) baseStart_7993399 baseEnd_7993399 := by
    simpa [prefixWord, tailWord_7993399, baseEnd_7993399] using wordTrace_append hprefix tailTrace_7993399
  have hstable : (prefixWord ++ tailWord_7993399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993399).length < 2 ^ (prefixWord ++ tailWord_7993399).sum := by decide
  have hdescent : baseEnd_7993399 < baseStart_7993399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993409 : List Nat := [1, 2, 5, 1, 2, 2, 1, 9]
def baseStart_7993409 : Nat := 118140960795 + 7993409 * 2 ^ 59
def prefixEnd_7993409 : Nat := 4983230072969 + 3 ^ 40 * 7993409 * 2
def baseEnd_7993409 : Nat := 152017069813889684600981

theorem tailTrace_7993409 : CollatzResearch.WordTrace tailWord_7993409 prefixEnd_7993409 152017069813889684600981 := by
  unfold tailWord_7993409
  simp only [CollatzResearch.WordTrace]
  refine ⟨291543577498251833415927281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194362384998834555610618187 291543577498251833415927281)
  ·
    refine ⟨218657683123688875061945461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291543577498251833415927281 218657683123688875061945461)
    ·
      refine ⟨20499157792845832037057387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218657683123688875061945461 20499157792845832037057387)
      ·
        refine ⟨30748736689268748055586081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20499157792845832037057387 30748736689268748055586081)
        ·
          refine ⟨23061552516951561041689561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30748736689268748055586081 23061552516951561041689561)
          ·
            refine ⟨17296164387713670781267171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23061552516951561041689561 17296164387713670781267171)
            ·
              refine ⟨25944246581570506171900757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17296164387713670781267171 25944246581570506171900757)
              ·
                refine ⟨152017069813889684600981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25944246581570506171900757 152017069813889684600981)
                ·
                  rfl

theorem cell23_7993409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 9].length) (baseStart_7993409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993409 prefixEnd_7993409 := by exact prefixLift 7993409
  have htrace : WordTrace (prefixWord ++ tailWord_7993409) baseStart_7993409 baseEnd_7993409 := by
    simpa [prefixWord, tailWord_7993409, baseEnd_7993409] using wordTrace_append hprefix tailTrace_7993409
  have hstable : (prefixWord ++ tailWord_7993409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993409).length < 2 ^ (prefixWord ++ tailWord_7993409).sum := by decide
  have hdescent : baseEnd_7993409 < baseStart_7993409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993420 : List Nat := [2, 2, 1, 3, 1, 1, 5, 3, 1, 2, 2]
def baseStart_7993420 : Nat := 118140960795 + 7993420 * 2 ^ 59
def prefixEnd_7993420 : Nat := 4983230072969 + 3 ^ 40 * 7993420 * 2
def baseEnd_7993420 : Nat := 4104466533262220941188937

theorem tailTrace_7993420 : CollatzResearch.WordTrace tailWord_7993420 prefixEnd_7993420 4104466533262220941188937 := by
  unfold tailWord_7993420
  simp only [CollatzResearch.WordTrace]
  refine ⟨145771989350605991147288857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194362652467474654863051809 145771989350605991147288857)
  ·
    refine ⟨109328992012954493360466643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145771989350605991147288857 109328992012954493360466643)
    ·
      refine ⟨163993488019431740040699965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109328992012954493360466643 163993488019431740040699965)
      ·
        refine ⟨61497558007286902515262487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163993488019431740040699965 61497558007286902515262487)
        ·
          refine ⟨92246337010930353772893731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61497558007286902515262487 92246337010930353772893731)
          ·
            refine ⟨138369505516395530659340597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92246337010930353772893731 138369505516395530659340597)
            ·
              refine ⟨12972141142162080999313181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138369505516395530659340597 12972141142162080999313181)
              ·
                refine ⟨4864552928310780374742443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12972141142162080999313181 4864552928310780374742443)
                ·
                  refine ⟨7296829392466170562113665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864552928310780374742443 7296829392466170562113665)
                  ·
                    refine ⟨5472622044349627921585249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296829392466170562113665 5472622044349627921585249)
                    ·
                      refine ⟨4104466533262220941188937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472622044349627921585249 4104466533262220941188937)
                      ·
                        rfl

theorem cell23_7993420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_7993420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993420 prefixEnd_7993420 := by exact prefixLift 7993420
  have htrace : WordTrace (prefixWord ++ tailWord_7993420) baseStart_7993420 baseEnd_7993420 := by
    simpa [prefixWord, tailWord_7993420, baseEnd_7993420] using wordTrace_append hprefix tailTrace_7993420
  have hstable : (prefixWord ++ tailWord_7993420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993420).length < 2 ^ (prefixWord ++ tailWord_7993420).sum := by decide
  have hdescent : baseEnd_7993420 < baseStart_7993420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993426 : List Nat := [3, 2, 2, 1, 5, 1, 9]
def baseStart_7993426 : Nat := 118140960795 + 7993426 * 2 ^ 59
def prefixEnd_7993426 : Nat := 4983230072969 + 3 ^ 40 * 7993426 * 2
def baseEnd_7993426 : Nat := 50672464372174665650789

theorem tailTrace_7993426 : CollatzResearch.WordTrace tailWord_7993426 prefixEnd_7993426 50672464372174665650789 := by
  unfold tailWord_7993426
  simp only [CollatzResearch.WordTrace]
  refine ⟨72886049384797561329824033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194362798359460163546197421 72886049384797561329824033)
  ·
    refine ⟨54664537038598170997368025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72886049384797561329824033 54664537038598170997368025)
    ·
      refine ⟨40998402778948628248026019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54664537038598170997368025 40998402778948628248026019)
      ·
        refine ⟨61497604168422942372039029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40998402778948628248026019 61497604168422942372039029)
        ·
          refine ⟨5765400390789650847378659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61497604168422942372039029 5765400390789650847378659)
          ·
            refine ⟨8648100586184476271067989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765400390789650847378659 8648100586184476271067989)
            ·
              refine ⟨50672464372174665650789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8648100586184476271067989 50672464372174665650789)
              ·
                rfl

theorem cell23_7993426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 9].length) (baseStart_7993426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993426 prefixEnd_7993426 := by exact prefixLift 7993426
  have htrace : WordTrace (prefixWord ++ tailWord_7993426) baseStart_7993426 baseEnd_7993426 := by
    simpa [prefixWord, tailWord_7993426, baseEnd_7993426] using wordTrace_append hprefix tailTrace_7993426
  have hstable : (prefixWord ++ tailWord_7993426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993426).length < 2 ^ (prefixWord ++ tailWord_7993426).sum := by decide
  have hdescent : baseEnd_7993426 < baseStart_7993426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993437 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7993437 : Nat := 118140960795 + 7993437 * 2 ^ 59
def prefixEnd_7993437 : Nat := 4983230072969 + 3 ^ 40 * 7993437 * 2
def baseEnd_7993437 : Nat := 4104475262433347374676359

theorem tailTrace_7993437 : CollatzResearch.WordTrace tailWord_7993437 prefixEnd_7993437 4104475262433347374676359 := by
  unfold tailWord_7993437
  simp only [CollatzResearch.WordTrace]
  refine ⟨291544598742150394197946565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194363065828100262798631043 291544598742150394197946565)
  ·
    refine ⟨54664612264153198912114981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291544598742150394197946565 54664612264153198912114981)
    ·
      refine ⟨10249614799528724796021559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54664612264153198912114981 10249614799528724796021559)
      ·
        refine ⟨15374422199293087194032339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10249614799528724796021559 15374422199293087194032339)
        ·
          refine ⟨23061633298939630791048509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15374422199293087194032339 23061633298939630791048509)
          ·
            refine ⟨8648112487102361546643191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23061633298939630791048509 8648112487102361546643191)
            ·
              refine ⟨12972168730653542319964787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648112487102361546643191 12972168730653542319964787)
              ·
                refine ⟨19458253095980313479947181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12972168730653542319964787 19458253095980313479947181)
                ·
                  refine ⟨7296844910992617554980193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19458253095980313479947181 7296844910992617554980193)
                  ·
                    refine ⟨5472633683244463166235145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296844910992617554980193 5472633683244463166235145)
                    ·
                      refine ⟨4104475262433347374676359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472633683244463166235145 4104475262433347374676359)
                      ·
                        rfl

theorem cell23_7993437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7993437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993437 prefixEnd_7993437 := by exact prefixLift 7993437
  have htrace : WordTrace (prefixWord ++ tailWord_7993437) baseStart_7993437 baseEnd_7993437 := by
    simpa [prefixWord, tailWord_7993437, baseEnd_7993437] using wordTrace_append hprefix tailTrace_7993437
  have hstable : (prefixWord ++ tailWord_7993437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993437).length < 2 ^ (prefixWord ++ tailWord_7993437).sum := by decide
  have hdescent : baseEnd_7993437 < baseStart_7993437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993453 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_7993453 : Nat := 118140960795 + 7993453 * 2 ^ 59
def prefixEnd_7993453 : Nat := 4983230072969 + 3 ^ 40 * 7993453 * 2
def baseEnd_7993453 : Nat := 4104483478123819312076285

theorem tailTrace_7993453 : CollatzResearch.WordTrace tailWord_7993453 prefixEnd_7993453 4104483478123819312076285 := by
  unfold tailWord_7993453
  simp only [CollatzResearch.WordTrace]
  refine ⟨291545182310092428930529013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194363454873394952620352675 291545182310092428930529013)
  ·
    refine ⟨27332360841571165212237095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291545182310092428930529013 27332360841571165212237095)
    ·
      refine ⟨40998541262356747818355643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27332360841571165212237095 40998541262356747818355643)
      ·
        refine ⟨61497811893535121727533465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40998541262356747818355643 61497811893535121727533465)
        ·
          refine ⟨46123358920151341295650099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61497811893535121727533465 46123358920151341295650099)
          ·
            refine ⟨69185038380227011943475149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46123358920151341295650099 69185038380227011943475149)
            ·
              refine ⟨25944389392585129478803181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69185038380227011943475149 25944389392585129478803181)
              ·
                refine ⟨9729146022219423554551193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25944389392585129478803181 9729146022219423554551193)
                ·
                  refine ⟨7296859516664567665913395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729146022219423554551193 7296859516664567665913395)
                  ·
                    refine ⟨10945289274996851498870093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7296859516664567665913395 10945289274996851498870093)
                    ·
                      refine ⟨4104483478123819312076285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10945289274996851498870093 4104483478123819312076285)
                      ·
                        rfl

theorem cell23_7993453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_7993453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993453 prefixEnd_7993453 := by exact prefixLift 7993453
  have htrace : WordTrace (prefixWord ++ tailWord_7993453) baseStart_7993453 baseEnd_7993453 := by
    simpa [prefixWord, tailWord_7993453, baseEnd_7993453] using wordTrace_append hprefix tailTrace_7993453
  have hstable : (prefixWord ++ tailWord_7993453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993453).length < 2 ^ (prefixWord ++ tailWord_7993453).sum := by decide
  have hdescent : baseEnd_7993453 < baseStart_7993453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993463 : List Nat := [1, 1, 3, 1, 1, 5, 3, 2, 1, 3, 2]
def baseStart_7993463 : Nat := 118140960795 + 7993463 * 2 ^ 59
def prefixEnd_7993463 : Nat := 4983230072969 + 3 ^ 40 * 7993463 * 2
def baseEnd_7993463 : Nat := 4104488612930364272951239

theorem tailTrace_7993463 : CollatzResearch.WordTrace tailWord_7993463 prefixEnd_7993463 4104488612930364272951239 := by
  unfold tailWord_7993463
  simp only [CollatzResearch.WordTrace]
  refine ⟨291545547040056200638393043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194363698026704133758928695 291545547040056200638393043)
  ·
    refine ⟨437318320560084300957589565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291545547040056200638393043 437318320560084300957589565)
    ·
      refine ⟨163994370210031612859096087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437318320560084300957589565 163994370210031612859096087)
      ·
        refine ⟨245991555315047419288644131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163994370210031612859096087 245991555315047419288644131)
        ·
          refine ⟨368987332972571128932966197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245991555315047419288644131 368987332972571128932966197)
          ·
            refine ⟨34592562466178543337465581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368987332972571128932966197 34592562466178543337465581)
            ·
              refine ⟨12972210924816953751549593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34592562466178543337465581 12972210924816953751549593)
              ·
                refine ⟨9729158193612715313662195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12972210924816953751549593 9729158193612715313662195)
                ·
                  refine ⟨14593737290419072970493293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9729158193612715313662195 14593737290419072970493293)
                  ·
                    refine ⟨5472651483907152363934985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14593737290419072970493293 5472651483907152363934985)
                    ·
                      refine ⟨4104488612930364272951239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472651483907152363934985 4104488612930364272951239)
                      ·
                        rfl

theorem cell23_7993463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_7993463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993463 prefixEnd_7993463 := by exact prefixLift 7993463
  have htrace : WordTrace (prefixWord ++ tailWord_7993463) baseStart_7993463 baseEnd_7993463 := by
    simpa [prefixWord, tailWord_7993463, baseEnd_7993463] using wordTrace_append hprefix tailTrace_7993463
  have hstable : (prefixWord ++ tailWord_7993463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993463).length < 2 ^ (prefixWord ++ tailWord_7993463).sum := by decide
  have hdescent : baseEnd_7993463 < baseStart_7993463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993479 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_7993479 : Nat := 118140960795 + 7993479 * 2 ^ 59
def prefixEnd_7993479 : Nat := 4983230072969 + 3 ^ 40 * 7993479 * 2
def baseEnd_7993479 : Nat := 4104496828620836210351165

theorem tailTrace_7993479 : CollatzResearch.WordTrace tailWord_7993479 prefixEnd_7993479 4104496828620836210351165 := by
  unfold tailWord_7993479
  simp only [CollatzResearch.WordTrace]
  refine ⟨291546130607998235370975491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194364087071998823580650327 291546130607998235370975491)
  ·
    refine ⟨437319195911997353056463237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291546130607998235370975491 437319195911997353056463237)
    ·
      refine ⟨81997349233499503698086857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437319195911997353056463237 81997349233499503698086857)
      ·
        refine ⟨61498011925124627773565143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81997349233499503698086857 61498011925124627773565143)
        ·
          refine ⟨92247017887686941660347715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61498011925124627773565143 92247017887686941660347715)
          ·
            refine ⟨138370526831530412490521573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92247017887686941660347715 138370526831530412490521573)
            ·
              refine ⟨25944473780911952341972795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138370526831530412490521573 25944473780911952341972795)
              ·
                refine ⟨38916710671367928512959193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25944473780911952341972795 38916710671367928512959193)
                ·
                  refine ⟨29187533003525946384719395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38916710671367928512959193 29187533003525946384719395)
                  ·
                    refine ⟨43781299505288919577079093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29187533003525946384719395 43781299505288919577079093)
                    ·
                      refine ⟨4104496828620836210351165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43781299505288919577079093 4104496828620836210351165)
                      ·
                        rfl

theorem cell23_7993479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_7993479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993479 prefixEnd_7993479 := by exact prefixLift 7993479
  have htrace : WordTrace (prefixWord ++ tailWord_7993479) baseStart_7993479 baseEnd_7993479 := by
    simpa [prefixWord, tailWord_7993479, baseEnd_7993479] using wordTrace_append hprefix tailTrace_7993479
  have hstable : (prefixWord ++ tailWord_7993479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993479).length < 2 ^ (prefixWord ++ tailWord_7993479).sum := by decide
  have hdescent : baseEnd_7993479 < baseStart_7993479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993494 : List Nat := [5, 3, 2, 1, 2, 1, 1, 8]
def baseStart_7993494 : Nat := 118140960795 + 7993494 * 2 ^ 59
def prefixEnd_7993494 : Nat := 4983230072969 + 3 ^ 40 * 7993494 * 2
def baseEnd_7993494 : Nat := 152018686327061246357911

theorem tailTrace_7993494 : CollatzResearch.WordTrace tailWord_7993494 prefixEnd_7993494 152018686327061246357911 := by
  unfold tailWord_7993494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18221667356433993308298221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194364451801962595288514357 18221667356433993308298221)
  ·
    refine ⟨6833125258662747490611833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18221667356433993308298221 6833125258662747490611833)
    ·
      refine ⟨5124843943997060617958875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6833125258662747490611833 5124843943997060617958875)
      ·
        refine ⟨7687265915995590926938313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124843943997060617958875 7687265915995590926938313)
        ·
          refine ⟨5765449436996693195203735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7687265915995590926938313 5765449436996693195203735)
          ·
            refine ⟨8648174155495039792805603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765449436996693195203735 8648174155495039792805603)
            ·
              refine ⟨12972261233242559689208405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648174155495039792805603 12972261233242559689208405)
              ·
                refine ⟨152018686327061246357911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12972261233242559689208405 152018686327061246357911)
                ·
                  rfl

theorem cell23_7993494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_7993494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993494 prefixEnd_7993494 := by exact prefixLift 7993494
  have htrace : WordTrace (prefixWord ++ tailWord_7993494) baseStart_7993494 baseEnd_7993494 := by
    simpa [prefixWord, tailWord_7993494, baseEnd_7993494] using wordTrace_append hprefix tailTrace_7993494
  have hstable : (prefixWord ++ tailWord_7993494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993494).length < 2 ^ (prefixWord ++ tailWord_7993494).sum := by decide
  have hdescent : baseEnd_7993494 < baseStart_7993494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993506 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7993506 : Nat := 118140960795 + 7993506 * 2 ^ 59
def prefixEnd_7993506 : Nat := 4983230072969 + 3 ^ 40 * 7993506 * 2
def baseEnd_7993506 : Nat := 4104510692598507604713541

theorem tailTrace_7993506 : CollatzResearch.WordTrace tailWord_7993506 prefixEnd_7993506 4104510692598507604713541 := by
  unfold tailWord_7993506
  simp only [CollatzResearch.WordTrace]
  refine ⟨72886778844725104745552093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194364743585933612654805581 72886778844725104745552093)
  ·
    refine ⟨27332542066771914279582035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72886778844725104745552093 27332542066771914279582035)
    ·
      refine ⟨40998813100157871419373053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27332542066771914279582035 40998813100157871419373053)
      ·
        refine ⟨15374554912559201782264895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40998813100157871419373053 15374554912559201782264895)
        ·
          refine ⟨23061832368838802673397343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15374554912559201782264895 23061832368838802673397343)
          ·
            refine ⟨34592748553258204010096015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23061832368838802673397343 34592748553258204010096015)
            ·
              refine ⟨51889122829887306015144023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34592748553258204010096015 51889122829887306015144023)
              ·
                refine ⟨77833684244830959022716035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51889122829887306015144023 77833684244830959022716035)
                ·
                  refine ⟨116750526367246438534074053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77833684244830959022716035 116750526367246438534074053)
                  ·
                    refine ⟨21890723693858707225138885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116750526367246438534074053 21890723693858707225138885)
                    ·
                      refine ⟨4104510692598507604713541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21890723693858707225138885 4104510692598507604713541)
                      ·
                        rfl

theorem cell23_7993506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7993506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993506 prefixEnd_7993506 := by exact prefixLift 7993506
  have htrace : WordTrace (prefixWord ++ tailWord_7993506) baseStart_7993506 baseEnd_7993506 := by
    simpa [prefixWord, tailWord_7993506, baseEnd_7993506] using wordTrace_append hprefix tailTrace_7993506
  have hstable : (prefixWord ++ tailWord_7993506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993506).length < 2 ^ (prefixWord ++ tailWord_7993506).sum := by decide
  have hdescent : baseEnd_7993506 < baseStart_7993506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993529 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 1, 7]
def baseStart_7993529 : Nat := 118140960795 + 7993529 * 2 ^ 59
def prefixEnd_7993529 : Nat := 4983230072969 + 3 ^ 40 * 7993529 * 2
def baseEnd_7993529 : Nat := 1368174167551187004908645

theorem tailTrace_7993529 : CollatzResearch.WordTrace tailWord_7993529 prefixEnd_7993529 1368174167551187004908645 := by
  unfold tailWord_7993529
  simp only [CollatzResearch.WordTrace]
  refine ⟨291547954257817093910295641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194365302838544729273530427 291547954257817093910295641)
  ·
    refine ⟨218660965693362820432721731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291547954257817093910295641 218660965693362820432721731)
    ·
      refine ⟨327991448540044230649082597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218660965693362820432721731 327991448540044230649082597)
      ·
        refine ⟨61498396601258293246702987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327991448540044230649082597 61498396601258293246702987)
        ·
          refine ⟨92247594901887439870054481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61498396601258293246702987 92247594901887439870054481)
          ·
            refine ⟨69185696176415579902540861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92247594901887439870054481 69185696176415579902540861)
            ·
              refine ⟨25944636066155842463452823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69185696176415579902540861 25944636066155842463452823)
              ·
                refine ⟨38916954099233763695179235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25944636066155842463452823 38916954099233763695179235)
                ·
                  refine ⟨58375431148850645542768853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38916954099233763695179235 58375431148850645542768853)
                  ·
                    refine ⟨1368174167551187004908645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58375431148850645542768853 1368174167551187004908645)
                    ·
                      rfl

theorem cell23_7993529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_7993529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993529 prefixEnd_7993529 := by exact prefixLift 7993529
  have htrace : WordTrace (prefixWord ++ tailWord_7993529) baseStart_7993529 baseEnd_7993529 := by
    simpa [prefixWord, tailWord_7993529, baseEnd_7993529] using wordTrace_append hprefix tailTrace_7993529
  have hstable : (prefixWord ++ tailWord_7993529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993529).length < 2 ^ (prefixWord ++ tailWord_7993529).sum := by decide
  have hdescent : baseEnd_7993529 < baseStart_7993529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993579 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4]
def baseStart_7993579 : Nat := 118140960795 + 7993579 * 2 ^ 59
def prefixEnd_7993579 : Nat := 4983230072969 + 3 ^ 40 * 7993579 * 2
def baseEnd_7993579 : Nat := 4104548176686285819100705

theorem tailTrace_7993579 : CollatzResearch.WordTrace tailWord_7993579 prefixEnd_7993579 4104548176686285819100705 := by
  unfold tailWord_7993579
  simp only [CollatzResearch.WordTrace]
  refine ⟨291549777907635952449615791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194366518605090634966410527 291549777907635952449615791)
  ·
    refine ⟨437324666861453928674423687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291549777907635952449615791 437324666861453928674423687)
    ·
      refine ⟨655987000292180893011635531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437324666861453928674423687 655987000292180893011635531)
      ·
        refine ⟨983980500438271339517453297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655987000292180893011635531 983980500438271339517453297)
        ·
          refine ⟨737985375328703504638089973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 983980500438271339517453297 737985375328703504638089973)
          ·
            refine ⟨69186128937065953559820935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 737985375328703504638089973 69186128937065953559820935)
            ·
              refine ⟨103779193405598930339731403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69186128937065953559820935 103779193405598930339731403)
              ·
                refine ⟨155668790108398395509597105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103779193405598930339731403 155668790108398395509597105)
                ·
                  refine ⟨116751592581298796632197829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155668790108398395509597105 116751592581298796632197829)
                  ·
                    refine ⟨21890923608993524368537093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116751592581298796632197829 21890923608993524368537093)
                    ·
                      refine ⟨4104548176686285819100705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21890923608993524368537093 4104548176686285819100705)
                      ·
                        rfl

theorem cell23_7993579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_7993579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993579 prefixEnd_7993579 := by exact prefixLift 7993579
  have htrace : WordTrace (prefixWord ++ tailWord_7993579) baseStart_7993579 baseEnd_7993579 := by
    simpa [prefixWord, tailWord_7993579, baseEnd_7993579] using wordTrace_append hprefix tailTrace_7993579
  have hstable : (prefixWord ++ tailWord_7993579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993579).length < 2 ^ (prefixWord ++ tailWord_7993579).sum := by decide
  have hdescent : baseEnd_7993579 < baseStart_7993579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993593 : List Nat := [1, 2, 1, 3, 1, 1, 2, 7, 1, 4]
def baseStart_7993593 : Nat := 118140960795 + 7993593 * 2 ^ 59
def prefixEnd_7993593 : Nat := 4983230072969 + 3 ^ 40 * 7993593 * 2
def baseEnd_7993593 : Nat := 1368185121805149588108547

theorem tailTrace_7993593 : CollatzResearch.WordTrace tailWord_7993593 prefixEnd_7993593 1368185121805149588108547 := by
  unfold tailWord_7993593
  simp only [CollatzResearch.WordTrace]
  refine ⟨291550288529585232840625433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194366859019723488560416955 291550288529585232840625433)
  ·
    refine ⟨218662716397188924630469075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291550288529585232840625433 218662716397188924630469075)
    ·
      refine ⟨327994074595783386945703613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218662716397188924630469075 327994074595783386945703613)
      ·
        refine ⟨122997777973418770104638855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327994074595783386945703613 122997777973418770104638855)
        ·
          refine ⟨184496666960128155156958283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122997777973418770104638855 184496666960128155156958283)
          ·
            refine ⟨276745000440192232735437425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184496666960128155156958283 276745000440192232735437425)
            ·
              refine ⟨207558750330144174551578069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276745000440192232735437425 207558750330144174551578069)
              ·
                refine ⟨4864658210862754091052611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207558750330144174551578069 4864658210862754091052611)
                ·
                  refine ⟨7296987316294131136578917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864658210862754091052611 7296987316294131136578917)
                  ·
                    refine ⟨1368185121805149588108547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7296987316294131136578917 1368185121805149588108547)
                    ·
                      rfl

theorem cell23_7993593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 4].length) (baseStart_7993593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993593 prefixEnd_7993593 := by exact prefixLift 7993593
  have htrace : WordTrace (prefixWord ++ tailWord_7993593) baseStart_7993593 baseEnd_7993593 := by
    simpa [prefixWord, tailWord_7993593, baseEnd_7993593] using wordTrace_append hprefix tailTrace_7993593
  have hstable : (prefixWord ++ tailWord_7993593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993593).length < 2 ^ (prefixWord ++ tailWord_7993593).sum := by decide
  have hdescent : baseEnd_7993593 < baseStart_7993593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993623 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 6]
def baseStart_7993623 : Nat := 118140960795 + 7993623 * 2 ^ 59
def prefixEnd_7993623 : Nat := 4983230072969 + 3 ^ 40 * 7993623 * 2
def baseEnd_7993623 : Nat := 456063418870564849661167

theorem tailTrace_7993623 : CollatzResearch.WordTrace tailWord_7993623 prefixEnd_7993623 456063418870564849661167 := by
  unfold tailWord_7993623
  simp only [CollatzResearch.WordTrace]
  refine ⟨291551382719476547964217523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194367588479651031976145015 291551382719476547964217523)
  ·
    refine ⟨437327074079214821946326285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291551382719476547964217523 437327074079214821946326285)
    ·
      refine ⟨163997652779705558229872357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437327074079214821946326285 163997652779705558229872357)
      ·
        refine ⟨30749559896194792168101067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163997652779705558229872357 30749559896194792168101067)
        ·
          refine ⟨46124339844292188252151601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30749559896194792168101067 46124339844292188252151601)
          ·
            refine ⟨34593254883219141189113701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46124339844292188252151601 34593254883219141189113701)
            ·
              refine ⟨6486235290603588972958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34593254883219141189113701 6486235290603588972958819)
              ·
                refine ⟨9729352935905383459438229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486235290603588972958819 9729352935905383459438229)
                ·
                  refine ⟨456063418870564849661167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9729352935905383459438229 456063418870564849661167)
                  ·
                    rfl

theorem cell23_7993623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 6].length) (baseStart_7993623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993623 prefixEnd_7993623 := by exact prefixLift 7993623
  have htrace : WordTrace (prefixWord ++ tailWord_7993623) baseStart_7993623 baseEnd_7993623 := by
    simpa [prefixWord, tailWord_7993623, baseEnd_7993623] using wordTrace_append hprefix tailTrace_7993623
  have hstable : (prefixWord ++ tailWord_7993623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993623).length < 2 ^ (prefixWord ++ tailWord_7993623).sum := by decide
  have hdescent : baseEnd_7993623 < baseStart_7993623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993633 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_7993633 : Nat := 118140960795 + 7993633 * 2 ^ 59
def prefixEnd_7993633 : Nat := 4983230072969 + 3 ^ 40 * 7993633 * 2
def baseEnd_7993633 : Nat := 4104575904641628607825457

theorem tailTrace_7993633 : CollatzResearch.WordTrace tailWord_7993633 prefixEnd_7993633 4104575904641628607825457 := by
  unfold tailWord_7993633
  simp only [CollatzResearch.WordTrace]
  refine ⟨291551747449440319672081553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194367831632960213114721035 291551747449440319672081553)
  ·
    refine ⟨218663810587080239754061165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291551747449440319672081553 218663810587080239754061165)
    ·
      refine ⟨81998928970155089907772937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218663810587080239754061165 81998928970155089907772937)
      ·
        refine ⟨61499196727616317430829703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81998928970155089907772937 61499196727616317430829703)
        ·
          refine ⟨92248795091424476146244555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61499196727616317430829703 92248795091424476146244555)
          ·
            refine ⟨138373192637136714219366833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92248795091424476146244555 138373192637136714219366833)
            ·
              refine ⟨103779894477852535664525125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138373192637136714219366833 103779894477852535664525125)
              ·
                refine ⟨19458730214597350437098461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103779894477852535664525125 19458730214597350437098461)
                ·
                  refine ⟨7297023830474006413911923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19458730214597350437098461 7297023830474006413911923)
                  ·
                    refine ⟨10945535745711009620867885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7297023830474006413911923 10945535745711009620867885)
                    ·
                      refine ⟨4104575904641628607825457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10945535745711009620867885 4104575904641628607825457)
                      ·
                        rfl

theorem cell23_7993633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_7993633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993633 prefixEnd_7993633 := by exact prefixLift 7993633
  have htrace : WordTrace (prefixWord ++ tailWord_7993633) baseStart_7993633 baseEnd_7993633 := by
    simpa [prefixWord, tailWord_7993633, baseEnd_7993633] using wordTrace_append hprefix tailTrace_7993633
  have hstable : (prefixWord ++ tailWord_7993633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993633).length < 2 ^ (prefixWord ++ tailWord_7993633).sum := by decide
  have hdescent : baseEnd_7993633 < baseStart_7993633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993667 : List Nat := [1, 1, 1, 3, 1, 3, 6, 2, 1, 1, 3]
def baseStart_7993667 : Nat := 118140960795 + 7993667 * 2 ^ 59
def prefixEnd_7993667 : Nat := 4983230072969 + 3 ^ 40 * 7993667 * 2
def baseEnd_7993667 : Nat := 4104593362983881474800301

theorem tailTrace_7993667 : CollatzResearch.WordTrace tailWord_7993667 prefixEnd_7993667 4104593362983881474800301 := by
  unfold tailWord_7993667
  simp only [CollatzResearch.WordTrace]
  refine ⟨291552987531317143478819255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194368658354211428985879503 291552987531317143478819255)
  ·
    refine ⟨437329481296975715218228883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291552987531317143478819255 437329481296975715218228883)
    ·
      refine ⟨655994221945463572827343325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437329481296975715218228883 655994221945463572827343325)
      ·
        refine ⟨245997833229548839810253747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655994221945463572827343325 245997833229548839810253747)
        ·
          refine ⟨368996749844323259715380621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245997833229548839810253747 368996749844323259715380621)
          ·
            refine ⟨138373781191621222393267733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368996749844323259715380621 138373781191621222393267733)
            ·
              refine ⟨6486270993357244799684425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138373781191621222393267733 6486270993357244799684425)
              ·
                refine ⟨4864703245017933599763319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6486270993357244799684425 4864703245017933599763319)
                ·
                  refine ⟨7297054867526900399644979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864703245017933599763319 7297054867526900399644979)
                  ·
                    refine ⟨10945582301290350599467469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7297054867526900399644979 10945582301290350599467469)
                    ·
                      refine ⟨4104593362983881474800301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10945582301290350599467469 4104593362983881474800301)
                      ·
                        rfl

theorem cell23_7993667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_7993667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993667 prefixEnd_7993667 := by exact prefixLift 7993667
  have htrace : WordTrace (prefixWord ++ tailWord_7993667) baseStart_7993667 baseEnd_7993667 := by
    simpa [prefixWord, tailWord_7993667, baseEnd_7993667] using wordTrace_append hprefix tailTrace_7993667
  have hstable : (prefixWord ++ tailWord_7993667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993667).length < 2 ^ (prefixWord ++ tailWord_7993667).sum := by decide
  have hdescent : baseEnd_7993667 < baseStart_7993667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993676 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_7993676 : Nat := 118140960795 + 7993676 * 2 ^ 59
def prefixEnd_7993676 : Nat := 4983230072969 + 3 ^ 40 * 7993676 * 2
def baseEnd_7993676 : Nat := 4104597984309771939587759

theorem tailTrace_7993676 : CollatzResearch.WordTrace tailWord_7993676 prefixEnd_7993676 4104597984309771939587759 := by
  unfold tailWord_7993676
  simp only [CollatzResearch.WordTrace]
  refine ⟨145776657894142269007948441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194368877192189692010597921 145776657894142269007948441)
  ·
    refine ⟨109332493420606701755961331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145776657894142269007948441 109332493420606701755961331)
    ·
      refine ⟨163998740130910052633941997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109332493420606701755961331 163998740130910052633941997)
      ·
        refine ⟨61499527549091269737728249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163998740130910052633941997 61499527549091269737728249)
        ·
          refine ⟨46124645661818452303296187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61499527549091269737728249 46124645661818452303296187)
          ·
            refine ⟨69186968492727678454944281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46124645661818452303296187 69186968492727678454944281)
            ·
              refine ⟨51890226369545758841208211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69186968492727678454944281 51890226369545758841208211)
              ·
                refine ⟨77835339554318638261812317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51890226369545758841208211 77835339554318638261812317)
                ·
                  refine ⟨29188252332869489348179619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77835339554318638261812317 29188252332869489348179619)
                  ·
                    refine ⟨43782378499304234022269429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29188252332869489348179619 43782378499304234022269429)
                    ·
                      refine ⟨4104597984309771939587759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43782378499304234022269429 4104597984309771939587759)
                      ·
                        rfl

theorem cell23_7993676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_7993676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993676 prefixEnd_7993676 := by exact prefixLift 7993676
  have htrace : WordTrace (prefixWord ++ tailWord_7993676) baseStart_7993676 baseEnd_7993676 := by
    simpa [prefixWord, tailWord_7993676, baseEnd_7993676] using wordTrace_append hprefix tailTrace_7993676
  have hstable : (prefixWord ++ tailWord_7993676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993676).length < 2 ^ (prefixWord ++ tailWord_7993676).sum := by decide
  have hdescent : baseEnd_7993676 < baseStart_7993676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993679 : List Nat := [1, 1, 2, 1, 1, 2, 1, 14]
def baseStart_7993679 : Nat := 118140960795 + 7993679 * 2 ^ 59
def prefixEnd_7993679 : Nat := 4983230072969 + 3 ^ 40 * 7993679 * 2
def baseEnd_7993679 : Nat := 152022204620434645475935

theorem tailTrace_7993679 : CollatzResearch.WordTrace tailWord_7993679 prefixEnd_7993679 152022204620434645475935 := by
  unfold tailWord_7993679
  simp only [CollatzResearch.WordTrace]
  refine ⟨291553425207273669528256091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194368950138182446352170727 291553425207273669528256091)
  ·
    refine ⟨437330137810910504292384137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291553425207273669528256091 437330137810910504292384137)
    ·
      refine ⟨327997603358182878219288103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437330137810910504292384137 327997603358182878219288103)
      ·
        refine ⟨491996405037274317328932155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327997603358182878219288103 491996405037274317328932155)
        ·
          refine ⟨737994607555911475993398233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491996405037274317328932155 737994607555911475993398233)
          ·
            refine ⟨553495955666933606995048675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737994607555911475993398233 553495955666933606995048675)
            ·
              refine ⟨830243933500400410492573013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553495955666933606995048675 830243933500400410492573013)
              ·
                refine ⟨152022204620434645475935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 830243933500400410492573013 152022204620434645475935)
                ·
                  rfl

theorem cell23_7993679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 14].length) (baseStart_7993679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993679 prefixEnd_7993679 := by exact prefixLift 7993679
  have htrace : WordTrace (prefixWord ++ tailWord_7993679) baseStart_7993679 baseEnd_7993679 := by
    simpa [prefixWord, tailWord_7993679, baseEnd_7993679] using wordTrace_append hprefix tailTrace_7993679
  have hstable : (prefixWord ++ tailWord_7993679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993679).length < 2 ^ (prefixWord ++ tailWord_7993679).sum := by decide
  have hdescent : baseEnd_7993679 < baseStart_7993679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993703 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_7993703 : Nat := 118140960795 + 7993703 * 2 ^ 59
def prefixEnd_7993703 : Nat := 4983230072969 + 3 ^ 40 * 7993703 * 2
def baseEnd_7993703 : Nat := 4104611848287443333950135

theorem tailTrace_7993703 : CollatzResearch.WordTrace tailWord_7993703 prefixEnd_7993703 4104611848287443333950135 := by
  unfold tailWord_7993703
  simp only [CollatzResearch.WordTrace]
  refine ⟨291554300559186721627129763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194369533706124481084753175 291554300559186721627129763)
  ·
    refine ⟨437331450838780082440694645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291554300559186721627129763 437331450838780082440694645)
    ·
      refine ⟨40999823516135632728815123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 437331450838780082440694645 40999823516135632728815123)
      ·
        refine ⟨61499735274203449093222685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40999823516135632728815123 61499735274203449093222685)
        ·
          refine ⟨23062400727826293409958507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61499735274203449093222685 23062400727826293409958507)
          ·
            refine ⟨34593601091739440114937761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23062400727826293409958507 34593601091739440114937761)
            ·
              refine ⟨25945200818804580086203321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34593601091739440114937761 25945200818804580086203321)
              ·
                refine ⟨19458900614103435064652491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25945200818804580086203321 19458900614103435064652491)
                ·
                  refine ⟨29188350921155152596978737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19458900614103435064652491 29188350921155152596978737)
                  ·
                    refine ⟨21891263190866364447734053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29188350921155152596978737 21891263190866364447734053)
                    ·
                      refine ⟨4104611848287443333950135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21891263190866364447734053 4104611848287443333950135)
                      ·
                        rfl

theorem cell23_7993703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_7993703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993703 prefixEnd_7993703 := by exact prefixLift 7993703
  have htrace : WordTrace (prefixWord ++ tailWord_7993703) baseStart_7993703 baseEnd_7993703 := by
    simpa [prefixWord, tailWord_7993703, baseEnd_7993703] using wordTrace_append hprefix tailTrace_7993703
  have hstable : (prefixWord ++ tailWord_7993703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993703).length < 2 ^ (prefixWord ++ tailWord_7993703).sum := by decide
  have hdescent : baseEnd_7993703 < baseStart_7993703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993717 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7993717 : Nat := 118140960795 + 7993717 * 2 ^ 59
def prefixEnd_7993717 : Nat := 4983230072969 + 3 ^ 40 * 7993717 * 2
def baseEnd_7993717 : Nat := 1368206345672202093058357

theorem tailTrace_7993717 : CollatzResearch.WordTrace tailWord_7993717 prefixEnd_7993717 1368206345672202093058357 := by
  unfold tailWord_7993717
  simp only [CollatzResearch.WordTrace]
  refine ⟨291554811181136002018139405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194369874120757334678759603 291554811181136002018139405)
  ·
    refine ⟨109333054192926000756802277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291554811181136002018139405 109333054192926000756802277)
    ·
      refine ⟨20499947661173625141900427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109333054192926000756802277 20499947661173625141900427)
      ·
        refine ⟨30749921491760437712850641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20499947661173625141900427 30749921491760437712850641)
        ·
          refine ⟨23062441118820328284637981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30749921491760437712850641 23062441118820328284637981)
          ·
            refine ⟨8648415419557623106739243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23062441118820328284637981 8648415419557623106739243)
            ·
              refine ⟨12972623129336434660108865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648415419557623106739243 12972623129336434660108865)
              ·
                refine ⟨9729467347002325995081649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12972623129336434660108865 9729467347002325995081649)
                ·
                  refine ⟨7297100510251744496311237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729467347002325995081649 7297100510251744496311237)
                  ·
                    refine ⟨1368206345672202093058357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7297100510251744496311237 1368206345672202093058357)
                    ·
                      rfl

theorem cell23_7993717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7993717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993717 prefixEnd_7993717 := by exact prefixLift 7993717
  have htrace : WordTrace (prefixWord ++ tailWord_7993717) baseStart_7993717 baseEnd_7993717 := by
    simpa [prefixWord, tailWord_7993717, baseEnd_7993717] using wordTrace_append hprefix tailTrace_7993717
  have hstable : (prefixWord ++ tailWord_7993717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993717).length < 2 ^ (prefixWord ++ tailWord_7993717).sum := by decide
  have hdescent : baseEnd_7993717 < baseStart_7993717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993740 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_7993740 : Nat := 118140960795 + 7993740 * 2 ^ 59
def prefixEnd_7993740 : Nat := 4983230072969 + 3 ^ 40 * 7993740 * 2
def baseEnd_7993740 : Nat := 4104630847071659689187465

theorem tailTrace_7993740 : CollatzResearch.WordTrace tailWord_7993740 prefixEnd_7993740 4104630847071659689187465 := by
  unfold tailWord_7993740
  simp only [CollatzResearch.WordTrace]
  refine ⟨145777825030026338473113337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194370433373368451297484449 145777825030026338473113337)
  ·
    refine ⟨109333368772519753854835003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145777825030026338473113337 109333368772519753854835003)
    ·
      refine ⟨164000053158779630782252505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109333368772519753854835003 164000053158779630782252505)
      ·
        refine ⟨123000039869084723086689379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164000053158779630782252505 123000039869084723086689379)
        ·
          refine ⟨184500059803627084630034069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123000039869084723086689379 184500059803627084630034069)
          ·
            refine ⟨8648440303295019592032847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184500059803627084630034069 8648440303295019592032847)
            ·
              refine ⟨12972660454942529388049271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648440303295019592032847 12972660454942529388049271)
              ·
                refine ⟨19458990682413794082073907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12972660454942529388049271 19458990682413794082073907)
                ·
                  refine ⟨29188486023620691123110861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19458990682413794082073907 29188486023620691123110861)
                  ·
                    refine ⟨10945682258857759171166573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29188486023620691123110861 10945682258857759171166573)
                    ·
                      refine ⟨4104630847071659689187465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10945682258857759171166573 4104630847071659689187465)
                      ·
                        rfl

theorem cell23_7993740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_7993740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993740 prefixEnd_7993740 := by exact prefixLift 7993740
  have htrace : WordTrace (prefixWord ++ tailWord_7993740) baseStart_7993740 baseEnd_7993740 := by
    simpa [prefixWord, tailWord_7993740, baseEnd_7993740] using wordTrace_append hprefix tailTrace_7993740
  have hstable : (prefixWord ++ tailWord_7993740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993740).length < 2 ^ (prefixWord ++ tailWord_7993740).sum := by decide
  have hdescent : baseEnd_7993740 < baseStart_7993740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993758 : List Nat := [4, 3, 1, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7993758 : Nat := 118140960795 + 7993758 * 2 ^ 59
def prefixEnd_7993758 : Nat := 4983230072969 + 3 ^ 40 * 7993758 * 2
def baseEnd_7993758 : Nat := 4104640089723440618762383

theorem tailTrace_7993758 : CollatzResearch.WordTrace tailWord_7993758 prefixEnd_7993758 4104640089723440618762383 := by
  unfold tailWord_7993758
  simp only [CollatzResearch.WordTrace]
  refine ⟨36444538321748433252547741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194370871049324977346921285 36444538321748433252547741)
  ·
    refine ⟨13666701870655662469705403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36444538321748433252547741 13666701870655662469705403)
    ·
      refine ⟨20500052805983493704558105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13666701870655662469705403 20500052805983493704558105)
      ·
        refine ⟨15375039604487620278418579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20500052805983493704558105 15375039604487620278418579)
        ·
          refine ⟨23062559406731430417627869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15375039604487620278418579 23062559406731430417627869)
          ·
            refine ⟨8648459777524286406610451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23062559406731430417627869 8648459777524286406610451)
            ·
              refine ⟨12972689666286429609915677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648459777524286406610451 12972689666286429609915677)
              ·
                refine ⟨4864758624857411103718379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12972689666286429609915677 4864758624857411103718379)
                ·
                  refine ⟨7297137937286116655577569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864758624857411103718379 7297137937286116655577569)
                  ·
                    refine ⟨5472853452964587491683177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7297137937286116655577569 5472853452964587491683177)
                    ·
                      refine ⟨4104640089723440618762383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472853452964587491683177 4104640089723440618762383)
                      ·
                        rfl

theorem cell23_7993758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7993758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993758 prefixEnd_7993758 := by exact prefixLift 7993758
  have htrace : WordTrace (prefixWord ++ tailWord_7993758) baseStart_7993758 baseEnd_7993758 := by
    simpa [prefixWord, tailWord_7993758, baseEnd_7993758] using wordTrace_append hprefix tailTrace_7993758
  have hstable : (prefixWord ++ tailWord_7993758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993758).length < 2 ^ (prefixWord ++ tailWord_7993758).sum := by decide
  have hdescent : baseEnd_7993758 < baseStart_7993758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993767 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_7993767 : Nat := 118140960795 + 7993767 * 2 ^ 59
def prefixEnd_7993767 : Nat := 4983230072969 + 3 ^ 40 * 7993767 * 2
def baseEnd_7993767 : Nat := 4104644711049331083549841

theorem tailTrace_7993767 : CollatzResearch.WordTrace tailWord_7993767 prefixEnd_7993767 4104644711049331083549841 := by
  unfold tailWord_7993767
  simp only [CollatzResearch.WordTrace]
  refine ⟨291556634830954860557459555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194371089887303240371639703 291556634830954860557459555)
  ·
    refine ⟨437334952246432290836189333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291556634830954860557459555 437334952246432290836189333)
    ·
      refine ⟨20500075886551513632946375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 437334952246432290836189333 20500075886551513632946375)
      ·
        refine ⟨30750113829827270449419563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20500075886551513632946375 30750113829827270449419563)
        ·
          refine ⟨46125170744740905674129345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30750113829827270449419563 46125170744740905674129345)
          ·
            refine ⟨34593878058555679255597009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46125170744740905674129345 34593878058555679255597009)
            ·
              refine ⟨25945408543916759441697757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34593878058555679255597009 25945408543916759441697757)
              ·
                refine ⟨9729528203968784790636659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25945408543916759441697757 9729528203968784790636659)
                ·
                  refine ⟨14594292305953177185954989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9729528203968784790636659 14594292305953177185954989)
                  ·
                    refine ⟨5472859614732441444733121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14594292305953177185954989 5472859614732441444733121)
                    ·
                      refine ⟨4104644711049331083549841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5472859614732441444733121 4104644711049331083549841)
                      ·
                        rfl

theorem cell23_7993767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_7993767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993767 prefixEnd_7993767 := by exact prefixLift 7993767
  have htrace : WordTrace (prefixWord ++ tailWord_7993767) baseStart_7993767 baseEnd_7993767 := by
    simpa [prefixWord, tailWord_7993767, baseEnd_7993767] using wordTrace_append hprefix tailTrace_7993767
  have hstable : (prefixWord ++ tailWord_7993767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993767).length < 2 ^ (prefixWord ++ tailWord_7993767).sum := by decide
  have hdescent : baseEnd_7993767 < baseStart_7993767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993837 : List Nat := [1, 5, 1, 3, 1, 2, 1, 4, 5]
def baseStart_7993837 : Nat := 118140960795 + 7993837 * 2 ^ 59
def prefixEnd_7993837 : Nat := 4983230072969 + 3 ^ 40 * 7993837 * 2
def baseEnd_7993837 : Nat := 456075628299460645519391

theorem tailTrace_7993837 : CollatzResearch.WordTrace tailWord_7993837 prefixEnd_7993837 456075628299460645519391 := by
  unfold tailWord_7993837
  simp only [CollatzResearch.WordTrace]
  refine ⟨291559187940701262512507765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194372791960467508341671843 291559187940701262512507765)
  ·
    refine ⟨27333673869440743360547603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291559187940701262512507765 27333673869440743360547603)
    ·
      refine ⟨41000510804161115040821405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27333673869440743360547603 41000510804161115040821405)
      ·
        refine ⟨15375191551560418140308027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41000510804161115040821405 15375191551560418140308027)
        ·
          refine ⟨23062787327340627210462041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15375191551560418140308027 23062787327340627210462041)
          ·
            refine ⟨17297090495505470407846531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23062787327340627210462041 17297090495505470407846531)
            ·
              refine ⟨25945635743258205611769797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17297090495505470407846531 25945635743258205611769797)
              ·
                refine ⟨4864806701860913552206837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25945635743258205611769797 4864806701860913552206837)
                ·
                  refine ⟨456075628299460645519391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4864806701860913552206837 456075628299460645519391)
                  ·
                    rfl

theorem cell23_7993837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_7993837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993837 prefixEnd_7993837 := by exact prefixLift 7993837
  have htrace : WordTrace (prefixWord ++ tailWord_7993837) baseStart_7993837 baseEnd_7993837 := by
    simpa [prefixWord, tailWord_7993837, baseEnd_7993837] using wordTrace_append hprefix tailTrace_7993837
  have hstable : (prefixWord ++ tailWord_7993837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993837).length < 2 ^ (prefixWord ++ tailWord_7993837).sum := by decide
  have hdescent : baseEnd_7993837 < baseStart_7993837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993853 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_7993853 : Nat := 118140960795 + 7993853 * 2 ^ 59
def prefixEnd_7993853 : Nat := 4983230072969 + 3 ^ 40 * 7993853 * 2
def baseEnd_7993853 : Nat := 4104688870385617747074445

theorem tailTrace_7993853 : CollatzResearch.WordTrace tailWord_7993853 prefixEnd_7993853 4104688870385617747074445 := by
  unfold tailWord_7993853
  simp only [CollatzResearch.WordTrace]
  refine ⟨291559771508643297245090213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194373181005762198163393475 291559771508643297245090213)
  ·
    refine ⟨54667457157870618233454415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291559771508643297245090213 54667457157870618233454415)
    ·
      refine ⟨82001185736805927350181623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54667457157870618233454415 82001185736805927350181623)
      ·
        refine ⟨123001778605208891025272435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82001185736805927350181623 123001778605208891025272435)
        ·
          refine ⟨184502667907813336537908653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123001778605208891025272435 184502667907813336537908653)
          ·
            refine ⟨69188500465430001201715745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184502667907813336537908653 69188500465430001201715745)
            ·
              refine ⟨51891375349072500901286809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69188500465430001201715745 51891375349072500901286809)
              ·
                refine ⟨38918531511804375675965107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51891375349072500901286809 38918531511804375675965107)
                ·
                  refine ⟨58377797267706563513947661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38918531511804375675965107 58377797267706563513947661)
                  ·
                    refine ⟨21891673975389961317730373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58377797267706563513947661 21891673975389961317730373)
                    ·
                      refine ⟨4104688870385617747074445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21891673975389961317730373 4104688870385617747074445)
                      ·
                        rfl

theorem cell23_7993853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_7993853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993853 prefixEnd_7993853 := by exact prefixLift 7993853
  have htrace : WordTrace (prefixWord ++ tailWord_7993853) baseStart_7993853 baseEnd_7993853 := by
    simpa [prefixWord, tailWord_7993853, baseEnd_7993853] using wordTrace_append hprefix tailTrace_7993853
  have hstable : (prefixWord ++ tailWord_7993853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993853).length < 2 ^ (prefixWord ++ tailWord_7993853).sum := by decide
  have hdescent : baseEnd_7993853 < baseStart_7993853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993870 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_7993870 : Nat := 118140960795 + 7993870 * 2 ^ 59
def prefixEnd_7993870 : Nat := 4983230072969 + 3 ^ 40 * 7993870 * 2
def baseEnd_7993870 : Nat := 4104697599556744180561867

theorem tailTrace_7993870 : CollatzResearch.WordTrace tailWord_7993870 prefixEnd_7993870 4104697599556744180561867 := by
  unfold tailWord_7993870
  simp only [CollatzResearch.WordTrace]
  refine ⟨36445048943697713643557383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194373594366387806098972709 36445048943697713643557383)
  ·
    refine ⟨54667573415546570465336075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36445048943697713643557383 54667573415546570465336075)
    ·
      refine ⟨82001360123319855698004113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54667573415546570465336075 82001360123319855698004113)
      ·
        refine ⟨61501020092489891773503085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82001360123319855698004113 61501020092489891773503085)
        ·
          refine ⟨23062882534683709415063657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61501020092489891773503085 23062882534683709415063657)
          ·
            refine ⟨17297161901012782061297743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23062882534683709415063657 17297161901012782061297743)
            ·
              refine ⟨25945742851519173091946615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17297161901012782061297743 25945742851519173091946615)
              ·
                refine ⟨38918614277278759637919923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25945742851519173091946615 38918614277278759637919923)
                ·
                  refine ⟨58377921415918139456879885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38918614277278759637919923 58377921415918139456879885)
                  ·
                    refine ⟨21891720530969302296329957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58377921415918139456879885 21891720530969302296329957)
                    ·
                      refine ⟨4104697599556744180561867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21891720530969302296329957 4104697599556744180561867)
                      ·
                        rfl

theorem cell23_7993870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_7993870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993870 prefixEnd_7993870 := by exact prefixLift 7993870
  have htrace : WordTrace (prefixWord ++ tailWord_7993870) baseStart_7993870 baseEnd_7993870 := by
    simpa [prefixWord, tailWord_7993870, baseEnd_7993870] using wordTrace_append hprefix tailTrace_7993870
  have hstable : (prefixWord ++ tailWord_7993870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993870).length < 2 ^ (prefixWord ++ tailWord_7993870).sum := by decide
  have hdescent : baseEnd_7993870 < baseStart_7993870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993890 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_7993890 : Nat := 118140960795 + 7993890 * 2 ^ 59
def prefixEnd_7993890 : Nat := 4983230072969 + 3 ^ 40 * 7993890 * 2
def baseEnd_7993890 : Nat := 4104707869169834102311775

theorem tailTrace_7993890 : CollatzResearch.WordTrace tailWord_7993890 prefixEnd_7993890 4104707869169834102311775 := by
  unfold tailWord_7993890
  simp only [CollatzResearch.WordTrace]
  refine ⟨72890280252377313141046781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194374080673006168376124749 72890280252377313141046781)
  ·
    refine ⟨27333855094641492427892543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72890280252377313141046781 27333855094641492427892543)
    ·
      refine ⟨41000782641962238641838815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27333855094641492427892543 41000782641962238641838815)
      ·
        refine ⟨61501173962943357962758223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41000782641962238641838815 61501173962943357962758223)
        ·
          refine ⟨92251760944415036944137335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61501173962943357962758223 92251760944415036944137335)
          ·
            refine ⟨138377641416622555416206003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92251760944415036944137335 138377641416622555416206003)
            ·
              refine ⟨207566462124933833124309005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138377641416622555416206003 207566462124933833124309005)
              ·
                refine ⟨77837423296850187421615877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207566462124933833124309005 77837423296850187421615877)
                ·
                  refine ⟨14594516868159410141552977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77837423296850187421615877 14594516868159410141552977)
                  ·
                    refine ⟨10945887651119557606164733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14594516868159410141552977 10945887651119557606164733)
                    ·
                      refine ⟨4104707869169834102311775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10945887651119557606164733 4104707869169834102311775)
                      ·
                        rfl

theorem cell23_7993890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_7993890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993890 prefixEnd_7993890 := by exact prefixLift 7993890
  have htrace : WordTrace (prefixWord ++ tailWord_7993890) baseStart_7993890 baseEnd_7993890 := by
    simpa [prefixWord, tailWord_7993890, baseEnd_7993890] using wordTrace_append hprefix tailTrace_7993890
  have hstable : (prefixWord ++ tailWord_7993890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993890).length < 2 ^ (prefixWord ++ tailWord_7993890).sum := by decide
  have hdescent : baseEnd_7993890 < baseStart_7993890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993913 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7993913 : Nat := 118140960795 + 7993913 * 2 ^ 59
def prefixEnd_7993913 : Nat := 4983230072969 + 3 ^ 40 * 7993913 * 2
def baseEnd_7993913 : Nat := 4104719679224887512324169

theorem tailTrace_7993913 : CollatzResearch.WordTrace tailWord_7993913 prefixEnd_7993913 4104719679224887512324169 := by
  unfold tailWord_7993913
  simp only [CollatzResearch.WordTrace]
  refine ⟨291561959888425927492274393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194374639925617284994849595 291561959888425927492274393)
  ·
    refine ⟨218671469916319445619205795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291561959888425927492274393 218671469916319445619205795)
    ·
      refine ⟨328007204874479168428808693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218671469916319445619205795 328007204874479168428808693)
      ·
        refine ⟨30750675456982422040200815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328007204874479168428808693 30750675456982422040200815)
        ·
          refine ⟨46126013185473633060301223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30750675456982422040200815 46126013185473633060301223)
          ·
            refine ⟨69189019778210449590451835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46126013185473633060301223 69189019778210449590451835)
            ·
              refine ⟨103783529667315674385677753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69189019778210449590451835 103783529667315674385677753)
              ·
                refine ⟨77837647250486755789258315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103783529667315674385677753 77837647250486755789258315)
                ·
                  refine ⟨116756470875730133683887473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77837647250486755789258315 116756470875730133683887473)
                  ·
                    refine ⟨87567353156797600262915605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116756470875730133683887473 87567353156797600262915605)
                    ·
                      refine ⟨4104719679224887512324169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87567353156797600262915605 4104719679224887512324169)
                      ·
                        rfl

theorem cell23_7993913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7993913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993913 prefixEnd_7993913 := by exact prefixLift 7993913
  have htrace : WordTrace (prefixWord ++ tailWord_7993913) baseStart_7993913 baseEnd_7993913 := by
    simpa [prefixWord, tailWord_7993913, baseEnd_7993913] using wordTrace_append hprefix tailTrace_7993913
  have hstable : (prefixWord ++ tailWord_7993913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993913).length < 2 ^ (prefixWord ++ tailWord_7993913).sum := by decide
  have hdescent : baseEnd_7993913 < baseStart_7993913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993923 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 3, 5]
def baseStart_7993923 : Nat := 118140960795 + 7993923 * 2 ^ 59
def prefixEnd_7993923 : Nat := 4983230072969 + 3 ^ 40 * 7993923 * 2
def baseEnd_7993923 : Nat := 1368241604677144157733041

theorem tailTrace_7993923 : CollatzResearch.WordTrace tailWord_7993923 prefixEnd_7993923 1368241604677144157733041 := by
  unfold tailWord_7993923
  simp only [CollatzResearch.WordTrace]
  refine ⟨291562324618389699200138423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194374883078926466133425615 291562324618389699200138423)
  ·
    refine ⟨437343486927584548800207635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291562324618389699200138423 437343486927584548800207635)
    ·
      refine ⟨656015230391376823200311453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437343486927584548800207635 656015230391376823200311453)
      ·
        refine ⟨246005711396766308700116795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 656015230391376823200311453 246005711396766308700116795)
        ·
          refine ⟨369008567095149463050175193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246005711396766308700116795 369008567095149463050175193)
          ·
            refine ⟨276756425321362097287631395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369008567095149463050175193 276756425321362097287631395)
            ·
              refine ⟨415134637982043145931447093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276756425321362097287631395 415134637982043145931447093)
              ·
                refine ⟨38918872310816544931073165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 415134637982043145931447093 38918872310816544931073165)
                ·
                  refine ⟨14594577116556204349152437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38918872310816544931073165 14594577116556204349152437)
                  ·
                    refine ⟨1368241604677144157733041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14594577116556204349152437 1368241604677144157733041)
                    ·
                      rfl

theorem cell23_7993923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 5].length) (baseStart_7993923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993923 prefixEnd_7993923 := by exact prefixLift 7993923
  have htrace : WordTrace (prefixWord ++ tailWord_7993923) baseStart_7993923 baseEnd_7993923 := by
    simpa [prefixWord, tailWord_7993923, baseEnd_7993923] using wordTrace_append hprefix tailTrace_7993923
  have hstable : (prefixWord ++ tailWord_7993923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993923).length < 2 ^ (prefixWord ++ tailWord_7993923).sum := by decide
  have hdescent : baseEnd_7993923 < baseStart_7993923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993963 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5]
def baseStart_7993963 : Nat := 118140960795 + 7993963 * 2 ^ 59
def prefixEnd_7993963 : Nat := 4983230072969 + 3 ^ 40 * 7993963 * 2
def baseEnd_7993963 : Nat := 4104745353257612316698939

theorem tailTrace_7993963 : CollatzResearch.WordTrace tailWord_7993963 prefixEnd_7993963 4104745353257612316698939 := by
  unfold tailWord_7993963
  simp only [CollatzResearch.WordTrace]
  refine ⟨291563783538244786031594543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194375855692163190687729695 291563783538244786031594543)
  ·
    refine ⟨437345675307367179047391815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291563783538244786031594543 437345675307367179047391815)
    ·
      refine ⟨656018512961050768571087723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437345675307367179047391815 656018512961050768571087723)
      ·
        refine ⟨984027769441576152856631585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656018512961050768571087723 984027769441576152856631585)
        ·
          refine ⟨738020827081182114642473689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984027769441576152856631585 738020827081182114642473689)
          ·
            refine ⟨553515620310886585981855267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738020827081182114642473689 553515620310886585981855267)
            ·
              refine ⟨830273430466329878972782901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553515620310886585981855267 830273430466329878972782901)
              ·
                refine ⟨77838134106218426153698397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830273430466329878972782901 77838134106218426153698397)
                ·
                  refine ⟨29189300289831909807636899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77838134106218426153698397 29189300289831909807636899)
                  ·
                    refine ⟨43783950434747864711455349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29189300289831909807636899 43783950434747864711455349)
                    ·
                      refine ⟨4104745353257612316698939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43783950434747864711455349 4104745353257612316698939)
                      ·
                        rfl

theorem cell23_7993963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_7993963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993963 prefixEnd_7993963 := by exact prefixLift 7993963
  have htrace : WordTrace (prefixWord ++ tailWord_7993963) baseStart_7993963 baseEnd_7993963 := by
    simpa [prefixWord, tailWord_7993963, baseEnd_7993963] using wordTrace_append hprefix tailTrace_7993963
  have hstable : (prefixWord ++ tailWord_7993963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993963).length < 2 ^ (prefixWord ++ tailWord_7993963).sum := by decide
  have hdescent : baseEnd_7993963 < baseStart_7993963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7993977 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 4]
def baseStart_7993977 : Nat := 118140960795 + 7993977 * 2 ^ 59
def prefixEnd_7993977 : Nat := 4983230072969 + 3 ^ 40 * 7993977 * 2
def baseEnd_7993977 : Nat := 4104752541986775261923875

theorem tailTrace_7993977 : CollatzResearch.WordTrace tailWord_7993977 prefixEnd_7993977 4104752541986775261923875 := by
  unfold tailWord_7993977
  simp only [CollatzResearch.WordTrace]
  refine ⟨291564294160194066422604185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194376196106796044281736123 291564294160194066422604185)
  ·
    refine ⟨218673220620145549816953139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291564294160194066422604185 218673220620145549816953139)
    ·
      refine ⟨328009830930218324725429709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218673220620145549816953139 328009830930218324725429709)
      ·
        refine ⟨123003686598831871772036141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328009830930218324725429709 123003686598831871772036141)
        ·
          refine ⟨46126382474561951914513553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123003686598831871772036141 46126382474561951914513553)
          ·
            refine ⟨34594786855921463935885165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46126382474561951914513553 34594786855921463935885165)
            ·
              refine ⟨12973045070970548975956937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34594786855921463935885165 12973045070970548975956937)
              ·
                refine ⟨9729783803227911731967703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12973045070970548975956937 9729783803227911731967703)
                ·
                  refine ⟨14594675704841867597951555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9729783803227911731967703 14594675704841867597951555)
                  ·
                    refine ⟨21892013557262801396927333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14594675704841867597951555 21892013557262801396927333)
                    ·
                      refine ⟨4104752541986775261923875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21892013557262801396927333 4104752541986775261923875)
                      ·
                        rfl

theorem cell23_7993977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_7993977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7993977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7993977 prefixEnd_7993977 := by exact prefixLift 7993977
  have htrace : WordTrace (prefixWord ++ tailWord_7993977) baseStart_7993977 baseEnd_7993977 := by
    simpa [prefixWord, tailWord_7993977, baseEnd_7993977] using wordTrace_append hprefix tailTrace_7993977
  have hstable : (prefixWord ++ tailWord_7993977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7993977).length < 2 ^ (prefixWord ++ tailWord_7993977).sum := by decide
  have hdescent : baseEnd_7993977 < baseStart_7993977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7993977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994004 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_7994004 : Nat := 118140960795 + 7994004 * 2 ^ 59
def prefixEnd_7994004 : Nat := 4983230072969 + 3 ^ 40 * 7994004 * 2
def baseEnd_7994004 : Nat := 1368255468654815552095417

theorem tailTrace_7994004 : CollatzResearch.WordTrace tailWord_7994004 prefixEnd_7994004 1368255468654815552095417 := by
  unfold tailWord_7994004
  simp only [CollatzResearch.WordTrace]
  refine ⟨145782639465548125016918533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194376852620730833355891377 145782639465548125016918533)
  ·
    refine ⟨27334244899790273440672225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145782639465548125016918533 27334244899790273440672225)
    ·
      refine ⟨20500683674842705080504169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27334244899790273440672225 20500683674842705080504169)
      ·
        refine ⟨15375512756132028810378127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20500683674842705080504169 15375512756132028810378127)
        ·
          refine ⟨23063269134198043215567191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15375512756132028810378127 23063269134198043215567191)
          ·
            refine ⟨34594903701297064823350787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23063269134198043215567191 34594903701297064823350787)
            ·
              refine ⟨51892355551945597235026181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34594903701297064823350787 51892355551945597235026181)
              ·
                refine ⟨9729816665989799481567409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51892355551945597235026181 9729816665989799481567409)
                ·
                  refine ⟨7297362499492349611175557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729816665989799481567409 7297362499492349611175557)
                  ·
                    refine ⟨1368255468654815552095417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7297362499492349611175557 1368255468654815552095417)
                    ·
                      rfl

theorem cell23_7994004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_7994004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994004 prefixEnd_7994004 := by exact prefixLift 7994004
  have htrace : WordTrace (prefixWord ++ tailWord_7994004) baseStart_7994004 baseEnd_7994004 := by
    simpa [prefixWord, tailWord_7994004, baseEnd_7994004] using wordTrace_append hprefix tailTrace_7994004
  have hstable : (prefixWord ++ tailWord_7994004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994004).length < 2 ^ (prefixWord ++ tailWord_7994004).sum := by decide
  have hdescent : baseEnd_7994004 < baseStart_7994004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994017 : List Nat := [1, 2, 3, 3, 3, 2, 1, 8]
def baseStart_7994017 : Nat := 118140960795 + 7994017 * 2 ^ 59
def prefixEnd_7994017 : Nat := 4983230072969 + 3 ^ 40 * 7994017 * 2
def baseEnd_7994017 : Nat := 152028632637516855756433

theorem tailTrace_7994017 : CollatzResearch.WordTrace tailWord_7994017 prefixEnd_7994017 152028632637516855756433 := by
  unfold tailWord_7994017
  simp only [CollatzResearch.WordTrace]
  refine ⟨291565753080049153254060305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194377168720032768836040203 291565753080049153254060305)
  ·
    refine ⟨218674314810036864940545229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291565753080049153254060305 218674314810036864940545229)
    ·
      refine ⟨82002868053763824352704461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218674314810036864940545229 82002868053763824352704461)
      ·
        refine ⟨30751075520161434132264173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82002868053763824352704461 30751075520161434132264173)
        ·
          refine ⟨11531653320060537799599065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30751075520161434132264173 11531653320060537799599065)
          ·
            refine ⟨8648739990045403349699299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11531653320060537799599065 8648739990045403349699299)
            ·
              refine ⟨12973109985068105024548949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648739990045403349699299 12973109985068105024548949)
              ·
                refine ⟨152028632637516855756433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12973109985068105024548949 152028632637516855756433)
                ·
                  rfl

theorem cell23_7994017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 8].length) (baseStart_7994017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994017 prefixEnd_7994017 := by exact prefixLift 7994017
  have htrace : WordTrace (prefixWord ++ tailWord_7994017) baseStart_7994017 baseEnd_7994017 := by
    simpa [prefixWord, tailWord_7994017, baseEnd_7994017] using wordTrace_append hprefix tailTrace_7994017
  have hstable : (prefixWord ++ tailWord_7994017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994017).length < 2 ^ (prefixWord ++ tailWord_7994017).sum := by decide
  have hdescent : baseEnd_7994017 < baseStart_7994017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994084 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_7994084 : Nat := 118140960795 + 7994084 * 2 ^ 59
def prefixEnd_7994084 : Nat := 4983230072969 + 3 ^ 40 * 7994084 * 2
def baseEnd_7994084 : Nat := 4104807484416806343285883

theorem tailTrace_7994084 : CollatzResearch.WordTrace tailWord_7994084 prefixEnd_7994084 4104807484416806343285883 := by
  unfold tailWord_7994084
  simp only [CollatzResearch.WordTrace]
  refine ⟨145784098385403211848374653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194378797847204282464499537 145784098385403211848374653)
  ·
    refine ⟨54669036894526204443140495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145784098385403211848374653 54669036894526204443140495)
    ·
      refine ⟨82003555341789306664710743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54669036894526204443140495 82003555341789306664710743)
      ·
        refine ⟨123005333012683959997066115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82003555341789306664710743 123005333012683959997066115)
        ·
          refine ⟨184507999519025939995599173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123005333012683959997066115 184507999519025939995599173)
          ·
            refine ⟨34595249909817363749174845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184507999519025939995599173 34595249909817363749174845)
            ·
              refine ⟨12973218716181511405940567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34595249909817363749174845 12973218716181511405940567)
              ·
                refine ⟨19459828074272267108910851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12973218716181511405940567 19459828074272267108910851)
                ·
                  refine ⟨29189742111408400663366277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19459828074272267108910851 29189742111408400663366277)
                  ·
                    refine ⟨5473076645889075124381177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29189742111408400663366277 5473076645889075124381177)
                    ·
                      refine ⟨4104807484416806343285883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473076645889075124381177 4104807484416806343285883)
                      ·
                        rfl

theorem cell23_7994084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_7994084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994084 prefixEnd_7994084 := by exact prefixLift 7994084
  have htrace : WordTrace (prefixWord ++ tailWord_7994084) baseStart_7994084 baseEnd_7994084 := by
    simpa [prefixWord, tailWord_7994084, baseEnd_7994084] using wordTrace_append hprefix tailTrace_7994084
  have hstable : (prefixWord ++ tailWord_7994084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994084).length < 2 ^ (prefixWord ++ tailWord_7994084).sum := by decide
  have hdescent : baseEnd_7994084 < baseStart_7994084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994127 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 2, 5, 2]
def baseStart_7994127 : Nat := 118140960795 + 7994127 * 2 ^ 59
def prefixEnd_7994127 : Nat := 4983230072969 + 3 ^ 40 * 7994127 * 2
def baseEnd_7994127 : Nat := 4104829564084949675048185

theorem tailTrace_7994127 : CollatzResearch.WordTrace tailWord_7994127 prefixEnd_7994127 4104829564084949675048185 := by
  unfold tailWord_7994127
  simp only [CollatzResearch.WordTrace]
  refine ⟨291569765109650642040564635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194379843406433761360376423 291569765109650642040564635)
  ·
    refine ⟨437354647664475963060846953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291569765109650642040564635 437354647664475963060846953)
    ·
      refine ⟨328015985748356972295635215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437354647664475963060846953 328015985748356972295635215)
      ·
        refine ⟨492023978622535458443452823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328015985748356972295635215 492023978622535458443452823)
        ·
          refine ⟨738035967933803187665179235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492023978622535458443452823 738035967933803187665179235)
          ·
            refine ⟨1107053951900704781497768853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738035967933803187665179235 1107053951900704781497768853)
            ·
              refine ⟨51893153995345536632707915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1107053951900704781497768853 51893153995345536632707915)
              ·
                refine ⟨77839730993018304949061873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51893153995345536632707915 77839730993018304949061873)
                ·
                  refine ⟨58379798244763728711796405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77839730993018304949061873 58379798244763728711796405)
                  ·
                    refine ⟨5473106085446599566730913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58379798244763728711796405 5473106085446599566730913)
                    ·
                      refine ⟨4104829564084949675048185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473106085446599566730913 4104829564084949675048185)
                      ·
                        rfl

theorem cell23_7994127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 5, 2].length) (baseStart_7994127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994127 prefixEnd_7994127 := by exact prefixLift 7994127
  have htrace : WordTrace (prefixWord ++ tailWord_7994127) baseStart_7994127 baseEnd_7994127 := by
    simpa [prefixWord, tailWord_7994127, baseEnd_7994127] using wordTrace_append hprefix tailTrace_7994127
  have hstable : (prefixWord ++ tailWord_7994127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994127).length < 2 ^ (prefixWord ++ tailWord_7994127).sum := by decide
  have hdescent : baseEnd_7994127 < baseStart_7994127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994135 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7994135 : Nat := 118140960795 + 7994135 * 2 ^ 59
def prefixEnd_7994135 : Nat := 4983230072969 + 3 ^ 40 * 7994135 * 2
def baseEnd_7994135 : Nat := 4104833671930185643748149

theorem tailTrace_7994135 : CollatzResearch.WordTrace tailWord_7994135 prefixEnd_7994135 4104833671930185643748149 := by
  unfold tailWord_7994135
  simp only [CollatzResearch.WordTrace]
  refine ⟨291570056893621659406855859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194380037929081106271237239 291570056893621659406855859)
  ·
    refine ⟨437355085340432489110283789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291570056893621659406855859 437355085340432489110283789)
    ·
      refine ⟨164008157002662183416356421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437355085340432489110283789 164008157002662183416356421)
      ·
        refine ⟨30751529437999159390566829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164008157002662183416356421 30751529437999159390566829)
        ·
          refine ⟨11531823539249684771462561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30751529437999159390566829 11531823539249684771462561)
          ·
            refine ⟨8648867654437263578596921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11531823539249684771462561 8648867654437263578596921)
            ·
              refine ⟨6486650740827947683947691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8648867654437263578596921 6486650740827947683947691)
              ·
                refine ⟨9729976111241921525921537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486650740827947683947691 9729976111241921525921537)
                ·
                  refine ⟨7297482083431441144441153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729976111241921525921537 7297482083431441144441153)
                  ·
                    refine ⟨5473111562573580858330865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7297482083431441144441153 5473111562573580858330865)
                    ·
                      refine ⟨4104833671930185643748149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473111562573580858330865 4104833671930185643748149)
                      ·
                        rfl

theorem cell23_7994135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7994135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994135 prefixEnd_7994135 := by exact prefixLift 7994135
  have htrace : WordTrace (prefixWord ++ tailWord_7994135) baseStart_7994135 baseEnd_7994135 := by
    simpa [prefixWord, tailWord_7994135, baseEnd_7994135] using wordTrace_append hprefix tailTrace_7994135
  have hstable : (prefixWord ++ tailWord_7994135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994135).length < 2 ^ (prefixWord ++ tailWord_7994135).sum := by decide
  have hdescent : baseEnd_7994135 < baseStart_7994135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994197 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 6]
def baseStart_7994197 : Nat := 118140960795 + 7994197 * 2 ^ 59
def prefixEnd_7994197 : Nat := 4983230072969 + 3 ^ 40 * 7994197 * 2
def baseEnd_7994197 : Nat := 456096167525640489019207

theorem tailTrace_7994197 : CollatzResearch.WordTrace tailWord_7994197 prefixEnd_7994197 456096167525640489019207 := by
  unfold tailWord_7994197
  simp only [CollatzResearch.WordTrace]
  refine ⟨291572318219397043995612845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194381545479598029330408563 291572318219397043995612845)
  ·
    refine ⟨109339619332273891498354817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291572318219397043995612845 109339619332273891498354817)
    ·
      refine ⟨82004714499205418623766113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109339619332273891498354817 82004714499205418623766113)
      ·
        refine ⟨61503535874404063967824585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82004714499205418623766113 61503535874404063967824585)
        ·
          refine ⟨46127651905803047975868439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61503535874404063967824585 46127651905803047975868439)
          ·
            refine ⟨69191477858704571963802659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46127651905803047975868439 69191477858704571963802659)
            ·
              refine ⟨103787216788056857945703989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69191477858704571963802659 103787216788056857945703989)
              ·
                refine ⟨9730051573880330432409749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103787216788056857945703989 9730051573880330432409749)
                ·
                  refine ⟨456096167525640489019207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9730051573880330432409749 456096167525640489019207)
                  ·
                    rfl

theorem cell23_7994197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_7994197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994197 prefixEnd_7994197 := by exact prefixLift 7994197
  have htrace : WordTrace (prefixWord ++ tailWord_7994197) baseStart_7994197 baseEnd_7994197 := by
    simpa [prefixWord, tailWord_7994197, baseEnd_7994197] using wordTrace_append hprefix tailTrace_7994197
  have hstable : (prefixWord ++ tailWord_7994197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994197).length < 2 ^ (prefixWord ++ tailWord_7994197).sum := by decide
  have hdescent : baseEnd_7994197 < baseStart_7994197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994211 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 3]
def baseStart_7994211 : Nat := 118140960795 + 7994211 * 2 ^ 59
def prefixEnd_7994211 : Nat := 4983230072969 + 3 ^ 40 * 7994211 * 2
def baseEnd_7994211 : Nat := 4104872696459927346397799

theorem tailTrace_7994211 : CollatzResearch.WordTrace tailWord_7994211 prefixEnd_7994211 4104872696459927346397799 := by
  unfold tailWord_7994211
  simp only [CollatzResearch.WordTrace]
  refine ⟨291572828841346324386622487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194381885894230882924414991 291572828841346324386622487)
  ·
    refine ⟨437359243262019486579933731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291572828841346324386622487 437359243262019486579933731)
    ·
      refine ⟨656038864893029229869900597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437359243262019486579933731 656038864893029229869900597)
      ·
        refine ⟨61503643583721490300303181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656038864893029229869900597 61503643583721490300303181)
        ·
          refine ⟨23063866343895558862613693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61503643583721490300303181 23063866343895558862613693)
          ·
            refine ⟨8648949878960834573480135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23063866343895558862613693 8648949878960834573480135)
            ·
              refine ⟨12973424818441251860220203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648949878960834573480135 12973424818441251860220203)
              ·
                refine ⟨19460137227661877790330305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12973424818441251860220203 19460137227661877790330305)
                ·
                  refine ⟨14595102920746408342747729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19460137227661877790330305 14595102920746408342747729)
                  ·
                    refine ⟨10946327190559806257060797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14595102920746408342747729 10946327190559806257060797)
                    ·
                      refine ⟨4104872696459927346397799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946327190559806257060797 4104872696459927346397799)
                      ·
                        rfl

theorem cell23_7994211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_7994211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994211 prefixEnd_7994211 := by exact prefixLift 7994211
  have htrace : WordTrace (prefixWord ++ tailWord_7994211) baseStart_7994211 baseEnd_7994211 := by
    simpa [prefixWord, tailWord_7994211, baseEnd_7994211] using wordTrace_append hprefix tailTrace_7994211
  have hstable : (prefixWord ++ tailWord_7994211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994211).length < 2 ^ (prefixWord ++ tailWord_7994211).sum := by decide
  have hdescent : baseEnd_7994211 < baseStart_7994211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994234 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2]
def baseStart_7994234 : Nat := 118140960795 + 7994234 * 2 ^ 59
def prefixEnd_7994234 : Nat := 4983230072969 + 3 ^ 40 * 7994234 * 2
def baseEnd_7994234 : Nat := 4104884506514980756410193

theorem tailTrace_7994234 : CollatzResearch.WordTrace tailWord_7994234 prefixEnd_7994234 4104884506514980756410193 := by
  unfold tailWord_7994234
  simp only [CollatzResearch.WordTrace]
  refine ⟨72893416930065749828677439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194382445146841999543139837 72893416930065749828677439)
  ·
    refine ⟨109340125395098624743016159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72893416930065749828677439 109340125395098624743016159)
    ·
      refine ⟨164010188092647937114524239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109340125395098624743016159 164010188092647937114524239)
      ·
        refine ⟨246015282138971905671786359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164010188092647937114524239 246015282138971905671786359)
        ·
          refine ⟨369022923208457858507679539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246015282138971905671786359 369022923208457858507679539)
          ·
            refine ⟨553534384812686787761519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369022923208457858507679539 553534384812686787761519309)
            ·
              refine ⟨207575394304757545410569741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553534384812686787761519309 207575394304757545410569741)
              ·
                refine ⟨77840772864284079528963653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207575394304757545410569741 77840772864284079528963653)
                ·
                  refine ⟨14595144912053264911680685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77840772864284079528963653 14595144912053264911680685)
                  ·
                    refine ⟨5473179342019974341880257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14595144912053264911680685 5473179342019974341880257)
                    ·
                      refine ⟨4104884506514980756410193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473179342019974341880257 4104884506514980756410193)
                      ·
                        rfl

theorem cell23_7994234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_7994234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994234 prefixEnd_7994234 := by exact prefixLift 7994234
  have htrace : WordTrace (prefixWord ++ tailWord_7994234) baseStart_7994234 baseEnd_7994234 := by
    simpa [prefixWord, tailWord_7994234, baseEnd_7994234] using wordTrace_append hprefix tailTrace_7994234
  have hstable : (prefixWord ++ tailWord_7994234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994234).length < 2 ^ (prefixWord ++ tailWord_7994234).sum := by decide
  have hdescent : baseEnd_7994234 < baseStart_7994234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994285 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7994285 : Nat := 118140960795 + 7994285 * 2 ^ 59
def prefixEnd_7994285 : Nat := 4983230072969 + 3 ^ 40 * 7994285 * 2
def baseEnd_7994285 : Nat := 4104910694028360056872459

theorem tailTrace_7994285 : CollatzResearch.WordTrace tailWord_7994285 prefixEnd_7994285 4104910694028360056872459 := by
  unfold tailWord_7994285
  simp only [CollatzResearch.WordTrace]
  refine ⟨291575527843078235024816309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194383685228718823349877539 291575527843078235024816309)
  ·
    refine ⟨27335205735288584533576529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291575527843078235024816309 27335205735288584533576529)
    ·
      refine ⟨20501404301466438400182397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27335205735288584533576529 20501404301466438400182397)
      ·
        refine ⟨7688026613049914400068399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20501404301466438400182397 7688026613049914400068399)
        ·
          refine ⟨11532039919574871600102599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688026613049914400068399 11532039919574871600102599)
          ·
            refine ⟨17298059879362307400153899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11532039919574871600102599 17298059879362307400153899)
            ·
              refine ⟨25947089819043461100230849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17298059879362307400153899 25947089819043461100230849)
              ·
                refine ⟨19460317364282595825173137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25947089819043461100230849 19460317364282595825173137)
                ·
                  refine ⟨14595238023211946868879853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19460317364282595825173137 14595238023211946868879853)
                  ·
                    refine ⟨5473214258704480075829945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14595238023211946868879853 5473214258704480075829945)
                    ·
                      refine ⟨4104910694028360056872459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473214258704480075829945 4104910694028360056872459)
                      ·
                        rfl

theorem cell23_7994285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7994285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994285 prefixEnd_7994285 := by exact prefixLift 7994285
  have htrace : WordTrace (prefixWord ++ tailWord_7994285) baseStart_7994285 baseEnd_7994285 := by
    simpa [prefixWord, tailWord_7994285, baseEnd_7994285] using wordTrace_append hprefix tailTrace_7994285
  have hstable : (prefixWord ++ tailWord_7994285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994285).length < 2 ^ (prefixWord ++ tailWord_7994285).sum := by decide
  have hdescent : baseEnd_7994285 < baseStart_7994285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994314 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_7994314 : Nat := 118140960795 + 7994314 * 2 ^ 59
def prefixEnd_7994314 : Nat := 4983230072969 + 3 ^ 40 * 7994314 * 2
def baseEnd_7994314 : Nat := 4104925584967340443409825

theorem tailTrace_7994314 : CollatzResearch.WordTrace tailWord_7994314 prefixEnd_7994314 4104925584967340443409825 := by
  unfold tailWord_7994314
  simp only [CollatzResearch.WordTrace]
  refine ⟨72894146389993293244405499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194384390373315448651747997 72894146389993293244405499)
  ·
    refine ⟨109341219584989939866608249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72894146389993293244405499 109341219584989939866608249)
    ·
      refine ⟨82005914688742454899956187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109341219584989939866608249 82005914688742454899956187)
      ·
        refine ⟨123008872033113682349934281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82005914688742454899956187 123008872033113682349934281)
        ·
          refine ⟨92256654024835261762450711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123008872033113682349934281 92256654024835261762450711)
          ·
            refine ⟨138384981037252892643676067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92256654024835261762450711 138384981037252892643676067)
            ·
              refine ⟨207577471555879338965514101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138384981037252892643676067 207577471555879338965514101)
              ·
                refine ⟨19460387958363688028016947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207577471555879338965514101 19460387958363688028016947)
                ·
                  refine ⟨29190581937545532042025421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19460387958363688028016947 29190581937545532042025421)
                  ·
                    refine ⟨10946468226579574515759533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29190581937545532042025421 10946468226579574515759533)
                    ·
                      refine ⟨4104925584967340443409825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946468226579574515759533 4104925584967340443409825)
                      ·
                        rfl

theorem cell23_7994314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_7994314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994314 prefixEnd_7994314 := by exact prefixLift 7994314
  have htrace : WordTrace (prefixWord ++ tailWord_7994314) baseStart_7994314 baseEnd_7994314 := by
    simpa [prefixWord, tailWord_7994314, baseEnd_7994314] using wordTrace_append hprefix tailTrace_7994314
  have hstable : (prefixWord ++ tailWord_7994314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994314).length < 2 ^ (prefixWord ++ tailWord_7994314).sum := by decide
  have hdescent : baseEnd_7994314 < baseStart_7994314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994318 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_7994318 : Nat := 118140960795 + 7994318 * 2 ^ 59
def prefixEnd_7994318 : Nat := 4983230072969 + 3 ^ 40 * 7994318 * 2
def baseEnd_7994318 : Nat := 4104927638889958427759807

theorem tailTrace_7994318 : CollatzResearch.WordTrace tailWord_7994318 prefixEnd_7994318 4104927638889958427759807 := by
  unfold tailWord_7994318
  simp only [CollatzResearch.WordTrace]
  refine ⟨36447091431494835207595951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194384487634639121107178405 36447091431494835207595951)
  ·
    refine ⟨54670637147242252811393927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36447091431494835207595951 54670637147242252811393927)
    ·
      refine ⟨82005955720863379217090891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54670637147242252811393927 82005955720863379217090891)
      ·
        refine ⟨123008933581295068825636337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82005955720863379217090891 123008933581295068825636337)
        ·
          refine ⟨92256700185971301619227253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123008933581295068825636337 92256700185971301619227253)
          ·
            refine ⟨8649065642434809526802555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92256700185971301619227253 8649065642434809526802555)
            ·
              refine ⟨12973598463652214290203833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8649065642434809526802555 12973598463652214290203833)
              ·
                refine ⟨9730198847739160717652875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12973598463652214290203833 9730198847739160717652875)
                ·
                  refine ⟨14595298271608741076479313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9730198847739160717652875 14595298271608741076479313)
                  ·
                    refine ⟨10946473703706555807359485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14595298271608741076479313 10946473703706555807359485)
                    ·
                      refine ⟨4104927638889958427759807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946473703706555807359485 4104927638889958427759807)
                      ·
                        rfl

theorem cell23_7994318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_7994318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994318 prefixEnd_7994318 := by exact prefixLift 7994318
  have htrace : WordTrace (prefixWord ++ tailWord_7994318) baseStart_7994318 baseEnd_7994318 := by
    simpa [prefixWord, tailWord_7994318, baseEnd_7994318] using wordTrace_append hprefix tailTrace_7994318
  have hstable : (prefixWord ++ tailWord_7994318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994318).length < 2 ^ (prefixWord ++ tailWord_7994318).sum := by decide
  have hdescent : baseEnd_7994318 < baseStart_7994318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994327 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_7994327 : Nat := 118140960795 + 7994327 * 2 ^ 59
def prefixEnd_7994327 : Nat := 4983230072969 + 3 ^ 40 * 7994327 * 2
def baseEnd_7994327 : Nat := 4104932260215848892547265

theorem tailTrace_7994327 : CollatzResearch.WordTrace tailWord_7994327 prefixEnd_7994327 4104932260215848892547265 := by
  unfold tailWord_7994327
  simp only [CollatzResearch.WordTrace]
  refine ⟨291577059708926076197845235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194384706472617384131896823 291577059708926076197845235)
  ·
    refine ⟨437365589563389114296767853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291577059708926076197845235 437365589563389114296767853)
    ·
      refine ⟨164012096086270917861287945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437365589563389114296767853 164012096086270917861287945)
      ·
        refine ⟨123009072064703188395965959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164012096086270917861287945 123009072064703188395965959)
        ·
          refine ⟨184513608097054782593948939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123009072064703188395965959 184513608097054782593948939)
          ·
            refine ⟨276770412145582173890923409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184513608097054782593948939 276770412145582173890923409)
            ·
              refine ⟨207577809109186630418192557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276770412145582173890923409 207577809109186630418192557)
              ·
                refine ⟨77841678415944986406822209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207577809109186630418192557 77841678415944986406822209)
                ·
                  refine ⟨58381258811958739805116657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77841678415944986406822209 58381258811958739805116657)
                  ·
                    refine ⟨43785944108969054853837493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58381258811958739805116657 43785944108969054853837493)
                    ·
                      refine ⟨4104932260215848892547265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43785944108969054853837493 4104932260215848892547265)
                      ·
                        rfl

theorem cell23_7994327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_7994327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994327 prefixEnd_7994327 := by exact prefixLift 7994327
  have htrace : WordTrace (prefixWord ++ tailWord_7994327) baseStart_7994327 baseEnd_7994327 := by
    simpa [prefixWord, tailWord_7994327, baseEnd_7994327] using wordTrace_append hprefix tailTrace_7994327
  have hstable : (prefixWord ++ tailWord_7994327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994327).length < 2 ^ (prefixWord ++ tailWord_7994327).sum := by decide
  have hdescent : baseEnd_7994327 < baseStart_7994327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994358 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_7994358 : Nat := 118140960795 + 7994358 * 2 ^ 59
def prefixEnd_7994358 : Nat := 4983230072969 + 3 ^ 40 * 7994358 * 2
def baseEnd_7994358 : Nat := 4104948178116138271259623

theorem tailTrace_7994358 : CollatzResearch.WordTrace tailWord_7994358 prefixEnd_7994358 4104948178116138271259623 := by
  unfold tailWord_7994358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18223636898238360530763983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194385460247875845661482485 18223636898238360530763983)
  ·
    refine ⟨27335455347357540796145975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18223636898238360530763983 27335455347357540796145975)
    ·
      refine ⟨41003183021036311194218963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27335455347357540796145975 41003183021036311194218963)
      ·
        refine ⟨61504774531554466791328445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41003183021036311194218963 61504774531554466791328445)
        ·
          refine ⟨23064290449332925046748167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61504774531554466791328445 23064290449332925046748167)
          ·
            refine ⟨34596435673999387570122251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23064290449332925046748167 34596435673999387570122251)
            ·
              refine ⟨51894653510999081355183377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34596435673999387570122251 51894653510999081355183377)
              ·
                refine ⟨38920990133249311016387533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51894653510999081355183377 38920990133249311016387533)
                ·
                  refine ⟨14595371299968491631145325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38920990133249311016387533 14595371299968491631145325)
                  ·
                    refine ⟨5473264237488184361679497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14595371299968491631145325 5473264237488184361679497)
                    ·
                      refine ⟨4104948178116138271259623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473264237488184361679497 4104948178116138271259623)
                      ·
                        rfl

theorem cell23_7994358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_7994358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994358 prefixEnd_7994358 := by exact prefixLift 7994358
  have htrace : WordTrace (prefixWord ++ tailWord_7994358) baseStart_7994358 baseEnd_7994358 := by
    simpa [prefixWord, tailWord_7994358, baseEnd_7994358] using wordTrace_append hprefix tailTrace_7994358
  have hstable : (prefixWord ++ tailWord_7994358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994358).length < 2 ^ (prefixWord ++ tailWord_7994358).sum := by decide
  have hdescent : baseEnd_7994358 < baseStart_7994358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994364 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_7994364 : Nat := 118140960795 + 7994364 * 2 ^ 59
def prefixEnd_7994364 : Nat := 4983230072969 + 3 ^ 40 * 7994364 * 2
def baseEnd_7994364 : Nat := 1368317086333355082594865

theorem tailTrace_7994364 : CollatzResearch.WordTrace tailWord_7994364 prefixEnd_7994364 1368317086333355082594865 := by
  unfold tailWord_7994364
  simp only [CollatzResearch.WordTrace]
  refine ⟨145789204604896015758471073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194385606139861354344628097 145789204604896015758471073)
  ·
    refine ⟨109341903453672011818853305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145789204604896015758471073 109341903453672011818853305)
    ·
      refine ⟨82006427590254008864139979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109341903453672011818853305 82006427590254008864139979)
      ·
        refine ⟨123009641385381013296209969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82006427590254008864139979 123009641385381013296209969)
        ·
          refine ⟨92257231039035759972157477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123009641385381013296209969 92257231039035759972157477)
          ·
            refine ⟨17298230819819204994779527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92257231039035759972157477 17298230819819204994779527)
            ·
              refine ⟨25947346229728807492169291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17298230819819204994779527 25947346229728807492169291)
              ·
                refine ⟨38921019344593211238253937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25947346229728807492169291 38921019344593211238253937)
                ·
                  refine ⟨29190764508444908428690453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38921019344593211238253937 29190764508444908428690453)
                  ·
                    refine ⟨1368317086333355082594865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29190764508444908428690453 1368317086333355082594865)
                    ·
                      rfl

theorem cell23_7994364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_7994364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994364 prefixEnd_7994364 := by exact prefixLift 7994364
  have htrace : WordTrace (prefixWord ++ tailWord_7994364) baseStart_7994364 baseEnd_7994364 := by
    simpa [prefixWord, tailWord_7994364, baseEnd_7994364] using wordTrace_append hprefix tailTrace_7994364
  have hstable : (prefixWord ++ tailWord_7994364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994364).length < 2 ^ (prefixWord ++ tailWord_7994364).sum := by decide
  have hdescent : baseEnd_7994364 < baseStart_7994364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994371 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 8, 2, 2]
def baseStart_7994371 : Nat := 118140960795 + 7994371 * 2 ^ 59
def prefixEnd_7994371 : Nat := 4983230072969 + 3 ^ 40 * 7994371 * 2
def baseEnd_7994371 : Nat := 4104954853364646720397063

theorem tailTrace_7994371 : CollatzResearch.WordTrace tailWord_7994371 prefixEnd_7994371 4104954853364646720397063 := by
  unfold tailWord_7994371
  simp only [CollatzResearch.WordTrace]
  refine ⟨291578664520766671712446967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194385776347177781141631311 291578664520766671712446967)
  ·
    refine ⟨437367996781150007568670451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291578664520766671712446967 437367996781150007568670451)
    ·
      refine ⟨656051995171725011353005677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437367996781150007568670451 656051995171725011353005677)
      ·
        refine ⟨246019498189396879257377129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 656051995171725011353005677 246019498189396879257377129)
        ·
          refine ⟨184514623642047659443032847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246019498189396879257377129 184514623642047659443032847)
          ·
            refine ⟨276771935463071489164549271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184514623642047659443032847 276771935463071489164549271)
            ·
              refine ⟨415157903194607233746823907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276771935463071489164549271 415157903194607233746823907)
              ·
                refine ⟨622736854791910850620235861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415157903194607233746823907 622736854791910850620235861)
                ·
                  refine ⟨7297697517092705280705889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 622736854791910850620235861 7297697517092705280705889)
                  ·
                    refine ⟨5473273137819528960529417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7297697517092705280705889 5473273137819528960529417)
                    ·
                      refine ⟨4104954853364646720397063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473273137819528960529417 4104954853364646720397063)
                      ·
                        rfl

theorem cell23_7994371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_7994371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994371 prefixEnd_7994371 := by exact prefixLift 7994371
  have htrace : WordTrace (prefixWord ++ tailWord_7994371) baseStart_7994371 baseEnd_7994371 := by
    simpa [prefixWord, tailWord_7994371, baseEnd_7994371] using wordTrace_append hprefix tailTrace_7994371
  have hstable : (prefixWord ++ tailWord_7994371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994371).length < 2 ^ (prefixWord ++ tailWord_7994371).sum := by decide
  have hdescent : baseEnd_7994371 < baseStart_7994371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994386 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7994386 : Nat := 118140960795 + 7994386 * 2 ^ 59
def prefixEnd_7994386 : Nat := 4983230072969 + 3 ^ 40 * 7994386 * 2
def baseEnd_7994386 : Nat := 4104962555574464161709495

theorem tailTrace_7994386 : CollatzResearch.WordTrace tailWord_7994386 prefixEnd_7994386 4104962555574464161709495 := by
  unfold tailWord_7994386
  simp only [CollatzResearch.WordTrace]
  refine ⟨72894802903928082318560753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194386141077141552849495341 72894802903928082318560753)
  ·
    refine ⟨54671102177946061738920565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72894802903928082318560753 54671102177946061738920565)
    ·
      refine ⟨5125415829182443288023803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54671102177946061738920565 5125415829182443288023803)
      ·
        refine ⟨7688123743773664932035705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125415829182443288023803 7688123743773664932035705)
        ·
          refine ⟨5766092807830248699026779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7688123743773664932035705 5766092807830248699026779)
          ·
            refine ⟨8649139211745373048540169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766092807830248699026779 8649139211745373048540169)
            ·
              refine ⟨6486854408809029786405127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8649139211745373048540169 6486854408809029786405127)
              ·
                refine ⟨9730281613213544679607691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486854408809029786405127 9730281613213544679607691)
                ·
                  refine ⟨14595422419820317019411537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9730281613213544679607691 14595422419820317019411537)
                  ·
                    refine ⟨10946566814865237764558653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14595422419820317019411537 10946566814865237764558653)
                    ·
                      refine ⟨4104962555574464161709495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10946566814865237764558653 4104962555574464161709495)
                      ·
                        rfl

theorem cell23_7994386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7994386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994386 prefixEnd_7994386 := by exact prefixLift 7994386
  have htrace : WordTrace (prefixWord ++ tailWord_7994386) baseStart_7994386 baseEnd_7994386 := by
    simpa [prefixWord, tailWord_7994386, baseEnd_7994386] using wordTrace_append hprefix tailTrace_7994386
  have hstable : (prefixWord ++ tailWord_7994386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994386).length < 2 ^ (prefixWord ++ tailWord_7994386).sum := by decide
  have hdescent : baseEnd_7994386 < baseStart_7994386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994387 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7]
def baseStart_7994387 : Nat := 118140960795 + 7994387 * 2 ^ 59
def prefixEnd_7994387 : Nat := 4983230072969 + 3 ^ 40 * 7994387 * 2
def baseEnd_7994387 : Nat := 4104963069055118657796989

theorem tailTrace_7994387 : CollatzResearch.WordTrace tailWord_7994387 prefixEnd_7994387 4104963069055118657796989 := by
  unfold tailWord_7994387
  simp only [CollatzResearch.WordTrace]
  refine ⟨291579248088708706445029415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194386165392472470963352943 291579248088708706445029415)
  ·
    refine ⟨437368872133063059667544123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291579248088708706445029415 437368872133063059667544123)
    ·
      refine ⟨656053308199594589501316185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437368872133063059667544123 656053308199594589501316185)
      ·
        refine ⟨492039981149695942125987139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656053308199594589501316185 492039981149695942125987139)
        ·
          refine ⟨738059971724543913188980709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492039981149695942125987139 738059971724543913188980709)
          ·
            refine ⟨138386244698351983722933883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 738059971724543913188980709 138386244698351983722933883)
            ·
              refine ⟨207579367047527975584400825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138386244698351983722933883 207579367047527975584400825)
              ·
                refine ⟨155684525285645981688300619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207579367047527975584400825 155684525285645981688300619)
                ·
                  refine ⟨233526787928468972532450929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155684525285645981688300619 233526787928468972532450929)
                  ·
                    refine ⟨175145090946351729399338197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233526787928468972532450929 175145090946351729399338197)
                    ·
                      refine ⟨4104963069055118657796989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175145090946351729399338197 4104963069055118657796989)
                      ·
                        rfl

theorem cell23_7994387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_7994387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994387 prefixEnd_7994387 := by exact prefixLift 7994387
  have htrace : WordTrace (prefixWord ++ tailWord_7994387) baseStart_7994387 baseEnd_7994387 := by
    simpa [prefixWord, tailWord_7994387, baseEnd_7994387] using wordTrace_append hprefix tailTrace_7994387
  have hstable : (prefixWord ++ tailWord_7994387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994387).length < 2 ^ (prefixWord ++ tailWord_7994387).sum := by decide
  have hdescent : baseEnd_7994387 < baseStart_7994387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994424 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 1, 7]
def baseStart_7994424 : Nat := 118140960795 + 7994424 * 2 ^ 59
def prefixEnd_7994424 : Nat := 4983230072969 + 3 ^ 40 * 7994424 * 2
def baseEnd_7994424 : Nat := 1368327355946445004344773

theorem tailTrace_7994424 : CollatzResearch.WordTrace tailWord_7994424 prefixEnd_7994424 1368327355946445004344773 := by
  unfold tailWord_7994424
  simp only [CollatzResearch.WordTrace]
  refine ⟨145790298794787330882063163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194387065059716441176084217 145790298794787330882063163)
  ·
    refine ⟨218685448192180996323094745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145790298794787330882063163 218685448192180996323094745)
    ·
      refine ⟨164014086144135747242321059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218685448192180996323094745 164014086144135747242321059)
      ·
        refine ⟨246021129216203620863481589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164014086144135747242321059 246021129216203620863481589)
        ·
          refine ⟨23064480864019089455951399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246021129216203620863481589 23064480864019089455951399)
          ·
            refine ⟨34596721296028634183927099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23064480864019089455951399 34596721296028634183927099)
            ·
              refine ⟨51895081944042951275890649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34596721296028634183927099 51895081944042951275890649)
              ·
                refine ⟨38921311458032213456917987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51895081944042951275890649 38921311458032213456917987)
                ·
                  refine ⟨58381967187048320185376981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38921311458032213456917987 58381967187048320185376981)
                  ·
                    refine ⟨1368327355946445004344773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58381967187048320185376981 1368327355946445004344773)
                    ·
                      rfl

theorem cell23_7994424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_7994424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994424 prefixEnd_7994424 := by exact prefixLift 7994424
  have htrace : WordTrace (prefixWord ++ tailWord_7994424) baseStart_7994424 baseEnd_7994424 := by
    simpa [prefixWord, tailWord_7994424, baseEnd_7994424] using wordTrace_append hprefix tailTrace_7994424
  have hstable : (prefixWord ++ tailWord_7994424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994424).length < 2 ^ (prefixWord ++ tailWord_7994424).sum := by decide
  have hdescent : baseEnd_7994424 < baseStart_7994424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994445 : List Nat := [1, 6, 1, 1, 1, 4, 1, 3, 5]
def baseStart_7994445 : Nat := 118140960795 + 7994445 * 2 ^ 59
def prefixEnd_7994445 : Nat := 4983230072969 + 3 ^ 40 * 7994445 * 2
def baseEnd_7994445 : Nat := 456110316770342158985747

theorem tailTrace_7994445 : CollatzResearch.WordTrace tailWord_7994445 prefixEnd_7994445 456110316770342158985747 := by
  unfold tailWord_7994445
  simp only [CollatzResearch.WordTrace]
  refine ⟨291581363522498582350640789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194387575681665721567093859 291581363522498582350640789)
  ·
    refine ⟨13667876415117121047686287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 291581363522498582350640789 13667876415117121047686287)
    ·
      refine ⟨20501814622675681571529431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13667876415117121047686287 20501814622675681571529431)
      ·
        refine ⟨30752721934013522357294147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20501814622675681571529431 30752721934013522357294147)
        ·
          refine ⟨46129082901020283535941221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30752721934013522357294147 46129082901020283535941221)
          ·
            refine ⟨8649203043941303162988979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46129082901020283535941221 8649203043941303162988979)
            ·
              refine ⟨12973804565911954744483469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8649203043941303162988979 12973804565911954744483469)
              ·
                refine ⟨4865176712216983029181301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12973804565911954744483469 4865176712216983029181301)
                ·
                  refine ⟨456110316770342158985747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4865176712216983029181301 456110316770342158985747)
                  ·
                    rfl

theorem cell23_7994445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_7994445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994445 prefixEnd_7994445 := by exact prefixLift 7994445
  have htrace : WordTrace (prefixWord ++ tailWord_7994445) baseStart_7994445 baseEnd_7994445 := by
    simpa [prefixWord, tailWord_7994445, baseEnd_7994445] using wordTrace_append hprefix tailTrace_7994445
  have hstable : (prefixWord ++ tailWord_7994445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994445).length < 2 ^ (prefixWord ++ tailWord_7994445).sum := by decide
  have hdescent : baseEnd_7994445 < baseStart_7994445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7994521 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 5, 5, 2]
def baseStart_7994521 : Nat := 118140960795 + 7994521 * 2 ^ 59
def prefixEnd_7994521 : Nat := 4983230072969 + 3 ^ 40 * 7994521 * 2
def baseEnd_7994521 : Nat := 4105031875462821133521373

theorem tailTrace_7994521 : CollatzResearch.WordTrace tailWord_7994521 prefixEnd_7994521 4105031875462821133521373 := by
  unfold tailWord_7994521
  simp only [CollatzResearch.WordTrace]
  refine ⟨291584135470223247330407417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194389423646815498220271611 291584135470223247330407417)
  ·
    refine ⟨218688101602667435497805563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291584135470223247330407417 218688101602667435497805563)
    ·
      refine ⟨328032152404001153246708345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218688101602667435497805563 328032152404001153246708345)
      ·
        refine ⟨246024114303000864935031259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328032152404001153246708345 246024114303000864935031259)
        ·
          refine ⟨369036171454501297402546889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246024114303000864935031259 369036171454501297402546889)
          ·
            refine ⟨276777128590875973051910167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369036171454501297402546889 276777128590875973051910167)
            ·
              refine ⟨415165692886313959577865251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276777128590875973051910167 415165692886313959577865251)
              ·
                refine ⟨622748539329470939366797877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415165692886313959577865251 622748539329470939366797877)
                ·
                  refine ⟨58382675562137900565637301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622748539329470939366797877 58382675562137900565637301)
                  ·
                    refine ⟨5473375833950428178028497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58382675562137900565637301 5473375833950428178028497)
                    ·
                      refine ⟨4105031875462821133521373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5473375833950428178028497 4105031875462821133521373)
                      ·
                        rfl

theorem cell23_7994521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_7994521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7994521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7994521 prefixEnd_7994521 := by exact prefixLift 7994521
  have htrace : WordTrace (prefixWord ++ tailWord_7994521) baseStart_7994521 baseEnd_7994521 := by
    simpa [prefixWord, tailWord_7994521, baseEnd_7994521] using wordTrace_append hprefix tailTrace_7994521
  have hstable : (prefixWord ++ tailWord_7994521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7994521).length < 2 ^ (prefixWord ++ tailWord_7994521).sum := by decide
  have hdescent : baseEnd_7994521 < baseStart_7994521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7994521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
