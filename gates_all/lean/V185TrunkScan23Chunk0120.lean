import V185TrunkScan23Chunk0119

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_709618 : List Nat := [3, 2, 1, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_709618 : Nat := 118140960795 + 709618 * 2 ^ 59
def prefixEnd_709618 : Nat := 4983230072969 + 3 ^ 40 * 709618 * 2
def baseEnd_709618 : Nat := 364375115082309850011533

theorem tailTrace_709618 : CollatzResearch.WordTrace tailWord_709618 prefixEnd_709618 364375115082309850011533 := by
  unfold tailWord_709618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470473685795663487708377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17254596495455102633889005 6470473685795663487708377)
  ·
    refine ⟨4852855264346747615781283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6470473685795663487708377 4852855264346747615781283)
    ·
      refine ⟨7279282896520121423671925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4852855264346747615781283 7279282896520121423671925)
      ·
        refine ⟨682432771548761383469243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7279282896520121423671925 682432771548761383469243)
        ·
          refine ⟨1023649157323142075203865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682432771548761383469243 1023649157323142075203865)
          ·
            refine ⟨767736867992356556402899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023649157323142075203865 767736867992356556402899)
            ·
              refine ⟨1151605301988534834604349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767736867992356556402899 1151605301988534834604349)
              ·
                refine ⟨431851988245700562976631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151605301988534834604349 431851988245700562976631)
                ·
                  refine ⟨647777982368550844464947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431851988245700562976631 647777982368550844464947)
                  ·
                    refine ⟨971666973552826266697421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 647777982368550844464947 971666973552826266697421)
                    ·
                      refine ⟨364375115082309850011533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971666973552826266697421 364375115082309850011533)
                      ·
                        rfl

theorem cell23_709618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_709618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709618 prefixEnd_709618 := by exact prefixLift 709618
  have htrace : WordTrace (prefixWord ++ tailWord_709618) baseStart_709618 baseEnd_709618 := by
    simpa [prefixWord, tailWord_709618, baseEnd_709618] using wordTrace_append hprefix tailTrace_709618
  have hstable : (prefixWord ++ tailWord_709618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709618).length < 2 ^ (prefixWord ++ tailWord_709618).sum := by decide
  have hdescent : baseEnd_709618 < baseStart_709618 := by decide
  rcases family_descends (prefixWord ++ tailWord_709618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709661 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_709661 : Nat := 118140960795 + 709661 * 2 ^ 59
def prefixEnd_709661 : Nat := 4983230072969 + 3 ^ 40 * 709661 * 2
def baseEnd_709661 : Nat := 364397194750453181773835

theorem tailTrace_709661 : CollatzResearch.WordTrace tailWord_709661 prefixEnd_709661 364397194750453181773835 := by
  unfold tailWord_709661
  simp only [CollatzResearch.WordTrace]
  refine ⟨25883463082026872294648837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17255642054684581529765891 25883463082026872294648837)
  ·
    refine ⟨4853149327880038555246657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25883463082026872294648837 4853149327880038555246657)
    ·
      refine ⟨3639861995910028916434993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4853149327880038555246657 3639861995910028916434993)
      ·
        refine ⟨2729896496932521687326245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3639861995910028916434993 2729896496932521687326245)
        ·
          refine ⟨511855593174847816373671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2729896496932521687326245 511855593174847816373671)
          ·
            refine ⟨767783389762271724560507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511855593174847816373671 767783389762271724560507)
            ·
              refine ⟨1151675084643407586840761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767783389762271724560507 1151675084643407586840761)
              ·
                refine ⟨863756313482555690130571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151675084643407586840761 863756313482555690130571)
                ·
                  refine ⟨1295634470223833535195857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863756313482555690130571 1295634470223833535195857)
                  ·
                    refine ⟨971725852667875151396893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1295634470223833535195857 971725852667875151396893)
                    ·
                      refine ⟨364397194750453181773835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 971725852667875151396893 364397194750453181773835)
                      ·
                        rfl

theorem cell23_709661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_709661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709661 prefixEnd_709661 := by exact prefixLift 709661
  have htrace : WordTrace (prefixWord ++ tailWord_709661) baseStart_709661 baseEnd_709661 := by
    simpa [prefixWord, tailWord_709661, baseEnd_709661] using wordTrace_append hprefix tailTrace_709661
  have hstable : (prefixWord ++ tailWord_709661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709661).length < 2 ^ (prefixWord ++ tailWord_709661).sum := by decide
  have hdescent : baseEnd_709661 < baseStart_709661 := by decide
  rcases family_descends (prefixWord ++ tailWord_709661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709667 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 3, 3, 2]
def baseStart_709667 : Nat := 118140960795 + 709667 * 2 ^ 59
def prefixEnd_709667 : Nat := 4983230072969 + 3 ^ 40 * 709667 * 2
def baseEnd_709667 : Nat := 364400275634380158298807

theorem tailTrace_709667 : CollatzResearch.WordTrace tailWord_709667 prefixEnd_709667 364400275634380158298807 := by
  unfold tailWord_709667
  simp only [CollatzResearch.WordTrace]
  refine ⟨25883681920005135319367255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17255787946670090212911503 25883681920005135319367255)
  ·
    refine ⟨38825522880007702979050883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25883681920005135319367255 38825522880007702979050883)
    ·
      refine ⟨58238284320011554468576325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38825522880007702979050883 58238284320011554468576325)
      ·
        refine ⟨10919678310002166462858061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58238284320011554468576325 10919678310002166462858061)
        ·
          refine ⟨4094879366250812423571773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10919678310002166462858061 4094879366250812423571773)
          ·
            refine ⟨1535579762344054658839415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4094879366250812423571773 1535579762344054658839415)
            ·
              refine ⟨2303369643516081988259123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535579762344054658839415 2303369643516081988259123)
              ·
                refine ⟨3455054465274122982388685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303369643516081988259123 3455054465274122982388685)
                ·
                  refine ⟨1295645424477796118395757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3455054465274122982388685 1295645424477796118395757)
                  ·
                    refine ⟨485867034179173544398409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1295645424477796118395757 485867034179173544398409)
                    ·
                      refine ⟨364400275634380158298807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485867034179173544398409 364400275634380158298807)
                      ·
                        rfl

theorem cell23_709667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_709667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709667 prefixEnd_709667 := by exact prefixLift 709667
  have htrace : WordTrace (prefixWord ++ tailWord_709667) baseStart_709667 baseEnd_709667 := by
    simpa [prefixWord, tailWord_709667, baseEnd_709667] using wordTrace_append hprefix tailTrace_709667
  have hstable : (prefixWord ++ tailWord_709667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709667).length < 2 ^ (prefixWord ++ tailWord_709667).sum := by decide
  have hdescent : baseEnd_709667 < baseStart_709667 := by decide
  rcases family_descends (prefixWord ++ tailWord_709667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709710 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_709710 : Nat := 118140960795 + 709710 * 2 ^ 59
def prefixEnd_709710 : Nat := 4983230072969 + 3 ^ 40 * 709710 * 2
def baseEnd_709710 : Nat := 364422355302523490061109

theorem tailTrace_709710 : CollatzResearch.WordTrace tailWord_709710 prefixEnd_709710 364422355302523490061109 := by
  unfold tailWord_709710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235656282356169207897823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17256833505899569108788389 3235656282356169207897823)
  ·
    refine ⟨4853484423534253811846735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3235656282356169207897823 4853484423534253811846735)
    ·
      refine ⟨7280226635301380717770103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4853484423534253811846735 7280226635301380717770103)
      ·
        refine ⟨10920339952952071076655155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7280226635301380717770103 10920339952952071076655155)
        ·
          refine ⟨16380509929428106614982733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10920339952952071076655155 16380509929428106614982733)
          ·
            refine ⟨6142691223535539980618525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16380509929428106614982733 6142691223535539980618525)
            ·
              refine ⟨2303509208825827492731947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6142691223535539980618525 2303509208825827492731947)
              ·
                refine ⟨3455263813238741239097921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303509208825827492731947 3455263813238741239097921)
                ·
                  refine ⟨2591447859929055929323441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3455263813238741239097921 2591447859929055929323441)
                  ·
                    refine ⟨1943585894946791946992581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2591447859929055929323441 1943585894946791946992581)
                    ·
                      refine ⟨364422355302523490061109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1943585894946791946992581 364422355302523490061109)
                      ·
                        rfl

theorem cell23_709710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_709710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709710 prefixEnd_709710 := by exact prefixLift 709710
  have htrace : WordTrace (prefixWord ++ tailWord_709710) baseStart_709710 baseEnd_709710 := by
    simpa [prefixWord, tailWord_709710, baseEnd_709710] using wordTrace_append hprefix tailTrace_709710
  have hstable : (prefixWord ++ tailWord_709710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709710).length < 2 ^ (prefixWord ++ tailWord_709710).sum := by decide
  have hdescent : baseEnd_709710 < baseStart_709710 := by decide
  rcases family_descends (prefixWord ++ tailWord_709710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709714 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_709714 : Nat := 118140960795 + 709714 * 2 ^ 59
def prefixEnd_709714 : Nat := 4983230072969 + 3 ^ 40 * 709714 * 2
def baseEnd_709714 : Nat := 364424409225141474411091

theorem tailTrace_709714 : CollatzResearch.WordTrace tailWord_709714 prefixEnd_709714 364424409225141474411091 := by
  unfold tailWord_709714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471349037708715586582049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17256930767223241564218797 6471349037708715586582049)
  ·
    refine ⟨4853511778281536689936537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6471349037708715586582049 4853511778281536689936537)
    ·
      refine ⟨3640133833711152517452403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4853511778281536689936537 3640133833711152517452403)
      ·
        refine ⟨5460200750566728776178605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640133833711152517452403 5460200750566728776178605)
        ·
          refine ⟨2047575281462523291066977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5460200750566728776178605 2047575281462523291066977)
          ·
            refine ⟨1535681461096892468300233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047575281462523291066977 1535681461096892468300233)
            ·
              refine ⟨1151761095822669351225175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535681461096892468300233 1151761095822669351225175)
              ·
                refine ⟨1727641643734004026837763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151761095822669351225175 1727641643734004026837763)
                ·
                  refine ⟨2591462465601006040256645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727641643734004026837763 2591462465601006040256645)
                  ·
                    refine ⟨485899212300188632548121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2591462465601006040256645 485899212300188632548121)
                    ·
                      refine ⟨364424409225141474411091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485899212300188632548121 364424409225141474411091)
                      ·
                        rfl

theorem cell23_709714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_709714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709714 prefixEnd_709714 := by exact prefixLift 709714
  have htrace : WordTrace (prefixWord ++ tailWord_709714) baseStart_709714 baseEnd_709714 := by
    simpa [prefixWord, tailWord_709714, baseEnd_709714] using wordTrace_append hprefix tailTrace_709714
  have hstable : (prefixWord ++ tailWord_709714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709714).length < 2 ^ (prefixWord ++ tailWord_709714).sum := by decide
  have hdescent : baseEnd_709714 < baseStart_709714 := by decide
  rcases family_descends (prefixWord ++ tailWord_709714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709737 : List Nat := [1, 2, 1, 1, 1, 7, 2, 3, 5]
def baseStart_709737 : Nat := 118140960795 + 709737 * 2 ^ 59
def prefixEnd_709737 : Nat := 4983230072969 + 3 ^ 40 * 709737 * 2
def baseEnd_709737 : Nat := 40492913253354987158165

theorem tailTrace_709737 : CollatzResearch.WordTrace tailWord_709737 prefixEnd_709737 40492913253354987158165 := by
  unfold tailWord_709737
  simp only [CollatzResearch.WordTrace]
  refine ⟨25886235029751537274415465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17257490019834358182943643 25886235029751537274415465)
  ·
    refine ⟨19414676272313652955811599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25886235029751537274415465 19414676272313652955811599)
    ·
      refine ⟨29122014408470479433717399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19414676272313652955811599 29122014408470479433717399)
      ·
        refine ⟨43683021612705719150576099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29122014408470479433717399 43683021612705719150576099)
        ·
          refine ⟨65524532419058578725864149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43683021612705719150576099 65524532419058578725864149)
          ·
            refine ⟨1535731228571685438887441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 65524532419058578725864149 1535731228571685438887441)
            ·
              refine ⟨1151798421428764079165581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535731228571685438887441 1151798421428764079165581)
              ·
                refine ⟨431924408035786529687093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151798421428764079165581 431924408035786529687093)
                ·
                  refine ⟨40492913253354987158165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 431924408035786529687093 40492913253354987158165)
                  ·
                    rfl

theorem cell23_709737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 5].length) (baseStart_709737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709737 prefixEnd_709737 := by exact prefixLift 709737
  have htrace : WordTrace (prefixWord ++ tailWord_709737) baseStart_709737 baseEnd_709737 := by
    simpa [prefixWord, tailWord_709737, baseEnd_709737] using wordTrace_append hprefix tailTrace_709737
  have hstable : (prefixWord ++ tailWord_709737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709737).length < 2 ^ (prefixWord ++ tailWord_709737).sum := by decide
  have hdescent : baseEnd_709737 < baseStart_709737 := by decide
  rcases family_descends (prefixWord ++ tailWord_709737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709770 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_709770 : Nat := 118140960795 + 709770 * 2 ^ 59
def prefixEnd_709770 : Nat := 4983230072969 + 3 ^ 40 * 709770 * 2
def baseEnd_709770 : Nat := 364453164141793255310833

theorem tailTrace_709770 : CollatzResearch.WordTrace tailWord_709770 prefixEnd_709770 364453164141793255310833 := by
  unfold tailWord_709770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471859659657995977591691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17258292425754655940244509 6471859659657995977591691)
  ·
    refine ⟨9707789489486993966387537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6471859659657995977591691 9707789489486993966387537)
    ·
      refine ⟨7280842117115245474790653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9707789489486993966387537 7280842117115245474790653)
      ·
        refine ⟨2730315793918217053046495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7280842117115245474790653 2730315793918217053046495)
        ·
          refine ⟨4095473690877325579569743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730315793918217053046495 4095473690877325579569743)
          ·
            refine ⟨6143210536315988369354615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095473690877325579569743 6143210536315988369354615)
            ·
              refine ⟨9214815804473982554031923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143210536315988369354615 9214815804473982554031923)
              ·
                refine ⟨13822223706710973831047885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9214815804473982554031923 13822223706710973831047885)
                ·
                  refine ⟨5183333890016615186642957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13822223706710973831047885 5183333890016615186642957)
                  ·
                    refine ⟨1943750208756230694991109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5183333890016615186642957 1943750208756230694991109)
                    ·
                      refine ⟨364453164141793255310833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1943750208756230694991109 364453164141793255310833)
                      ·
                        rfl

theorem cell23_709770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_709770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709770 prefixEnd_709770 := by exact prefixLift 709770
  have htrace : WordTrace (prefixWord ++ tailWord_709770) baseStart_709770 baseEnd_709770 := by
    simpa [prefixWord, tailWord_709770, baseEnd_709770] using wordTrace_append hprefix tailTrace_709770
  have hstable : (prefixWord ++ tailWord_709770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709770).length < 2 ^ (prefixWord ++ tailWord_709770).sum := by decide
  have hdescent : baseEnd_709770 < baseStart_709770 := by decide
  rcases family_descends (prefixWord ++ tailWord_709770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709810 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 8]
def baseStart_709810 : Nat := 118140960795 + 709810 * 2 ^ 59
def prefixEnd_709810 : Nat := 4983230072969 + 3 ^ 40 * 709810 * 2
def baseEnd_709810 : Nat := 40497078151997010978961

theorem tailTrace_709810 : CollatzResearch.WordTrace tailWord_709810 prefixEnd_709810 40497078151997010978961 := by
  unfold tailWord_709810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6472224389621767685455721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17259265038991380494548589 6472224389621767685455721)
  ·
    refine ⟨4854168292216325764091791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6472224389621767685455721 4854168292216325764091791)
    ·
      refine ⟨7281252438324488646137687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4854168292216325764091791 7281252438324488646137687)
      ·
        refine ⟨10921878657486732969206531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7281252438324488646137687 10921878657486732969206531)
        ·
          refine ⟨16382817986230099453809797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10921878657486732969206531 16382817986230099453809797)
          ·
            refine ⟨3071778372418143647589337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16382817986230099453809797 3071778372418143647589337)
            ·
              refine ⟨2303833779313607735692003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071778372418143647589337 2303833779313607735692003)
              ·
                refine ⟨3455750668970411603538005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303833779313607735692003 3455750668970411603538005)
                ·
                  refine ⟨40497078151997010978961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3455750668970411603538005 40497078151997010978961)
                  ·
                    rfl

theorem cell23_709810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_709810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709810 prefixEnd_709810 := by exact prefixLift 709810
  have htrace : WordTrace (prefixWord ++ tailWord_709810) baseStart_709810 baseEnd_709810 := by
    simpa [prefixWord, tailWord_709810, baseEnd_709810] using wordTrace_append hprefix tailTrace_709810
  have hstable : (prefixWord ++ tailWord_709810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709810).length < 2 ^ (prefixWord ++ tailWord_709810).sum := by decide
  have hdescent : baseEnd_709810 < baseStart_709810 := by decide
  rcases family_descends (prefixWord ++ tailWord_709810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709847 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 1, 5, 2]
def baseStart_709847 : Nat := 118140960795 + 709847 * 2 ^ 59
def prefixEnd_709847 : Nat := 4983230072969 + 3 ^ 40 * 709847 * 2
def baseEnd_709847 : Nat := 364492702152189454047979

theorem tailTrace_709847 : CollatzResearch.WordTrace tailWord_709847 prefixEnd_709847 364492702152189454047979 := by
  unfold tailWord_709847
  simp only [CollatzResearch.WordTrace]
  refine ⟨25890247059353026060919795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17260164706235350707279863 25890247059353026060919795)
  ·
    refine ⟨38835370589029539091379693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25890247059353026060919795 38835370589029539091379693)
    ·
      refine ⟨14563263970886077159267385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38835370589029539091379693 14563263970886077159267385)
      ·
        refine ⟨10922447978164557869450539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14563263970886077159267385 10922447978164557869450539)
        ·
          refine ⟨16383671967246836804175809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10922447978164557869450539 16383671967246836804175809)
          ·
            refine ⟨12287753975435127603131857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16383671967246836804175809 12287753975435127603131857)
            ·
              refine ⟨9215815481576345702348893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12287753975435127603131857 9215815481576345702348893)
              ·
                refine ⟨3455930805591129638380835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9215815481576345702348893 3455930805591129638380835)
                ·
                  refine ⟨5183896208386694457571253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455930805591129638380835 5183896208386694457571253)
                  ·
                    refine ⟨485990269536252605397305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5183896208386694457571253 485990269536252605397305)
                    ·
                      refine ⟨364492702152189454047979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 485990269536252605397305 364492702152189454047979)
                      ·
                        rfl

theorem cell23_709847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_709847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709847 prefixEnd_709847 := by exact prefixLift 709847
  have htrace : WordTrace (prefixWord ++ tailWord_709847) baseStart_709847 baseEnd_709847 := by
    simpa [prefixWord, tailWord_709847, baseEnd_709847] using wordTrace_append hprefix tailTrace_709847
  have hstable : (prefixWord ++ tailWord_709847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709847).length < 2 ^ (prefixWord ++ tailWord_709847).sum := by decide
  have hdescent : baseEnd_709847 < baseStart_709847 := by decide
  rcases family_descends (prefixWord ++ tailWord_709847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709864 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_709864 : Nat := 118140960795 + 709864 * 2 ^ 59
def prefixEnd_709864 : Nat := 4983230072969 + 3 ^ 40 * 709864 * 2
def baseEnd_709864 : Nat := 364501431323315887535401

theorem tailTrace_709864 : CollatzResearch.WordTrace tailWord_709864 prefixEnd_709864 364501431323315887535401 := by
  unfold tailWord_709864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945433550145718982144323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17260578066860958642859097 12945433550145718982144323)
  ·
    refine ⟨19418150325218578473216485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12945433550145718982144323 19418150325218578473216485)
    ·
      refine ⟨3640903185978483463728091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19418150325218578473216485 3640903185978483463728091)
      ·
        refine ⟨5461354778967725195592137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640903185978483463728091 5461354778967725195592137)
        ·
          refine ⟨4096016084225793896694103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5461354778967725195592137 4096016084225793896694103)
          ·
            refine ⟨6144024126338690845041155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096016084225793896694103 6144024126338690845041155)
            ·
              refine ⟨9216036189508036267561733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144024126338690845041155 9216036189508036267561733)
              ·
                refine ⟨1728006785532756800167825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9216036189508036267561733 1728006785532756800167825)
                ·
                  refine ⟨1296005089149567600125869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1728006785532756800167825 1296005089149567600125869)
                  ·
                    refine ⟨486001908431087850047201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296005089149567600125869 486001908431087850047201)
                    ·
                      refine ⟨364501431323315887535401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486001908431087850047201 364501431323315887535401)
                      ·
                        rfl

theorem cell23_709864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_709864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709864 prefixEnd_709864 := by exact prefixLift 709864
  have htrace : WordTrace (prefixWord ++ tailWord_709864) baseStart_709864 baseEnd_709864 := by
    simpa [prefixWord, tailWord_709864, baseEnd_709864] using wordTrace_append hprefix tailTrace_709864
  have hstable : (prefixWord ++ tailWord_709864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709864).length < 2 ^ (prefixWord ++ tailWord_709864).sum := by decide
  have hdescent : baseEnd_709864 < baseStart_709864 := by decide
  rcases family_descends (prefixWord ++ tailWord_709864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709887 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 1, 6]
def baseStart_709887 : Nat := 118140960795 + 709887 * 2 ^ 59
def prefixEnd_709887 : Nat := 4983230072969 + 3 ^ 40 * 709887 * 2
def baseEnd_709887 : Nat := 121504413792789765849265

theorem tailTrace_709887 : CollatzResearch.WordTrace tailWord_709887 prefixEnd_709887 121504413792789765849265 := by
  unfold tailWord_709887
  simp only [CollatzResearch.WordTrace]
  refine ⟨25891705979208112892375915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17261137319472075261583943 25891705979208112892375915)
  ·
    refine ⟨38837558968812169338563873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25891705979208112892375915 38837558968812169338563873)
    ·
      refine ⟨29128169226609127003922905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38837558968812169338563873 29128169226609127003922905)
      ·
        refine ⟨21846126919956845252942179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29128169226609127003922905 21846126919956845252942179)
        ·
          refine ⟨32769190379935267879413269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21846126919956845252942179 32769190379935267879413269)
          ·
            refine ⟨1536055799059465681847497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32769190379935267879413269 1536055799059465681847497)
            ·
              refine ⟨1152041849294599261385623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536055799059465681847497 1152041849294599261385623)
              ·
                refine ⟨1728062773941898892078435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152041849294599261385623 1728062773941898892078435)
                ·
                  refine ⟨2592094160912848338117653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728062773941898892078435 2592094160912848338117653)
                  ·
                    refine ⟨121504413792789765849265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2592094160912848338117653 121504413792789765849265)
                    ·
                      rfl

theorem cell23_709887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_709887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709887 prefixEnd_709887 := by exact prefixLift 709887
  have htrace : WordTrace (prefixWord ++ tailWord_709887) baseStart_709887 baseEnd_709887 := by
    simpa [prefixWord, tailWord_709887, baseEnd_709887] using wordTrace_append hprefix tailTrace_709887
  have hstable : (prefixWord ++ tailWord_709887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709887).length < 2 ^ (prefixWord ++ tailWord_709887).sum := by decide
  have hdescent : baseEnd_709887 < baseStart_709887 := by decide
  rcases family_descends (prefixWord ++ tailWord_709887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709897 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 3]
def baseStart_709897 : Nat := 118140960795 + 709897 * 2 ^ 59
def prefixEnd_709897 : Nat := 4983230072969 + 3 ^ 40 * 709897 * 2
def baseEnd_709897 : Nat := 364518376184914258422749

theorem tailTrace_709897 : CollatzResearch.WordTrace tailWord_709897 prefixEnd_709897 364518376184914258422749 := by
  unfold tailWord_709897
  simp only [CollatzResearch.WordTrace]
  refine ⟨25892070709171884600239945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17261380472781256400159963 25892070709171884600239945)
  ·
    refine ⟨19419053031878913450179959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25892070709171884600239945 19419053031878913450179959)
    ·
      refine ⟨29128579547818370175269939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19419053031878913450179959 29128579547818370175269939)
      ·
        refine ⟨43692869321727555262904909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29128579547818370175269939 43692869321727555262904909)
        ·
          refine ⟨16384825995647833223589341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43692869321727555262904909 16384825995647833223589341)
          ·
            refine ⟨6144309748367937458846003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16384825995647833223589341 6144309748367937458846003)
            ·
              refine ⟨9216464622551906188269005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144309748367937458846003 9216464622551906188269005)
              ·
                refine ⟨3456174233456964820600877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9216464622551906188269005 3456174233456964820600877)
                ·
                  refine ⟨1296065337546361807725329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3456174233456964820600877 1296065337546361807725329)
                  ·
                    refine ⟨972049003159771355793997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1296065337546361807725329 972049003159771355793997)
                    ·
                      refine ⟨364518376184914258422749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 972049003159771355793997 364518376184914258422749)
                      ·
                        rfl

theorem cell23_709897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_709897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709897 prefixEnd_709897 := by exact prefixLift 709897
  have htrace : WordTrace (prefixWord ++ tailWord_709897) baseStart_709897 baseEnd_709897 := by
    simpa [prefixWord, tailWord_709897, baseEnd_709897] using wordTrace_append hprefix tailTrace_709897
  have hstable : (prefixWord ++ tailWord_709897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709897).length < 2 ^ (prefixWord ++ tailWord_709897).sum := by decide
  have hdescent : baseEnd_709897 < baseStart_709897 := by decide
  rcases family_descends (prefixWord ++ tailWord_709897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709917 : List Nat := [1, 4, 2, 3, 1, 2, 10]
def baseStart_709917 : Nat := 118140960795 + 709917 * 2 ^ 59
def prefixEnd_709917 : Nat := 4983230072969 + 3 ^ 40 * 709917 * 2
def baseEnd_709917 : Nat := 4500353651827212100897

theorem tailTrace_709917 : CollatzResearch.WordTrace tailWord_709917 prefixEnd_709917 4500353651827212100897 := by
  unfold tailWord_709917
  simp only [CollatzResearch.WordTrace]
  refine ⟨25892800169099428015968005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17261866779399618677312003 25892800169099428015968005)
  ·
    refine ⟨4854900031706142752994001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25892800169099428015968005 4854900031706142752994001)
    ·
      refine ⟨3641175023779607064745501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4854900031706142752994001 3641175023779607064745501)
      ·
        refine ⟨1365440633917352649279563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3641175023779607064745501 1365440633917352649279563)
        ·
          refine ⟨2048160950876028973919345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365440633917352649279563 2048160950876028973919345)
          ·
            refine ⟨1536120713157021730439509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2048160950876028973919345 1536120713157021730439509)
            ·
              refine ⟨4500353651827212100897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1536120713157021730439509 4500353651827212100897)
              ·
                rfl

theorem cell23_709917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 10].length) (baseStart_709917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709917 prefixEnd_709917 := by exact prefixLift 709917
  have htrace : WordTrace (prefixWord ++ tailWord_709917) baseStart_709917 baseEnd_709917 := by
    simpa [prefixWord, tailWord_709917, baseEnd_709917] using wordTrace_append hprefix tailTrace_709917
  have hstable : (prefixWord ++ tailWord_709917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709917).length < 2 ^ (prefixWord ++ tailWord_709917).sum := by decide
  have hdescent : baseEnd_709917 < baseStart_709917 := by decide
  rcases family_descends (prefixWord ++ tailWord_709917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709928 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_709928 : Nat := 118140960795 + 709928 * 2 ^ 59
def prefixEnd_709928 : Nat := 4983230072969 + 3 ^ 40 * 709928 * 2
def baseEnd_709928 : Nat := 364534294085203637135107

theorem tailTrace_709928 : CollatzResearch.WordTrace tailWord_709928 prefixEnd_709928 364534294085203637135107 := by
  unfold tailWord_709928
  simp only [CollatzResearch.WordTrace]
  refine ⟨12946600686029788447309219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17262134248039717929745625 12946600686029788447309219)
  ·
    refine ⟨19419901029044682670963829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12946600686029788447309219 19419901029044682670963829)
    ·
      refine ⟨1820615721472939000402859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19419901029044682670963829 1820615721472939000402859)
      ·
        refine ⟨2730923582209408500604289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820615721472939000402859 2730923582209408500604289)
        ·
          refine ⟨2048192686657056375453217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2730923582209408500604289 2048192686657056375453217)
          ·
            refine ⟨1536144514992792281589913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2048192686657056375453217 1536144514992792281589913)
            ·
              refine ⟨1152108386244594211192435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536144514992792281589913 1152108386244594211192435)
              ·
                refine ⟨1728162579366891316788653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152108386244594211192435 1728162579366891316788653)
                ·
                  refine ⟨648060967262584243795745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1728162579366891316788653 648060967262584243795745)
                  ·
                    refine ⟨486045725446938182846809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 648060967262584243795745 486045725446938182846809)
                    ·
                      refine ⟨364534294085203637135107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486045725446938182846809 364534294085203637135107)
                      ·
                        rfl

theorem cell23_709928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_709928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_709928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_709928 prefixEnd_709928 := by exact prefixLift 709928
  have htrace : WordTrace (prefixWord ++ tailWord_709928) baseStart_709928 baseEnd_709928 := by
    simpa [prefixWord, tailWord_709928, baseEnd_709928] using wordTrace_append hprefix tailTrace_709928
  have hstable : (prefixWord ++ tailWord_709928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709928).length < 2 ^ (prefixWord ++ tailWord_709928).sum := by decide
  have hdescent : baseEnd_709928 < baseStart_709928 := by decide
  rcases family_descends (prefixWord ++ tailWord_709928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710005 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_710005 : Nat := 118140960795 + 710005 * 2 ^ 59
def prefixEnd_710005 : Nat := 4983230072969 + 3 ^ 40 * 710005 * 2
def baseEnd_710005 : Nat := 364573832095599835872253

theorem tailTrace_710005 : CollatzResearch.WordTrace tailWord_710005 prefixEnd_710005 364573832095599835872253 := by
  unfold tailWord_710005
  simp only [CollatzResearch.WordTrace]
  refine ⟨25896009792780619045171469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17264006528520412696780979 25896009792780619045171469)
  ·
    refine ⟨9711003672292732141939301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25896009792780619045171469 9711003672292732141939301)
    ·
      refine ⟨1820813188554887276613619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9711003672292732141939301 1820813188554887276613619)
      ·
        refine ⟨2731219782832330914920429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820813188554887276613619 2731219782832330914920429)
        ·
          refine ⟨1024207418562124093095161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2731219782832330914920429 1024207418562124093095161)
          ·
            refine ⟨768155563921593069821371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024207418562124093095161 768155563921593069821371)
            ·
              refine ⟨1152233345882389604732057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768155563921593069821371 1152233345882389604732057)
              ·
                refine ⟨864175009411792203549043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152233345882389604732057 864175009411792203549043)
                ·
                  refine ⟨1296262514117688305323565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864175009411792203549043 1296262514117688305323565)
                  ·
                    refine ⟨486098442794133114496337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1296262514117688305323565 486098442794133114496337)
                    ·
                      refine ⟨364573832095599835872253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486098442794133114496337 364573832095599835872253)
                      ·
                        rfl

theorem cell23_710005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_710005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710005 prefixEnd_710005 := by exact prefixLift 710005
  have htrace : WordTrace (prefixWord ++ tailWord_710005) baseStart_710005 baseEnd_710005 := by
    simpa [prefixWord, tailWord_710005, baseEnd_710005] using wordTrace_append hprefix tailTrace_710005
  have hstable : (prefixWord ++ tailWord_710005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710005).length < 2 ^ (prefixWord ++ tailWord_710005).sum := by decide
  have hdescent : baseEnd_710005 < baseStart_710005 := by decide
  rcases family_descends (prefixWord ++ tailWord_710005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710018 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_710018 : Nat := 118140960795 + 710018 * 2 ^ 59
def prefixEnd_710018 : Nat := 4983230072969 + 3 ^ 40 * 710018 * 2
def baseEnd_710018 : Nat := 364580507344108285009693

theorem tailTrace_710018 : CollatzResearch.WordTrace tailWord_710018 prefixEnd_710018 364580507344108285009693 := by
  unfold tailWord_710018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474120985433380566348677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17264322627822348176929805 6474120985433380566348677)
  ·
    refine ⟨1213897684768758856190377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6474120985433380566348677 1213897684768758856190377)
    ·
      refine ⟨910423263576569142142783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1213897684768758856190377 910423263576569142142783)
      ·
        refine ⟨1365634895364853713214175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910423263576569142142783 1365634895364853713214175)
        ·
          refine ⟨2048452343047280569821263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365634895364853713214175 2048452343047280569821263)
          ·
            refine ⟨3072678514570920854731895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048452343047280569821263 3072678514570920854731895)
            ·
              refine ⟨4609017771856381282097843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072678514570920854731895 4609017771856381282097843)
              ·
                refine ⟨6913526657784571923146765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609017771856381282097843 6913526657784571923146765)
                ·
                  refine ⟨2592572496669214471180037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6913526657784571923146765 2592572496669214471180037)
                  ·
                    refine ⟨486107343125477713346257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2592572496669214471180037 486107343125477713346257)
                    ·
                      refine ⟨364580507344108285009693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486107343125477713346257 364580507344108285009693)
                      ·
                        rfl

theorem cell23_710018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_710018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710018 prefixEnd_710018 := by exact prefixLift 710018
  have htrace : WordTrace (prefixWord ++ tailWord_710018) baseStart_710018 baseEnd_710018 := by
    simpa [prefixWord, tailWord_710018, baseEnd_710018] using wordTrace_append hprefix tailTrace_710018
  have hstable : (prefixWord ++ tailWord_710018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710018).length < 2 ^ (prefixWord ++ tailWord_710018).sum := by decide
  have hdescent : baseEnd_710018 < baseStart_710018 := by decide
  rcases family_descends (prefixWord ++ tailWord_710018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710041 : List Nat := [1, 2, 1, 2, 1, 5, 4, 2, 5]
def baseStart_710041 : Nat := 118140960795 + 710041 * 2 ^ 59
def prefixEnd_710041 : Nat := 4983230072969 + 3 ^ 40 * 710041 * 2
def baseEnd_710041 : Nat := 40510257488795743891343

theorem tailTrace_710041 : CollatzResearch.WordTrace tailWord_710041 prefixEnd_710041 40510257488795743891343 := by
  unfold tailWord_710041
  simp only [CollatzResearch.WordTrace]
  refine ⟨25897322820650197193481977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17264881880433464795654651 25897322820650197193481977)
  ·
    refine ⟨19422992115487647895111483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25897322820650197193481977 19422992115487647895111483)
    ·
      refine ⟨29134488173231471842667225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19422992115487647895111483 29134488173231471842667225)
      ·
        refine ⟨21850866129923603882000419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29134488173231471842667225 21850866129923603882000419)
        ·
          refine ⟨32776299194885405823000629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21850866129923603882000419 32776299194885405823000629)
          ·
            refine ⟨3072778049520506795906309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32776299194885405823000629 3072778049520506795906309)
            ·
              refine ⟨576145884285095024232433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3072778049520506795906309 576145884285095024232433)
              ·
                refine ⟨432109413213821268174325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576145884285095024232433 432109413213821268174325)
                ·
                  refine ⟨40510257488795743891343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 432109413213821268174325 40510257488795743891343)
                  ·
                    rfl

theorem cell23_710041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 5].length) (baseStart_710041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710041 prefixEnd_710041 := by exact prefixLift 710041
  have htrace : WordTrace (prefixWord ++ tailWord_710041) baseStart_710041 baseEnd_710041 := by
    simpa [prefixWord, tailWord_710041, baseEnd_710041] using wordTrace_append hprefix tailTrace_710041
  have hstable : (prefixWord ++ tailWord_710041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710041).length < 2 ^ (prefixWord ++ tailWord_710041).sum := by decide
  have hdescent : baseEnd_710041 < baseStart_710041 := by decide
  rcases family_descends (prefixWord ++ tailWord_710041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710087 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_710087 : Nat := 118140960795 + 710087 * 2 ^ 59
def prefixEnd_710087 : Nat := 4983230072969 + 3 ^ 40 * 710087 * 2
def baseEnd_710087 : Nat := 364615937509268515046875

theorem tailTrace_710087 : CollatzResearch.WordTrace tailWord_710087 prefixEnd_710087 364615937509268515046875 := by
  unfold tailWord_710087
  simp only [CollatzResearch.WordTrace]
  refine ⟨25899000578483547049656515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17266000385655698033104343 25899000578483547049656515)
  ·
    refine ⟨38848500867725320574484773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25899000578483547049656515 38848500867725320574484773)
    ·
      refine ⟨7284093912698497607715895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38848500867725320574484773 7284093912698497607715895)
      ·
        refine ⟨10926140869047746411573843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7284093912698497607715895 10926140869047746411573843)
        ·
          refine ⟨16389211303571619617360765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10926140869047746411573843 16389211303571619617360765)
          ·
            refine ⟨6145954238839357356510287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16389211303571619617360765 6145954238839357356510287)
            ·
              refine ⟨9218931358259036034765431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145954238839357356510287 9218931358259036034765431)
              ·
                refine ⟨13828397037388554052148147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9218931358259036034765431 13828397037388554052148147)
                ·
                  refine ⟨20742595556082831078222221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13828397037388554052148147 20742595556082831078222221)
                  ·
                    refine ⟨7778473333531061654333333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20742595556082831078222221 7778473333531061654333333)
                    ·
                      refine ⟨364615937509268515046875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7778473333531061654333333 364615937509268515046875)
                      ·
                        rfl

theorem cell23_710087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_710087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710087 prefixEnd_710087 := by exact prefixLift 710087
  have htrace : WordTrace (prefixWord ++ tailWord_710087) baseStart_710087 baseEnd_710087 := by
    simpa [prefixWord, tailWord_710087, baseEnd_710087] using wordTrace_append hprefix tailTrace_710087
  have hstable : (prefixWord ++ tailWord_710087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710087).length < 2 ^ (prefixWord ++ tailWord_710087).sum := by decide
  have hdescent : baseEnd_710087 < baseStart_710087 := by decide
  rcases family_descends (prefixWord ++ tailWord_710087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710101 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_710101 : Nat := 118140960795 + 710101 * 2 ^ 59
def prefixEnd_710101 : Nat := 4983230072969 + 3 ^ 40 * 710101 * 2
def baseEnd_710101 : Nat := 121541042079477153423937

theorem tailTrace_710101 : CollatzResearch.WordTrace tailWord_710101 prefixEnd_710101 121541042079477153423937 := by
  unfold tailWord_710101
  simp only [CollatzResearch.WordTrace]
  refine ⟨25899511200432827440666157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17266340800288551627110771 25899511200432827440666157)
  ·
    refine ⟨9712316700162310290249809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25899511200432827440666157 9712316700162310290249809)
    ·
      refine ⟨7284237525121732717687357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9712316700162310290249809 7284237525121732717687357)
      ·
        refine ⟨2731589071920649769132759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7284237525121732717687357 2731589071920649769132759)
        ·
          refine ⟨4097383607880974653699139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731589071920649769132759 4097383607880974653699139)
          ·
            refine ⟨6146075411821461980548709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097383607880974653699139 6146075411821461980548709)
            ·
              refine ⟨1152389139716524121352883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6146075411821461980548709 1152389139716524121352883)
              ·
                refine ⟨1728583709574786182029325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152389139716524121352883 1728583709574786182029325)
                ·
                  refine ⟨648218891090544818260997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1728583709574786182029325 648218891090544818260997)
                  ·
                    refine ⟨121541042079477153423937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 648218891090544818260997 121541042079477153423937)
                    ·
                      rfl

theorem cell23_710101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_710101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710101 prefixEnd_710101 := by exact prefixLift 710101
  have htrace : WordTrace (prefixWord ++ tailWord_710101) baseStart_710101 baseEnd_710101 := by
    simpa [prefixWord, tailWord_710101, baseEnd_710101] using wordTrace_append hprefix tailTrace_710101
  have hstable : (prefixWord ++ tailWord_710101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710101).length < 2 ^ (prefixWord ++ tailWord_710101).sum := by decide
  have hdescent : baseEnd_710101 < baseStart_710101 := by decide
  rcases family_descends (prefixWord ++ tailWord_710101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710201 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 5]
def baseStart_710201 : Nat := 118140960795 + 710201 * 2 ^ 59
def prefixEnd_710201 : Nat := 4983230072969 + 3 ^ 40 * 710201 * 2
def baseEnd_710201 : Nat := 364674474303881069021351

theorem tailTrace_710201 : CollatzResearch.WordTrace tailWord_710201 prefixEnd_710201 364674474303881069021351 := by
  unfold tailWord_710201
  simp only [CollatzResearch.WordTrace]
  refine ⟨25903158500070544519306457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17268772333380363012870971 25903158500070544519306457)
  ·
    refine ⟨19427368875052908389479843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25903158500070544519306457 19427368875052908389479843)
    ·
      refine ⟨29141053312579362584219765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19427368875052908389479843 29141053312579362584219765)
      ·
        refine ⟨2731973748054315242270603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29141053312579362584219765 2731973748054315242270603)
        ·
          refine ⟨4097960622081472863405905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731973748054315242270603 4097960622081472863405905)
          ·
            refine ⟨3073470466561104647554429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4097960622081472863405905 3073470466561104647554429)
            ·
              refine ⟨1152551424960414242832911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3073470466561104647554429 1152551424960414242832911)
              ·
                refine ⟨1728827137440621364249367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152551424960414242832911 1728827137440621364249367)
                ·
                  refine ⟨2593240706160932046374051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728827137440621364249367 2593240706160932046374051)
                  ·
                    refine ⟨3889861059241398069561077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2593240706160932046374051 3889861059241398069561077)
                    ·
                      refine ⟨364674474303881069021351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3889861059241398069561077 364674474303881069021351)
                      ·
                        rfl

theorem cell23_710201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_710201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710201 prefixEnd_710201 := by exact prefixLift 710201
  have htrace : WordTrace (prefixWord ++ tailWord_710201) baseStart_710201 baseEnd_710201 := by
    simpa [prefixWord, tailWord_710201, baseEnd_710201] using wordTrace_append hprefix tailTrace_710201
  have hstable : (prefixWord ++ tailWord_710201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710201).length < 2 ^ (prefixWord ++ tailWord_710201).sum := by decide
  have hdescent : baseEnd_710201 < baseStart_710201 := by decide
  rcases family_descends (prefixWord ++ tailWord_710201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710204 : List Nat := [2, 2, 2, 2, 4, 11]
def baseStart_710204 : Nat := 118140960795 + 710204 * 2 ^ 59
def prefixEnd_710204 : Nat := 4983230072969 + 3 ^ 40 * 710204 * 2
def baseEnd_710204 : Nat := 1500724340517878836559

theorem tailTrace_710204 : CollatzResearch.WordTrace tailWord_710204 prefixEnd_710204 1500724340517878836559 := by
  unfold tailWord_710204
  simp only [CollatzResearch.WordTrace]
  refine ⟨12951633959529838015832833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17268845279373117354443777 12951633959529838015832833)
  ·
    refine ⟨9713725469647378511874625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12951633959529838015832833 9713725469647378511874625)
    ·
      refine ⟨7285294102235533883905969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9713725469647378511874625 7285294102235533883905969)
      ·
        refine ⟨5463970576676650412929477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7285294102235533883905969 5463970576676650412929477)
        ·
          refine ⟨1024494483126871952424277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5463970576676650412929477 1024494483126871952424277)
          ·
            refine ⟨1500724340517878836559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1024494483126871952424277 1500724340517878836559)
            ·
              rfl

theorem cell23_710204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 11].length) (baseStart_710204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710204 prefixEnd_710204 := by exact prefixLift 710204
  have htrace : WordTrace (prefixWord ++ tailWord_710204) baseStart_710204 baseEnd_710204 := by
    simpa [prefixWord, tailWord_710204, baseEnd_710204] using wordTrace_append hprefix tailTrace_710204
  have hstable : (prefixWord ++ tailWord_710204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710204).length < 2 ^ (prefixWord ++ tailWord_710204).sum := by decide
  have hdescent : baseEnd_710204 < baseStart_710204 := by decide
  rcases family_descends (prefixWord ++ tailWord_710204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710231 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_710231 : Nat := 118140960795 + 710231 * 2 ^ 59
def prefixEnd_710231 : Nat := 4983230072969 + 3 ^ 40 * 710231 * 2
def baseEnd_710231 : Nat := 364689878723515951646213

theorem tailTrace_710231 : CollatzResearch.WordTrace tailWord_710231 prefixEnd_710231 364689878723515951646213 := by
  unfold tailWord_710231
  simp only [CollatzResearch.WordTrace]
  refine ⟨25904252689961859642898547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17269501793307906428599031 25904252689961859642898547)
  ·
    refine ⟨38856379034942789464347821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25904252689961859642898547 38856379034942789464347821)
    ·
      refine ⟨14571142138103546049130433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38856379034942789464347821 14571142138103546049130433)
      ·
        refine ⟨10928356603577659536847825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14571142138103546049130433 10928356603577659536847825)
        ·
          refine ⟨8196267452683244652635869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10928356603577659536847825 8196267452683244652635869)
          ·
            refine ⟨3073600294756216744738451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8196267452683244652635869 3073600294756216744738451)
            ·
              refine ⟨4610400442134325117107677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073600294756216744738451 4610400442134325117107677)
              ·
                refine ⟨1728900165800371918915379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4610400442134325117107677 1728900165800371918915379)
                ·
                  refine ⟨2593350248700557878373069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728900165800371918915379 2593350248700557878373069)
                  ·
                    refine ⟨972506343262709204389901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593350248700557878373069 972506343262709204389901)
                    ·
                      refine ⟨364689878723515951646213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 972506343262709204389901 364689878723515951646213)
                      ·
                        rfl

theorem cell23_710231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_710231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710231 prefixEnd_710231 := by exact prefixLift 710231
  have htrace : WordTrace (prefixWord ++ tailWord_710231) baseStart_710231 baseEnd_710231 := by
    simpa [prefixWord, tailWord_710231, baseEnd_710231] using wordTrace_append hprefix tailTrace_710231
  have hstable : (prefixWord ++ tailWord_710231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710231).length < 2 ^ (prefixWord ++ tailWord_710231).sum := by decide
  have hdescent : baseEnd_710231 < baseStart_710231 := by decide
  rcases family_descends (prefixWord ++ tailWord_710231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710248 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_710248 : Nat := 118140960795 + 710248 * 2 ^ 59
def prefixEnd_710248 : Nat := 4983230072969 + 3 ^ 40 * 710248 * 2
def baseEnd_710248 : Nat := 364698607894642385133635

theorem tailTrace_710248 : CollatzResearch.WordTrace tailWord_710248 prefixEnd_710248 364698607894642385133635 := by
  unfold tailWord_710248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952436365450135773133699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17269915153933514364178265 12952436365450135773133699)
  ·
    refine ⟨19428654548175203659700549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12952436365450135773133699 19428654548175203659700549)
    ·
      refine ⟨3642872727782850686193853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19428654548175203659700549 3642872727782850686193853)
      ·
        refine ⟨1366077272918569007322695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3642872727782850686193853 1366077272918569007322695)
        ·
          refine ⟨2049115909377853510984043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1366077272918569007322695 2049115909377853510984043)
          ·
            refine ⟨3073673864066780266476065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049115909377853510984043 3073673864066780266476065)
            ·
              refine ⟨2305255398050085199857049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3073673864066780266476065 2305255398050085199857049)
              ·
                refine ⟨1728941548537563899892787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305255398050085199857049 1728941548537563899892787)
                ·
                  refine ⟨2593412322806345849839181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1728941548537563899892787 2593412322806345849839181)
                  ·
                    refine ⟨972529621052379693689693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2593412322806345849839181 972529621052379693689693)
                    ·
                      refine ⟨364698607894642385133635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 972529621052379693689693 364698607894642385133635)
                      ·
                        rfl

theorem cell23_710248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_710248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710248 prefixEnd_710248 := by exact prefixLift 710248
  have htrace : WordTrace (prefixWord ++ tailWord_710248) baseStart_710248 baseEnd_710248 := by
    simpa [prefixWord, tailWord_710248, baseEnd_710248] using wordTrace_append hprefix tailTrace_710248
  have hstable : (prefixWord ++ tailWord_710248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710248).length < 2 ^ (prefixWord ++ tailWord_710248).sum := by decide
  have hdescent : baseEnd_710248 < baseStart_710248 := by decide
  rcases family_descends (prefixWord ++ tailWord_710248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710282 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_710282 : Nat := 118140960795 + 710282 * 2 ^ 59
def prefixEnd_710282 : Nat := 4983230072969 + 3 ^ 40 * 710282 * 2
def baseEnd_710282 : Nat := 364716066236895252108479

theorem tailTrace_710282 : CollatzResearch.WordTrace tailWord_710282 prefixEnd_710282 364716066236895252108479 := by
  unfold tailWord_710282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6476528203194273838251275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17270741875184730235336733 6476528203194273838251275)
  ·
    refine ⟨9714792304791410757376913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6476528203194273838251275 9714792304791410757376913)
    ·
      refine ⟨7286094228593558068032685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9714792304791410757376913 7286094228593558068032685)
      ·
        refine ⟨2732285335722584275512257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7286094228593558068032685 2732285335722584275512257)
        ·
          refine ⟨2049214001791938206634193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732285335722584275512257 2049214001791938206634193)
          ·
            refine ⟨1536910501343953654975645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2049214001791938206634193 1536910501343953654975645)
            ·
              refine ⟨576341438003982620615867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1536910501343953654975645 576341438003982620615867)
              ·
                refine ⟨864512157005973930923801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576341438003982620615867 864512157005973930923801)
                ·
                  refine ⟨648384117754480448192851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864512157005973930923801 648384117754480448192851)
                  ·
                    refine ⟨972576176631720672289277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 648384117754480448192851 972576176631720672289277)
                    ·
                      refine ⟨364716066236895252108479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 972576176631720672289277 364716066236895252108479)
                      ·
                        rfl

theorem cell23_710282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_710282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710282 prefixEnd_710282 := by exact prefixLift 710282
  have htrace : WordTrace (prefixWord ++ tailWord_710282) baseStart_710282 baseEnd_710282 := by
    simpa [prefixWord, tailWord_710282, baseEnd_710282] using wordTrace_append hprefix tailTrace_710282
  have hstable : (prefixWord ++ tailWord_710282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710282).length < 2 ^ (prefixWord ++ tailWord_710282).sum := by decide
  have hdescent : baseEnd_710282 < baseStart_710282 := by decide
  rcases family_descends (prefixWord ++ tailWord_710282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710305 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_710305 : Nat := 118140960795 + 710305 * 2 ^ 59
def prefixEnd_710305 : Nat := 4983230072969 + 3 ^ 40 * 710305 * 2
def baseEnd_710305 : Nat := 364727876291948662120873

theorem tailTrace_710305 : CollatzResearch.WordTrace tailWord_710305 prefixEnd_710305 364727876291948662120873 := by
  unfold tailWord_710305
  simp only [CollatzResearch.WordTrace]
  refine ⟨25906951691693770281092369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17271301127795846854061579 25906951691693770281092369)
  ·
    refine ⟨19430213768770327710819277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25906951691693770281092369 19430213768770327710819277)
    ·
      refine ⟨7286330163288872891557229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19430213768770327710819277 7286330163288872891557229)
      ·
        refine ⟨2732373811233327334333961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7286330163288872891557229 2732373811233327334333961)
        ·
          refine ⟨2049280358424995500750471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732373811233327334333961 2049280358424995500750471)
          ·
            refine ⟨3073920537637493251125707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049280358424995500750471 3073920537637493251125707)
            ·
              refine ⟨4610880806456239876688561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073920537637493251125707 4610880806456239876688561)
              ·
                refine ⟨3458160604842179907516421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610880806456239876688561 3458160604842179907516421)
                ·
                  refine ⟨648405113407908732659329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3458160604842179907516421 648405113407908732659329)
                  ·
                    refine ⟨486303835055931549494497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 648405113407908732659329 486303835055931549494497)
                    ·
                      refine ⟨364727876291948662120873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486303835055931549494497 364727876291948662120873)
                      ·
                        rfl

theorem cell23_710305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_710305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710305 prefixEnd_710305 := by exact prefixLift 710305
  have htrace : WordTrace (prefixWord ++ tailWord_710305) baseStart_710305 baseEnd_710305 := by
    simpa [prefixWord, tailWord_710305, baseEnd_710305] using wordTrace_append hprefix tailTrace_710305
  have hstable : (prefixWord ++ tailWord_710305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710305).length < 2 ^ (prefixWord ++ tailWord_710305).sum := by decide
  have hdescent : baseEnd_710305 < baseStart_710305 := by decide
  rcases family_descends (prefixWord ++ tailWord_710305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710378 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_710378 : Nat := 118140960795 + 710378 * 2 ^ 59
def prefixEnd_710378 : Nat := 4983230072969 + 3 ^ 40 * 710378 * 2
def baseEnd_710378 : Nat := 364765360379726876508037

theorem tailTrace_710378 : CollatzResearch.WordTrace tailWord_710378 prefixEnd_710378 364765360379726876508037 := by
  unfold tailWord_710378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6477403555107325937124947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17273076146952869165666525 6477403555107325937124947)
  ·
    refine ⟨9716105332660988905687421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6477403555107325937124947 9716105332660988905687421)
    ·
      refine ⟨3643539499747870839632783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9716105332660988905687421 3643539499747870839632783)
      ·
        refine ⟨5465309249621806259449175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3643539499747870839632783 5465309249621806259449175)
        ·
          refine ⟨8197963874432709389173763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5465309249621806259449175 8197963874432709389173763)
          ·
            refine ⟨12296945811649064083760645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8197963874432709389173763 12296945811649064083760645)
            ·
              refine ⟨2305677339684199515705121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12296945811649064083760645 2305677339684199515705121)
              ·
                refine ⟨1729258004763149636778841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305677339684199515705121 1729258004763149636778841)
                ·
                  refine ⟨1296943503572362227584131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1729258004763149636778841 1296943503572362227584131)
                  ·
                    refine ⟨1945415255358543341376197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1296943503572362227584131 1945415255358543341376197)
                    ·
                      refine ⟨364765360379726876508037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1945415255358543341376197 364765360379726876508037)
                      ·
                        rfl

theorem cell23_710378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_710378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710378 prefixEnd_710378 := by exact prefixLift 710378
  have htrace : WordTrace (prefixWord ++ tailWord_710378) baseStart_710378 baseEnd_710378 := by
    simpa [prefixWord, tailWord_710378, baseEnd_710378] using wordTrace_append hprefix tailTrace_710378
  have hstable : (prefixWord ++ tailWord_710378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710378).length < 2 ^ (prefixWord ++ tailWord_710378).sum := by decide
  have hdescent : baseEnd_710378 < baseStart_710378 := by decide
  rcases family_descends (prefixWord ++ tailWord_710378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710452 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 6]
def baseStart_710452 : Nat := 118140960795 + 710452 * 2 ^ 59
def prefixEnd_710452 : Nat := 4983230072969 + 3 ^ 40 * 710452 * 2
def baseEnd_710452 : Nat := 40533706438684398553633

theorem tailTrace_710452 : CollatzResearch.WordTrace tailWord_710452 prefixEnd_710452 40533706438684398553633 := by
  unfold tailWord_710452
  simp only [CollatzResearch.WordTrace]
  refine ⟨12956156611080607193346805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17274875481440809591129073 12956156611080607193346805)
  ·
    refine ⟨1214639682288806924376263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12956156611080607193346805 1214639682288806924376263)
    ·
      refine ⟨1821959523433210386564395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214639682288806924376263 1821959523433210386564395)
      ·
        refine ⟨2732939285149815579846593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821959523433210386564395 2732939285149815579846593)
        ·
          refine ⟨2049704463862361684884945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732939285149815579846593 2049704463862361684884945)
          ·
            refine ⟨1537278347896771263663709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2049704463862361684884945 1537278347896771263663709)
            ·
              refine ⟨576479380461289223873891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1537278347896771263663709 576479380461289223873891)
              ·
                refine ⟨864719070691933835810837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576479380461289223873891 864719070691933835810837)
                ·
                  refine ⟨40533706438684398553633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 864719070691933835810837 40533706438684398553633)
                  ·
                    rfl

theorem cell23_710452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_710452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710452 prefixEnd_710452 := by exact prefixLift 710452
  have htrace : WordTrace (prefixWord ++ tailWord_710452) baseStart_710452 baseEnd_710452 := by
    simpa [prefixWord, tailWord_710452, baseEnd_710452] using wordTrace_append hprefix tailTrace_710452
  have hstable : (prefixWord ++ tailWord_710452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710452).length < 2 ^ (prefixWord ++ tailWord_710452).sum := by decide
  have hdescent : baseEnd_710452 < baseStart_710452 := by decide
  rcases family_descends (prefixWord ++ tailWord_710452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710462 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_710462 : Nat := 118140960795 + 710462 * 2 ^ 59
def prefixEnd_710462 : Nat := 4983230072969 + 3 ^ 40 * 710462 * 2
def baseEnd_710462 : Nat := 364808492754704547857651

theorem tailTrace_710462 : CollatzResearch.WordTrace tailWord_710462 prefixEnd_710462 364808492754704547857651 := by
  unfold tailWord_710462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239084744015623261819705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17275118634749990729705093 3239084744015623261819705)
  ·
    refine ⟨2429313558011717446364779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3239084744015623261819705 2429313558011717446364779)
    ·
      refine ⟨3643970337017576169547169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2429313558011717446364779 3643970337017576169547169)
      ·
        refine ⟨2732977752763182127160377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3643970337017576169547169 2732977752763182127160377)
        ·
          refine ⟨2049733314572386595370283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732977752763182127160377 2049733314572386595370283)
          ·
            refine ⟨3074599971858579893055425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049733314572386595370283 3074599971858579893055425)
            ·
              refine ⟨2305949978893934919791569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074599971858579893055425 2305949978893934919791569)
              ·
                refine ⟨1729462484170451189843677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2305949978893934919791569 1729462484170451189843677)
                ·
                  refine ⟨648548431563919196191379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1729462484170451189843677 648548431563919196191379)
                  ·
                    refine ⟨972822647345878794287069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 648548431563919196191379 972822647345878794287069)
                    ·
                      refine ⟨364808492754704547857651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 972822647345878794287069 364808492754704547857651)
                      ·
                        rfl

theorem cell23_710462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_710462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710462 prefixEnd_710462 := by exact prefixLift 710462
  have htrace : WordTrace (prefixWord ++ tailWord_710462) baseStart_710462 baseEnd_710462 := by
    simpa [prefixWord, tailWord_710462, baseEnd_710462] using wordTrace_append hprefix tailTrace_710462
  have hstable : (prefixWord ++ tailWord_710462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710462).length < 2 ^ (prefixWord ++ tailWord_710462).sum := by decide
  have hdescent : baseEnd_710462 < baseStart_710462 := by decide
  rcases family_descends (prefixWord ++ tailWord_710462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710485 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_710485 : Nat := 118140960795 + 710485 * 2 ^ 59
def prefixEnd_710485 : Nat := 4983230072969 + 3 ^ 40 * 710485 * 2
def baseEnd_710485 : Nat := 364820302809757957870045

theorem tailTrace_710485 : CollatzResearch.WordTrace tailWord_710485 prefixEnd_710485 364820302809757957870045 := by
  unfold tailWord_710485
  simp only [CollatzResearch.WordTrace]
  refine ⟨25913516831041661022644909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17275677887361107348429939 25913516831041661022644909)
  ·
    refine ⟨9717568811640622883491841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25913516831041661022644909 9717568811640622883491841)
    ·
      refine ⟨7288176608730467162618881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9717568811640622883491841 7288176608730467162618881)
      ·
        refine ⟨5466132456547850371964161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7288176608730467162618881 5466132456547850371964161)
        ·
          refine ⟨4099599342410887778973121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5466132456547850371964161 4099599342410887778973121)
          ·
            refine ⟨3074699506808165834229841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4099599342410887778973121 3074699506808165834229841)
            ·
              refine ⟨2306024630106124375672381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074699506808165834229841 2306024630106124375672381)
              ·
                refine ⟨864759236289796640877143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2306024630106124375672381 864759236289796640877143)
                ·
                  refine ⟨1297138854434694961315715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864759236289796640877143 1297138854434694961315715)
                  ·
                    refine ⟨1945708281652042441973573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1297138854434694961315715 1945708281652042441973573)
                    ·
                      refine ⟨364820302809757957870045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1945708281652042441973573 364820302809757957870045)
                      ·
                        rfl

theorem cell23_710485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_710485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710485 prefixEnd_710485 := by exact prefixLift 710485
  have htrace : WordTrace (prefixWord ++ tailWord_710485) baseStart_710485 baseEnd_710485 := by
    simpa [prefixWord, tailWord_710485, baseEnd_710485] using wordTrace_append hprefix tailTrace_710485
  have hstable : (prefixWord ++ tailWord_710485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710485).length < 2 ^ (prefixWord ++ tailWord_710485).sum := by decide
  have hdescent : baseEnd_710485 < baseStart_710485 := by decide
  rcases family_descends (prefixWord ++ tailWord_710485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710488 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_710488 : Nat := 118140960795 + 710488 * 2 ^ 59
def prefixEnd_710488 : Nat := 4983230072969 + 3 ^ 40 * 710488 * 2
def baseEnd_710488 : Nat := 364821843251721446132531

theorem tailTrace_710488 : CollatzResearch.WordTrace tailWord_710488 prefixEnd_710488 364821843251721446132531 := by
  unfold tailWord_710488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12956813125015396267502059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17275750833353861690002745 12956813125015396267502059)
  ·
    refine ⟨19435219687523094401253089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12956813125015396267502059 19435219687523094401253089)
    ·
      refine ⟨14576414765642320800939817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19435219687523094401253089 14576414765642320800939817)
      ·
        refine ⟨10932311074231740600704863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14576414765642320800939817 10932311074231740600704863)
        ·
          refine ⟨16398466611347610901057295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10932311074231740600704863 16398466611347610901057295)
          ·
            refine ⟨24597699917021416351585943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16398466611347610901057295 24597699917021416351585943)
            ·
              refine ⟨36896549875532124527378915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24597699917021416351585943 36896549875532124527378915)
              ·
                refine ⟨55344824813298186791068373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36896549875532124527378915 55344824813298186791068373)
                ·
                  refine ⟨1297144331561676252915665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 55344824813298186791068373 1297144331561676252915665)
                  ·
                    refine ⟨972858248671257189686749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297144331561676252915665 972858248671257189686749)
                    ·
                      refine ⟨364821843251721446132531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 972858248671257189686749 364821843251721446132531)
                      ·
                        rfl

theorem cell23_710488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_710488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710488 prefixEnd_710488 := by exact prefixLift 710488
  have htrace : WordTrace (prefixWord ++ tailWord_710488) baseStart_710488 baseEnd_710488 := by
    simpa [prefixWord, tailWord_710488, baseEnd_710488] using wordTrace_append hprefix tailTrace_710488
  have hstable : (prefixWord ++ tailWord_710488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710488).length < 2 ^ (prefixWord ++ tailWord_710488).sum := by decide
  have hdescent : baseEnd_710488 < baseStart_710488 := by decide
  rcases family_descends (prefixWord ++ tailWord_710488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710508 : List Nat := [2, 2, 1, 1, 4, 3, 2, 8]
def baseStart_710508 : Nat := 118140960795 + 710508 * 2 ^ 59
def prefixEnd_710508 : Nat := 4983230072969 + 3 ^ 40 * 710508 * 2
def baseEnd_710508 : Nat := 13512300476474495106757

theorem tailTrace_710508 : CollatzResearch.WordTrace tailWord_710508 prefixEnd_710508 13512300476474495106757 := by
  unfold tailWord_710508
  simp only [CollatzResearch.WordTrace]
  refine ⟨12957177854979167975366089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17276237139972223967154785 12957177854979167975366089)
  ·
    refine ⟨9717883391234375981524567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12957177854979167975366089 9717883391234375981524567)
    ·
      refine ⟨14576825086851563972286851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9717883391234375981524567 14576825086851563972286851)
      ·
        refine ⟨21865237630277345958430277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14576825086851563972286851 21865237630277345958430277)
        ·
          refine ⟨4099732055677002367205677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21865237630277345958430277 4099732055677002367205677)
          ·
            refine ⟨1537399520878875887702129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4099732055677002367205677 1537399520878875887702129)
            ·
              refine ⟨1153049640659156915776597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537399520878875887702129 1153049640659156915776597)
              ·
                refine ⟨13512300476474495106757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1153049640659156915776597 13512300476474495106757)
                ·
                  rfl

theorem cell23_710508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 8].length) (baseStart_710508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710508 prefixEnd_710508 := by exact prefixLift 710508
  have htrace : WordTrace (prefixWord ++ tailWord_710508) baseStart_710508 baseEnd_710508 := by
    simpa [prefixWord, tailWord_710508, baseEnd_710508] using wordTrace_append hprefix tailTrace_710508
  have hstable : (prefixWord ++ tailWord_710508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710508).length < 2 ^ (prefixWord ++ tailWord_710508).sum := by decide
  have hdescent : baseEnd_710508 < baseStart_710508 := by decide
  rcases family_descends (prefixWord ++ tailWord_710508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710578 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_710578 : Nat := 118140960795 + 710578 * 2 ^ 59
def prefixEnd_710578 : Nat := 4983230072969 + 3 ^ 40 * 710578 * 2
def baseEnd_710578 : Nat := 364868056510626094007117

theorem tailTrace_710578 : CollatzResearch.WordTrace tailWord_710578 prefixEnd_710578 364868056510626094007117 := by
  unfold tailWord_710578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479227204926184476445097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17277939213136491937186925 6479227204926184476445097)
  ·
    refine ⟨4859420403694638357333823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6479227204926184476445097 4859420403694638357333823)
    ·
      refine ⟨7289130605541957536000735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4859420403694638357333823 7289130605541957536000735)
      ·
        refine ⟨10933695908312936304001103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289130605541957536000735 10933695908312936304001103)
        ·
          refine ⟨16400543862469404456001655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10933695908312936304001103 16400543862469404456001655)
          ·
            refine ⟨24600815793704106684002483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16400543862469404456001655 24600815793704106684002483)
            ·
              refine ⟨36901223690556160026003725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24600815793704106684002483 36901223690556160026003725)
              ·
                refine ⟨13837958883958560009751397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36901223690556160026003725 13837958883958560009751397)
                ·
                  refine ⟨2594617290742230001828387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13837958883958560009751397 2594617290742230001828387)
                  ·
                    refine ⟨3891925936113345002742581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2594617290742230001828387 3891925936113345002742581)
                    ·
                      refine ⟨364868056510626094007117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3891925936113345002742581 364868056510626094007117)
                      ·
                        rfl

theorem cell23_710578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_710578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710578 prefixEnd_710578 := by exact prefixLift 710578
  have htrace : WordTrace (prefixWord ++ tailWord_710578) baseStart_710578 baseEnd_710578 := by
    simpa [prefixWord, tailWord_710578, baseEnd_710578] using wordTrace_append hprefix tailTrace_710578
  have hstable : (prefixWord ++ tailWord_710578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710578).length < 2 ^ (prefixWord ++ tailWord_710578).sum := by decide
  have hdescent : baseEnd_710578 < baseStart_710578 := by decide
  rcases family_descends (prefixWord ++ tailWord_710578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710592 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 4, 2, 2]
def baseStart_710592 : Nat := 118140960795 + 710592 * 2 ^ 59
def prefixEnd_710592 : Nat := 4983230072969 + 3 ^ 40 * 710592 * 2
def baseEnd_710592 : Nat := 364875245239789039232053

theorem tailTrace_710592 : CollatzResearch.WordTrace tailWord_710592 prefixEnd_710592 364875245239789039232053 := by
  unfold tailWord_710592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12958709720827009148395015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17278279627769345531193353 12958709720827009148395015)
  ·
    refine ⟨19438064581240513722592523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12958709720827009148395015 19438064581240513722592523)
    ·
      refine ⟨29157096871860770583888785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19438064581240513722592523 29157096871860770583888785)
      ·
        refine ⟨21867822653895577937916589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29157096871860770583888785 21867822653895577937916589)
        ·
          refine ⟨8200433495210841726718721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21867822653895577937916589 8200433495210841726718721)
          ·
            refine ⟨6150325121408131295039041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8200433495210841726718721 6150325121408131295039041)
            ·
              refine ⟨4612743841056098471279281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6150325121408131295039041 4612743841056098471279281)
              ·
                refine ⟨3459557880792073853459461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612743841056098471279281 3459557880792073853459461)
                ·
                  refine ⟨648667102648513847523649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3459557880792073853459461 648667102648513847523649)
                  ·
                    refine ⟨486500326986385385642737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 648667102648513847523649 486500326986385385642737)
                    ·
                      refine ⟨364875245239789039232053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486500326986385385642737 364875245239789039232053)
                      ·
                        rfl

theorem cell23_710592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_710592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710592 prefixEnd_710592 := by exact prefixLift 710592
  have htrace : WordTrace (prefixWord ++ tailWord_710592) baseStart_710592 baseEnd_710592 := by
    simpa [prefixWord, tailWord_710592, baseEnd_710592] using wordTrace_append hprefix tailTrace_710592
  have hstable : (prefixWord ++ tailWord_710592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710592).length < 2 ^ (prefixWord ++ tailWord_710592).sum := by decide
  have hdescent : baseEnd_710592 < baseStart_710592 := by decide
  rcases family_descends (prefixWord ++ tailWord_710592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710615 : List Nat := [1, 1, 3, 2, 1, 1, 3, 6, 5]
def baseStart_710615 : Nat := 118140960795 + 710615 * 2 ^ 59
def prefixEnd_710615 : Nat := 4983230072969 + 3 ^ 40 * 710615 * 2
def baseEnd_710615 : Nat := 40543006143871383249383

theorem tailTrace_710615 : CollatzResearch.WordTrace tailWord_710615 prefixEnd_710615 40543006143871383249383 := by
  unfold tailWord_710615
  simp only [CollatzResearch.WordTrace]
  refine ⟨25918258320570693224877299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17278838880380462149918199 25918258320570693224877299)
  ·
    refine ⟨38877387480856039837315949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25918258320570693224877299 38877387480856039837315949)
    ·
      refine ⟨14579020305321014938993481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38877387480856039837315949 14579020305321014938993481)
      ·
        refine ⟨10934265228990761204245111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14579020305321014938993481 10934265228990761204245111)
        ·
          refine ⟨16401397843486141806367667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10934265228990761204245111 16401397843486141806367667)
          ·
            refine ⟨24602096765229212709551501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16401397843486141806367667 24602096765229212709551501)
            ·
              refine ⟨9225786286960954766081813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24602096765229212709551501 9225786286960954766081813)
              ·
                refine ⟨432458732201294754660085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9225786286960954766081813 432458732201294754660085)
                ·
                  refine ⟨40543006143871383249383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 432458732201294754660085 40543006143871383249383)
                  ·
                    rfl

theorem cell23_710615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 5].length) (baseStart_710615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710615 prefixEnd_710615 := by exact prefixLift 710615
  have htrace : WordTrace (prefixWord ++ tailWord_710615) baseStart_710615 baseEnd_710615 := by
    simpa [prefixWord, tailWord_710615, baseEnd_710615] using wordTrace_append hprefix tailTrace_710615
  have hstable : (prefixWord ++ tailWord_710615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710615).length < 2 ^ (prefixWord ++ tailWord_710615).sum := by decide
  have hdescent : baseEnd_710615 < baseStart_710615 := by decide
  rcases family_descends (prefixWord ++ tailWord_710615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710620 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_710620 : Nat := 118140960795 + 710620 * 2 ^ 59
def prefixEnd_710620 : Nat := 4983230072969 + 3 ^ 40 * 710620 * 2
def baseEnd_710620 : Nat := 364889622698114929681925

theorem tailTrace_710620 : CollatzResearch.WordTrace tailWord_710620 prefixEnd_710620 364889622698114929681925 := by
  unfold tailWord_710620
  simp only [CollatzResearch.WordTrace]
  refine ⟨12959220342776289539404657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17278960457035052719206209 12959220342776289539404657)
  ·
    refine ⟨9719415257082217154553493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12959220342776289539404657 9719415257082217154553493)
    ·
      refine ⟨455597590175728929119695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9719415257082217154553493 455597590175728929119695)
      ·
        refine ⟨683396385263593393679543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455597590175728929119695 683396385263593393679543)
        ·
          refine ⟨1025094577895390090519315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683396385263593393679543 1025094577895390090519315)
          ·
            refine ⟨1537641866843085135778973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025094577895390090519315 1537641866843085135778973)
            ·
              refine ⟨576615700066156925917115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1537641866843085135778973 576615700066156925917115)
              ·
                refine ⟨864923550099235388875673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576615700066156925917115 864923550099235388875673)
                ·
                  refine ⟨648692662574426541656755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864923550099235388875673 648692662574426541656755)
                  ·
                    refine ⟨973038993861639812485133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 648692662574426541656755 973038993861639812485133)
                    ·
                      refine ⟨364889622698114929681925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 973038993861639812485133 364889622698114929681925)
                      ·
                        rfl

theorem cell23_710620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_710620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710620 prefixEnd_710620 := by exact prefixLift 710620
  have htrace : WordTrace (prefixWord ++ tailWord_710620) baseStart_710620 baseEnd_710620 := by
    simpa [prefixWord, tailWord_710620, baseEnd_710620] using wordTrace_append hprefix tailTrace_710620
  have hstable : (prefixWord ++ tailWord_710620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710620).length < 2 ^ (prefixWord ++ tailWord_710620).sum := by decide
  have hdescent : baseEnd_710620 < baseStart_710620 := by decide
  rcases family_descends (prefixWord ++ tailWord_710620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710625 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_710625 : Nat := 118140960795 + 710625 * 2 ^ 59
def prefixEnd_710625 : Nat := 4983230072969 + 3 ^ 40 * 710625 * 2
def baseEnd_710625 : Nat := 364892190101387410119401

theorem tailTrace_710625 : CollatzResearch.WordTrace tailWord_710625 prefixEnd_710625 364892190101387410119401 := by
  unfold tailWord_710625
  simp only [CollatzResearch.WordTrace]
  refine ⟨25918623050534464932741329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17279082033689643288494219 25918623050534464932741329)
  ·
    refine ⟨19438967287900848699555997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25918623050534464932741329 19438967287900848699555997)
    ·
      refine ⟨7289612732962818262333499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19438967287900848699555997 7289612732962818262333499)
      ·
        refine ⟨10934419099444227393500249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289612732962818262333499 10934419099444227393500249)
        ·
          refine ⟨8200814324583170545125187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10934419099444227393500249 8200814324583170545125187)
          ·
            refine ⟨12301221486874755817687781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200814324583170545125187 12301221486874755817687781)
            ·
              refine ⟨2306479028789016715816459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12301221486874755817687781 2306479028789016715816459)
              ·
                refine ⟨3459718543183525073724689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306479028789016715816459 3459718543183525073724689)
                ·
                  refine ⟨2594788907387643805293517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3459718543183525073724689 2594788907387643805293517)
                  ·
                    refine ⟨973045840270366426985069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2594788907387643805293517 973045840270366426985069)
                    ·
                      refine ⟨364892190101387410119401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 973045840270366426985069 364892190101387410119401)
                      ·
                        rfl

theorem cell23_710625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_710625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710625 prefixEnd_710625 := by exact prefixLift 710625
  have htrace : WordTrace (prefixWord ++ tailWord_710625) baseStart_710625 baseEnd_710625 := by
    simpa [prefixWord, tailWord_710625, baseEnd_710625] using wordTrace_append hprefix tailTrace_710625
  have hstable : (prefixWord ++ tailWord_710625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710625).length < 2 ^ (prefixWord ++ tailWord_710625).sum := by decide
  have hdescent : baseEnd_710625 < baseStart_710625 := by decide
  rcases family_descends (prefixWord ++ tailWord_710625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710628 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_710628 : Nat := 118140960795 + 710628 * 2 ^ 59
def prefixEnd_710628 : Nat := 4983230072969 + 3 ^ 40 * 710628 * 2
def baseEnd_710628 : Nat := 121631243514450299460629

theorem tailTrace_710628 : CollatzResearch.WordTrace tailWord_710628 prefixEnd_710628 121631243514450299460629 := by
  unfold tailWord_710628
  simp only [CollatzResearch.WordTrace]
  refine ⟨12959366234761798222550269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17279154979682397630067025 12959366234761798222550269)
  ·
    refine ⟨4859762338035674333456351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12959366234761798222550269 4859762338035674333456351)
    ·
      refine ⟨7289643507053511500184527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4859762338035674333456351 7289643507053511500184527)
      ·
        refine ⟨10934465260580267250276791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289643507053511500184527 10934465260580267250276791)
        ·
          refine ⟨16401697890870400875415187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10934465260580267250276791 16401697890870400875415187)
          ·
            refine ⟨24602546836305601313122781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16401697890870400875415187 24602546836305601313122781)
            ·
              refine ⟨9225955063614600492421043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24602546836305601313122781 9225955063614600492421043)
              ·
                refine ⟨13838932595421900738631565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225955063614600492421043 13838932595421900738631565)
                ·
                  refine ⟨5189599723283212776986837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13838932595421900738631565 5189599723283212776986837)
                  ·
                    refine ⟨121631243514450299460629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5189599723283212776986837 121631243514450299460629)
                    ·
                      rfl

theorem cell23_710628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_710628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710628 prefixEnd_710628 := by exact prefixLift 710628
  have htrace : WordTrace (prefixWord ++ tailWord_710628) baseStart_710628 baseEnd_710628 := by
    simpa [prefixWord, tailWord_710628, baseEnd_710628] using wordTrace_append hprefix tailTrace_710628
  have hstable : (prefixWord ++ tailWord_710628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710628).length < 2 ^ (prefixWord ++ tailWord_710628).sum := by decide
  have hdescent : baseEnd_710628 < baseStart_710628 := by decide
  rcases family_descends (prefixWord ++ tailWord_710628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710635 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 2, 5, 2]
def baseStart_710635 : Nat := 118140960795 + 710635 * 2 ^ 59
def prefixEnd_710635 : Nat := 4983230072969 + 3 ^ 40 * 710635 * 2
def baseEnd_710635 : Nat := 364897324907932370994355

theorem tailTrace_710635 : CollatzResearch.WordTrace tailWord_710635 prefixEnd_710635 364897324907932370994355 := by
  unfold tailWord_710635
  simp only [CollatzResearch.WordTrace]
  refine ⟨25918987780498236640605359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17279325186998824427070239 25918987780498236640605359)
  ·
    refine ⟨38878481670747354960908039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25918987780498236640605359 38878481670747354960908039)
    ·
      refine ⟨58317722506121032441362059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38878481670747354960908039 58317722506121032441362059)
      ·
        refine ⟨87476583759181548662043089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58317722506121032441362059 87476583759181548662043089)
        ·
          refine ⟨65607437819386161496532317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87476583759181548662043089 65607437819386161496532317)
          ·
            refine ⟨24602789182269810561199619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65607437819386161496532317 24602789182269810561199619)
            ·
              refine ⟨36904183773404715841799429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24602789182269810561199619 36904183773404715841799429)
              ·
                refine ⟨6919534457513384220337393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36904183773404715841799429 6919534457513384220337393)
                ·
                  refine ⟨5189650843135038165253045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919534457513384220337393 5189650843135038165253045)
                  ·
                    refine ⟨486529766543909827992473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5189650843135038165253045 486529766543909827992473)
                    ·
                      refine ⟨364897324907932370994355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486529766543909827992473 364897324907932370994355)
                      ·
                        rfl

theorem cell23_710635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 5, 2].length) (baseStart_710635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710635 prefixEnd_710635 := by exact prefixLift 710635
  have htrace : WordTrace (prefixWord ++ tailWord_710635) baseStart_710635 baseEnd_710635 := by
    simpa [prefixWord, tailWord_710635, baseEnd_710635] using wordTrace_append hprefix tailTrace_710635
  have hstable : (prefixWord ++ tailWord_710635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710635).length < 2 ^ (prefixWord ++ tailWord_710635).sum := by decide
  have hdescent : baseEnd_710635 < baseStart_710635 := by decide
  rcases family_descends (prefixWord ++ tailWord_710635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710750 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_710750 : Nat := 118140960795 + 710750 * 2 ^ 59
def prefixEnd_710750 : Nat := 4983230072969 + 3 ^ 40 * 710750 * 2
def baseEnd_710750 : Nat := 364956375183199421056327

theorem tailTrace_710750 : CollatzResearch.WordTrace tailWord_710750 prefixEnd_710750 364956375183199421056327 := by
  unfold tailWord_710750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3240397771885201410130213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17282121450054407520694469 3240397771885201410130213)
  ·
    refine ⟨607574582228475264399415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3240397771885201410130213 607574582228475264399415)
    ·
      refine ⟨911361873342712896599123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607574582228475264399415 911361873342712896599123)
      ·
        refine ⟨1367042810014069344898685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911361873342712896599123 1367042810014069344898685)
        ·
          refine ⟨512641053755276004337007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1367042810014069344898685 512641053755276004337007)
          ·
            refine ⟨768961580632914006505511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512641053755276004337007 768961580632914006505511)
            ·
              refine ⟨1153442370949371009758267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768961580632914006505511 1153442370949371009758267)
              ·
                refine ⟨1730163556424056514637401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153442370949371009758267 1730163556424056514637401)
                ·
                  refine ⟨1297622667318042385978051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1730163556424056514637401 1297622667318042385978051)
                  ·
                    refine ⟨1946434000977063578967077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1297622667318042385978051 1946434000977063578967077)
                    ·
                      refine ⟨364956375183199421056327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1946434000977063578967077 364956375183199421056327)
                      ·
                        rfl

theorem cell23_710750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_710750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710750 prefixEnd_710750 := by exact prefixLift 710750
  have htrace : WordTrace (prefixWord ++ tailWord_710750) baseStart_710750 baseEnd_710750 := by
    simpa [prefixWord, tailWord_710750, baseEnd_710750] using wordTrace_append hprefix tailTrace_710750
  have hstable : (prefixWord ++ tailWord_710750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710750).length < 2 ^ (prefixWord ++ tailWord_710750).sum := by decide
  have hdescent : baseEnd_710750 < baseStart_710750 := by decide
  rcases family_descends (prefixWord ++ tailWord_710750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710792 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_710792 : Nat := 118140960795 + 710792 * 2 ^ 59
def prefixEnd_710792 : Nat := 4983230072969 + 3 ^ 40 * 710792 * 2
def baseEnd_710792 : Nat := 364977941370688256731133

theorem tailTrace_710792 : CollatzResearch.WordTrace tailWord_710792 prefixEnd_710792 364977941370688256731133 := by
  unfold tailWord_710792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12962357020464726227035315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17283142693952968302713753 12962357020464726227035315)
  ·
    refine ⟨19443535530697089340552973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12962357020464726227035315 19443535530697089340552973)
    ·
      refine ⟨7291325824011408502707365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19443535530697089340552973 7291325824011408502707365)
      ·
        refine ⟨1367123592002139094257631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7291325824011408502707365 1367123592002139094257631)
        ·
          refine ⟨2050685388003208641386447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367123592002139094257631 2050685388003208641386447)
          ·
            refine ⟨3076028082004812962079671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050685388003208641386447 3076028082004812962079671)
            ·
              refine ⟨4614042123007219443119507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076028082004812962079671 4614042123007219443119507)
              ·
                refine ⟨6921063184510829164679261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4614042123007219443119507 6921063184510829164679261)
                ·
                  refine ⟨2595398694191560936754723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6921063184510829164679261 2595398694191560936754723)
                  ·
                    refine ⟨3893098041287341405132085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595398694191560936754723 3893098041287341405132085)
                    ·
                      refine ⟨364977941370688256731133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3893098041287341405132085 364977941370688256731133)
                      ·
                        rfl

theorem cell23_710792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_710792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710792 prefixEnd_710792 := by exact prefixLift 710792
  have htrace : WordTrace (prefixWord ++ tailWord_710792) baseStart_710792 baseEnd_710792 := by
    simpa [prefixWord, tailWord_710792, baseEnd_710792] using wordTrace_append hprefix tailTrace_710792
  have hstable : (prefixWord ++ tailWord_710792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710792).length < 2 ^ (prefixWord ++ tailWord_710792).sum := by decide
  have hdescent : baseEnd_710792 < baseStart_710792 := by decide
  rcases family_descends (prefixWord ++ tailWord_710792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710802 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_710802 : Nat := 118140960795 + 710802 * 2 ^ 59
def prefixEnd_710802 : Nat := 4983230072969 + 3 ^ 40 * 710802 * 2
def baseEnd_710802 : Nat := 364983076177233217606087

theorem tailTrace_710802 : CollatzResearch.WordTrace tailWord_710802 prefixEnd_710802 364983076177233217606087 := by
  unfold tailWord_710802
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481269692723306040483665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17283385847262149441289773 6481269692723306040483665)
  ·
    refine ⟨4860952269542479530362749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6481269692723306040483665 4860952269542479530362749)
    ·
      refine ⟨1822857101078429823886031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4860952269542479530362749 1822857101078429823886031)
      ·
        refine ⟨2734285651617644735829047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822857101078429823886031 2734285651617644735829047)
        ·
          refine ⟨4101428477426467103743571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734285651617644735829047 4101428477426467103743571)
          ·
            refine ⟨6152142716139700655615357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101428477426467103743571 6152142716139700655615357)
            ·
              refine ⟨2307053518552387745855759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6152142716139700655615357 2307053518552387745855759)
              ·
                refine ⟨3460580277828581618783639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307053518552387745855759 3460580277828581618783639)
                ·
                  refine ⟨5190870416742872428175459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460580277828581618783639 5190870416742872428175459)
                  ·
                    refine ⟨7786305625114308642263189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5190870416742872428175459 7786305625114308642263189)
                    ·
                      refine ⟨364983076177233217606087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7786305625114308642263189 364983076177233217606087)
                      ·
                        rfl

theorem cell23_710802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_710802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710802 prefixEnd_710802 := by exact prefixLift 710802
  have htrace : WordTrace (prefixWord ++ tailWord_710802) baseStart_710802 baseEnd_710802 := by
    simpa [prefixWord, tailWord_710802, baseEnd_710802] using wordTrace_append hprefix tailTrace_710802
  have hstable : (prefixWord ++ tailWord_710802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710802).length < 2 ^ (prefixWord ++ tailWord_710802).sum := by decide
  have hdescent : baseEnd_710802 < baseStart_710802 := by decide
  rcases family_descends (prefixWord ++ tailWord_710802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710826 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_710826 : Nat := 118140960795 + 710826 * 2 ^ 59
def prefixEnd_710826 : Nat := 4983230072969 + 3 ^ 40 * 710826 * 2
def baseEnd_710826 : Nat := 364995399712941123705977

theorem tailTrace_710826 : CollatzResearch.WordTrace tailWord_710826 prefixEnd_710826 364995399712941123705977 := by
  unfold tailWord_710826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481488530701569065202083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17283969415204184173872221 6481488530701569065202083)
  ·
    refine ⟨9722232796052353597803125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6481488530701569065202083 9722232796052353597803125)
    ·
      refine ⟨911459324629908149794043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9722232796052353597803125 911459324629908149794043)
      ·
        refine ⟨1367188986944862224691065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911459324629908149794043 1367188986944862224691065)
        ·
          refine ⟨1025391740208646668518299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1367188986944862224691065 1025391740208646668518299)
          ·
            refine ⟨1538087610312970002777449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025391740208646668518299 1538087610312970002777449)
            ·
              refine ⟨1153565707734727502083087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538087610312970002777449 1153565707734727502083087)
              ·
                refine ⟨1730348561602091253124631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153565707734727502083087 1730348561602091253124631)
                ·
                  refine ⟨2595522842403136879686947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1730348561602091253124631 2595522842403136879686947)
                  ·
                    refine ⟨3893284263604705319530421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2595522842403136879686947 3893284263604705319530421)
                    ·
                      refine ⟨364995399712941123705977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3893284263604705319530421 364995399712941123705977)
                      ·
                        rfl

theorem cell23_710826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_710826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710826 prefixEnd_710826 := by exact prefixLift 710826
  have htrace : WordTrace (prefixWord ++ tailWord_710826) baseStart_710826 baseEnd_710826 := by
    simpa [prefixWord, tailWord_710826, baseEnd_710826] using wordTrace_append hprefix tailTrace_710826
  have hstable : (prefixWord ++ tailWord_710826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710826).length < 2 ^ (prefixWord ++ tailWord_710826).sum := by decide
  have hdescent : baseEnd_710826 < baseStart_710826 := by decide
  rcases family_descends (prefixWord ++ tailWord_710826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710835 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5]
def baseStart_710835 : Nat := 118140960795 + 710835 * 2 ^ 59
def prefixEnd_710835 : Nat := 4983230072969 + 3 ^ 40 * 710835 * 2
def baseEnd_710835 : Nat := 365000021038831588493435

theorem tailTrace_710835 : CollatzResearch.WordTrace tailWord_710835 prefixEnd_710835 365000021038831588493435 := by
  unfold tailWord_710835
  simp only [CollatzResearch.WordTrace]
  refine ⟨25926282379773670797885959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17284188253182447198590639 25926282379773670797885959)
  ·
    refine ⟨38889423569660506196828939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25926282379773670797885959 38889423569660506196828939)
    ·
      refine ⟨58334135354490759295243409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38889423569660506196828939 58334135354490759295243409)
      ·
        refine ⟨43750601515868069471432557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58334135354490759295243409 43750601515868069471432557)
        ·
          refine ⟨16406475568450526051787209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43750601515868069471432557 16406475568450526051787209)
          ·
            refine ⟨12304856676337894538840407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16406475568450526051787209 12304856676337894538840407)
            ·
              refine ⟨18457285014506841808260611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12304856676337894538840407 18457285014506841808260611)
              ·
                refine ⟨27685927521760262712390917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18457285014506841808260611 27685927521760262712390917)
                ·
                  refine ⟨5191111410330049258573297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27685927521760262712390917 5191111410330049258573297)
                  ·
                    refine ⟨3893333557747536943929973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5191111410330049258573297 3893333557747536943929973)
                    ·
                      refine ⟨365000021038831588493435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3893333557747536943929973 365000021038831588493435)
                      ·
                        rfl

theorem cell23_710835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_710835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710835 prefixEnd_710835 := by exact prefixLift 710835
  have htrace : WordTrace (prefixWord ++ tailWord_710835) baseStart_710835 baseEnd_710835 := by
    simpa [prefixWord, tailWord_710835, baseEnd_710835] using wordTrace_append hprefix tailTrace_710835
  have hstable : (prefixWord ++ tailWord_710835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710835).length < 2 ^ (prefixWord ++ tailWord_710835).sum := by decide
  have hdescent : baseEnd_710835 < baseStart_710835 := by decide
  rcases family_descends (prefixWord ++ tailWord_710835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710839 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_710839 : Nat := 118140960795 + 710839 * 2 ^ 59
def prefixEnd_710839 : Nat := 4983230072969 + 3 ^ 40 * 710839 * 2
def baseEnd_710839 : Nat := 365002074961449572843417

theorem tailTrace_710839 : CollatzResearch.WordTrace tailWord_710839 prefixEnd_710839 365002074961449572843417 := by
  unfold tailWord_710839
  simp only [CollatzResearch.WordTrace]
  refine ⟨25926428271759179481031571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17284285514506119654021047 25926428271759179481031571)
  ·
    refine ⟨38889642407638769221547357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25926428271759179481031571 38889642407638769221547357)
    ·
      refine ⟨14583615902864538458080259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38889642407638769221547357 14583615902864538458080259)
      ·
        refine ⟨21875423854296807687120389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14583615902864538458080259 21875423854296807687120389)
        ·
          refine ⟨4101641972680651441335073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21875423854296807687120389 4101641972680651441335073)
          ·
            refine ⟨3076231479510488581001305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4101641972680651441335073 3076231479510488581001305)
            ·
              refine ⟨2307173609632866435750979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3076231479510488581001305 2307173609632866435750979)
              ·
                refine ⟨3460760414449299653626469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307173609632866435750979 3460760414449299653626469)
                ·
                  refine ⟨648892577709243685054963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3460760414449299653626469 648892577709243685054963)
                  ·
                    refine ⟨973338866563865527582445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 648892577709243685054963 973338866563865527582445)
                    ·
                      refine ⟨365002074961449572843417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 973338866563865527582445 365002074961449572843417)
                      ·
                        rfl

theorem cell23_710839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_710839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710839 prefixEnd_710839 := by exact prefixLift 710839
  have htrace : WordTrace (prefixWord ++ tailWord_710839) baseStart_710839 baseEnd_710839 := by
    simpa [prefixWord, tailWord_710839, baseEnd_710839] using wordTrace_append hprefix tailTrace_710839
  have hstable : (prefixWord ++ tailWord_710839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710839).length < 2 ^ (prefixWord ++ tailWord_710839).sum := by decide
  have hdescent : baseEnd_710839 < baseStart_710839 := by decide
  rcases family_descends (prefixWord ++ tailWord_710839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710850 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_710850 : Nat := 118140960795 + 710850 * 2 ^ 59
def prefixEnd_710850 : Nat := 4983230072969 + 3 ^ 40 * 710850 * 2
def baseEnd_710850 : Nat := 121669241082883009935289

theorem tailTrace_710850 : CollatzResearch.WordTrace tailWord_710850 prefixEnd_710850 121669241082883009935289 := by
  unfold tailWord_710850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481707368679832089920501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17284552983146218906454669 6481707368679832089920501)
  ·
    refine ⟨607660065813734258430047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6481707368679832089920501 607660065813734258430047)
    ·
      refine ⟨911490098720601387645071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607660065813734258430047 911490098720601387645071)
      ·
        refine ⟨1367235148080902081467607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911490098720601387645071 1367235148080902081467607)
        ·
          refine ⟨2050852722121353122201411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367235148080902081467607 2050852722121353122201411)
          ·
            refine ⟨3076279083182029683302117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050852722121353122201411 3076279083182029683302117)
            ·
              refine ⟨576802328096630565619147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3076279083182029683302117 576802328096630565619147)
              ·
                refine ⟨865203492144945848428721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576802328096630565619147 865203492144945848428721)
                ·
                  refine ⟨648902619108709386321541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 865203492144945848428721 648902619108709386321541)
                  ·
                    refine ⟨121669241082883009935289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 648902619108709386321541 121669241082883009935289)
                    ·
                      rfl

theorem cell23_710850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_710850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710850 prefixEnd_710850 := by exact prefixLift 710850
  have htrace : WordTrace (prefixWord ++ tailWord_710850) baseStart_710850 baseEnd_710850 := by
    simpa [prefixWord, tailWord_710850, baseEnd_710850] using wordTrace_append hprefix tailTrace_710850
  have hstable : (prefixWord ++ tailWord_710850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710850).length < 2 ^ (prefixWord ++ tailWord_710850).sum := by decide
  have hdescent : baseEnd_710850 < baseStart_710850 := by decide
  rcases family_descends (prefixWord ++ tailWord_710850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710860 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 1, 2, 3]
def baseStart_710860 : Nat := 118140960795 + 710860 * 2 ^ 59
def prefixEnd_710860 : Nat := 4983230072969 + 3 ^ 40 * 710860 * 2
def baseEnd_710860 : Nat := 365012858055193990680821

theorem tailTrace_710860 : CollatzResearch.WordTrace tailWord_710860 prefixEnd_710860 365012858055193990680821 := by
  unfold tailWord_710860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12963597102341550033773017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17284796136455400045030689 12963597102341550033773017)
  ·
    refine ⟨9722697826756162525329763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12963597102341550033773017 9722697826756162525329763)
    ·
      refine ⟨14584046740134243787994645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9722697826756162525329763 14584046740134243787994645)
      ·
        refine ⟨683627190943792677562249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14584046740134243787994645 683627190943792677562249)
        ·
          refine ⟨512720393207844508171687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683627190943792677562249 512720393207844508171687)
          ·
            refine ⟨769080589811766762257531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512720393207844508171687 769080589811766762257531)
            ·
              refine ⟨1153620884717650143386297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769080589811766762257531 1153620884717650143386297)
              ·
                refine ⟨865215663538237607539723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153620884717650143386297 865215663538237607539723)
                ·
                  refine ⟨1297823495307356411309585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865215663538237607539723 1297823495307356411309585)
                  ·
                    refine ⟨973367621480517308482189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1297823495307356411309585 973367621480517308482189)
                    ·
                      refine ⟨365012858055193990680821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 973367621480517308482189 365012858055193990680821)
                      ·
                        rfl

theorem cell23_710860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_710860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710860 prefixEnd_710860 := by exact prefixLift 710860
  have htrace : WordTrace (prefixWord ++ tailWord_710860) baseStart_710860 baseEnd_710860 := by
    simpa [prefixWord, tailWord_710860, baseEnd_710860] using wordTrace_append hprefix tailTrace_710860
  have hstable : (prefixWord ++ tailWord_710860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710860).length < 2 ^ (prefixWord ++ tailWord_710860).sum := by decide
  have hdescent : baseEnd_710860 < baseStart_710860 := by decide
  rcases family_descends (prefixWord ++ tailWord_710860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710866 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_710866 : Nat := 118140960795 + 710866 * 2 ^ 59
def prefixEnd_710866 : Nat := 4983230072969 + 3 ^ 40 * 710866 * 2
def baseEnd_710866 : Nat := 365015938939120967205793

theorem tailTrace_710866 : CollatzResearch.WordTrace tailWord_710866 prefixEnd_710866 365015938939120967205793 := by
  unfold tailWord_710866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481853260665340773066113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17284942028440908728176301 6481853260665340773066113)
  ·
    refine ⟨4861389945499005579799585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6481853260665340773066113 4861389945499005579799585)
    ·
      refine ⟨3646042459124254184849689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4861389945499005579799585 3646042459124254184849689)
      ·
        refine ⟨2734531844343190638637267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3646042459124254184849689 2734531844343190638637267)
        ·
          refine ⟨4101797766514785957955901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734531844343190638637267 4101797766514785957955901)
          ·
            refine ⟨1538174162443044734233463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4101797766514785957955901 1538174162443044734233463)
            ·
              refine ⟨2307261243664567101350195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538174162443044734233463 2307261243664567101350195)
              ·
                refine ⟨3460891865496850652025293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2307261243664567101350195 3460891865496850652025293)
                ·
                  refine ⟨1297834449561318994509485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3460891865496850652025293 1297834449561318994509485)
                  ·
                    refine ⟨486687918585494622941057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1297834449561318994509485 486687918585494622941057)
                    ·
                      refine ⟨365015938939120967205793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486687918585494622941057 365015938939120967205793)
                      ·
                        rfl

theorem cell23_710866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_710866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710866 prefixEnd_710866 := by exact prefixLift 710866
  have htrace : WordTrace (prefixWord ++ tailWord_710866) baseStart_710866 baseEnd_710866 := by
    simpa [prefixWord, tailWord_710866, baseEnd_710866] using wordTrace_append hprefix tailTrace_710866
  have hstable : (prefixWord ++ tailWord_710866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710866).length < 2 ^ (prefixWord ++ tailWord_710866).sum := by decide
  have hdescent : baseEnd_710866 < baseStart_710866 := by decide
  rcases family_descends (prefixWord ++ tailWord_710866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710892 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_710892 : Nat := 118140960795 + 710892 * 2 ^ 59
def prefixEnd_710892 : Nat := 4983230072969 + 3 ^ 40 * 710892 * 2
def baseEnd_710892 : Nat := 365029289436137865480673

theorem tailTrace_710892 : CollatzResearch.WordTrace tailWord_710892 prefixEnd_710892 365029289436137865480673 := by
  unfold tailWord_710892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12964180670283584766355465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17285574227044779688473953 12964180670283584766355465)
  ·
    refine ⟨9723135502712688574766599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12964180670283584766355465 9723135502712688574766599)
    ·
      refine ⟨14584703254069032862149899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9723135502712688574766599 14584703254069032862149899)
      ·
        refine ⟨21877054881103549293224849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14584703254069032862149899 21877054881103549293224849)
        ·
          refine ⟨16407791160827661969918637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21877054881103549293224849 16407791160827661969918637)
          ·
            refine ⟨6152921685310373238719489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16407791160827661969918637 6152921685310373238719489)
            ·
              refine ⟨4614691263982779929039617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6152921685310373238719489 4614691263982779929039617)
              ·
                refine ⟨3461018447987084946779713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614691263982779929039617 3461018447987084946779713)
                ·
                  refine ⟨2595763835990313710084785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461018447987084946779713 2595763835990313710084785)
                  ·
                    refine ⟨1946822876992735282563589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2595763835990313710084785 1946822876992735282563589)
                    ·
                      refine ⟨365029289436137865480673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1946822876992735282563589 365029289436137865480673)
                      ·
                        rfl

theorem cell23_710892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_710892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710892 prefixEnd_710892 := by exact prefixLift 710892
  have htrace : WordTrace (prefixWord ++ tailWord_710892) baseStart_710892 baseEnd_710892 := by
    simpa [prefixWord, tailWord_710892, baseEnd_710892] using wordTrace_append hprefix tailTrace_710892
  have hstable : (prefixWord ++ tailWord_710892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710892).length < 2 ^ (prefixWord ++ tailWord_710892).sum := by decide
  have hdescent : baseEnd_710892 < baseStart_710892 := by decide
  rcases family_descends (prefixWord ++ tailWord_710892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710912 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3]
def baseStart_710912 : Nat := 118140960795 + 710912 * 2 ^ 59
def prefixEnd_710912 : Nat := 4983230072969 + 3 ^ 40 * 710912 * 2
def baseEnd_710912 : Nat := 365039559049227787230581

theorem tailTrace_710912 : CollatzResearch.WordTrace tailWord_710912 prefixEnd_710912 365039559049227787230581 := by
  unfold tailWord_710912
  simp only [CollatzResearch.WordTrace]
  refine ⟨12964545400247356474219495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17286060533663141965625993 12964545400247356474219495)
  ·
    refine ⟨19446818100371034711329243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12964545400247356474219495 19446818100371034711329243)
    ·
      refine ⟨29170227150556552066993865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19446818100371034711329243 29170227150556552066993865)
      ·
        refine ⟨21877670362917414050245399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29170227150556552066993865 21877670362917414050245399)
        ·
          refine ⟨32816505544376121075368099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21877670362917414050245399 32816505544376121075368099)
          ·
            refine ⟨49224758316564181613052149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32816505544376121075368099 49224758316564181613052149)
            ·
              refine ⟨4614821092177892026223639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49224758316564181613052149 4614821092177892026223639)
              ·
                refine ⟨6922231638266838039335459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4614821092177892026223639 6922231638266838039335459)
                ·
                  refine ⟨10383347457400257059003189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6922231638266838039335459 10383347457400257059003189)
                  ·
                    refine ⟨973438824131274099281549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10383347457400257059003189 973438824131274099281549)
                    ·
                      refine ⟨365039559049227787230581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 973438824131274099281549 365039559049227787230581)
                      ·
                        rfl

theorem cell23_710912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_710912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710912 prefixEnd_710912 := by exact prefixLift 710912
  have htrace : WordTrace (prefixWord ++ tailWord_710912) baseStart_710912 baseEnd_710912 := by
    simpa [prefixWord, tailWord_710912, baseEnd_710912] using wordTrace_append hprefix tailTrace_710912
  have hstable : (prefixWord ++ tailWord_710912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710912).length < 2 ^ (prefixWord ++ tailWord_710912).sum := by decide
  have hdescent : baseEnd_710912 < baseStart_710912 := by decide
  rcases family_descends (prefixWord ++ tailWord_710912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710969 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_710969 : Nat := 118140960795 + 710969 * 2 ^ 59
def prefixEnd_710969 : Nat := 4983230072969 + 3 ^ 40 * 710969 * 2
def baseEnd_710969 : Nat := 365068827446534064217819

theorem tailTrace_710969 : CollatzResearch.WordTrace tailWord_710969 prefixEnd_710969 365068827446534064217819 := by
  unfold tailWord_710969
  simp only [CollatzResearch.WordTrace]
  refine ⟨25931169761288211683263961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17287446507525474455509307 25931169761288211683263961)
  ·
    refine ⟨19448377320966158762447971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25931169761288211683263961 19448377320966158762447971)
    ·
      refine ⟨29172565981449238143671957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19448377320966158762447971 29172565981449238143671957)
      ·
        refine ⟨1367464030380433037984623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29172565981449238143671957 1367464030380433037984623)
        ·
          refine ⟨2051196045570649556976935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367464030380433037984623 2051196045570649556976935)
          ·
            refine ⟨3076794068355974335465403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051196045570649556976935 3076794068355974335465403)
            ·
              refine ⟨4615191102533961503198105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076794068355974335465403 4615191102533961503198105)
              ·
                refine ⟨3461393326900471127398579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4615191102533961503198105 3461393326900471127398579)
                ·
                  refine ⟨5192089990350706691097869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461393326900471127398579 5192089990350706691097869)
                  ·
                    refine ⟨1947033746381515009161701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5192089990350706691097869 1947033746381515009161701)
                    ·
                      refine ⟨365068827446534064217819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1947033746381515009161701 365068827446534064217819)
                      ·
                        rfl

theorem cell23_710969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_710969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710969 prefixEnd_710969 := by exact prefixLift 710969
  have htrace : WordTrace (prefixWord ++ tailWord_710969) baseStart_710969 baseEnd_710969 := by
    simpa [prefixWord, tailWord_710969, baseEnd_710969] using wordTrace_append hprefix tailTrace_710969
  have hstable : (prefixWord ++ tailWord_710969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710969).length < 2 ^ (prefixWord ++ tailWord_710969).sum := by decide
  have hdescent : baseEnd_710969 < baseStart_710969 := by decide
  rcases family_descends (prefixWord ++ tailWord_710969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710979 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 3, 4]
def baseStart_710979 : Nat := 118140960795 + 710979 * 2 ^ 59
def prefixEnd_710979 : Nat := 4983230072969 + 3 ^ 40 * 710979 * 2
def baseEnd_710979 : Nat := 121691320751026341697591

theorem tailTrace_710979 : CollatzResearch.WordTrace tailWord_710979 prefixEnd_710979 121691320751026341697591 := by
  unfold tailWord_710979
  simp only [CollatzResearch.WordTrace]
  refine ⟨25931534491251983391127991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17287689660834655594085327 25931534491251983391127991)
  ·
    refine ⟨38897301736877975086691987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25931534491251983391127991 38897301736877975086691987)
    ·
      refine ⟨58345952605316962630037981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38897301736877975086691987 58345952605316962630037981)
      ·
        refine ⟨21879732226993860986264243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58345952605316962630037981 21879732226993860986264243)
        ·
          refine ⟨32819598340490791479396365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21879732226993860986264243 32819598340490791479396365)
          ·
            refine ⟨12307349377684046804773637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32819598340490791479396365 12307349377684046804773637)
            ·
              refine ⟨2307628008315758775895057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12307349377684046804773637 2307628008315758775895057)
              ·
                refine ⟨1730721006236819081921293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307628008315758775895057 1730721006236819081921293)
                ·
                  refine ⟨649020377338807155720485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1730721006236819081921293 649020377338807155720485)
                  ·
                    refine ⟨121691320751026341697591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649020377338807155720485 121691320751026341697591)
                    ·
                      rfl

theorem cell23_710979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 4].length) (baseStart_710979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710979 prefixEnd_710979 := by exact prefixLift 710979
  have htrace : WordTrace (prefixWord ++ tailWord_710979) baseStart_710979 baseEnd_710979 := by
    simpa [prefixWord, tailWord_710979, baseEnd_710979] using wordTrace_append hprefix tailTrace_710979
  have hstable : (prefixWord ++ tailWord_710979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710979).length < 2 ^ (prefixWord ++ tailWord_710979).sum := by decide
  have hdescent : baseEnd_710979 < baseStart_710979 := by decide
  rcases family_descends (prefixWord ++ tailWord_710979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710992 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 8]
def baseStart_710992 : Nat := 118140960795 + 710992 * 2 ^ 59
def prefixEnd_710992 : Nat := 4983230072969 + 3 ^ 40 * 710992 * 2
def baseEnd_710992 : Nat := 40564515277954163803357

theorem tailTrace_710992 : CollatzResearch.WordTrace tailWord_710992 prefixEnd_710992 40564515277954163803357 := by
  unfold tailWord_710992
  simp only [CollatzResearch.WordTrace]
  refine ⟨12966004320102443305675615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17288005760136591074234153 12966004320102443305675615)
  ·
    refine ⟨19449006480153664958513423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12966004320102443305675615 19449006480153664958513423)
    ·
      refine ⟨29173509720230497437770135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19449006480153664958513423 29173509720230497437770135)
      ·
        refine ⟨43760264580345746156655203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29173509720230497437770135 43760264580345746156655203)
        ·
          refine ⟨65640396870518619234982805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43760264580345746156655203 65640396870518619234982805)
          ·
            refine ⟨3076893603305560276639819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65640396870518619234982805 3076893603305560276639819)
            ·
              refine ⟨4615340404958340414959729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076893603305560276639819 4615340404958340414959729)
              ·
                refine ⟨3461505303718755311219797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4615340404958340414959729 3461505303718755311219797)
                ·
                  refine ⟨40564515277954163803357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3461505303718755311219797 40564515277954163803357)
                  ·
                    rfl

theorem cell23_710992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_710992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_710992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_710992 prefixEnd_710992 := by exact prefixLift 710992
  have htrace : WordTrace (prefixWord ++ tailWord_710992) baseStart_710992 baseEnd_710992 := by
    simpa [prefixWord, tailWord_710992, baseEnd_710992] using wordTrace_append hprefix tailTrace_710992
  have hstable : (prefixWord ++ tailWord_710992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710992).length < 2 ^ (prefixWord ++ tailWord_710992).sum := by decide
  have hdescent : baseEnd_710992 < baseStart_710992 := by decide
  rcases family_descends (prefixWord ++ tailWord_710992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711026 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 6]
def baseStart_711026 : Nat := 118140960795 + 711026 * 2 ^ 59
def prefixEnd_711026 : Nat := 4983230072969 + 3 ^ 40 * 711026 * 2
def baseEnd_711026 : Nat := 40566455093760037911673

theorem tailTrace_711026 : CollatzResearch.WordTrace tailWord_711026 prefixEnd_711026 40566455093760037911673 := by
  unfold tailWord_711026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6483312180520427604522233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17288832481387806945392621 6483312180520427604522233)
  ·
    refine ⟨4862484135390320703391675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6483312180520427604522233 4862484135390320703391675)
    ·
      refine ⟨7293726203085481055087513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4862484135390320703391675 7293726203085481055087513)
      ·
        refine ⟨5470294652314110791315635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7293726203085481055087513 5470294652314110791315635)
        ·
          refine ⟨8205441978471166186973453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5470294652314110791315635 8205441978471166186973453)
          ·
            refine ⟨3077040741926687320115045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8205441978471166186973453 3077040741926687320115045)
            ·
              refine ⟨576945139111253872521571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3077040741926687320115045 576945139111253872521571)
              ·
                refine ⟨865417708666880808782357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576945139111253872521571 865417708666880808782357)
                ·
                  refine ⟨40566455093760037911673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 865417708666880808782357 40566455093760037911673)
                  ·
                    rfl

theorem cell23_711026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_711026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711026 prefixEnd_711026 := by exact prefixLift 711026
  have htrace : WordTrace (prefixWord ++ tailWord_711026) baseStart_711026 baseEnd_711026 := by
    simpa [prefixWord, tailWord_711026, baseEnd_711026] using wordTrace_append hprefix tailTrace_711026
  have hstable : (prefixWord ++ tailWord_711026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711026).length < 2 ^ (prefixWord ++ tailWord_711026).sum := by decide
  have hdescent : baseEnd_711026 < baseStart_711026 := by decide
  rcases family_descends (prefixWord ++ tailWord_711026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711096 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_711096 : Nat := 118140960795 + 711096 * 2 ^ 59
def prefixEnd_711096 : Nat := 4983230072969 + 3 ^ 40 * 711096 * 2
def baseEnd_711096 : Nat := 365134039489655067329735

theorem tailTrace_711096 : CollatzResearch.WordTrace tailWord_711096 prefixEnd_711096 365134039489655067329735 := by
  unfold tailWord_711096
  simp only [CollatzResearch.WordTrace]
  refine ⟨12967900915914056186568571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17290534554552074915424761 12967900915914056186568571)
  ·
    refine ⟨19451851373871084279852857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12967900915914056186568571 19451851373871084279852857)
    ·
      refine ⟨14588888530403313209889643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19451851373871084279852857 14588888530403313209889643)
      ·
        refine ⟨21883332795604969814834465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14588888530403313209889643 21883332795604969814834465)
        ·
          refine ⟨16412499596703727361125849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21883332795604969814834465 16412499596703727361125849)
          ·
            refine ⟨12309374697527795520844387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16412499596703727361125849 12309374697527795520844387)
            ·
              refine ⟨18464062046291693281266581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12309374697527795520844387 18464062046291693281266581)
              ·
                refine ⟨865502908419923122559371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18464062046291693281266581 865502908419923122559371)
                ·
                  refine ⟨1298254362629884683839057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865502908419923122559371 1298254362629884683839057)
                  ·
                    refine ⟨973690771972413512879293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1298254362629884683839057 973690771972413512879293)
                    ·
                      refine ⟨365134039489655067329735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 973690771972413512879293 365134039489655067329735)
                      ·
                        rfl

theorem cell23_711096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_711096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711096 prefixEnd_711096 := by exact prefixLift 711096
  have htrace : WordTrace (prefixWord ++ tailWord_711096) baseStart_711096 baseEnd_711096 := by
    simpa [prefixWord, tailWord_711096, baseEnd_711096] using wordTrace_append hprefix tailTrace_711096
  have hstable : (prefixWord ++ tailWord_711096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711096).length < 2 ^ (prefixWord ++ tailWord_711096).sum := by decide
  have hdescent : baseEnd_711096 < baseStart_711096 := by decide
  rcases family_descends (prefixWord ++ tailWord_711096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711113 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 1, 2, 3]
def baseStart_711113 : Nat := 118140960795 + 711113 * 2 ^ 59
def prefixEnd_711113 : Nat := 4983230072969 + 3 ^ 40 * 711113 * 2
def baseEnd_711113 : Nat := 365142768660781500817157

theorem tailTrace_711113 : CollatzResearch.WordTrace tailWord_711113 prefixEnd_711113 365142768660781500817157 := by
  unfold tailWord_711113
  simp only [CollatzResearch.WordTrace]
  refine ⟨25936421872766524276505993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17290947915177682851003995 25936421872766524276505993)
  ·
    refine ⟨19452316404574893207379495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25936421872766524276505993 19452316404574893207379495)
    ·
      refine ⟨29178474606862339811069243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19452316404574893207379495 29178474606862339811069243)
      ·
        refine ⟨43767711910293509716603865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29178474606862339811069243 43767711910293509716603865)
        ·
          refine ⟨32825783932720132287452899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43767711910293509716603865 32825783932720132287452899)
          ·
            refine ⟨49238675899080198431179349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32825783932720132287452899 49238675899080198431179349)
            ·
              refine ⟨577015733192346075365383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 49238675899080198431179349 577015733192346075365383)
              ·
                refine ⟨865523599788519113048075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577015733192346075365383 865523599788519113048075)
                ·
                  refine ⟨1298285399682778669572113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865523599788519113048075 1298285399682778669572113)
                  ·
                    refine ⟨973714049762084002179085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1298285399682778669572113 973714049762084002179085)
                    ·
                      refine ⟨365142768660781500817157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 973714049762084002179085 365142768660781500817157)
                      ·
                        rfl

theorem cell23_711113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 2, 3].length) (baseStart_711113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711113 prefixEnd_711113 := by exact prefixLift 711113
  have htrace : WordTrace (prefixWord ++ tailWord_711113) baseStart_711113 baseEnd_711113 := by
    simpa [prefixWord, tailWord_711113, baseEnd_711113] using wordTrace_append hprefix tailTrace_711113
  have hstable : (prefixWord ++ tailWord_711113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711113).length < 2 ^ (prefixWord ++ tailWord_711113).sum := by decide
  have hdescent : baseEnd_711113 < baseStart_711113 := by decide
  rcases family_descends (prefixWord ++ tailWord_711113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711204 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_711204 : Nat := 118140960795 + 711204 * 2 ^ 59
def prefixEnd_711204 : Nat := 4983230072969 + 3 ^ 40 * 711204 * 2
def baseEnd_711204 : Nat := 365189495400340644779239

theorem tailTrace_711204 : CollatzResearch.WordTrace tailWord_711204 prefixEnd_711204 365189495400340644779239 := by
  unfold tailWord_711204
  simp only [CollatzResearch.WordTrace]
  refine ⟨12969870457718423409034333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17293160610291231212045777 12969870457718423409034333)
  ·
    refine ⟨4863701421644408778387875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12969870457718423409034333 4863701421644408778387875)
    ·
      refine ⟨7295552132466613167581813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4863701421644408778387875 7295552132466613167581813)
      ·
        refine ⟨683958012418744984460795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7295552132466613167581813 683958012418744984460795)
        ·
          refine ⟨1025937018628117476691193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683958012418744984460795 1025937018628117476691193)
          ·
            refine ⟨769452763971088107518395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025937018628117476691193 769452763971088107518395)
            ·
              refine ⟨1154179145956632161277593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769452763971088107518395 1154179145956632161277593)
              ·
                refine ⟨865634359467474120958195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154179145956632161277593 865634359467474120958195)
                ·
                  refine ⟨1298451539201211181437293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865634359467474120958195 1298451539201211181437293)
                  ·
                    refine ⟨486919327200454193038985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298451539201211181437293 486919327200454193038985)
                    ·
                      refine ⟨365189495400340644779239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 486919327200454193038985 365189495400340644779239)
                      ·
                        rfl

theorem cell23_711204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_711204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711204 prefixEnd_711204 := by exact prefixLift 711204
  have htrace : WordTrace (prefixWord ++ tailWord_711204) baseStart_711204 baseEnd_711204 := by
    simpa [prefixWord, tailWord_711204, baseEnd_711204] using wordTrace_append hprefix tailTrace_711204
  have hstable : (prefixWord ++ tailWord_711204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711204).length < 2 ^ (prefixWord ++ tailWord_711204).sum := by decide
  have hdescent : baseEnd_711204 < baseStart_711204 := by decide
  rcases family_descends (prefixWord ++ tailWord_711204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711246 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_711246 : Nat := 118140960795 + 711246 * 2 ^ 59
def prefixEnd_711246 : Nat := 4983230072969 + 3 ^ 40 * 711246 * 2
def baseEnd_711246 : Nat := 365211061587829480454045

theorem tailTrace_711246 : CollatzResearch.WordTrace tailWord_711246 prefixEnd_711246 365211061587829480454045 := by
  unfold tailWord_711246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242659097660585998887199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17294181854189791994065061 3242659097660585998887199)
  ·
    refine ⟨4863988646490878998330799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3242659097660585998887199 4863988646490878998330799)
    ·
      refine ⟨7295982969736318497496199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4863988646490878998330799 7295982969736318497496199)
      ·
        refine ⟨10943974454604477746244299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7295982969736318497496199 10943974454604477746244299)
        ·
          refine ⟨16415961681906716619366449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10943974454604477746244299 16415961681906716619366449)
          ·
            refine ⟨12311971261430037464524837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16415961681906716619366449 12311971261430037464524837)
            ·
              refine ⟨2308494611518132024598407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12311971261430037464524837 2308494611518132024598407)
              ·
                refine ⟨3462741917277198036897611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308494611518132024598407 3462741917277198036897611)
                ·
                  refine ⟨5194112875915797055346417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462741917277198036897611 5194112875915797055346417)
                  ·
                    refine ⟨3895584656936847791509813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5194112875915797055346417 3895584656936847791509813)
                    ·
                      refine ⟨365211061587829480454045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3895584656936847791509813 365211061587829480454045)
                      ·
                        rfl

theorem cell23_711246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_711246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711246 prefixEnd_711246 := by exact prefixLift 711246
  have htrace : WordTrace (prefixWord ++ tailWord_711246) baseStart_711246 baseEnd_711246 := by
    simpa [prefixWord, tailWord_711246, baseEnd_711246] using wordTrace_append hprefix tailTrace_711246
  have hstable : (prefixWord ++ tailWord_711246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711246).length < 2 ^ (prefixWord ++ tailWord_711246).sum := by decide
  have hdescent : baseEnd_711246 < baseStart_711246 := by decide
  rcases family_descends (prefixWord ++ tailWord_711246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711256 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_711256 : Nat := 118140960795 + 711256 * 2 ^ 59
def prefixEnd_711256 : Nat := 4983230072969 + 3 ^ 40 * 711256 * 2
def baseEnd_711256 : Nat := 365216196394374441328999

theorem tailTrace_711256 : CollatzResearch.WordTrace tailWord_711256 prefixEnd_711256 365216196394374441328999 := by
  unfold tailWord_711256
  simp only [CollatzResearch.WordTrace]
  refine ⟨12970818755624229849480811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17294425007498973132641081 12970818755624229849480811)
  ·
    refine ⟨19456228133436344774221217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12970818755624229849480811 19456228133436344774221217)
    ·
      refine ⟨14592171100077258580665913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19456228133436344774221217 14592171100077258580665913)
      ·
        refine ⟨10944128325057943935499435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14592171100077258580665913 10944128325057943935499435)
        ·
          refine ⟨16416192487586915903249153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10944128325057943935499435 16416192487586915903249153)
          ·
            refine ⟨12312144365690186927436865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16416192487586915903249153 12312144365690186927436865)
            ·
              refine ⟨9234108274267640195577649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12312144365690186927436865 9234108274267640195577649)
              ·
                refine ⟨6925581205700730146683237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9234108274267640195577649 6925581205700730146683237)
                ·
                  refine ⟨1298546476068886902503107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6925581205700730146683237 1298546476068886902503107)
                  ·
                    refine ⟨1947819714103330353754661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1298546476068886902503107 1947819714103330353754661)
                    ·
                      refine ⟨365216196394374441328999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1947819714103330353754661 365216196394374441328999)
                      ·
                        rfl

theorem cell23_711256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_711256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711256 prefixEnd_711256 := by exact prefixLift 711256
  have htrace : WordTrace (prefixWord ++ tailWord_711256) baseStart_711256 baseEnd_711256 := by
    simpa [prefixWord, tailWord_711256, baseEnd_711256] using wordTrace_append hprefix tailTrace_711256
  have hstable : (prefixWord ++ tailWord_711256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711256).length < 2 ^ (prefixWord ++ tailWord_711256).sum := by decide
  have hdescent : baseEnd_711256 < baseStart_711256 := by decide
  rcases family_descends (prefixWord ++ tailWord_711256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711296 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 8]
def baseStart_711296 : Nat := 118140960795 + 711296 * 2 ^ 59
def prefixEnd_711296 : Nat := 4983230072969 + 3 ^ 40 * 711296 * 2
def baseEnd_711296 : Nat := 40581859513394920536535

theorem tailTrace_711296 : CollatzResearch.WordTrace tailWord_711296 prefixEnd_711296 40581859513394920536535 := by
  unfold tailWord_711296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12971548215551773265208871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17295397620735697686945161 12971548215551773265208871)
  ·
    refine ⟨19457322323327659897813307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12971548215551773265208871 19457322323327659897813307)
    ·
      refine ⟨29185983484991489846719961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19457322323327659897813307 29185983484991489846719961)
      ·
        refine ⟨21889487613743617385039971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29185983484991489846719961 21889487613743617385039971)
        ·
          refine ⟨32834231420615426077559957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21889487613743617385039971 32834231420615426077559957)
          ·
            refine ⟨1539104597841348097385623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32834231420615426077559957 1539104597841348097385623)
            ·
              refine ⟨2308656896762022146078435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539104597841348097385623 2308656896762022146078435)
              ·
                refine ⟨3462985345143033219117653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308656896762022146078435 3462985345143033219117653)
                ·
                  refine ⟨40581859513394920536535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3462985345143033219117653 40581859513394920536535)
                  ·
                    rfl

theorem cell23_711296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_711296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711296 prefixEnd_711296 := by exact prefixLift 711296
  have htrace : WordTrace (prefixWord ++ tailWord_711296) baseStart_711296 baseEnd_711296 := by
    simpa [prefixWord, tailWord_711296, baseEnd_711296] using wordTrace_append hprefix tailTrace_711296
  have hstable : (prefixWord ++ tailWord_711296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711296).length < 2 ^ (prefixWord ++ tailWord_711296).sum := by decide
  have hdescent : baseEnd_711296 < baseStart_711296 := by decide
  rcases family_descends (prefixWord ++ tailWord_711296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711300 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_711300 : Nat := 118140960795 + 711300 * 2 ^ 59
def prefixEnd_711300 : Nat := 4983230072969 + 3 ^ 40 * 711300 * 2
def baseEnd_711300 : Nat := 121746263181057423059599

theorem tailTrace_711300 : CollatzResearch.WordTrace tailWord_711300 prefixEnd_711300 121746263181057423059599 := by
  unfold tailWord_711300
  simp only [CollatzResearch.WordTrace]
  refine ⟨12971621161544527606781677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17295494882059370142375569 12971621161544527606781677)
  ·
    refine ⟨4864357935579197852543129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12971621161544527606781677 4864357935579197852543129)
    ·
      refine ⟨3648268451684398389407347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4864357935579197852543129 3648268451684398389407347)
      ·
        refine ⟨5472402677526597584111021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648268451684398389407347 5472402677526597584111021)
        ·
          refine ⟨2052151004072474094041633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5472402677526597584111021 2052151004072474094041633)
          ·
            refine ⟨1539113253054355570531225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052151004072474094041633 1539113253054355570531225)
            ·
              refine ⟨1154334939790766677898419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539113253054355570531225 1154334939790766677898419)
              ·
                refine ⟨1731502409686150016847629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154334939790766677898419 1731502409686150016847629)
                ·
                  refine ⟨649313403632306256317861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1731502409686150016847629 649313403632306256317861)
                  ·
                    refine ⟨121746263181057423059599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649313403632306256317861 121746263181057423059599)
                    ·
                      rfl

theorem cell23_711300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_711300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711300 prefixEnd_711300 := by exact prefixLift 711300
  have htrace : WordTrace (prefixWord ++ tailWord_711300) baseStart_711300 baseEnd_711300 := by
    simpa [prefixWord, tailWord_711300, baseEnd_711300] using wordTrace_append hprefix tailTrace_711300
  have hstable : (prefixWord ++ tailWord_711300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711300).length < 2 ^ (prefixWord ++ tailWord_711300).sum := by decide
  have hdescent : baseEnd_711300 < baseStart_711300 := by decide
  rcases family_descends (prefixWord ++ tailWord_711300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711343 : List Nat := [1, 1, 2, 1, 2, 5, 2, 3, 1, 5]
def baseStart_711343 : Nat := 118140960795 + 711343 * 2 ^ 59
def prefixEnd_711343 : Nat := 4983230072969 + 3 ^ 40 * 711343 * 2
def baseEnd_711343 : Nat := 121753623070438533647033

theorem tailTrace_711343 : CollatzResearch.WordTrace tailWord_711343 prefixEnd_711343 121753623070438533647033 := by
  unfold tailWord_711343
  simp only [CollatzResearch.WordTrace]
  refine ⟨25944810661933273557378683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17296540441288849038252455 25944810661933273557378683)
  ·
    refine ⟨38917215992899910336068025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25944810661933273557378683 38917215992899910336068025)
    ·
      refine ⟨29187911994674932752051019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38917215992899910336068025 29187911994674932752051019)
      ·
        refine ⟨43781867992012399128076529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29187911994674932752051019 43781867992012399128076529)
        ·
          refine ⟨32836400994009299346057397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43781867992012399128076529 32836400994009299346057397)
          ·
            refine ⟨3078412593188371813692881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32836400994009299346057397 3078412593188371813692881)
            ·
              refine ⟨2308809444891278860269661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3078412593188371813692881 2308809444891278860269661)
              ·
                refine ⟨865803541834229572601123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2308809444891278860269661 865803541834229572601123)
                ·
                  refine ⟨1298705312751344358901685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865803541834229572601123 1298705312751344358901685)
                  ·
                    refine ⟨121753623070438533647033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1298705312751344358901685 121753623070438533647033)
                    ·
                      rfl

theorem cell23_711343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_711343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711343 prefixEnd_711343 := by exact prefixLift 711343
  have htrace : WordTrace (prefixWord ++ tailWord_711343) baseStart_711343 baseEnd_711343 := by
    simpa [prefixWord, tailWord_711343, baseEnd_711343] using wordTrace_append hprefix tailTrace_711343
  have hstable : (prefixWord ++ tailWord_711343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711343).length < 2 ^ (prefixWord ++ tailWord_711343).sum := by decide
  have hdescent : baseEnd_711343 < baseStart_711343 := by decide
  rcases family_descends (prefixWord ++ tailWord_711343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711357 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_711357 : Nat := 118140960795 + 711357 * 2 ^ 59
def prefixEnd_711357 : Nat := 4983230072969 + 3 ^ 40 * 711357 * 2
def baseEnd_711357 : Nat := 365268057940478546166035

theorem tailTrace_711357 : CollatzResearch.WordTrace tailWord_711357 prefixEnd_711357 365268057940478546166035 := by
  unfold tailWord_711357
  simp only [CollatzResearch.WordTrace]
  refine ⟨25945321283882553948388325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17296880855921702632258883 25945321283882553948388325)
  ·
    refine ⟨4864747740727978865322811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25945321283882553948388325 4864747740727978865322811)
    ·
      refine ⟨7297121611091968297984217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4864747740727978865322811 7297121611091968297984217)
      ·
        refine ⟨5472841208318976223488163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7297121611091968297984217 5472841208318976223488163)
        ·
          refine ⟨8209261812478464335232245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472841208318976223488163 8209261812478464335232245)
          ·
            refine ⟨769618294919856031428023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8209261812478464335232245 769618294919856031428023)
            ·
              refine ⟨1154427442379784047142035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769618294919856031428023 1154427442379784047142035)
              ·
                refine ⟨1731641163569676070713053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154427442379784047142035 1731641163569676070713053)
                ·
                  refine ⟨649365436338628526517395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1731641163569676070713053 649365436338628526517395)
                  ·
                    refine ⟨974048154507942789776093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 649365436338628526517395 974048154507942789776093)
                    ·
                      refine ⟨365268057940478546166035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 974048154507942789776093 365268057940478546166035)
                      ·
                        rfl

theorem cell23_711357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_711357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711357 prefixEnd_711357 := by exact prefixLift 711357
  have htrace : WordTrace (prefixWord ++ tailWord_711357) baseStart_711357 baseEnd_711357 := by
    simpa [prefixWord, tailWord_711357, baseEnd_711357] using wordTrace_append hprefix tailTrace_711357
  have hstable : (prefixWord ++ tailWord_711357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711357).length < 2 ^ (prefixWord ++ tailWord_711357).sum := by decide
  have hdescent : baseEnd_711357 < baseStart_711357 := by decide
  rcases family_descends (prefixWord ++ tailWord_711357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711386 : List Nat := [3, 1, 1, 2, 2, 2, 1, 11]
def baseStart_711386 : Nat := 118140960795 + 711386 * 2 ^ 59
def prefixEnd_711386 : Nat := 4983230072969 + 3 ^ 40 * 711386 * 2
def baseEnd_711386 : Nat := 13528998106646627137163

theorem tailTrace_711386 : CollatzResearch.WordTrace tailWord_711386 prefixEnd_711386 13528998106646627137163 := by
  unfold tailWord_711386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486594750194372975298503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17297586000518327934129341 6486594750194372975298503)
  ·
    refine ⟨9729892125291559462947755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6486594750194372975298503 9729892125291559462947755)
    ·
      refine ⟨14594838187937339194421633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9729892125291559462947755 14594838187937339194421633)
      ·
        refine ⟨10946128640953004395816225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14594838187937339194421633 10946128640953004395816225)
        ·
          refine ⟨8209596480714753296862169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10946128640953004395816225 8209596480714753296862169)
          ·
            refine ⟨6157197360536064972646627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8209596480714753296862169 6157197360536064972646627)
            ·
              refine ⟨9235796040804097458969941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157197360536064972646627 9235796040804097458969941)
              ·
                refine ⟨13528998106646627137163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 9235796040804097458969941 13528998106646627137163)
                ·
                  rfl

theorem cell23_711386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_711386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711386 prefixEnd_711386 := by exact prefixLift 711386
  have htrace : WordTrace (prefixWord ++ tailWord_711386) baseStart_711386 baseEnd_711386 := by
    simpa [prefixWord, tailWord_711386, baseEnd_711386] using wordTrace_append hprefix tailTrace_711386
  have hstable : (prefixWord ++ tailWord_711386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711386).length < 2 ^ (prefixWord ++ tailWord_711386).sum := by decide
  have hdescent : baseEnd_711386 < baseStart_711386 := by decide
  rcases family_descends (prefixWord ++ tailWord_711386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711393 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_711393 : Nat := 118140960795 + 711393 * 2 ^ 59
def prefixEnd_711393 : Nat := 4983230072969 + 3 ^ 40 * 711393 * 2
def baseEnd_711393 : Nat := 365286543244040405315869

theorem tailTrace_711393 : CollatzResearch.WordTrace tailWord_711393 prefixEnd_711393 365286543244040405315869 := by
  unfold tailWord_711393
  simp only [CollatzResearch.WordTrace]
  refine ⟨25946634311752132096698833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17297756207834754731132555 25946634311752132096698833)
  ·
    refine ⟨19459975733814099072524125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25946634311752132096698833 19459975733814099072524125)
    ·
      refine ⟨7297490900180287152196547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19459975733814099072524125 7297490900180287152196547)
      ·
        refine ⟨10946236350270430728294821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297490900180287152196547 10946236350270430728294821)
        ·
          refine ⟨2052419315675705761555279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10946236350270430728294821 2052419315675705761555279)
          ·
            refine ⟨3078628973513558642332919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052419315675705761555279 3078628973513558642332919)
            ·
              refine ⟨4617943460270337963499379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078628973513558642332919 4617943460270337963499379)
              ·
                refine ⟨6926915190405506945249069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617943460270337963499379 6926915190405506945249069)
                ·
                  refine ⟨2597593196402065104468401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6926915190405506945249069 2597593196402065104468401)
                  ·
                    refine ⟨1948194897301548828351301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2597593196402065104468401 1948194897301548828351301)
                    ·
                      refine ⟨365286543244040405315869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1948194897301548828351301 365286543244040405315869)
                      ·
                        rfl

theorem cell23_711393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_711393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711393 prefixEnd_711393 := by exact prefixLift 711393
  have htrace : WordTrace (prefixWord ++ tailWord_711393) baseStart_711393 baseEnd_711393 := by
    simpa [prefixWord, tailWord_711393, baseEnd_711393] using wordTrace_append hprefix tailTrace_711393
  have hstable : (prefixWord ++ tailWord_711393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711393).length < 2 ^ (prefixWord ++ tailWord_711393).sum := by decide
  have hdescent : baseEnd_711393 < baseStart_711393 := by decide
  rcases family_descends (prefixWord ++ tailWord_711393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711397 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 1, 1, 4]
def baseStart_711397 : Nat := 118140960795 + 711397 * 2 ^ 59
def prefixEnd_711397 : Nat := 4983230072969 + 3 ^ 40 * 711397 * 2
def baseEnd_711397 : Nat := 365288597166658389665851

theorem tailTrace_711397 : CollatzResearch.WordTrace tailWord_711397 prefixEnd_711397 365288597166658389665851 := by
  unfold tailWord_711397
  simp only [CollatzResearch.WordTrace]
  refine ⟨25946780203737640779844445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17297853469158427186562963 25946780203737640779844445)
  ·
    refine ⟨9730042576401615292441667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25946780203737640779844445 9730042576401615292441667)
    ·
      refine ⟨14595063864602422938662501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9730042576401615292441667 14595063864602422938662501)
      ·
        refine ⟨2736574474612954300999219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14595063864602422938662501 2736574474612954300999219)
        ·
          refine ⟨4104861711919431451498829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736574474612954300999219 4104861711919431451498829)
          ·
            refine ⟨1539323141969786794312061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4104861711919431451498829 1539323141969786794312061)
            ·
              refine ⟨577246178238670047867023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1539323141969786794312061 577246178238670047867023)
              ·
                refine ⟨865869267358005071800535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577246178238670047867023 865869267358005071800535)
                ·
                  refine ⟨1298803901037007607700803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865869267358005071800535 1298803901037007607700803)
                  ·
                    refine ⟨1948205851555511411551205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1298803901037007607700803 1948205851555511411551205)
                    ·
                      refine ⟨365288597166658389665851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1948205851555511411551205 365288597166658389665851)
                      ·
                        rfl

theorem cell23_711397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_711397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711397 prefixEnd_711397 := by exact prefixLift 711397
  have htrace : WordTrace (prefixWord ++ tailWord_711397) baseStart_711397 baseEnd_711397 := by
    simpa [prefixWord, tailWord_711397, baseEnd_711397] using wordTrace_append hprefix tailTrace_711397
  have hstable : (prefixWord ++ tailWord_711397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711397).length < 2 ^ (prefixWord ++ tailWord_711397).sum := by decide
  have hdescent : baseEnd_711397 < baseStart_711397 := by decide
  rcases family_descends (prefixWord ++ tailWord_711397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711416 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 9]
def baseStart_711416 : Nat := 118140960795 + 711416 * 2 ^ 59
def prefixEnd_711416 : Nat := 4983230072969 + 3 ^ 40 * 711416 * 2
def baseEnd_711416 : Nat := 121766117766364605109421

theorem tailTrace_711416 : CollatzResearch.WordTrace tailWord_711416 prefixEnd_711416 121766117766364605109421 := by
  unfold tailWord_711416
  simp only [CollatzResearch.WordTrace]
  refine ⟨12973736595334403512393051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17298315460445871349857401 12973736595334403512393051)
  ·
    refine ⟨19460604893001605268589577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12973736595334403512393051 19460604893001605268589577)
    ·
      refine ⟨14595453669751203951442183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19460604893001605268589577 14595453669751203951442183)
      ·
        refine ⟨21893180504626805927163275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14595453669751203951442183 21893180504626805927163275)
        ·
          refine ⟨32839770756940208890744913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21893180504626805927163275 32839770756940208890744913)
          ·
            refine ⟨24629828067705156668058685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32839770756940208890744913 24629828067705156668058685)
            ·
              refine ⟨9236185525389433750522007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24629828067705156668058685 9236185525389433750522007)
              ·
                refine ⟨13854278288084150625783011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9236185525389433750522007 13854278288084150625783011)
                ·
                  refine ⟨20781417432126225938674517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13854278288084150625783011 20781417432126225938674517)
                  ·
                    refine ⟨121766117766364605109421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 20781417432126225938674517 121766117766364605109421)
                    ·
                      rfl

theorem cell23_711416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_711416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711416 prefixEnd_711416 := by exact prefixLift 711416
  have htrace : WordTrace (prefixWord ++ tailWord_711416) baseStart_711416 baseEnd_711416 := by
    simpa [prefixWord, tailWord_711416, baseEnd_711416] using wordTrace_append hprefix tailTrace_711416
  have hstable : (prefixWord ++ tailWord_711416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711416).length < 2 ^ (prefixWord ++ tailWord_711416).sum := by decide
  have hdescent : baseEnd_711416 < baseStart_711416 := by decide
  rcases family_descends (prefixWord ++ tailWord_711416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711457 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_711457 : Nat := 118140960795 + 711457 * 2 ^ 59
def prefixEnd_711457 : Nat := 4983230072969 + 3 ^ 40 * 711457 * 2
def baseEnd_711457 : Nat := 365319406005928154915575

theorem tailTrace_711457 : CollatzResearch.WordTrace tailWord_711457 prefixEnd_711457 365319406005928154915575 := by
  unfold tailWord_711457
  simp only [CollatzResearch.WordTrace]
  refine ⟨25948968583520271027028625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17299312389013514018019083 25948968583520271027028625)
  ·
    refine ⟨19461726437640203270271469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25948968583520271027028625 19461726437640203270271469)
    ·
      refine ⟨7298147414115076226351801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19461726437640203270271469 7298147414115076226351801)
      ·
        refine ⟨5473610560586307169763851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7298147414115076226351801 5473610560586307169763851)
        ·
          refine ⟨8210415840879460754645777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473610560586307169763851 8210415840879460754645777)
          ·
            refine ⟨6157811880659595565984333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8210415840879460754645777 6157811880659595565984333)
            ·
              refine ⟨2309179455247348337244125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6157811880659595565984333 2309179455247348337244125)
              ·
                refine ⟨865942295717755626466547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2309179455247348337244125 865942295717755626466547)
                ·
                  refine ⟨1298913443576633439699821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865942295717755626466547 1298913443576633439699821)
                  ·
                    refine ⟨487092541341237539887433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1298913443576633439699821 487092541341237539887433)
                    ·
                      refine ⟨365319406005928154915575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487092541341237539887433 365319406005928154915575)
                      ·
                        rfl

theorem cell23_711457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_711457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711457 prefixEnd_711457 := by exact prefixLift 711457
  have htrace : WordTrace (prefixWord ++ tailWord_711457) baseStart_711457 baseEnd_711457 := by
    simpa [prefixWord, tailWord_711457, baseEnd_711457] using wordTrace_append hprefix tailTrace_711457
  have hstable : (prefixWord ++ tailWord_711457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711457).length < 2 ^ (prefixWord ++ tailWord_711457).sum := by decide
  have hdescent : baseEnd_711457 < baseStart_711457 := by decide
  rcases family_descends (prefixWord ++ tailWord_711457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711487 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 1, 4, 2]
def baseStart_711487 : Nat := 118140960795 + 711487 * 2 ^ 59
def prefixEnd_711487 : Nat := 4983230072969 + 3 ^ 40 * 711487 * 2
def baseEnd_711487 : Nat := 365334810425563037540437

theorem tailTrace_711487 : CollatzResearch.WordTrace tailWord_711487 prefixEnd_711487 365334810425563037540437 := by
  unfold tailWord_711487
  simp only [CollatzResearch.WordTrace]
  refine ⟨25950062773411586150620715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17300041848941057433747143 25950062773411586150620715)
  ·
    refine ⟨38925094160117379225931073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25950062773411586150620715 38925094160117379225931073)
    ·
      refine ⟨29193820620088034419448305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38925094160117379225931073 29193820620088034419448305)
      ·
        refine ⟨21895365465066025814586229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29193820620088034419448305 21895365465066025814586229)
        ·
          refine ⟨2052690512349939920117459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21895365465066025814586229 2052690512349939920117459)
          ·
            refine ⟨3079035768524909880176189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052690512349939920117459 3079035768524909880176189)
            ·
              refine ⟨1154638413196841205066071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3079035768524909880176189 1154638413196841205066071)
              ·
                refine ⟨1731957619795261807599107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154638413196841205066071 1731957619795261807599107)
                ·
                  refine ⟨2597936429692892711398661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731957619795261807599107 2597936429692892711398661)
                  ·
                    refine ⟨487113080567417383387249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2597936429692892711398661 487113080567417383387249)
                    ·
                      refine ⟨365334810425563037540437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487113080567417383387249 365334810425563037540437)
                      ·
                        rfl

theorem cell23_711487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_711487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711487 prefixEnd_711487 := by exact prefixLift 711487
  have htrace : WordTrace (prefixWord ++ tailWord_711487) baseStart_711487 baseEnd_711487 := by
    simpa [prefixWord, tailWord_711487, baseEnd_711487] using wordTrace_append hprefix tailTrace_711487
  have hstable : (prefixWord ++ tailWord_711487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711487).length < 2 ^ (prefixWord ++ tailWord_711487).sum := by decide
  have hdescent : baseEnd_711487 < baseStart_711487 := by decide
  rcases family_descends (prefixWord ++ tailWord_711487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711543 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_711543 : Nat := 118140960795 + 711543 * 2 ^ 59
def prefixEnd_711543 : Nat := 4983230072969 + 3 ^ 40 * 711543 * 2
def baseEnd_711543 : Nat := 365363565342214818440179

theorem tailTrace_711543 : CollatzResearch.WordTrace tailWord_711543 prefixEnd_711543 365363565342214818440179 := by
  unfold tailWord_711543
  simp only [CollatzResearch.WordTrace]
  refine ⟨25952105261208707714659283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17301403507472471809772855 25952105261208707714659283)
  ·
    refine ⟨38928157891813061571988925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25952105261208707714659283 38928157891813061571988925)
    ·
      refine ⟨14598059209429898089495847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38928157891813061571988925 14598059209429898089495847)
      ·
        refine ⟨21897088814144847134243771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14598059209429898089495847 21897088814144847134243771)
        ·
          refine ⟨32845633221217270701365657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21897088814144847134243771 32845633221217270701365657)
          ·
            refine ⟨24634224915912953026024243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32845633221217270701365657 24634224915912953026024243)
            ·
              refine ⟨36951337373869429539036365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24634224915912953026024243 36951337373869429539036365)
              ·
                refine ⟨13856751515201036077138637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36951337373869429539036365 13856751515201036077138637)
                ·
                  refine ⟨5196281818200388528926989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13856751515201036077138637 5196281818200388528926989)
                  ·
                    refine ⟨1948605681825145698347621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5196281818200388528926989 1948605681825145698347621)
                    ·
                      refine ⟨365363565342214818440179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1948605681825145698347621 365363565342214818440179)
                      ·
                        rfl

theorem cell23_711543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_711543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711543 prefixEnd_711543 := by exact prefixLift 711543
  have htrace : WordTrace (prefixWord ++ tailWord_711543) baseStart_711543 baseEnd_711543 := by
    simpa [prefixWord, tailWord_711543, baseEnd_711543] using wordTrace_append hprefix tailTrace_711543
  have hstable : (prefixWord ++ tailWord_711543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711543).length < 2 ^ (prefixWord ++ tailWord_711543).sum := by decide
  have hdescent : baseEnd_711543 < baseStart_711543 := by decide
  rcases family_descends (prefixWord ++ tailWord_711543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711603 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6]
def baseStart_711603 : Nat := 118140960795 + 711603 * 2 ^ 59
def prefixEnd_711603 : Nat := 4983230072969 + 3 ^ 40 * 711603 * 2
def baseEnd_711603 : Nat := 365394374181484583689903

theorem tailTrace_711603 : CollatzResearch.WordTrace tailWord_711603 prefixEnd_711603 365394374181484583689903 := by
  unfold tailWord_711603
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954293640991337961843463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17302862427327558641228975 25954293640991337961843463)
  ·
    refine ⟨38931440461487006942765195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25954293640991337961843463 38931440461487006942765195)
    ·
      refine ⟨58397160692230510414147793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38931440461487006942765195 58397160692230510414147793)
      ·
        refine ⟨43797870519172882810610845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58397160692230510414147793 43797870519172882810610845)
        ·
          refine ⟨16424201444689831053979067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43797870519172882810610845 16424201444689831053979067)
          ·
            refine ⟨24636302167034746580968601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16424201444689831053979067 24636302167034746580968601)
            ·
              refine ⟨18477226625276059935726451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24636302167034746580968601 18477226625276059935726451)
              ·
                refine ⟨27715839937914089903589677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18477226625276059935726451 27715839937914089903589677)
                ·
                  refine ⟨10393439976717783713846129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27715839937914089903589677 10393439976717783713846129)
                  ·
                    refine ⟨7795079982538337785384597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10393439976717783713846129 7795079982538337785384597)
                    ·
                      refine ⟨365394374181484583689903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7795079982538337785384597 365394374181484583689903)
                      ·
                        rfl

theorem cell23_711603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_711603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711603 prefixEnd_711603 := by exact prefixLift 711603
  have htrace : WordTrace (prefixWord ++ tailWord_711603) baseStart_711603 baseEnd_711603 := by
    simpa [prefixWord, tailWord_711603, baseEnd_711603] using wordTrace_append hprefix tailTrace_711603
  have hstable : (prefixWord ++ tailWord_711603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711603).length < 2 ^ (prefixWord ++ tailWord_711603).sum := by decide
  have hdescent : baseEnd_711603 < baseStart_711603 := by decide
  rcases family_descends (prefixWord ++ tailWord_711603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711604 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_711604 : Nat := 118140960795 + 711604 * 2 ^ 59
def prefixEnd_711604 : Nat := 4983230072969 + 3 ^ 40 * 711604 * 2
def baseEnd_711604 : Nat := 121798295887379693259133

theorem tailTrace_711604 : CollatzResearch.WordTrace tailWord_711604 prefixEnd_711604 121798295887379693259133 := by
  unfold tailWord_711604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12977165056993857566314933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17302886742658476755086577 12977165056993857566314933)
  ·
    refine ⟨1216609224093174146842025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12977165056993857566314933 1216609224093174146842025)
    ·
      refine ⟨912456918069880610131519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1216609224093174146842025 912456918069880610131519)
      ·
        refine ⟨1368685377104820915197279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912456918069880610131519 1368685377104820915197279)
        ·
          refine ⟨2053028065657231372795919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368685377104820915197279 2053028065657231372795919)
          ·
            refine ⟨3079542098485847059193879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053028065657231372795919 3079542098485847059193879)
            ·
              refine ⟨4619313147728770588790819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079542098485847059193879 4619313147728770588790819)
              ·
                refine ⟨6928969721593155883186229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619313147728770588790819 6928969721593155883186229)
                ·
                  refine ⟨649590911399358364048709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6928969721593155883186229 649590911399358364048709)
                  ·
                    refine ⟨121798295887379693259133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649590911399358364048709 121798295887379693259133)
                    ·
                      rfl

theorem cell23_711604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_711604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711604 prefixEnd_711604 := by exact prefixLift 711604
  have htrace : WordTrace (prefixWord ++ tailWord_711604) baseStart_711604 baseEnd_711604 := by
    simpa [prefixWord, tailWord_711604, baseEnd_711604] using wordTrace_append hprefix tailTrace_711604
  have hstable : (prefixWord ++ tailWord_711604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711604).length < 2 ^ (prefixWord ++ tailWord_711604).sum := by decide
  have hdescent : baseEnd_711604 < baseStart_711604 := by decide
  rcases family_descends (prefixWord ++ tailWord_711604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711634 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 6]
def baseStart_711634 : Nat := 118140960795 + 711634 * 2 ^ 59
def prefixEnd_711634 : Nat := 4983230072969 + 3 ^ 40 * 711634 * 2
def baseEnd_711634 : Nat := 40601143564641551378029

theorem tailTrace_711634 : CollatzResearch.WordTrace tailWord_711634 prefixEnd_711634 40601143564641551378029 := by
  unfold tailWord_711634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488856075969757564055489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17303616202586020170814637 6488856075969757564055489)
  ·
    refine ⟨4866642056977318173041617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6488856075969757564055489 4866642056977318173041617)
    ·
      refine ⟨3649981542732988629781213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4866642056977318173041617 3649981542732988629781213)
      ·
        refine ⟨1368743078524870736167955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3649981542732988629781213 1368743078524870736167955)
        ·
          refine ⟨2053114617787306104251933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368743078524870736167955 2053114617787306104251933)
          ·
            refine ⟨769917981670239789094475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2053114617787306104251933 769917981670239789094475)
            ·
              refine ⟨1154876972505359683641713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769917981670239789094475 1154876972505359683641713)
              ·
                refine ⟨866157729379019762731285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154876972505359683641713 866157729379019762731285)
                ·
                  refine ⟨40601143564641551378029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 866157729379019762731285 40601143564641551378029)
                  ·
                    rfl

theorem cell23_711634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_711634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711634 prefixEnd_711634 := by exact prefixLift 711634
  have htrace : WordTrace (prefixWord ++ tailWord_711634) baseStart_711634 baseEnd_711634 := by
    simpa [prefixWord, tailWord_711634, baseEnd_711634] using wordTrace_append hprefix tailTrace_711634
  have hstable : (prefixWord ++ tailWord_711634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711634).length < 2 ^ (prefixWord ++ tailWord_711634).sum := by decide
  have hdescent : baseEnd_711634 < baseStart_711634 := by decide
  rcases family_descends (prefixWord ++ tailWord_711634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711687 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_711687 : Nat := 118140960795 + 711687 * 2 ^ 59
def prefixEnd_711687 : Nat := 4983230072969 + 3 ^ 40 * 711687 * 2
def baseEnd_711687 : Nat := 365437506556462255039517

theorem tailTrace_711687 : CollatzResearch.WordTrace tailWord_711687 prefixEnd_711687 365437506556462255039517 := by
  unfold tailWord_711687
  simp only [CollatzResearch.WordTrace]
  refine ⟨25957357372687020307901315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17304904915124680205267543 25957357372687020307901315)
  ·
    refine ⟨38936036059030530461851973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25957357372687020307901315 38936036059030530461851973)
    ·
      refine ⟨7300506761068224461597245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38936036059030530461851973 7300506761068224461597245)
      ·
        refine ⟨2737690035400584173098967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7300506761068224461597245 2737690035400584173098967)
        ·
          refine ⟨4106535053100876259648451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737690035400584173098967 4106535053100876259648451)
          ·
            refine ⟨6159802579651314389472677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106535053100876259648451 6159802579651314389472677)
            ·
              refine ⟨1154962983684621448026127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6159802579651314389472677 1154962983684621448026127)
              ·
                refine ⟨1732444475526932172039191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154962983684621448026127 1732444475526932172039191)
                ·
                  refine ⟨2598666713290398258058787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732444475526932172039191 2598666713290398258058787)
                  ·
                    refine ⟨3898000069935597387088181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2598666713290398258058787 3898000069935597387088181)
                    ·
                      refine ⟨365437506556462255039517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3898000069935597387088181 365437506556462255039517)
                      ·
                        rfl

theorem cell23_711687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_711687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711687 prefixEnd_711687 := by exact prefixLift 711687
  have htrace : WordTrace (prefixWord ++ tailWord_711687) baseStart_711687 baseEnd_711687 := by
    simpa [prefixWord, tailWord_711687, baseEnd_711687] using wordTrace_append hprefix tailTrace_711687
  have hstable : (prefixWord ++ tailWord_711687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711687).length < 2 ^ (prefixWord ++ tailWord_711687).sum := by decide
  have hdescent : baseEnd_711687 < baseStart_711687 := by decide
  rcases family_descends (prefixWord ++ tailWord_711687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711690 : List Nat := [3, 1, 2, 2, 3, 1, 11]
def baseStart_711690 : Nat := 118140960795 + 711690 * 2 ^ 59
def prefixEnd_711690 : Nat := 4983230072969 + 3 ^ 40 * 711690 * 2
def baseEnd_711690 : Nat := 4511593172820070904963

theorem tailTrace_711690 : CollatzResearch.WordTrace tailWord_711690 prefixEnd_711690 4511593172820070904963 := by
  unfold tailWord_711690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6489366697919037955065131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17304977861117434546840349 6489366697919037955065131)
  ·
    refine ⟨9734050046878556932597697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6489366697919037955065131 9734050046878556932597697)
    ·
      refine ⟨7300537535158917699448273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9734050046878556932597697 7300537535158917699448273)
      ·
        refine ⟨5475403151369188274586205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7300537535158917699448273 5475403151369188274586205)
        ·
          refine ⟨2053276181763445602969827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5475403151369188274586205 2053276181763445602969827)
          ·
            refine ⟨3079914272645168404454741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053276181763445602969827 3079914272645168404454741)
            ·
              refine ⟨4511593172820070904963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3079914272645168404454741 4511593172820070904963)
              ·
                rfl

theorem cell23_711690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 11].length) (baseStart_711690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711690 prefixEnd_711690 := by exact prefixLift 711690
  have htrace : WordTrace (prefixWord ++ tailWord_711690) baseStart_711690 baseEnd_711690 := by
    simpa [prefixWord, tailWord_711690, baseEnd_711690] using wordTrace_append hprefix tailTrace_711690
  have hstable : (prefixWord ++ tailWord_711690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711690).length < 2 ^ (prefixWord ++ tailWord_711690).sum := by decide
  have hdescent : baseEnd_711690 < baseStart_711690 := by decide
  rcases family_descends (prefixWord ++ tailWord_711690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711701 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_711701 : Nat := 118140960795 + 711701 * 2 ^ 59
def prefixEnd_711701 : Nat := 4983230072969 + 3 ^ 40 * 711701 * 2
def baseEnd_711701 : Nat := 365444695285625200264453

theorem tailTrace_711701 : CollatzResearch.WordTrace tailWord_711701 prefixEnd_711701 365444695285625200264453 := by
  unfold tailWord_711701
  simp only [CollatzResearch.WordTrace]
  refine ⟨25957867994636300698910957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17305245329757533799273971 25957867994636300698910957)
  ·
    refine ⟨9734200497988612762091609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25957867994636300698910957 9734200497988612762091609)
    ·
      refine ⟨7300650373491459571568707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9734200497988612762091609 7300650373491459571568707)
      ·
        refine ⟨10950975560237189357353061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7300650373491459571568707 10950975560237189357353061)
        ·
          refine ⟨2053307917544473004503699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10950975560237189357353061 2053307917544473004503699)
          ·
            refine ⟨3079961876316709506755549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053307917544473004503699 3079961876316709506755549)
            ·
              refine ⟨1154985703618766065033331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3079961876316709506755549 1154985703618766065033331)
              ·
                refine ⟨1732478555428149097549997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154985703618766065033331 1732478555428149097549997)
                ·
                  refine ⟨649679458285555911581249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1732478555428149097549997 649679458285555911581249)
                  ·
                    refine ⟨487259593714166933685937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 649679458285555911581249 487259593714166933685937)
                    ·
                      refine ⟨365444695285625200264453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487259593714166933685937 365444695285625200264453)
                      ·
                        rfl

theorem cell23_711701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_711701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711701 prefixEnd_711701 := by exact prefixLift 711701
  have htrace : WordTrace (prefixWord ++ tailWord_711701) baseStart_711701 baseEnd_711701 := by
    simpa [prefixWord, tailWord_711701, baseEnd_711701] using wordTrace_append hprefix tailTrace_711701
  have hstable : (prefixWord ++ tailWord_711701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711701).length < 2 ^ (prefixWord ++ tailWord_711701).sum := by decide
  have hdescent : baseEnd_711701 < baseStart_711701 := by decide
  rcases family_descends (prefixWord ++ tailWord_711701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711711 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 2, 4]
def baseStart_711711 : Nat := 118140960795 + 711711 * 2 ^ 59
def prefixEnd_711711 : Nat := 4983230072969 + 3 ^ 40 * 711711 * 2
def baseEnd_711711 : Nat := 121816610030723387046469

theorem tailTrace_711711 : CollatzResearch.WordTrace tailWord_711711 prefixEnd_711711 121816610030723387046469 := by
  unfold tailWord_711711
  simp only [CollatzResearch.WordTrace]
  refine ⟨25958232724600072406774987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17305488483066714937849991 25958232724600072406774987)
  ·
    refine ⟨38937349086900108610162481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25958232724600072406774987 38937349086900108610162481)
    ·
      refine ⟨29203011815175081457621861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38937349086900108610162481 29203011815175081457621861)
      ·
        refine ⟨5475564715345327773304099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29203011815175081457621861 5475564715345327773304099)
        ·
          refine ⟨8213347073017991659956149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5475564715345327773304099 8213347073017991659956149)
          ·
            refine ⟨770001288095436718120889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8213347073017991659956149 770001288095436718120889)
            ·
              refine ⟨577500966071577538590667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770001288095436718120889 577500966071577538590667)
              ·
                refine ⟨866251449107366307886001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577500966071577538590667 866251449107366307886001)
                ·
                  refine ⟨649688586830524730914501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866251449107366307886001 649688586830524730914501)
                  ·
                    refine ⟨121816610030723387046469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649688586830524730914501 121816610030723387046469)
                    ·
                      rfl

theorem cell23_711711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 2, 4].length) (baseStart_711711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711711 prefixEnd_711711 := by exact prefixLift 711711
  have htrace : WordTrace (prefixWord ++ tailWord_711711) baseStart_711711 baseEnd_711711 := by
    simpa [prefixWord, tailWord_711711, baseEnd_711711] using wordTrace_append hprefix tailTrace_711711
  have hstable : (prefixWord ++ tailWord_711711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711711).length < 2 ^ (prefixWord ++ tailWord_711711).sum := by decide
  have hdescent : baseEnd_711711 < baseStart_711711 := by decide
  rcases family_descends (prefixWord ++ tailWord_711711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711717 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_711717 : Nat := 118140960795 + 711717 * 2 ^ 59
def prefixEnd_711717 : Nat := 4983230072969 + 3 ^ 40 * 711717 * 2
def baseEnd_711717 : Nat := 365452910976097137664379

theorem tailTrace_711717 : CollatzResearch.WordTrace tailWord_711717 prefixEnd_711717 365452910976097137664379 := by
  unfold tailWord_711717
  simp only [CollatzResearch.WordTrace]
  refine ⟨25958451562578335431493405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17305634375052223620995603 25958451562578335431493405)
  ·
    refine ⟨9734419335966875786810027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25958451562578335431493405 9734419335966875786810027)
    ·
      refine ⟨14601629003950313680215041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9734419335966875786810027 14601629003950313680215041)
      ·
        refine ⟨10951221752962735260161281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14601629003950313680215041 10951221752962735260161281)
        ·
          refine ⟨8213416314722051445120961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10951221752962735260161281 8213416314722051445120961)
          ·
            refine ⟨6160062236041538583840721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8213416314722051445120961 6160062236041538583840721)
            ·
              refine ⟨4620046677031153937880541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6160062236041538583840721 4620046677031153937880541)
              ·
                refine ⟨1732517503886682726705203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4620046677031153937880541 1732517503886682726705203)
                ·
                  refine ⟨2598776255830024090057805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1732517503886682726705203 2598776255830024090057805)
                  ·
                    refine ⟨974541095936259033771677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598776255830024090057805 974541095936259033771677)
                    ·
                      refine ⟨365452910976097137664379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 974541095936259033771677 365452910976097137664379)
                      ·
                        rfl

theorem cell23_711717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_711717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711717 prefixEnd_711717 := by exact prefixLift 711717
  have htrace : WordTrace (prefixWord ++ tailWord_711717) baseStart_711717 baseEnd_711717 := by
    simpa [prefixWord, tailWord_711717, baseEnd_711717] using wordTrace_append hprefix tailTrace_711717
  have hstable : (prefixWord ++ tailWord_711717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711717).length < 2 ^ (prefixWord ++ tailWord_711717).sum := by decide
  have hdescent : baseEnd_711717 < baseStart_711717 := by decide
  rcases family_descends (prefixWord ++ tailWord_711717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711734 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_711734 : Nat := 118140960795 + 711734 * 2 ^ 59
def prefixEnd_711734 : Nat := 4983230072969 + 3 ^ 40 * 711734 * 2
def baseEnd_711734 : Nat := 365461640147223571151801

theorem tailTrace_711734 : CollatzResearch.WordTrace tailWord_711734 prefixEnd_711734 365461640147223571151801 := by
  unfold tailWord_711734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622441975219796708428891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17306047735677831556574837 1622441975219796708428891)
  ·
    refine ⟨2433662962829695062643337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1622441975219796708428891 2433662962829695062643337)
    ·
      refine ⟨1825247222122271296982503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2433662962829695062643337 1825247222122271296982503)
      ·
        refine ⟨2737870833183406945473755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825247222122271296982503 2737870833183406945473755)
        ·
          refine ⟨4106806249775110418210633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737870833183406945473755 4106806249775110418210633)
          ·
            refine ⟨3080104687331332813657975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4106806249775110418210633 3080104687331332813657975)
            ·
              refine ⟨4620157030996999220486963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080104687331332813657975 4620157030996999220486963)
              ·
                refine ⟨6930235546495498830730445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620157030996999220486963 6930235546495498830730445)
                ·
                  refine ⟨2598838329935812061523917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6930235546495498830730445 2598838329935812061523917)
                  ·
                    refine ⟨974564373725929523071469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2598838329935812061523917 974564373725929523071469)
                    ·
                      refine ⟨365461640147223571151801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 974564373725929523071469 365461640147223571151801)
                      ·
                        rfl

theorem cell23_711734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_711734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711734 prefixEnd_711734 := by exact prefixLift 711734
  have htrace : WordTrace (prefixWord ++ tailWord_711734) baseStart_711734 baseEnd_711734 := by
    simpa [prefixWord, tailWord_711734, baseEnd_711734] using wordTrace_append hprefix tailTrace_711734
  have hstable : (prefixWord ++ tailWord_711734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711734).length < 2 ^ (prefixWord ++ tailWord_711734).sum := by decide
  have hdescent : baseEnd_711734 < baseStart_711734 := by decide
  rcases family_descends (prefixWord ++ tailWord_711734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711751 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_711751 : Nat := 118140960795 + 711751 * 2 ^ 59
def prefixEnd_711751 : Nat := 4983230072969 + 3 ^ 40 * 711751 * 2
def baseEnd_711751 : Nat := 365470369318350004639223

theorem tailTrace_711751 : CollatzResearch.WordTrace tailWord_711751 prefixEnd_711751 365470369318350004639223 := by
  unfold tailWord_711751
  simp only [CollatzResearch.WordTrace]
  refine ⟨25959691644455159238231107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17306461096303439492154071 25959691644455159238231107)
  ·
    refine ⟨38939537466682738857346661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25959691644455159238231107 38939537466682738857346661)
    ·
      refine ⟨7301163275003013535752499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38939537466682738857346661 7301163275003013535752499)
      ·
        refine ⟨10951744912504520303628749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7301163275003013535752499 10951744912504520303628749)
        ·
          refine ⟨4106904342189195113860781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10951744912504520303628749 4106904342189195113860781)
          ·
            refine ⟨1540089128320948167697793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4106904342189195113860781 1540089128320948167697793)
            ·
              refine ⟨1155066846240711125773345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540089128320948167697793 1155066846240711125773345)
              ·
                refine ⟨866300134680533344330009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155066846240711125773345 866300134680533344330009)
                ·
                  refine ⟨649725101010400008247507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866300134680533344330009 649725101010400008247507)
                  ·
                    refine ⟨974587651515600012371261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 649725101010400008247507 974587651515600012371261)
                    ·
                      refine ⟨365470369318350004639223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 974587651515600012371261 365470369318350004639223)
                      ·
                        rfl

theorem cell23_711751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_711751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711751 prefixEnd_711751 := by exact prefixLift 711751
  have htrace : WordTrace (prefixWord ++ tailWord_711751) baseStart_711751 baseEnd_711751 := by
    simpa [prefixWord, tailWord_711751, baseEnd_711751] using wordTrace_append hprefix tailTrace_711751
  have hstable : (prefixWord ++ tailWord_711751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711751).length < 2 ^ (prefixWord ++ tailWord_711751).sum := by decide
  have hdescent : baseEnd_711751 < baseStart_711751 := by decide
  rcases family_descends (prefixWord ++ tailWord_711751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711760 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_711760 : Nat := 118140960795 + 711760 * 2 ^ 59
def prefixEnd_711760 : Nat := 4983230072969 + 3 ^ 40 * 711760 * 2
def baseEnd_711760 : Nat := 365474990644240469426681

theorem tailTrace_711760 : CollatzResearch.WordTrace tailWord_711760 prefixEnd_711760 365474990644240469426681 := by
  unfold tailWord_711760
  simp only [CollatzResearch.WordTrace]
  refine ⟨12980009950711276887654367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17306679934281702516872489 12980009950711276887654367)
  ·
    refine ⟨19470014926066915331481551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12980009950711276887654367 19470014926066915331481551)
    ·
      refine ⟨29205022389100372997222327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19470014926066915331481551 29205022389100372997222327)
      ·
        refine ⟨43807533583650559495833491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29205022389100372997222327 43807533583650559495833491)
        ·
          refine ⟨65711300375475839243750237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43807533583650559495833491 65711300375475839243750237)
          ·
            refine ⟨24641737640803439716406339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65711300375475839243750237 24641737640803439716406339)
            ·
              refine ⟨36962606461205159574609509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24641737640803439716406339 36962606461205159574609509)
              ·
                refine ⟨6930488711475967420239283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36962606461205159574609509 6930488711475967420239283)
                ·
                  refine ⟨10395733067213951130358925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6930488711475967420239283 10395733067213951130358925)
                  ·
                    refine ⟨3898399900205231673884597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10395733067213951130358925 3898399900205231673884597)
                    ·
                      refine ⟨365474990644240469426681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3898399900205231673884597 365474990644240469426681)
                      ·
                        rfl

theorem cell23_711760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_711760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711760 prefixEnd_711760 := by exact prefixLift 711760
  have htrace : WordTrace (prefixWord ++ tailWord_711760) baseStart_711760 baseEnd_711760 := by
    simpa [prefixWord, tailWord_711760, baseEnd_711760] using wordTrace_append hprefix tailTrace_711760
  have hstable : (prefixWord ++ tailWord_711760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711760).length < 2 ^ (prefixWord ++ tailWord_711760).sum := by decide
  have hdescent : baseEnd_711760 < baseStart_711760 := by decide
  rcases family_descends (prefixWord ++ tailWord_711760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711864 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 2, 4, 2]
def baseStart_711864 : Nat := 118140960795 + 711864 * 2 ^ 59
def prefixEnd_711864 : Nat := 4983230072969 + 3 ^ 40 * 711864 * 2
def baseEnd_711864 : Nat := 365528392632308062526203

theorem tailTrace_711864 : CollatzResearch.WordTrace tailWord_711864 prefixEnd_711864 365528392632308062526203 := by
  unfold tailWord_711864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12981906546522889768547323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17309208728697186358063097 12981906546522889768547323)
  ·
    refine ⟨19472859819784334652820985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12981906546522889768547323 19472859819784334652820985)
    ·
      refine ⟨14604644864838250989615739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19472859819784334652820985 14604644864838250989615739)
      ·
        refine ⟨21906967297257376484423609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14604644864838250989615739 21906967297257376484423609)
        ·
          refine ⟨16430225472943032363317707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21906967297257376484423609 16430225472943032363317707)
          ·
            refine ⟨24645338209414548544976561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16430225472943032363317707 24645338209414548544976561)
            ·
              refine ⟨18484003657060911408732421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24645338209414548544976561 18484003657060911408732421)
              ·
                refine ⟨3465750685698920889137329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18484003657060911408732421 3465750685698920889137329)
                ·
                  refine ⟨2599313014274190666852997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3465750685698920889137329 2599313014274190666852997)
                  ·
                    refine ⟨487371190176410750034937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2599313014274190666852997 487371190176410750034937)
                    ·
                      refine ⟨365528392632308062526203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487371190176410750034937 365528392632308062526203)
                      ·
                        rfl

theorem cell23_711864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_711864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711864 prefixEnd_711864 := by exact prefixLift 711864
  have htrace : WordTrace (prefixWord ++ tailWord_711864) baseStart_711864 baseEnd_711864 := by
    simpa [prefixWord, tailWord_711864, baseEnd_711864] using wordTrace_append hprefix tailTrace_711864
  have hstable : (prefixWord ++ tailWord_711864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711864).length < 2 ^ (prefixWord ++ tailWord_711864).sum := by decide
  have hdescent : baseEnd_711864 < baseStart_711864 := by decide
  rcases family_descends (prefixWord ++ tailWord_711864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711867 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 3]
def baseStart_711867 : Nat := 118140960795 + 711867 * 2 ^ 59
def prefixEnd_711867 : Nat := 4983230072969 + 3 ^ 40 * 711867 * 2
def baseEnd_711867 : Nat := 365529933074271550788689

theorem tailTrace_711867 : CollatzResearch.WordTrace tailWord_711867 prefixEnd_711867 365529933074271550788689 := by
  unfold tailWord_711867
  simp only [CollatzResearch.WordTrace]
  refine ⟨25963922512034911049453855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17309281674689940699635903 25963922512034911049453855)
  ·
    refine ⟨38945883768052366574180783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25963922512034911049453855 38945883768052366574180783)
    ·
      refine ⟨58418825652078549861271175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38945883768052366574180783 58418825652078549861271175)
      ·
        refine ⟨87628238478117824791906763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58418825652078549861271175 87628238478117824791906763)
        ·
          refine ⟨131442357717176737187860145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87628238478117824791906763 131442357717176737187860145)
          ·
            refine ⟨98581768287882552890895109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131442357717176737187860145 98581768287882552890895109)
            ·
              refine ⟨18484081553977978667042833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98581768287882552890895109 18484081553977978667042833)
              ·
                refine ⟨13863061165483484000282125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18484081553977978667042833 13863061165483484000282125)
                ·
                  refine ⟨5198647937056306500105797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13863061165483484000282125 5198647937056306500105797)
                  ·
                    refine ⟨974746488198057468769837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5198647937056306500105797 974746488198057468769837)
                    ·
                      refine ⟨365529933074271550788689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 974746488198057468769837 365529933074271550788689)
                      ·
                        rfl

theorem cell23_711867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 3].length) (baseStart_711867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711867 prefixEnd_711867 := by exact prefixLift 711867
  have htrace : WordTrace (prefixWord ++ tailWord_711867) baseStart_711867 baseEnd_711867 := by
    simpa [prefixWord, tailWord_711867, baseEnd_711867] using wordTrace_append hprefix tailTrace_711867
  have hstable : (prefixWord ++ tailWord_711867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711867).length < 2 ^ (prefixWord ++ tailWord_711867).sum := by decide
  have hdescent : baseEnd_711867 < baseStart_711867 := by decide
  rcases family_descends (prefixWord ++ tailWord_711867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711964 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_711964 : Nat := 118140960795 + 711964 * 2 ^ 59
def prefixEnd_711964 : Nat := 4983230072969 + 3 ^ 40 * 711964 * 2
def baseEnd_711964 : Nat := 121859913565919223758581

theorem tailTrace_711964 : CollatzResearch.WordTrace tailWord_711964 prefixEnd_711964 121859913565919223758581 := by
  unfold tailWord_711964
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983730196341748307867473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17311640261788997743823297 12983730196341748307867473)
  ·
    refine ⟨9737797647256311230900605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12983730196341748307867473 9737797647256311230900605)
    ·
      refine ⟨3651674117721116711587727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9737797647256311230900605 3651674117721116711587727)
      ·
        refine ⟨5477511176581675067381591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651674117721116711587727 5477511176581675067381591)
        ·
          refine ⟨8216266764872512601072387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477511176581675067381591 8216266764872512601072387)
          ·
            refine ⟨12324400147308768901608581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216266764872512601072387 12324400147308768901608581)
            ·
              refine ⟨2310825027620394169051609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12324400147308768901608581 2310825027620394169051609)
              ·
                refine ⟨1733118770715295626788707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310825027620394169051609 1733118770715295626788707)
                ·
                  refine ⟨2599678156072943440183061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733118770715295626788707 2599678156072943440183061)
                  ·
                    refine ⟨121859913565919223758581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2599678156072943440183061 121859913565919223758581)
                    ·
                      rfl

theorem cell23_711964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_711964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711964 prefixEnd_711964 := by exact prefixLift 711964
  have htrace : WordTrace (prefixWord ++ tailWord_711964) baseStart_711964 baseEnd_711964 := by
    simpa [prefixWord, tailWord_711964, baseEnd_711964] using wordTrace_append hprefix tailTrace_711964
  have hstable : (prefixWord ++ tailWord_711964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711964).length < 2 ^ (prefixWord ++ tailWord_711964).sum := by decide
  have hdescent : baseEnd_711964 < baseStart_711964 := by decide
  rcases family_descends (prefixWord ++ tailWord_711964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711965 : List Nat := [1, 4, 2, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_711965 : Nat := 118140960795 + 711965 * 2 ^ 59
def prefixEnd_711965 : Nat := 4983230072969 + 3 ^ 40 * 711965 * 2
def baseEnd_711965 : Nat := 365580254178412167363239

theorem tailTrace_711965 : CollatzResearch.WordTrace tailWord_711965 prefixEnd_711965 365580254178412167363239 := by
  unfold tailWord_711965
  simp only [CollatzResearch.WordTrace]
  refine ⟨25967496865679873786521349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17311664577119915857680899 25967496865679873786521349)
  ·
    refine ⟨4868905662314976334972753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25967496865679873786521349 4868905662314976334972753)
    ·
      refine ⟨3651679246736232251229565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4868905662314976334972753 3651679246736232251229565)
      ·
        refine ⟨1369379717526087094211087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3651679246736232251229565 1369379717526087094211087)
        ·
          refine ⟨2054069576289130641316631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369379717526087094211087 2054069576289130641316631)
          ·
            refine ⟨3081104364433695961974947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054069576289130641316631 3081104364433695961974947)
            ·
              refine ⟨4621656546650543942962421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081104364433695961974947 4621656546650543942962421)
              ·
                refine ⟨433280301248488494652727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4621656546650543942962421 433280301248488494652727)
                ·
                  refine ⟨649920451872732741979091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433280301248488494652727 649920451872732741979091)
                  ·
                    refine ⟨974880677809099112968637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 649920451872732741979091 974880677809099112968637)
                    ·
                      refine ⟨365580254178412167363239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 974880677809099112968637 365580254178412167363239)
                      ·
                        rfl

theorem cell23_711965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_711965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711965 prefixEnd_711965 := by exact prefixLift 711965
  have htrace : WordTrace (prefixWord ++ tailWord_711965) baseStart_711965 baseEnd_711965 := by
    simpa [prefixWord, tailWord_711965, baseEnd_711965] using wordTrace_append hprefix tailTrace_711965
  have hstable : (prefixWord ++ tailWord_711965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711965).length < 2 ^ (prefixWord ++ tailWord_711965).sum := by decide
  have hdescent : baseEnd_711965 < baseStart_711965 := by decide
  rcases family_descends (prefixWord ++ tailWord_711965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711971 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 4]
def baseStart_711971 : Nat := 118140960795 + 711971 * 2 ^ 59
def prefixEnd_711971 : Nat := 4983230072969 + 3 ^ 40 * 711971 * 2
def baseEnd_711971 : Nat := 365583335062339143888211

theorem tailTrace_711971 : CollatzResearch.WordTrace tailWord_711971 prefixEnd_711971 365583335062339143888211 := by
  unfold tailWord_711971
  simp only [CollatzResearch.WordTrace]
  refine ⟨25967715703658136811239767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17311810469105424540826511 25967715703658136811239767)
  ·
    refine ⟨38951573555487205216859651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25967715703658136811239767 38951573555487205216859651)
    ·
      refine ⟨58427360333230807825289477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38951573555487205216859651 58427360333230807825289477)
      ·
        refine ⟨10955130062480776467241777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58427360333230807825289477 10955130062480776467241777)
        ·
          refine ⟨8216347546860582350431333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10955130062480776467241777 8216347546860582350431333)
          ·
            refine ⟨1540565165036359190705875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8216347546860582350431333 1540565165036359190705875)
            ·
              refine ⟨2310847747554538786058813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540565165036359190705875 2310847747554538786058813)
              ·
                refine ⟨866567905332952044772055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2310847747554538786058813 866567905332952044772055)
                ·
                  refine ⟨1299851857999428067158083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866567905332952044772055 1299851857999428067158083)
                  ·
                    refine ⟨1949777786999142100737125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1299851857999428067158083 1949777786999142100737125)
                    ·
                      refine ⟨365583335062339143888211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1949777786999142100737125 365583335062339143888211)
                      ·
                        rfl

theorem cell23_711971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_711971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_711971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_711971 prefixEnd_711971 := by exact prefixLift 711971
  have htrace : WordTrace (prefixWord ++ tailWord_711971) baseStart_711971 baseEnd_711971 := by
    simpa [prefixWord, tailWord_711971, baseEnd_711971] using wordTrace_append hprefix tailTrace_711971
  have hstable : (prefixWord ++ tailWord_711971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711971).length < 2 ^ (prefixWord ++ tailWord_711971).sum := by decide
  have hdescent : baseEnd_711971 < baseStart_711971 := by decide
  rcases family_descends (prefixWord ++ tailWord_711971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712001 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_712001 : Nat := 118140960795 + 712001 * 2 ^ 59
def prefixEnd_712001 : Nat := 4983230072969 + 3 ^ 40 * 712001 * 2
def baseEnd_712001 : Nat := 365598739481974026513073

theorem tailTrace_712001 : CollatzResearch.WordTrace tailWord_712001 prefixEnd_712001 365598739481974026513073 := by
  unfold tailWord_712001
  simp only [CollatzResearch.WordTrace]
  refine ⟨25968809893549451934831857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17312539929032967956554571 25968809893549451934831857)
  ·
    refine ⟨19476607420162088951123893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25968809893549451934831857 19476607420162088951123893)
    ·
      refine ⟨1825931945640195839167865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19476607420162088951123893 1825931945640195839167865)
      ·
        refine ⟨1369448959230146879375899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1825931945640195839167865 1369448959230146879375899)
        ·
          refine ⟨2054173438845220319063849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369448959230146879375899 2054173438845220319063849)
          ·
            refine ⟨1540630079133915239297887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2054173438845220319063849 1540630079133915239297887)
            ·
              refine ⟨2310945118700872858946831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540630079133915239297887 2310945118700872858946831)
              ·
                refine ⟨3466417678051309288420247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310945118700872858946831 3466417678051309288420247)
                ·
                  refine ⟨5199626517076963932630371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466417678051309288420247 5199626517076963932630371)
                  ·
                    refine ⟨7799439775615445898945557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5199626517076963932630371 7799439775615445898945557)
                    ·
                      refine ⟨365598739481974026513073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7799439775615445898945557 365598739481974026513073)
                      ·
                        rfl

theorem cell23_712001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_712001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712001 prefixEnd_712001 := by exact prefixLift 712001
  have htrace : WordTrace (prefixWord ++ tailWord_712001) baseStart_712001 baseEnd_712001 := by
    simpa [prefixWord, tailWord_712001, baseEnd_712001] using wordTrace_append hprefix tailTrace_712001
  have hstable : (prefixWord ++ tailWord_712001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712001).length < 2 ^ (prefixWord ++ tailWord_712001).sum := by decide
  have hdescent : baseEnd_712001 < baseStart_712001 := by decide
  rcases family_descends (prefixWord ++ tailWord_712001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712031 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 5, 3, 2]
def baseStart_712031 : Nat := 118140960795 + 712031 * 2 ^ 59
def prefixEnd_712031 : Nat := 4983230072969 + 3 ^ 40 * 712031 * 2
def baseEnd_712031 : Nat := 365614143901608909137935

theorem tailTrace_712031 : CollatzResearch.WordTrace tailWord_712031 prefixEnd_712031 365614143901608909137935 := by
  unfold tailWord_712031
  simp only [CollatzResearch.WordTrace]
  refine ⟨25969904083440767058423947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17313269388960511372282631 25969904083440767058423947)
  ·
    refine ⟨38954856125161150587635921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25969904083440767058423947 38954856125161150587635921)
    ·
      refine ⟨29216142093870862940726941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38954856125161150587635921 29216142093870862940726941)
      ·
        refine ⟨10956053285201573602772603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29216142093870862940726941 10956053285201573602772603)
        ·
          refine ⟨16434079927802360404158905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10956053285201573602772603 16434079927802360404158905)
          ·
            refine ⟨12325559945851770303119179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16434079927802360404158905 12325559945851770303119179)
            ·
              refine ⟨18488339918777655454678769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12325559945851770303119179 18488339918777655454678769)
              ·
                refine ⟨13866254939083241591009077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18488339918777655454678769 13866254939083241591009077)
                ·
                  refine ⟨1299961400539053899157101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13866254939083241591009077 1299961400539053899157101)
                  ·
                    refine ⟨487485525202145212183913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1299961400539053899157101 487485525202145212183913)
                    ·
                      refine ⟨365614143901608909137935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487485525202145212183913 365614143901608909137935)
                      ·
                        rfl

theorem cell23_712031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_712031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712031 prefixEnd_712031 := by exact prefixLift 712031
  have htrace : WordTrace (prefixWord ++ tailWord_712031) baseStart_712031 baseEnd_712031 := by
    simpa [prefixWord, tailWord_712031, baseEnd_712031] using wordTrace_append hprefix tailTrace_712031
  have hstable : (prefixWord ++ tailWord_712031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712031).length < 2 ^ (prefixWord ++ tailWord_712031).sum := by decide
  have hdescent : baseEnd_712031 < baseStart_712031 := by decide
  rcases family_descends (prefixWord ++ tailWord_712031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712039 : List Nat := [1, 1, 5, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_712039 : Nat := 118140960795 + 712039 * 2 ^ 59
def prefixEnd_712039 : Nat := 4983230072969 + 3 ^ 40 * 712039 * 2
def baseEnd_712039 : Nat := 365618251746844877837899

theorem tailTrace_712039 : CollatzResearch.WordTrace tailWord_712039 prefixEnd_712039 365618251746844877837899 := by
  unfold tailWord_712039
  simp only [CollatzResearch.WordTrace]
  refine ⟨25970195867411784424715171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17313463911607856283143447 25970195867411784424715171)
  ·
    refine ⟨38955293801117676637072757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25970195867411784424715171 38955293801117676637072757)
    ·
      refine ⟨3652058793854782184725571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38955293801117676637072757 3652058793854782184725571)
      ·
        refine ⟨5478088190782173277088357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652058793854782184725571 5478088190782173277088357)
        ·
          refine ⟨1027141535771657489454067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5478088190782173277088357 1027141535771657489454067)
          ·
            refine ⟨1540712303657486234181101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027141535771657489454067 1540712303657486234181101)
            ·
              refine ⟨577767113871557337817913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1540712303657486234181101 577767113871557337817913)
              ·
                refine ⟨433325335403668003363435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577767113871557337817913 433325335403668003363435)
                ·
                  refine ⟨649988003105502005045153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433325335403668003363435 649988003105502005045153)
                  ·
                    refine ⟨487491002329126503783865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 649988003105502005045153 487491002329126503783865)
                    ·
                      refine ⟨365618251746844877837899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487491002329126503783865 365618251746844877837899)
                      ·
                        rfl

theorem cell23_712039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_712039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712039 prefixEnd_712039 := by exact prefixLift 712039
  have htrace : WordTrace (prefixWord ++ tailWord_712039) baseStart_712039 baseEnd_712039 := by
    simpa [prefixWord, tailWord_712039, baseEnd_712039] using wordTrace_append hprefix tailTrace_712039
  have hstable : (prefixWord ++ tailWord_712039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712039).length < 2 ^ (prefixWord ++ tailWord_712039).sum := by decide
  have hdescent : baseEnd_712039 < baseStart_712039 := by decide
  rcases family_descends (prefixWord ++ tailWord_712039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712065 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_712065 : Nat := 118140960795 + 712065 * 2 ^ 59
def prefixEnd_712065 : Nat := 4983230072969 + 3 ^ 40 * 712065 * 2
def baseEnd_712065 : Nat := 365631602243861776112779

theorem tailTrace_712065 : CollatzResearch.WordTrace tailWord_712065 prefixEnd_712065 365631602243861776112779 := by
  unfold tailWord_712065
  simp only [CollatzResearch.WordTrace]
  refine ⟨25971144165317590865161649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17314096110211727243441099 25971144165317590865161649)
  ·
    refine ⟨19478358123988193148871237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25971144165317590865161649 19478358123988193148871237)
    ·
      refine ⟨3652192148247786215413357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19478358123988193148871237 3652192148247786215413357)
      ·
        refine ⟨1369572055592919830780009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3652192148247786215413357 1369572055592919830780009)
        ·
          refine ⟨1027179041694689873085007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1369572055592919830780009 1027179041694689873085007)
          ·
            refine ⟨1540768562542034809627511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027179041694689873085007 1540768562542034809627511)
            ·
              refine ⟨2311152843813052214441267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540768562542034809627511 2311152843813052214441267)
              ·
                refine ⟨3466729265719578321661901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311152843813052214441267 3466729265719578321661901)
                ·
                  refine ⟨1300023474644841870623213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3466729265719578321661901 1300023474644841870623213)
                  ·
                    refine ⟨487508802991815701483705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1300023474644841870623213 487508802991815701483705)
                    ·
                      refine ⟨365631602243861776112779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487508802991815701483705 365631602243861776112779)
                      ·
                        rfl

theorem cell23_712065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_712065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712065 prefixEnd_712065 := by exact prefixLift 712065
  have htrace : WordTrace (prefixWord ++ tailWord_712065) baseStart_712065 baseEnd_712065 := by
    simpa [prefixWord, tailWord_712065, baseEnd_712065] using wordTrace_append hprefix tailTrace_712065
  have hstable : (prefixWord ++ tailWord_712065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712065).length < 2 ^ (prefixWord ++ tailWord_712065).sum := by decide
  have hdescent : baseEnd_712065 < baseStart_712065 := by decide
  rcases family_descends (prefixWord ++ tailWord_712065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712095 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 2, 2, 2]
def baseStart_712095 : Nat := 118140960795 + 712095 * 2 ^ 59
def prefixEnd_712095 : Nat := 4983230072969 + 3 ^ 40 * 712095 * 2
def baseEnd_712095 : Nat := 365647006663496658737641

theorem tailTrace_712095 : CollatzResearch.WordTrace tailWord_712095 prefixEnd_712095 365647006663496658737641 := by
  unfold tailWord_712095
  simp only [CollatzResearch.WordTrace]
  refine ⟨25972238355208905988753739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17314825570139270659169159 25972238355208905988753739)
  ·
    refine ⟨38958357532813358983130609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25972238355208905988753739 38958357532813358983130609)
    ·
      refine ⟨29218768149610019237347957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38958357532813358983130609 29218768149610019237347957)
      ·
        refine ⟨2739259514025939303501371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29218768149610019237347957 2739259514025939303501371)
        ·
          refine ⟨4108889271038908955252057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739259514025939303501371 4108889271038908955252057)
          ·
            refine ⟨3081666953279181716439043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108889271038908955252057 3081666953279181716439043)
            ·
              refine ⟨4622500429918772574658565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081666953279181716439043 4622500429918772574658565)
              ·
                refine ⟨866718830609769857748481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4622500429918772574658565 866718830609769857748481)
                ·
                  refine ⟨650039122957327393311361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866718830609769857748481 650039122957327393311361)
                  ·
                    refine ⟨487529342217995544983521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 650039122957327393311361 487529342217995544983521)
                    ·
                      refine ⟨365647006663496658737641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487529342217995544983521 365647006663496658737641)
                      ·
                        rfl

theorem cell23_712095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_712095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712095 prefixEnd_712095 := by exact prefixLift 712095
  have htrace : WordTrace (prefixWord ++ tailWord_712095) baseStart_712095 baseEnd_712095 := by
    simpa [prefixWord, tailWord_712095, baseEnd_712095] using wordTrace_append hprefix tailTrace_712095
  have hstable : (prefixWord ++ tailWord_712095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712095).length < 2 ^ (prefixWord ++ tailWord_712095).sum := by decide
  have hdescent : baseEnd_712095 < baseStart_712095 := by decide
  rcases family_descends (prefixWord ++ tailWord_712095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712131 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 2, 5]
def baseStart_712131 : Nat := 118140960795 + 712131 * 2 ^ 59
def prefixEnd_712131 : Nat := 4983230072969 + 3 ^ 40 * 712131 * 2
def baseEnd_712131 : Nat := 121888497322352839295825

theorem tailTrace_712131 : CollatzResearch.WordTrace tailWord_712131 prefixEnd_712131 121888497322352839295825 := by
  unfold tailWord_712131
  simp only [CollatzResearch.WordTrace]
  refine ⟨25973551383078484137064247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17315700922052322758042831 25973551383078484137064247)
  ·
    refine ⟨38960327074617726205596371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25973551383078484137064247 38960327074617726205596371)
    ·
      refine ⟨58440490611926589308394557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38960327074617726205596371 58440490611926589308394557)
      ·
        refine ⟨21915183979472470990647959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58440490611926589308394557 21915183979472470990647959)
        ·
          refine ⟨32872775969208706485971939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21915183979472470990647959 32872775969208706485971939)
          ·
            refine ⟨49309163953813059728957909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32872775969208706485971939 49309163953813059728957909)
            ·
              refine ⟨1155683530167493587397451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49309163953813059728957909 1155683530167493587397451)
              ·
                refine ⟨1733525295251240381096177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155683530167493587397451 1733525295251240381096177)
                ·
                  refine ⟨1300143971438430285822133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733525295251240381096177 1300143971438430285822133)
                  ·
                    refine ⟨121888497322352839295825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1300143971438430285822133 121888497322352839295825)
                    ·
                      rfl

theorem cell23_712131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 5].length) (baseStart_712131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712131 prefixEnd_712131 := by exact prefixLift 712131
  have htrace : WordTrace (prefixWord ++ tailWord_712131) baseStart_712131 baseEnd_712131 := by
    simpa [prefixWord, tailWord_712131, baseEnd_712131] using wordTrace_append hprefix tailTrace_712131
  have hstable : (prefixWord ++ tailWord_712131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712131).length < 2 ^ (prefixWord ++ tailWord_712131).sum := by decide
  have hdescent : baseEnd_712131 < baseStart_712131 := by decide
  rcases family_descends (prefixWord ++ tailWord_712131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712151 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_712151 : Nat := 118140960795 + 712151 * 2 ^ 59
def prefixEnd_712151 : Nat := 4983230072969 + 3 ^ 40 * 712151 * 2
def baseEnd_712151 : Nat := 365675761580148439637383

theorem tailTrace_712151 : CollatzResearch.WordTrace tailWord_712151 prefixEnd_712151 365675761580148439637383 := by
  unfold tailWord_712151
  simp only [CollatzResearch.WordTrace]
  refine ⟨25974280843006027552792307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17316187228670685035194871 25974280843006027552792307)
  ·
    refine ⟨38961421264509041329188461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25974280843006027552792307 38961421264509041329188461)
    ·
      refine ⟨14610532974190890498445673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38961421264509041329188461 14610532974190890498445673)
      ·
        refine ⟨10957899730643167873834255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14610532974190890498445673 10957899730643167873834255)
        ·
          refine ⟨16436849595964751810751383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10957899730643167873834255 16436849595964751810751383)
          ·
            refine ⟨24655274393947127716127075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16436849595964751810751383 24655274393947127716127075)
            ·
              refine ⟨36982911590920691574190613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24655274393947127716127075 36982911590920691574190613)
              ·
                refine ⟨1733573980824407417540185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36982911590920691574190613 1733573980824407417540185)
                ·
                  refine ⟨1300180485618305563155139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733573980824407417540185 1300180485618305563155139)
                  ·
                    refine ⟨1950270728427458344732709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300180485618305563155139 1950270728427458344732709)
                    ·
                      refine ⟨365675761580148439637383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1950270728427458344732709 365675761580148439637383)
                      ·
                        rfl

theorem cell23_712151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_712151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712151 prefixEnd_712151 := by exact prefixLift 712151
  have htrace : WordTrace (prefixWord ++ tailWord_712151) baseStart_712151 baseEnd_712151 := by
    simpa [prefixWord, tailWord_712151, baseEnd_712151] using wordTrace_append hprefix tailTrace_712151
  have hstable : (prefixWord ++ tailWord_712151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712151).length < 2 ^ (prefixWord ++ tailWord_712151).sum := by decide
  have hdescent : baseEnd_712151 < baseStart_712151 := by decide
  rcases family_descends (prefixWord ++ tailWord_712151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712168 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_712168 : Nat := 118140960795 + 712168 * 2 ^ 59
def prefixEnd_712168 : Nat := 4983230072969 + 3 ^ 40 * 712168 * 2
def baseEnd_712168 : Nat := 365684490751274873124805

theorem tailTrace_712168 : CollatzResearch.WordTrace tailWord_712168 prefixEnd_712168 365684490751274873124805 := by
  unfold tailWord_712168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987450441972219728080579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17316600589296292970774105 12987450441972219728080579)
  ·
    refine ⟨19481175662958329592120869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987450441972219728080579 19481175662958329592120869)
    ·
      refine ⟨3652720436804686798522663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19481175662958329592120869 3652720436804686798522663)
      ·
        refine ⟨5479080655207030197783995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652720436804686798522663 5479080655207030197783995)
        ·
          refine ⟨8218620982810545296675993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479080655207030197783995 8218620982810545296675993)
          ·
            refine ⟨6163965737107908972506995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8218620982810545296675993 6163965737107908972506995)
            ·
              refine ⟨9245948605661863458760493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163965737107908972506995 9245948605661863458760493)
              ·
                refine ⟨3467230727123198797035185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9245948605661863458760493 3467230727123198797035185)
                ·
                  refine ⟨2600423045342399097776389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3467230727123198797035185 2600423045342399097776389)
                  ·
                    refine ⟨487579321001699830833073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2600423045342399097776389 487579321001699830833073)
                    ·
                      refine ⟨365684490751274873124805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487579321001699830833073 365684490751274873124805)
                      ·
                        rfl

theorem cell23_712168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_712168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712168 prefixEnd_712168 := by exact prefixLift 712168
  have htrace : WordTrace (prefixWord ++ tailWord_712168) baseStart_712168 baseEnd_712168 := by
    simpa [prefixWord, tailWord_712168, baseEnd_712168] using wordTrace_append hprefix tailTrace_712168
  have hstable : (prefixWord ++ tailWord_712168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712168).length < 2 ^ (prefixWord ++ tailWord_712168).sum := by decide
  have hdescent : baseEnd_712168 < baseStart_712168 := by decide
  rcases family_descends (prefixWord ++ tailWord_712168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712171 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 3]
def baseStart_712171 : Nat := 118140960795 + 712171 * 2 ^ 59
def prefixEnd_712171 : Nat := 4983230072969 + 3 ^ 40 * 712171 * 2
def baseEnd_712171 : Nat := 365686031193238361387291

theorem tailTrace_712171 : CollatzResearch.WordTrace tailWord_712171 prefixEnd_712171 365686031193238361387291 := by
  unfold tailWord_712171
  simp only [CollatzResearch.WordTrace]
  refine ⟨25975010302933570968520367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17316673535289047312346911 25975010302933570968520367)
  ·
    refine ⟨38962515454400356452780551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25975010302933570968520367 38962515454400356452780551)
    ·
      refine ⟨58443773181600534679170827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38962515454400356452780551 58443773181600534679170827)
      ·
        refine ⟨87665659772400802018756241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58443773181600534679170827 87665659772400802018756241)
        ·
          refine ⟨65749244829300601514067181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87665659772400802018756241 65749244829300601514067181)
          ·
            refine ⟨24655966810987725567775193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65749244829300601514067181 24655966810987725567775193)
            ·
              refine ⟨18491975108240794175831395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24655966810987725567775193 18491975108240794175831395)
              ·
                refine ⟨27737962662361191263747093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18491975108240794175831395 27737962662361191263747093)
                ·
                  refine ⟨1300216999798180840488145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27737962662361191263747093 1300216999798180840488145)
                  ·
                    refine ⟨975162749848635630366109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1300216999798180840488145 975162749848635630366109)
                    ·
                      refine ⟨365686031193238361387291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 975162749848635630366109 365686031193238361387291)
                      ·
                        rfl

theorem cell23_712171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 3].length) (baseStart_712171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712171 prefixEnd_712171 := by exact prefixLift 712171
  have htrace : WordTrace (prefixWord ++ tailWord_712171) baseStart_712171 baseEnd_712171 := by
    simpa [prefixWord, tailWord_712171, baseEnd_712171] using wordTrace_append hprefix tailTrace_712171
  have hstable : (prefixWord ++ tailWord_712171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712171).length < 2 ^ (prefixWord ++ tailWord_712171).sum := by decide
  have hdescent : baseEnd_712171 < baseStart_712171 := by decide
  rcases family_descends (prefixWord ++ tailWord_712171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712225 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 6]
def baseStart_712225 : Nat := 118140960795 + 712225 * 2 ^ 59
def prefixEnd_712225 : Nat := 4983230072969 + 3 ^ 40 * 712225 * 2
def baseEnd_712225 : Nat := 40634862127620127790227

theorem tailTrace_712225 : CollatzResearch.WordTrace tailWord_712225 prefixEnd_712225 40634862127620127790227 := by
  unfold tailWord_712225
  simp only [CollatzResearch.WordTrace]
  refine ⟨25976979844737938190986129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17317986563158625460657419 25976979844737938190986129)
  ·
    refine ⟨19482734883553453643239597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25976979844737938190986129 19482734883553453643239597)
    ·
      refine ⟨7306025581332545116214849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19482734883553453643239597 7306025581332545116214849)
      ·
        refine ⟨5479519185999408837161137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7306025581332545116214849 5479519185999408837161137)
        ·
          refine ⟨4109639389499556627870853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479519185999408837161137 4109639389499556627870853)
          ·
            refine ⟨770557385531166867725785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4109639389499556627870853 770557385531166867725785)
            ·
              refine ⟨577918039148375150794339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770557385531166867725785 577918039148375150794339)
              ·
                refine ⟨866877058722562726191509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577918039148375150794339 866877058722562726191509)
                ·
                  refine ⟨40634862127620127790227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 866877058722562726191509 40634862127620127790227)
                  ·
                    rfl

theorem cell23_712225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 6].length) (baseStart_712225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712225 prefixEnd_712225 := by exact prefixLift 712225
  have htrace : WordTrace (prefixWord ++ tailWord_712225) baseStart_712225 baseEnd_712225 := by
    simpa [prefixWord, tailWord_712225, baseEnd_712225] using wordTrace_append hprefix tailTrace_712225
  have hstable : (prefixWord ++ tailWord_712225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712225).length < 2 ^ (prefixWord ++ tailWord_712225).sum := by decide
  have hdescent : baseEnd_712225 < baseStart_712225 := by decide
  rcases family_descends (prefixWord ++ tailWord_712225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712245 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_712245 : Nat := 118140960795 + 712245 * 2 ^ 59
def prefixEnd_712245 : Nat := 4983230072969 + 3 ^ 40 * 712245 * 2
def baseEnd_712245 : Nat := 365724028761671071861951

theorem tailTrace_712245 : CollatzResearch.WordTrace tailWord_712245 prefixEnd_712245 365724028761671071861951 := by
  unfold tailWord_712245
  simp only [CollatzResearch.WordTrace]
  refine ⟨25977709304665481606714189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17318472869776987737809459 25977709304665481606714189)
  ·
    refine ⟨9741640989249555602517821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25977709304665481606714189 9741640989249555602517821)
    ·
      refine ⟨3653115370968583350944183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9741640989249555602517821 3653115370968583350944183)
      ·
        refine ⟨5479673056452875026416275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653115370968583350944183 5479673056452875026416275)
        ·
          refine ⟨8219509584679312539624413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479673056452875026416275 8219509584679312539624413)
          ·
            refine ⟨3082316094254742202359155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8219509584679312539624413 3082316094254742202359155)
            ·
              refine ⟨4623474141382113303538733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3082316094254742202359155 4623474141382113303538733)
              ·
                refine ⟨1733802803018292488827025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4623474141382113303538733 1733802803018292488827025)
                ·
                  refine ⟨1300352102263719366620269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733802803018292488827025 1300352102263719366620269)
                  ·
                    refine ⟨487632038348894762482601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1300352102263719366620269 487632038348894762482601)
                    ·
                      refine ⟨365724028761671071861951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487632038348894762482601 365724028761671071861951)
                      ·
                        rfl

theorem cell23_712245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_712245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712245 prefixEnd_712245 := by exact prefixLift 712245
  have htrace : WordTrace (prefixWord ++ tailWord_712245) baseStart_712245 baseEnd_712245 := by
    simpa [prefixWord, tailWord_712245, baseEnd_712245] using wordTrace_append hprefix tailTrace_712245
  have hstable : (prefixWord ++ tailWord_712245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712245).length < 2 ^ (prefixWord ++ tailWord_712245).sum := by decide
  have hdescent : baseEnd_712245 < baseStart_712245 := by decide
  rcases family_descends (prefixWord ++ tailWord_712245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712255 : List Nat := [1, 1, 2, 2, 3, 4, 3, 1, 1, 5]
def baseStart_712255 : Nat := 118140960795 + 712255 * 2 ^ 59
def prefixEnd_712255 : Nat := 4983230072969 + 3 ^ 40 * 712255 * 2
def baseEnd_712255 : Nat := 121909721189405344245635

theorem tailTrace_712255 : CollatzResearch.WordTrace tailWord_712255 prefixEnd_712255 121909721189405344245635 := by
  unfold tailWord_712255
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978074034629253314578219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17318716023086168876385479 25978074034629253314578219)
  ·
    refine ⟨38967111051943879971867329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25978074034629253314578219 38967111051943879971867329)
    ·
      refine ⟨29225333288957909978900497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38967111051943879971867329 29225333288957909978900497)
      ·
        refine ⟨21918999966718432484175373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29225333288957909978900497 21918999966718432484175373)
        ·
          refine ⟨8219624987519412181565765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21918999966718432484175373 8219624987519412181565765)
          ·
            refine ⟨1541179685159889784043581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8219624987519412181565765 1541179685159889784043581)
            ·
              refine ⟨577942381934958669016343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1541179685159889784043581 577942381934958669016343)
              ·
                refine ⟨866913572902438003524515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577942381934958669016343 866913572902438003524515)
                ·
                  refine ⟨1300370359353657005286773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866913572902438003524515 1300370359353657005286773)
                  ·
                    refine ⟨121909721189405344245635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1300370359353657005286773 121909721189405344245635)
                    ·
                      rfl

theorem cell23_712255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 1, 5].length) (baseStart_712255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712255 prefixEnd_712255 := by exact prefixLift 712255
  have htrace : WordTrace (prefixWord ++ tailWord_712255) baseStart_712255 baseEnd_712255 := by
    simpa [prefixWord, tailWord_712255, baseEnd_712255] using wordTrace_append hprefix tailTrace_712255
  have hstable : (prefixWord ++ tailWord_712255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712255).length < 2 ^ (prefixWord ++ tailWord_712255).sum := by decide
  have hdescent : baseEnd_712255 < baseStart_712255 := by decide
  rcases family_descends (prefixWord ++ tailWord_712255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712271 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_712271 : Nat := 118140960795 + 712271 * 2 ^ 59
def prefixEnd_712271 : Nat := 4983230072969 + 3 ^ 40 * 712271 * 2
def baseEnd_712271 : Nat := 365737379258687970136831

theorem tailTrace_712271 : CollatzResearch.WordTrace tailWord_712271 prefixEnd_712271 365737379258687970136831 := by
  unfold tailWord_712271
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978657602571288047160667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17319105068380858698107111 25978657602571288047160667)
  ·
    refine ⟨38967986403856932070741001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25978657602571288047160667 38967986403856932070741001)
    ·
      refine ⟨29225989802892699053055751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38967986403856932070741001 29225989802892699053055751)
      ·
        refine ⟨43838984704339048579583627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29225989802892699053055751 43838984704339048579583627)
        ·
          refine ⟨65758477056508572869375441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43838984704339048579583627 65758477056508572869375441)
          ·
            refine ⟨49318857792381429652031581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65758477056508572869375441 49318857792381429652031581)
            ·
              refine ⟨18494571672143036119511843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49318857792381429652031581 18494571672143036119511843)
              ·
                refine ⟨27741857508214554179267765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18494571672143036119511843 27741857508214554179267765)
                ·
                  refine ⟨2600799141395114454306353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27741857508214554179267765 2600799141395114454306353)
                  ·
                    refine ⟨1950599356046335840729765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2600799141395114454306353 1950599356046335840729765)
                    ·
                      refine ⟨365737379258687970136831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1950599356046335840729765 365737379258687970136831)
                      ·
                        rfl

theorem cell23_712271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_712271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712271 prefixEnd_712271 := by exact prefixLift 712271
  have htrace : WordTrace (prefixWord ++ tailWord_712271) baseStart_712271 baseEnd_712271 := by
    simpa [prefixWord, tailWord_712271, baseEnd_712271] using wordTrace_append hprefix tailTrace_712271
  have hstable : (prefixWord ++ tailWord_712271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712271).length < 2 ^ (prefixWord ++ tailWord_712271).sum := by decide
  have hdescent : baseEnd_712271 < baseStart_712271 := by decide
  rcases family_descends (prefixWord ++ tailWord_712271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712292 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_712292 : Nat := 118140960795 + 712292 * 2 ^ 59
def prefixEnd_712292 : Nat := 4983230072969 + 3 ^ 40 * 712292 * 2
def baseEnd_712292 : Nat := 365748162352432387974235

theorem tailTrace_712292 : CollatzResearch.WordTrace tailWord_712292 prefixEnd_712292 365748162352432387974235 := by
  unfold tailWord_712292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989711767747604316837565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17319615690330139089116753 12989711767747604316837565)
  ·
    refine ⟨4871141912905351618814087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12989711767747604316837565 4871141912905351618814087)
    ·
      refine ⟨7306712869358027428221131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4871141912905351618814087 7306712869358027428221131)
      ·
        refine ⟨10960069304037041142331697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7306712869358027428221131 10960069304037041142331697)
        ·
          refine ⟨8220051978027780856748773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10960069304037041142331697 8220051978027780856748773)
          ·
            refine ⟨1541259745880208910640395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8220051978027780856748773 1541259745880208910640395)
            ·
              refine ⟨2311889618820313365960593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541259745880208910640395 2311889618820313365960593)
              ·
                refine ⟨1733917214115235024470445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2311889618820313365960593 1733917214115235024470445)
                ·
                  refine ⟨650218955293213134176417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1733917214115235024470445 650218955293213134176417)
                  ·
                    refine ⟨487664216469909850632313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 650218955293213134176417 487664216469909850632313)
                    ·
                      refine ⟨365748162352432387974235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487664216469909850632313 365748162352432387974235)
                      ·
                        rfl

theorem cell23_712292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_712292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712292 prefixEnd_712292 := by exact prefixLift 712292
  have htrace : WordTrace (prefixWord ++ tailWord_712292) baseStart_712292 baseEnd_712292 := by
    simpa [prefixWord, tailWord_712292, baseEnd_712292] using wordTrace_append hprefix tailTrace_712292
  have hstable : (prefixWord ++ tailWord_712292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712292).length < 2 ^ (prefixWord ++ tailWord_712292).sum := by decide
  have hdescent : baseEnd_712292 < baseStart_712292 := by decide
  rcases family_descends (prefixWord ++ tailWord_712292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712309 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_712309 : Nat := 118140960795 + 712309 * 2 ^ 59
def prefixEnd_712309 : Nat := 4983230072969 + 3 ^ 40 * 712309 * 2
def baseEnd_712309 : Nat := 365756891523558821461657

theorem tailTrace_712309 : CollatzResearch.WordTrace tailWord_712309 prefixEnd_712309 365756891523558821461657 := by
  unfold tailWord_712309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980043576433620537043981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17320029050955747024695987 25980043576433620537043981)
  ·
    refine ⟨9742516341162607701391493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25980043576433620537043981 9742516341162607701391493)
    ·
      refine ⟨1826721813967988944010905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9742516341162607701391493 1826721813967988944010905)
      ·
        refine ⟨1370041360475991708008179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1826721813967988944010905 1370041360475991708008179)
        ·
          refine ⟨2055062040713987562012269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370041360475991708008179 2055062040713987562012269)
          ·
            refine ⟨770648265267745335754601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2055062040713987562012269 770648265267745335754601)
            ·
              refine ⟨577986198950809001815951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770648265267745335754601 577986198950809001815951)
              ·
                refine ⟨866979298426213502723927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577986198950809001815951 866979298426213502723927)
                ·
                  refine ⟨1300468947639320254085891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866979298426213502723927 1300468947639320254085891)
                  ·
                    refine ⟨1950703421458980381128837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300468947639320254085891 1950703421458980381128837)
                    ·
                      refine ⟨365756891523558821461657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1950703421458980381128837 365756891523558821461657)
                      ·
                        rfl

theorem cell23_712309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_712309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712309 prefixEnd_712309 := by exact prefixLift 712309
  have htrace : WordTrace (prefixWord ++ tailWord_712309) baseStart_712309 baseEnd_712309 := by
    simpa [prefixWord, tailWord_712309, baseEnd_712309] using wordTrace_append hprefix tailTrace_712309
  have hstable : (prefixWord ++ tailWord_712309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712309).length < 2 ^ (prefixWord ++ tailWord_712309).sum := by decide
  have hdescent : baseEnd_712309 < baseStart_712309 := by decide
  rcases family_descends (prefixWord ++ tailWord_712309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712325 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_712325 : Nat := 118140960795 + 712325 * 2 ^ 59
def prefixEnd_712325 : Nat := 4983230072969 + 3 ^ 40 * 712325 * 2
def baseEnd_712325 : Nat := 365765107214030758861583

theorem tailTrace_712325 : CollatzResearch.WordTrace tailWord_712325 prefixEnd_712325 365765107214030758861583 := by
  unfold tailWord_712325
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980627144375655269626429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17320418096250436846417619 25980627144375655269626429)
  ·
    refine ⟨9742735179140870726109911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25980627144375655269626429 9742735179140870726109911)
    ·
      refine ⟨14614102768711306089164867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9742735179140870726109911 14614102768711306089164867)
      ·
        refine ⟨21921154153066959133747301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14614102768711306089164867 21921154153066959133747301)
        ·
          refine ⟨4110216403700054837577619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21921154153066959133747301 4110216403700054837577619)
          ·
            refine ⟨6165324605550082256366429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110216403700054837577619 6165324605550082256366429)
            ·
              refine ⟨2311996727081280846137411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6165324605550082256366429 2311996727081280846137411)
              ·
                refine ⟨3467995090621921269206117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311996727081280846137411 3467995090621921269206117)
                ·
                  refine ⟨650249079491610237976147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3467995090621921269206117 650249079491610237976147)
                  ·
                    refine ⟨975373619237415356964221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 650249079491610237976147 975373619237415356964221)
                    ·
                      refine ⟨365765107214030758861583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 975373619237415356964221 365765107214030758861583)
                      ·
                        rfl

theorem cell23_712325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_712325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712325 prefixEnd_712325 := by exact prefixLift 712325
  have htrace : WordTrace (prefixWord ++ tailWord_712325) baseStart_712325 baseEnd_712325 := by
    simpa [prefixWord, tailWord_712325, baseEnd_712325] using wordTrace_append hprefix tailTrace_712325
  have hstable : (prefixWord ++ tailWord_712325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712325).length < 2 ^ (prefixWord ++ tailWord_712325).sum := by decide
  have hdescent : baseEnd_712325 < baseStart_712325 := by decide
  rcases family_descends (prefixWord ++ tailWord_712325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712352 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 1, 3, 2]
def baseStart_712352 : Nat := 118140960795 + 712352 * 2 ^ 59
def prefixEnd_712352 : Nat := 4983230072969 + 3 ^ 40 * 712352 * 2
def baseEnd_712352 : Nat := 365778971191702153223959

theorem tailTrace_712352 : CollatzResearch.WordTrace tailWord_712352 prefixEnd_712352 365778971191702153223959 := by
  unfold tailWord_712352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12990805957638919440429655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17321074610185225920572873 12990805957638919440429655)
  ·
    refine ⟨19486208936458379160644483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12990805957638919440429655 19486208936458379160644483)
    ·
      refine ⟨29229313404687568740966725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19486208936458379160644483 29229313404687568740966725)
      ·
        refine ⟨5480496263378919138931261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29229313404687568740966725 5480496263378919138931261)
        ·
          refine ⟨2055186098767094677099223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5480496263378919138931261 2055186098767094677099223)
          ·
            refine ⟨3082779148150642015648835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055186098767094677099223 3082779148150642015648835)
            ·
              refine ⟨4624168722225963023473253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3082779148150642015648835 4624168722225963023473253)
              ·
                refine ⟨867031635417368066901235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4624168722225963023473253 867031635417368066901235)
                ·
                  refine ⟨1300547453126052100351853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867031635417368066901235 1300547453126052100351853)
                  ·
                    refine ⟨487705294922269537631945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1300547453126052100351853 487705294922269537631945)
                    ·
                      refine ⟨365778971191702153223959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487705294922269537631945 365778971191702153223959)
                      ·
                        rfl

theorem cell23_712352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_712352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712352 prefixEnd_712352 := by exact prefixLift 712352
  have htrace : WordTrace (prefixWord ++ tailWord_712352) baseStart_712352 baseEnd_712352 := by
    simpa [prefixWord, tailWord_712352, baseEnd_712352] using wordTrace_append hprefix tailTrace_712352
  have hstable : (prefixWord ++ tailWord_712352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712352).length < 2 ^ (prefixWord ++ tailWord_712352).sum := by decide
  have hdescent : baseEnd_712352 < baseStart_712352 := by decide
  rcases family_descends (prefixWord ++ tailWord_712352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712361 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_712361 : Nat := 118140960795 + 712361 * 2 ^ 59
def prefixEnd_712361 : Nat := 4983230072969 + 3 ^ 40 * 712361 * 2
def baseEnd_712361 : Nat := 365783592517592618011417

theorem tailTrace_712361 : CollatzResearch.WordTrace tailWord_712361 prefixEnd_712361 365783592517592618011417 := by
  unfold tailWord_712361
  simp only [CollatzResearch.WordTrace]
  refine ⟨25981940172245233417936937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17321293448163488945291291 25981940172245233417936937)
  ·
    refine ⟨19486455129183925063452703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25981940172245233417936937 19486455129183925063452703)
    ·
      refine ⟨29229682693775887595179055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19486455129183925063452703 29229682693775887595179055)
      ·
        refine ⟨43844524040663831392768583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29229682693775887595179055 43844524040663831392768583)
        ·
          refine ⟨65766786060995747089152875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43844524040663831392768583 65766786060995747089152875)
          ·
            refine ⟨98650179091493620633729313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65766786060995747089152875 98650179091493620633729313)
            ·
              refine ⟨73987634318620215475296985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98650179091493620633729313 73987634318620215475296985)
              ·
                refine ⟨55490725738965161606472739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73987634318620215475296985 55490725738965161606472739)
                ·
                  refine ⟨83236088608447742409709109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55490725738965161606472739 83236088608447742409709109)
                  ·
                    refine ⟨7803383307041975850910229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83236088608447742409709109 7803383307041975850910229)
                    ·
                      refine ⟨365783592517592618011417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7803383307041975850910229 365783592517592618011417)
                      ·
                        rfl

theorem cell23_712361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_712361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712361 prefixEnd_712361 := by exact prefixLift 712361
  have htrace : WordTrace (prefixWord ++ tailWord_712361) baseStart_712361 baseEnd_712361 := by
    simpa [prefixWord, tailWord_712361, baseEnd_712361] using wordTrace_append hprefix tailTrace_712361
  have hstable : (prefixWord ++ tailWord_712361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712361).length < 2 ^ (prefixWord ++ tailWord_712361).sum := by decide
  have hdescent : baseEnd_712361 < baseStart_712361 := by decide
  rcases family_descends (prefixWord ++ tailWord_712361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712428 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_712428 : Nat := 118140960795 + 712428 * 2 ^ 59
def prefixEnd_712428 : Nat := 4983230072969 + 3 ^ 40 * 712428 * 2
def baseEnd_712428 : Nat := 365817995721443855873609

theorem tailTrace_712428 : CollatzResearch.WordTrace tailWord_712428 prefixEnd_712428 365817995721443855873609 := by
  unfold tailWord_712428
  simp only [CollatzResearch.WordTrace]
  refine ⟨12992191931501251930312969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17322922575335002573750625 12992191931501251930312969)
  ·
    refine ⟨9744143948625938947734727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12992191931501251930312969 9744143948625938947734727)
    ·
      refine ⟨14616215922938908421602091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9744143948625938947734727 14616215922938908421602091)
      ·
        refine ⟨21924323884408362632403137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14616215922938908421602091 21924323884408362632403137)
        ·
          refine ⟨16443242913306271974302353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21924323884408362632403137 16443242913306271974302353)
          ·
            refine ⟨12332432184979703980726765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16443242913306271974302353 12332432184979703980726765)
            ·
              refine ⟨4624662069367388992772537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12332432184979703980726765 4624662069367388992772537)
              ·
                refine ⟨3468496552025541744579403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624662069367388992772537 3468496552025541744579403)
                ·
                  refine ⟨5202744828038312616869105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468496552025541744579403 5202744828038312616869105)
                  ·
                    refine ⟨3902058621028734462651829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5202744828038312616869105 3902058621028734462651829)
                    ·
                      refine ⟨365817995721443855873609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3902058621028734462651829 365817995721443855873609)
                      ·
                        rfl

theorem cell23_712428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_712428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712428 prefixEnd_712428 := by exact prefixLift 712428
  have htrace : WordTrace (prefixWord ++ tailWord_712428) baseStart_712428 baseEnd_712428 := by
    simpa [prefixWord, tailWord_712428, baseEnd_712428] using wordTrace_append hprefix tailTrace_712428
  have hstable : (prefixWord ++ tailWord_712428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712428).length < 2 ^ (prefixWord ++ tailWord_712428).sum := by decide
  have hdescent : baseEnd_712428 < baseStart_712428 := by decide
  rcases family_descends (prefixWord ++ tailWord_712428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712522 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_712522 : Nat := 118140960795 + 712522 * 2 ^ 59
def prefixEnd_712522 : Nat := 4983230072969 + 3 ^ 40 * 712522 * 2
def baseEnd_712522 : Nat := 365866262902966488098177

theorem tailTrace_712522 : CollatzResearch.WordTrace tailWord_712522 prefixEnd_712522 365866262902966488098177 := by
  unfold tailWord_712522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496953081165489478636955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17325208216441305276365213 6496953081165489478636955)
  ·
    refine ⟨9745429621748234217955433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6496953081165489478636955 9745429621748234217955433)
    ·
      refine ⟨7309072216311175663466575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9745429621748234217955433 7309072216311175663466575)
      ·
        refine ⟨10963608324466763495199863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7309072216311175663466575 10963608324466763495199863)
        ·
          refine ⟨16445412486700145242799795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10963608324466763495199863 16445412486700145242799795)
          ·
            refine ⟨24668118730050217864199693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16445412486700145242799795 24668118730050217864199693)
            ·
              refine ⟨9250544523768831699074885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24668118730050217864199693 9250544523768831699074885)
              ·
                refine ⟨1734477098206655943576541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9250544523768831699074885 1734477098206655943576541)
                ·
                  refine ⟨650428911827495978841203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1734477098206655943576541 650428911827495978841203)
                  ·
                    refine ⟨975643367741243968261805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 650428911827495978841203 975643367741243968261805)
                    ·
                      refine ⟨365866262902966488098177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 975643367741243968261805 365866262902966488098177)
                      ·
                        rfl

theorem cell23_712522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_712522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712522 prefixEnd_712522 := by exact prefixLift 712522
  have htrace : WordTrace (prefixWord ++ tailWord_712522) baseStart_712522 baseEnd_712522 := by
    simpa [prefixWord, tailWord_712522, baseEnd_712522] using wordTrace_append hprefix tailTrace_712522
  have hstable : (prefixWord ++ tailWord_712522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712522).length < 2 ^ (prefixWord ++ tailWord_712522).sum := by decide
  have hdescent : baseEnd_712522 < baseStart_712522 := by decide
  rcases family_descends (prefixWord ++ tailWord_712522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712575 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_712575 : Nat := 118140960795 + 712575 * 2 ^ 59
def prefixEnd_712575 : Nat := 4983230072969 + 3 ^ 40 * 712575 * 2
def baseEnd_712575 : Nat := 365893477377654780735433

theorem tailTrace_712575 : CollatzResearch.WordTrace tailWord_712575 prefixEnd_712575 365893477377654780735433 := by
  unfold tailWord_712575
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989745393469947966227179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17326496928979965310818119 25989745393469947966227179)
  ·
    refine ⟨38984618090204921949340769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25989745393469947966227179 38984618090204921949340769)
    ·
      refine ⟨29238463567653691462005577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38984618090204921949340769 29238463567653691462005577)
      ·
        refine ⟨21928847675740268596504183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29238463567653691462005577 21928847675740268596504183)
        ·
          refine ⟨32893271513610402894756275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21928847675740268596504183 32893271513610402894756275)
          ·
            refine ⟨49339907270415604342134413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32893271513610402894756275 49339907270415604342134413)
            ·
              refine ⟨18502465226405851628300405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49339907270415604342134413 18502465226405851628300405)
              ·
                refine ⟨1734606114975548590153163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18502465226405851628300405 1734606114975548590153163)
                ·
                  refine ⟨2601909172463322885229745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734606114975548590153163 2601909172463322885229745)
                  ·
                    refine ⟨1951431879347492163922309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2601909172463322885229745 1951431879347492163922309)
                    ·
                      refine ⟨365893477377654780735433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1951431879347492163922309 365893477377654780735433)
                      ·
                        rfl

theorem cell23_712575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_712575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712575 prefixEnd_712575 := by exact prefixLift 712575
  have htrace : WordTrace (prefixWord ++ tailWord_712575) baseStart_712575 baseEnd_712575 := by
    simpa [prefixWord, tailWord_712575, baseEnd_712575] using wordTrace_append hprefix tailTrace_712575
  have hstable : (prefixWord ++ tailWord_712575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712575).length < 2 ^ (prefixWord ++ tailWord_712575).sum := by decide
  have hdescent : baseEnd_712575 < baseStart_712575 := by decide
  rcases family_descends (prefixWord ++ tailWord_712575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712579 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 4]
def baseStart_712579 : Nat := 118140960795 + 712579 * 2 ^ 59
def prefixEnd_712579 : Nat := 4983230072969 + 3 ^ 40 * 712579 * 2
def baseEnd_712579 : Nat := 365895531300272765085415

theorem tailTrace_712579 : CollatzResearch.WordTrace tailWord_712579 prefixEnd_712579 365895531300272765085415 := by
  unfold tailWord_712579
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989891285455456649372791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17326594190303637766248527 25989891285455456649372791)
  ·
    refine ⟨38984836928183184974059187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25989891285455456649372791 38984836928183184974059187)
    ·
      refine ⟨58477255392274777461088781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38984836928183184974059187 58477255392274777461088781)
      ·
        refine ⟨21928970772103041547908293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58477255392274777461088781 21928970772103041547908293)
        ·
          refine ⟨4111682019769320290232805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21928970772103041547908293 4111682019769320290232805)
          ·
            refine ⟨770940378706747554418651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4111682019769320290232805 770940378706747554418651)
            ·
              refine ⟨1156410568060121331627977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770940378706747554418651 1156410568060121331627977)
              ·
                refine ⟨867307926045090998720983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156410568060121331627977 867307926045090998720983)
                ·
                  refine ⟨1300961889067636498081475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867307926045090998720983 1300961889067636498081475)
                  ·
                    refine ⟨1951442833601454747122213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300961889067636498081475 1951442833601454747122213)
                    ·
                      refine ⟨365895531300272765085415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1951442833601454747122213 365895531300272765085415)
                      ·
                        rfl

theorem cell23_712579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_712579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712579 prefixEnd_712579 := by exact prefixLift 712579
  have htrace : WordTrace (prefixWord ++ tailWord_712579) baseStart_712579 baseEnd_712579 := by
    simpa [prefixWord, tailWord_712579, baseEnd_712579] using wordTrace_append hprefix tailTrace_712579
  have hstable : (prefixWord ++ tailWord_712579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712579).length < 2 ^ (prefixWord ++ tailWord_712579).sum := by decide
  have hdescent : baseEnd_712579 < baseStart_712579 := by decide
  rcases family_descends (prefixWord ++ tailWord_712579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712596 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_712596 : Nat := 118140960795 + 712596 * 2 ^ 59
def prefixEnd_712596 : Nat := 4983230072969 + 3 ^ 40 * 712596 * 2
def baseEnd_712596 : Nat := 365904260471399198572837

theorem tailTrace_712596 : CollatzResearch.WordTrace tailWord_712596 prefixEnd_712596 365904260471399198572837 := by
  unfold tailWord_712596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995255663196934276370821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17327007550929245701827761 12995255663196934276370821)
  ·
    refine ⟨2436610436849425176819529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12995255663196934276370821 2436610436849425176819529)
    ·
      refine ⟨1827457827637068882614647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2436610436849425176819529 1827457827637068882614647)
      ·
        refine ⟨2741186741455603323921971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827457827637068882614647 2741186741455603323921971)
        ·
          refine ⟨4111780112183404985882957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741186741455603323921971 4111780112183404985882957)
          ·
            refine ⟨1541917542068776869706109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4111780112183404985882957 1541917542068776869706109)
            ·
              refine ⟨578219078275791326139791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1541917542068776869706109 578219078275791326139791)
              ·
                refine ⟨867328617413686989209687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578219078275791326139791 867328617413686989209687)
                ·
                  refine ⟨1300992926120530483814531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867328617413686989209687 1300992926120530483814531)
                  ·
                    refine ⟨1951489389180795725721797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1300992926120530483814531 1951489389180795725721797)
                    ·
                      refine ⟨365904260471399198572837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1951489389180795725721797 365904260471399198572837)
                      ·
                        rfl

theorem cell23_712596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_712596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712596 prefixEnd_712596 := by exact prefixLift 712596
  have htrace : WordTrace (prefixWord ++ tailWord_712596) baseStart_712596 baseEnd_712596 := by
    simpa [prefixWord, tailWord_712596, baseEnd_712596] using wordTrace_append hprefix tailTrace_712596
  have hstable : (prefixWord ++ tailWord_712596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712596).length < 2 ^ (prefixWord ++ tailWord_712596).sum := by decide
  have hdescent : baseEnd_712596 < baseStart_712596 := by decide
  rcases family_descends (prefixWord ++ tailWord_712596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712629 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_712629 : Nat := 118140960795 + 712629 * 2 ^ 59
def prefixEnd_712629 : Nat := 4983230072969 + 3 ^ 40 * 712629 * 2
def baseEnd_712629 : Nat := 365921205332997569460185

theorem tailTrace_712629 : CollatzResearch.WordTrace tailWord_712629 prefixEnd_712629 365921205332997569460185 := by
  unfold tailWord_712629
  simp only [CollatzResearch.WordTrace]
  refine ⟨25991714935274315188692941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17327809956849543459128627 25991714935274315188692941)
  ·
    refine ⟨9746893100727868195759853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25991714935274315188692941 9746893100727868195759853)
    ·
      refine ⟨3655084912772950573409945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9746893100727868195759853 3655084912772950573409945)
      ·
        refine ⟨2741313684579712930057459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3655084912772950573409945 2741313684579712930057459)
        ·
          refine ⟨4111970526869569395086189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2741313684579712930057459 4111970526869569395086189)
          ·
            refine ⟨1541988947576088523157321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4111970526869569395086189 1541988947576088523157321)
            ·
              refine ⟨1156491710682066392367991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1541988947576088523157321 1156491710682066392367991)
              ·
                refine ⟨1734737566023099588551987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156491710682066392367991 1734737566023099588551987)
                ·
                  refine ⟨2602106349034649382827981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734737566023099588551987 2602106349034649382827981)
                  ·
                    refine ⟨975789880887993518560493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2602106349034649382827981 975789880887993518560493)
                    ·
                      refine ⟨365921205332997569460185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 975789880887993518560493 365921205332997569460185)
                      ·
                        rfl

theorem cell23_712629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_712629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712629 prefixEnd_712629 := by exact prefixLift 712629
  have htrace : WordTrace (prefixWord ++ tailWord_712629) baseStart_712629 baseEnd_712629 := by
    simpa [prefixWord, tailWord_712629, baseEnd_712629] using wordTrace_append hprefix tailTrace_712629
  have hstable : (prefixWord ++ tailWord_712629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712629).length < 2 ^ (prefixWord ++ tailWord_712629).sum := by decide
  have hdescent : baseEnd_712629 < baseStart_712629 := by decide
  rcases family_descends (prefixWord ++ tailWord_712629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712639 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 1, 3, 2]
def baseStart_712639 : Nat := 118140960795 + 712639 * 2 ^ 59
def prefixEnd_712639 : Nat := 4983230072969 + 3 ^ 40 * 712639 * 2
def baseEnd_712639 : Nat := 365926340139542530335139

theorem tailTrace_712639 : CollatzResearch.WordTrace tailWord_712639 prefixEnd_712639 365926340139542530335139 := by
  unfold tailWord_712639
  simp only [CollatzResearch.WordTrace]
  refine ⟨25992079665238086896556971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17328053110158724597704647 25992079665238086896556971)
  ·
    refine ⟨38988119497857130344835457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25992079665238086896556971 38988119497857130344835457)
    ·
      refine ⟨29241089623392847758626593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38988119497857130344835457 29241089623392847758626593)
      ·
        refine ⟨21930817217544635818969945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29241089623392847758626593 21930817217544635818969945)
        ·
          refine ⟨16448112913158476864227459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21930817217544635818969945 16448112913158476864227459)
          ·
            refine ⟨24672169369737715296341189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16448112913158476864227459 24672169369737715296341189)
            ·
              refine ⟨4626031756825821618063973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24672169369737715296341189 4626031756825821618063973)
              ·
                refine ⟨867380954404841553386995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4626031756825821618063973 867380954404841553386995)
                ·
                  refine ⟨1301071431607262330080493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867380954404841553386995 1301071431607262330080493)
                  ·
                    refine ⟨487901786852723373780185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1301071431607262330080493 487901786852723373780185)
                    ·
                      refine ⟨365926340139542530335139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487901786852723373780185 365926340139542530335139)
                      ·
                        rfl

theorem cell23_712639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_712639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712639 prefixEnd_712639 := by exact prefixLift 712639
  have htrace : WordTrace (prefixWord ++ tailWord_712639) baseStart_712639 baseEnd_712639 := by
    simpa [prefixWord, tailWord_712639, baseEnd_712639] using wordTrace_append hprefix tailTrace_712639
  have hstable : (prefixWord ++ tailWord_712639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712639).length < 2 ^ (prefixWord ++ tailWord_712639).sum := by decide
  have hdescent : baseEnd_712639 < baseStart_712639 := by decide
  rcases family_descends (prefixWord ++ tailWord_712639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712655 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_712655 : Nat := 118140960795 + 712655 * 2 ^ 59
def prefixEnd_712655 : Nat := 4983230072969 + 3 ^ 40 * 712655 * 2
def baseEnd_712655 : Nat := 365934555830014467735065

theorem tailTrace_712655 : CollatzResearch.WordTrace tailWord_712655 prefixEnd_712655 365934555830014467735065 := by
  unfold tailWord_712655
  simp only [CollatzResearch.WordTrace]
  refine ⟨25992663233180121629139419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17328442155453414419426279 25992663233180121629139419)
  ·
    refine ⟨38988994849770182443709129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25992663233180121629139419 38988994849770182443709129)
    ·
      refine ⟨29241746137327636832781847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38988994849770182443709129 29241746137327636832781847)
      ·
        refine ⟨43862619205991455249172771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29241746137327636832781847 43862619205991455249172771)
        ·
          refine ⟨65793928808987182873759157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43862619205991455249172771 65793928808987182873759157)
          ·
            refine ⟨6168180825842548394414921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65793928808987182873759157 6168180825842548394414921)
            ·
              refine ⟨4626135619381911295811191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6168180825842548394414921 4626135619381911295811191)
              ·
                refine ⟨6939203429072866943716787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626135619381911295811191 6939203429072866943716787)
                ·
                  refine ⟨10408805143609300415575181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939203429072866943716787 10408805143609300415575181)
                  ·
                    refine ⟨3903301928853487655840693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10408805143609300415575181 3903301928853487655840693)
                    ·
                      refine ⟨365934555830014467735065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3903301928853487655840693 365934555830014467735065)
                      ·
                        rfl

theorem cell23_712655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_712655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712655 prefixEnd_712655 := by exact prefixLift 712655
  have htrace : WordTrace (prefixWord ++ tailWord_712655) baseStart_712655 baseEnd_712655 := by
    simpa [prefixWord, tailWord_712655, baseEnd_712655] using wordTrace_append hprefix tailTrace_712655
  have hstable : (prefixWord ++ tailWord_712655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712655).length < 2 ^ (prefixWord ++ tailWord_712655).sum := by decide
  have hdescent : baseEnd_712655 < baseStart_712655 := by decide
  rcases family_descends (prefixWord ++ tailWord_712655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712656 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 1, 3, 2]
def baseStart_712656 : Nat := 118140960795 + 712656 * 2 ^ 59
def prefixEnd_712656 : Nat := 4983230072969 + 3 ^ 40 * 712656 * 2
def baseEnd_712656 : Nat := 365935069310668963822561

theorem tailTrace_712656 : CollatzResearch.WordTrace tailWord_712656 prefixEnd_712656 365935069310668963822561 := by
  unfold tailWord_712656
  simp only [CollatzResearch.WordTrace]
  refine ⟨12996349853088249399962911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17328466470784332533283881 12996349853088249399962911)
  ·
    refine ⟨19494524779632374099944367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12996349853088249399962911 19494524779632374099944367)
    ·
      refine ⟨29241787169448561149916551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19494524779632374099944367 29241787169448561149916551)
      ·
        refine ⟨43862680754172841724874827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29241787169448561149916551 43862680754172841724874827)
        ·
          refine ⟨65794021131259262587312241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43862680754172841724874827 65794021131259262587312241)
          ·
            refine ⟨49345515848444446940484181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65794021131259262587312241 49345515848444446940484181)
            ·
              refine ⟨578267763848958362583799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 49345515848444446940484181 578267763848958362583799)
              ·
                refine ⟨867401645773437543875699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578267763848958362583799 867401645773437543875699)
                ·
                  refine ⟨1301102468660156315813549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867401645773437543875699 1301102468660156315813549)
                  ·
                    refine ⟨487913425747558618430081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1301102468660156315813549 487913425747558618430081)
                    ·
                      refine ⟨365935069310668963822561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487913425747558618430081 365935069310668963822561)
                      ·
                        rfl

theorem cell23_712656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 3, 2].length) (baseStart_712656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712656 prefixEnd_712656 := by exact prefixLift 712656
  have htrace : WordTrace (prefixWord ++ tailWord_712656) baseStart_712656 baseEnd_712656 := by
    simpa [prefixWord, tailWord_712656, baseEnd_712656] using wordTrace_append hprefix tailTrace_712656
  have hstable : (prefixWord ++ tailWord_712656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712656).length < 2 ^ (prefixWord ++ tailWord_712656).sum := by decide
  have hdescent : baseEnd_712656 < baseStart_712656 := by decide
  rcases family_descends (prefixWord ++ tailWord_712656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712682 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_712682 : Nat := 118140960795 + 712682 * 2 ^ 59
def prefixEnd_712682 : Nat := 4983230072969 + 3 ^ 40 * 712682 * 2
def baseEnd_712682 : Nat := 365948419807685862097441

theorem tailTrace_712682 : CollatzResearch.WordTrace tailWord_712682 prefixEnd_712682 365948419807685862097441 := by
  unfold tailWord_712682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6498412001020576310093075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17329098669388203493581533 6498412001020576310093075)
  ·
    refine ⟨9747618001530864465139613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6498412001020576310093075 9747618001530864465139613)
    ·
      refine ⟨3655356750574074174427355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9747618001530864465139613 3655356750574074174427355)
      ·
        refine ⟨5483035125861111261641033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655356750574074174427355 5483035125861111261641033)
        ·
          refine ⟨4112276344395833446230775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5483035125861111261641033 4112276344395833446230775)
          ·
            refine ⟨6168414516593750169346163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112276344395833446230775 6168414516593750169346163)
            ·
              refine ⟨9252621774890625254019245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168414516593750169346163 9252621774890625254019245)
              ·
                refine ⟨3469733165583984470257217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9252621774890625254019245 3469733165583984470257217)
                ·
                  refine ⟨2602299874187988352692913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3469733165583984470257217 2602299874187988352692913)
                  ·
                    refine ⟨1951724905640991264519685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2602299874187988352692913 1951724905640991264519685)
                    ·
                      refine ⟨365948419807685862097441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1951724905640991264519685 365948419807685862097441)
                      ·
                        rfl

theorem cell23_712682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_712682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712682 prefixEnd_712682 := by exact prefixLift 712682
  have htrace : WordTrace (prefixWord ++ tailWord_712682) baseStart_712682 baseEnd_712682 := by
    simpa [prefixWord, tailWord_712682, baseEnd_712682] using wordTrace_append hprefix tailTrace_712682
  have hstable : (prefixWord ++ tailWord_712682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712682).length < 2 ^ (prefixWord ++ tailWord_712682).sum := by decide
  have hdescent : baseEnd_712682 < baseStart_712682 := by decide
  rcases family_descends (prefixWord ++ tailWord_712682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712686 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_712686 : Nat := 118140960795 + 712686 * 2 ^ 59
def prefixEnd_712686 : Nat := 4983230072969 + 3 ^ 40 * 712686 * 2
def baseEnd_712686 : Nat := 365950473730303846447423

theorem tailTrace_712686 : CollatzResearch.WordTrace tailWord_712686 prefixEnd_712686 365950473730303846447423 := by
  unfold tailWord_712686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3249224237008476740439739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17329195930711875949011941 3249224237008476740439739)
  ·
    refine ⟨4873836355512715110659609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3249224237008476740439739 4873836355512715110659609)
    ·
      refine ⟨3655377266634536332994707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4873836355512715110659609 3655377266634536332994707)
      ·
        refine ⟨5483065899951804499492061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655377266634536332994707 5483065899951804499492061)
        ·
          refine ⟨2056149712481926687309523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5483065899951804499492061 2056149712481926687309523)
          ·
            refine ⟨3084224568722890030964285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056149712481926687309523 3084224568722890030964285)
            ·
              refine ⟨1156584213271083761611607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3084224568722890030964285 1156584213271083761611607)
              ·
                refine ⟨1734876319906625642417411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156584213271083761611607 1734876319906625642417411)
                ·
                  refine ⟨2602314479859938463626117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734876319906625642417411 2602314479859938463626117)
                  ·
                    refine ⟨487933964973738461929897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2602314479859938463626117 487933964973738461929897)
                    ·
                      refine ⟨365950473730303846447423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487933964973738461929897 365950473730303846447423)
                      ·
                        rfl

theorem cell23_712686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_712686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712686 prefixEnd_712686 := by exact prefixLift 712686
  have htrace : WordTrace (prefixWord ++ tailWord_712686) baseStart_712686 baseEnd_712686 := by
    simpa [prefixWord, tailWord_712686, baseEnd_712686] using wordTrace_append hprefix tailTrace_712686
  have hstable : (prefixWord ++ tailWord_712686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712686).length < 2 ^ (prefixWord ++ tailWord_712686).sum := by decide
  have hdescent : baseEnd_712686 < baseStart_712686 := by decide
  rcases family_descends (prefixWord ++ tailWord_712686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712709 : List Nat := [1, 3, 1, 1, 2, 4, 3, 3, 5]
def baseStart_712709 : Nat := 118140960795 + 712709 * 2 ^ 59
def prefixEnd_712709 : Nat := 4983230072969 + 3 ^ 40 * 712709 * 2
def baseEnd_712709 : Nat := 40662475976150806273313

theorem tailTrace_712709 : CollatzResearch.WordTrace tailWord_712709 prefixEnd_712709 40662475976150806273313 := by
  unfold tailWord_712709
  simp only [CollatzResearch.WordTrace]
  refine ⟨25994632774984488851605181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17329755183322992567736787 25994632774984488851605181)
  ·
    refine ⟨9747987290619183319351943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25994632774984488851605181 9747987290619183319351943)
    ·
      refine ⟨14621980935928774979027915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9747987290619183319351943 14621980935928774979027915)
      ·
        refine ⟨21932971403893162468541873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14621980935928774979027915 21932971403893162468541873)
        ·
          refine ⟨16449728552919871851406405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21932971403893162468541873 16449728552919871851406405)
          ·
            refine ⟨3084324103672475972138701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16449728552919871851406405 3084324103672475972138701)
            ·
              refine ⟨1156621538877178489552013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3084324103672475972138701 1156621538877178489552013)
              ·
                refine ⟨433733077078941933582005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1156621538877178489552013 433733077078941933582005)
                ·
                  refine ⟨40662475976150806273313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 433733077078941933582005 40662475976150806273313)
                  ·
                    rfl

theorem cell23_712709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_712709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712709 prefixEnd_712709 := by exact prefixLift 712709
  have htrace : WordTrace (prefixWord ++ tailWord_712709) baseStart_712709 baseEnd_712709 := by
    simpa [prefixWord, tailWord_712709, baseEnd_712709] using wordTrace_append hprefix tailTrace_712709
  have hstable : (prefixWord ++ tailWord_712709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712709).length < 2 ^ (prefixWord ++ tailWord_712709).sum := by decide
  have hdescent : baseEnd_712709 < baseStart_712709 := by decide
  rcases family_descends (prefixWord ++ tailWord_712709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712732 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_712732 : Nat := 118140960795 + 712732 * 2 ^ 59
def prefixEnd_712732 : Nat := 4983230072969 + 3 ^ 40 * 712732 * 2
def baseEnd_712732 : Nat := 365974093840410666472211

theorem tailTrace_712732 : CollatzResearch.WordTrace tailWord_712732 prefixEnd_712732 365974093840410666472211 := by
  unfold tailWord_712732
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997735826950581889846225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17330314435934109186461633 12997735826950581889846225)
  ·
    refine ⟨9748301870212936417384669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12997735826950581889846225 9748301870212936417384669)
    ·
      refine ⟨3655613201329851156519251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9748301870212936417384669 3655613201329851156519251)
      ·
        refine ⟨5483419801994776734778877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655613201329851156519251 5483419801994776734778877)
        ·
          refine ⟨2056282425748041275542079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5483419801994776734778877 2056282425748041275542079)
          ·
            refine ⟨3084423638622061913313119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056282425748041275542079 3084423638622061913313119)
            ·
              refine ⟨4626635457933092869969679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3084423638622061913313119 4626635457933092869969679)
              ·
                refine ⟨6939953186899639304954519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626635457933092869969679 6939953186899639304954519)
                ·
                  refine ⟨10409929780349458957431779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939953186899639304954519 10409929780349458957431779)
                  ·
                    refine ⟨15614894670524188436147669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10409929780349458957431779 15614894670524188436147669)
                    ·
                      refine ⟨365974093840410666472211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15614894670524188436147669 365974093840410666472211)
                      ·
                        rfl

theorem cell23_712732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_712732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712732 prefixEnd_712732 := by exact prefixLift 712732
  have htrace : WordTrace (prefixWord ++ tailWord_712732) baseStart_712732 baseEnd_712732 := by
    simpa [prefixWord, tailWord_712732, baseEnd_712732] using wordTrace_append hprefix tailTrace_712732
  have hstable : (prefixWord ++ tailWord_712732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712732).length < 2 ^ (prefixWord ++ tailWord_712732).sum := by decide
  have hdescent : baseEnd_712732 < baseStart_712732 := by decide
  rcases family_descends (prefixWord ++ tailWord_712732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712737 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_712737 : Nat := 118140960795 + 712737 * 2 ^ 59
def prefixEnd_712737 : Nat := 4983230072969 + 3 ^ 40 * 712737 * 2
def baseEnd_712737 : Nat := 365976661243683146909689

theorem tailTrace_712737 : CollatzResearch.WordTrace tailWord_712737 prefixEnd_712737 365976661243683146909689 := by
  unfold tailWord_712737
  simp only [CollatzResearch.WordTrace]
  refine ⟨25995654018883049633624465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17330436012588699755749643 25995654018883049633624465)
  ·
    refine ⟨19496740514162287225218349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25995654018883049633624465 19496740514162287225218349)
    ·
      refine ⟨7311277692810857709456881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19496740514162287225218349 7311277692810857709456881)
      ·
        refine ⟨5483458269608143282092661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7311277692810857709456881 5483458269608143282092661)
        ·
          refine ⟨514074212775763432696187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5483458269608143282092661 514074212775763432696187)
          ·
            refine ⟨771111319163645149044281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514074212775763432696187 771111319163645149044281)
            ·
              refine ⟨578333489372733861783211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771111319163645149044281 578333489372733861783211)
              ·
                refine ⟨867500234059100792674817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578333489372733861783211 867500234059100792674817)
                ·
                  refine ⟨650625175544325594506113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 867500234059100792674817 650625175544325594506113)
                  ·
                    refine ⟨487968881658244195879585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 650625175544325594506113 487968881658244195879585)
                    ·
                      refine ⟨365976661243683146909689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 487968881658244195879585 365976661243683146909689)
                      ·
                        rfl

theorem cell23_712737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_712737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712737 prefixEnd_712737 := by exact prefixLift 712737
  have htrace : WordTrace (prefixWord ++ tailWord_712737) baseStart_712737 baseEnd_712737 := by
    simpa [prefixWord, tailWord_712737, baseEnd_712737] using wordTrace_append hprefix tailTrace_712737
  have hstable : (prefixWord ++ tailWord_712737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712737).length < 2 ^ (prefixWord ++ tailWord_712737).sum := by decide
  have hdescent : baseEnd_712737 < baseStart_712737 := by decide
  rcases family_descends (prefixWord ++ tailWord_712737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712745 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_712745 : Nat := 118140960795 + 712745 * 2 ^ 59
def prefixEnd_712745 : Nat := 4983230072969 + 3 ^ 40 * 712745 * 2
def baseEnd_712745 : Nat := 365980769088919115609651

theorem tailTrace_712745 : CollatzResearch.WordTrace tailWord_712745 prefixEnd_712745 365980769088919115609651 := by
  unfold tailWord_712745
  simp only [CollatzResearch.WordTrace]
  refine ⟨25995945802854066999915689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17330630535236044666610459 25995945802854066999915689)
  ·
    refine ⟨19496959352140550249936767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25995945802854066999915689 19496959352140550249936767)
    ·
      refine ⟨29245439028210825374905151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19496959352140550249936767 29245439028210825374905151)
      ·
        refine ⟨43868158542316238062357727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29245439028210825374905151 43868158542316238062357727)
        ·
          refine ⟨65802237813474357093536591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43868158542316238062357727 65802237813474357093536591)
          ·
            refine ⟨98703356720211535640304887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65802237813474357093536591 98703356720211535640304887)
            ·
              refine ⟨148055035080317303460457331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98703356720211535640304887 148055035080317303460457331)
              ·
                refine ⟨222082552620475955190685997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148055035080317303460457331 222082552620475955190685997)
                ·
                  refine ⟨83280957232678483196507249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222082552620475955190685997 83280957232678483196507249)
                  ·
                    refine ⟨62460717924508862397380437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83280957232678483196507249 62460717924508862397380437)
                    ·
                      refine ⟨365980769088919115609651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 62460717924508862397380437 365980769088919115609651)
                      ·
                        rfl

theorem cell23_712745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_712745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712745 prefixEnd_712745 := by exact prefixLift 712745
  have htrace : WordTrace (prefixWord ++ tailWord_712745) baseStart_712745 baseEnd_712745 := by
    simpa [prefixWord, tailWord_712745, baseEnd_712745] using wordTrace_append hprefix tailTrace_712745
  have hstable : (prefixWord ++ tailWord_712745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712745).length < 2 ^ (prefixWord ++ tailWord_712745).sum := by decide
  have hdescent : baseEnd_712745 < baseStart_712745 := by decide
  rcases family_descends (prefixWord ++ tailWord_712745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712833 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 6]
def baseStart_712833 : Nat := 118140960795 + 712833 * 2 ^ 59
def prefixEnd_712833 : Nat := 4983230072969 + 3 ^ 40 * 712833 * 2
def baseEnd_712833 : Nat := 40669550598501641256583

theorem tailTrace_712833 : CollatzResearch.WordTrace tailWord_712833 prefixEnd_712833 40669550598501641256583 := by
  unfold tailWord_712833
  simp only [CollatzResearch.WordTrace]
  refine ⟨25999155426535258029119153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17332770284356838686079435 25999155426535258029119153)
  ·
    refine ⟨19499366569901443521839365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25999155426535258029119153 19499366569901443521839365)
    ·
      refine ⟨3656131231856520660344881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19499366569901443521839365 3656131231856520660344881)
      ·
        refine ⟨2742098423892390495258661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3656131231856520660344881 2742098423892390495258661)
        ·
          refine ⟨514143454479823217860999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2742098423892390495258661 514143454479823217860999)
          ·
            refine ⟨771215181719734826791499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514143454479823217860999 771215181719734826791499)
            ·
              refine ⟨1156822772579602240187249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771215181719734826791499 1156822772579602240187249)
              ·
                refine ⟨867617079434701680140437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156822772579602240187249 867617079434701680140437)
                ·
                  refine ⟨40669550598501641256583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 867617079434701680140437 40669550598501641256583)
                  ·
                    rfl

theorem cell23_712833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 6].length) (baseStart_712833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712833 prefixEnd_712833 := by exact prefixLift 712833
  have htrace : WordTrace (prefixWord ++ tailWord_712833) baseStart_712833 baseEnd_712833 := by
    simpa [prefixWord, tailWord_712833, baseEnd_712833] using wordTrace_append hprefix tailTrace_712833
  have hstable : (prefixWord ++ tailWord_712833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712833).length < 2 ^ (prefixWord ++ tailWord_712833).sum := by decide
  have hdescent : baseEnd_712833 < baseStart_712833 := by decide
  rcases family_descends (prefixWord ++ tailWord_712833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712836 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_712836 : Nat := 118140960795 + 712836 * 2 ^ 59
def prefixEnd_712836 : Nat := 4983230072969 + 3 ^ 40 * 712836 * 2
def baseEnd_712836 : Nat := 366027495828478259571733

theorem tailTrace_712836 : CollatzResearch.WordTrace tailWord_712836 prefixEnd_712836 366027495828478259571733 := by
  unfold tailWord_712836
  simp only [CollatzResearch.WordTrace]
  refine ⟨12999632422762194770739181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17332843230349593027652241 12999632422762194770739181)
  ·
    refine ⟨4874862158535823039027193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12999632422762194770739181 4874862158535823039027193)
    ·
      refine ⟨3656146618901867279270395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4874862158535823039027193 3656146618901867279270395)
      ·
        refine ⟨5484219928352800918905593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3656146618901867279270395 5484219928352800918905593)
        ·
          refine ⟨4113164946264600689179195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5484219928352800918905593 4113164946264600689179195)
          ·
            refine ⟨6169747419396901033768793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113164946264600689179195 6169747419396901033768793)
            ·
              refine ⟨4627310564547675775326595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6169747419396901033768793 4627310564547675775326595)
              ·
                refine ⟨6940965846821513662989893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4627310564547675775326595 6940965846821513662989893)
                ·
                  refine ⟨1301431096279033811810605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6940965846821513662989893 1301431096279033811810605)
                  ·
                    refine ⟨488036661104637679428977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1301431096279033811810605 488036661104637679428977)
                    ·
                      refine ⟨366027495828478259571733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488036661104637679428977 366027495828478259571733)
                      ·
                        rfl

theorem cell23_712836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_712836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712836 prefixEnd_712836 := by exact prefixLift 712836
  have htrace : WordTrace (prefixWord ++ tailWord_712836) baseStart_712836 baseEnd_712836 := by
    simpa [prefixWord, tailWord_712836, baseEnd_712836] using wordTrace_append hprefix tailTrace_712836
  have hstable : (prefixWord ++ tailWord_712836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712836).length < 2 ^ (prefixWord ++ tailWord_712836).sum := by decide
  have hdescent : baseEnd_712836 < baseStart_712836 := by decide
  rcases family_descends (prefixWord ++ tailWord_712836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712877 : List Nat := [1, 5, 2, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_712877 : Nat := 118140960795 + 712877 * 2 ^ 59
def prefixEnd_712877 : Nat := 4983230072969 + 3 ^ 40 * 712877 * 2
def baseEnd_712877 : Nat := 366048548535312599159045

theorem tailTrace_712877 : CollatzResearch.WordTrace tailWord_712877 prefixEnd_712877 366048548535312599159045 := by
  unfold tailWord_712877
  simp only [CollatzResearch.WordTrace]
  refine ⟨26000760238375853543720885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17333840158917235695813923 26000760238375853543720885)
  ·
    refine ⟨2437571272347736269723833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26000760238375853543720885 2437571272347736269723833)
    ·
      refine ⟨1828178454260802202292875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2437571272347736269723833 1828178454260802202292875)
      ·
        refine ⟨2742267681391203303439313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828178454260802202292875 2742267681391203303439313)
        ·
          refine ⟨2056700761043402477579485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742267681391203303439313 2056700761043402477579485)
          ·
            refine ⟨771262785391275929092307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2056700761043402477579485 771262785391275929092307)
            ·
              refine ⟨1156894178086913893638461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771262785391275929092307 1156894178086913893638461)
              ·
                refine ⟨433835316782592710114423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1156894178086913893638461 433835316782592710114423)
                ·
                  refine ⟨650752975173889065171635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433835316782592710114423 650752975173889065171635)
                  ·
                    refine ⟨976129462760833597757453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 650752975173889065171635 976129462760833597757453)
                    ·
                      refine ⟨366048548535312599159045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 976129462760833597757453 366048548535312599159045)
                      ·
                        rfl

theorem cell23_712877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_712877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712877 prefixEnd_712877 := by exact prefixLift 712877
  have htrace : WordTrace (prefixWord ++ tailWord_712877) baseStart_712877 baseEnd_712877 := by
    simpa [prefixWord, tailWord_712877, baseEnd_712877] using wordTrace_append hprefix tailTrace_712877
  have hstable : (prefixWord ++ tailWord_712877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712877).length < 2 ^ (prefixWord ++ tailWord_712877).sum := by decide
  have hdescent : baseEnd_712877 < baseStart_712877 := by decide
  rcases family_descends (prefixWord ++ tailWord_712877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712900 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_712900 : Nat := 118140960795 + 712900 * 2 ^ 59
def prefixEnd_712900 : Nat := 4983230072969 + 3 ^ 40 * 712900 * 2
def baseEnd_712900 : Nat := 366060358590366009171439

theorem tailTrace_712900 : CollatzResearch.WordTrace tailWord_712900 prefixEnd_712900 366060358590366009171439 := by
  unfold tailWord_712900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13000799558646264235904077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17334399411528352314538769 13000799558646264235904077)
  ·
    refine ⟨4875299834492349088464029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13000799558646264235904077 4875299834492349088464029)
    ·
      refine ⟨1828237437934630908174011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4875299834492349088464029 1828237437934630908174011)
      ·
        refine ⟨2742356156901946362261017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828237437934630908174011 2742356156901946362261017)
        ·
          refine ⟨2056767117676459771695763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742356156901946362261017 2056767117676459771695763)
          ·
            refine ⟨3085150676514689657543645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056767117676459771695763 3085150676514689657543645)
            ·
              refine ⟨1156931503693008621578867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3085150676514689657543645 1156931503693008621578867)
              ·
                refine ⟨1735397255539512932368301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156931503693008621578867 1735397255539512932368301)
                ·
                  refine ⟨650773970827317349638113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1735397255539512932368301 650773970827317349638113)
                  ·
                    refine ⟨488080478120488012228585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 650773970827317349638113 488080478120488012228585)
                    ·
                      refine ⟨366060358590366009171439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488080478120488012228585 366060358590366009171439)
                      ·
                        rfl

theorem cell23_712900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_712900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712900 prefixEnd_712900 := by exact prefixLift 712900
  have htrace : WordTrace (prefixWord ++ tailWord_712900) baseStart_712900 baseEnd_712900 := by
    simpa [prefixWord, tailWord_712900, baseEnd_712900] using wordTrace_append hprefix tailTrace_712900
  have hstable : (prefixWord ++ tailWord_712900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712900).length < 2 ^ (prefixWord ++ tailWord_712900).sum := by decide
  have hdescent : baseEnd_712900 < baseStart_712900 := by decide
  rcases family_descends (prefixWord ++ tailWord_712900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712910 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_712910 : Nat := 118140960795 + 712910 * 2 ^ 59
def prefixEnd_712910 : Nat := 4983230072969 + 3 ^ 40 * 712910 * 2
def baseEnd_712910 : Nat := 122021831132303656682131

theorem tailTrace_712910 : CollatzResearch.WordTrace tailWord_712910 prefixEnd_712910 122021831132303656682131 := by
  unfold tailWord_712910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250245480907037522459023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17334642564837533453114789 3250245480907037522459023)
  ·
    refine ⟨4875368221360556283688535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3250245480907037522459023 4875368221360556283688535)
    ·
      refine ⟨7313052332040834425532803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4875368221360556283688535 7313052332040834425532803)
      ·
        refine ⟨10969578498061251638299205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313052332040834425532803 10969578498061251638299205)
        ·
          refine ⟨2056795968386484682181101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10969578498061251638299205 2056795968386484682181101)
          ·
            refine ⟨771298488144931755817913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2056795968386484682181101 771298488144931755817913)
            ·
              refine ⟨578473866108698816863435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771298488144931755817913 578473866108698816863435)
              ·
                refine ⟨867710799163048225295153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578473866108698816863435 867710799163048225295153)
                ·
                  refine ⟨650783099372286168971365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 867710799163048225295153 650783099372286168971365)
                  ·
                    refine ⟨122021831132303656682131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 650783099372286168971365 122021831132303656682131)
                    ·
                      rfl

theorem cell23_712910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_712910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712910 prefixEnd_712910 := by exact prefixLift 712910
  have htrace : WordTrace (prefixWord ++ tailWord_712910) baseStart_712910 baseEnd_712910 := by
    simpa [prefixWord, tailWord_712910, baseEnd_712910] using wordTrace_append hprefix tailTrace_712910
  have hstable : (prefixWord ++ tailWord_712910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712910).length < 2 ^ (prefixWord ++ tailWord_712910).sum := by decide
  have hdescent : baseEnd_712910 < baseStart_712910 := by decide
  rcases family_descends (prefixWord ++ tailWord_712910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712959 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 3]
def baseStart_712959 : Nat := 118140960795 + 712959 * 2 ^ 59
def prefixEnd_712959 : Nat := 4983230072969 + 3 ^ 40 * 712959 * 2
def baseEnd_712959 : Nat := 366090653948981278333667

theorem tailTrace_712959 : CollatzResearch.WordTrace tailWord_712959 prefixEnd_712959 366090653948981278333667 := by
  unfold tailWord_712959
  simp only [CollatzResearch.WordTrace]
  refine ⟨26003751024078781548205931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17335834016052521032137287 26003751024078781548205931)
  ·
    refine ⟨39005626536118172322308897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26003751024078781548205931 39005626536118172322308897)
    ·
      refine ⟨29254219902088629241731673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39005626536118172322308897 29254219902088629241731673)
      ·
        refine ⟨21940664926566471931298755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29254219902088629241731673 21940664926566471931298755)
        ·
          refine ⟨32910997389849707896948133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21940664926566471931298755 32910997389849707896948133)
          ·
            refine ⟨6170812010596820230677775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32910997389849707896948133 6170812010596820230677775)
            ·
              refine ⟨9256218015895230346016663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170812010596820230677775 9256218015895230346016663)
              ·
                refine ⟨13884327023842845519024995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256218015895230346016663 13884327023842845519024995)
                ·
                  refine ⟨20826490535764268278537493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13884327023842845519024995 20826490535764268278537493)
                  ·
                    refine ⟨976241743863950075556445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20826490535764268278537493 976241743863950075556445)
                    ·
                      refine ⟨366090653948981278333667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 976241743863950075556445 366090653948981278333667)
                      ·
                        rfl

theorem cell23_712959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_712959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712959 prefixEnd_712959 := by exact prefixLift 712959
  have htrace : WordTrace (prefixWord ++ tailWord_712959) baseStart_712959 baseEnd_712959 := by
    simpa [prefixWord, tailWord_712959, baseEnd_712959] using wordTrace_append hprefix tailTrace_712959
  have hstable : (prefixWord ++ tailWord_712959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712959).length < 2 ^ (prefixWord ++ tailWord_712959).sum := by decide
  have hdescent : baseEnd_712959 < baseStart_712959 := by decide
  rcases family_descends (prefixWord ++ tailWord_712959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712969 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_712969 : Nat := 118140960795 + 712969 * 2 ^ 59
def prefixEnd_712969 : Nat := 4983230072969 + 3 ^ 40 * 712969 * 2
def baseEnd_712969 : Nat := 366095788755526239208621

theorem tailTrace_712969 : CollatzResearch.WordTrace tailWord_712969 prefixEnd_712969 366095788755526239208621 := by
  unfold tailWord_712969
  simp only [CollatzResearch.WordTrace]
  refine ⟨26004115754042553256069961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17336077169361702170713307 26004115754042553256069961)
  ·
    refine ⟨19503086815531914942052471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26004115754042553256069961 19503086815531914942052471)
    ·
      refine ⟨29254630223297872413078707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19503086815531914942052471 29254630223297872413078707)
      ·
        refine ⟨43881945334946808619618061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29254630223297872413078707 43881945334946808619618061)
        ·
          refine ⟨16455729500605053232356773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43881945334946808619618061 16455729500605053232356773)
          ·
            refine ⟨3085449281363447481066895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16455729500605053232356773 3085449281363447481066895)
            ·
              refine ⟨4628173922045171221600343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085449281363447481066895 4628173922045171221600343)
              ·
                refine ⟨6942260883067756832400515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628173922045171221600343 6942260883067756832400515)
                ·
                  refine ⟨10413391324601635248600773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6942260883067756832400515 10413391324601635248600773)
                  ·
                    refine ⟨1952510873362806609112645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10413391324601635248600773 1952510873362806609112645)
                    ·
                      refine ⟨366095788755526239208621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1952510873362806609112645 366095788755526239208621)
                      ·
                        rfl

theorem cell23_712969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_712969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_712969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_712969 prefixEnd_712969 := by exact prefixLift 712969
  have htrace : WordTrace (prefixWord ++ tailWord_712969) baseStart_712969 baseEnd_712969 := by
    simpa [prefixWord, tailWord_712969, baseEnd_712969] using wordTrace_append hprefix tailTrace_712969
  have hstable : (prefixWord ++ tailWord_712969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712969).length < 2 ^ (prefixWord ++ tailWord_712969).sum := by decide
  have hdescent : baseEnd_712969 < baseStart_712969 := by decide
  rcases family_descends (prefixWord ++ tailWord_712969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713016 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 7, 2]
def baseStart_713016 : Nat := 118140960795 + 713016 * 2 ^ 59
def prefixEnd_713016 : Nat := 4983230072969 + 3 ^ 40 * 713016 * 2
def baseEnd_713016 : Nat := 366119922346287555320905

theorem tailTrace_713016 : CollatzResearch.WordTrace tailWord_713016 prefixEnd_713016 366119922346287555320905 := by
  unfold tailWord_713016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002914992436140141515451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17337219989914853522020601 13002914992436140141515451)
  ·
    refine ⟨19504372488654210212273177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13002914992436140141515451 19504372488654210212273177)
    ·
      refine ⟨14628279366490657659204883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19504372488654210212273177 14628279366490657659204883)
      ·
        refine ⟨21942419049735986488807325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14628279366490657659204883 21942419049735986488807325)
        ·
          refine ⟨8228407143650994933302747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21942419049735986488807325 8228407143650994933302747)
          ·
            refine ⟨12342610715476492399954121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8228407143650994933302747 12342610715476492399954121)
            ·
              refine ⟨9256958036607369299965591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12342610715476492399954121 9256958036607369299965591)
              ·
                refine ⟨13885437054911053949948387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256958036607369299965591 13885437054911053949948387)
                ·
                  refine ⟨20828155582366580924922581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13885437054911053949948387 20828155582366580924922581)
                  ·
                    refine ⟨488159896461716740427873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20828155582366580924922581 488159896461716740427873)
                    ·
                      refine ⟨366119922346287555320905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488159896461716740427873 366119922346287555320905)
                      ·
                        rfl

theorem cell23_713016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_713016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713016 prefixEnd_713016 := by exact prefixLift 713016
  have htrace : WordTrace (prefixWord ++ tailWord_713016) baseStart_713016 baseEnd_713016 := by
    simpa [prefixWord, tailWord_713016, baseEnd_713016] using wordTrace_append hprefix tailTrace_713016
  have hstable : (prefixWord ++ tailWord_713016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713016).length < 2 ^ (prefixWord ++ tailWord_713016).sum := by decide
  have hdescent : baseEnd_713016 < baseStart_713016 := by decide
  rcases family_descends (prefixWord ++ tailWord_713016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713049 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_713049 : Nat := 118140960795 + 713049 * 2 ^ 59
def prefixEnd_713049 : Nat := 4983230072969 + 3 ^ 40 * 713049 * 2
def baseEnd_713049 : Nat := 366136867207885926208253

theorem tailTrace_713049 : CollatzResearch.WordTrace tailWord_713049 prefixEnd_713049 366136867207885926208253 := by
  unfold tailWord_713049
  simp only [CollatzResearch.WordTrace]
  refine ⟨26007033593752726918982201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17338022395835151279321467 26007033593752726918982201)
  ·
    refine ⟨19505275195314545189236651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26007033593752726918982201 19505275195314545189236651)
    ·
      refine ⟨29257912792971817783854977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19505275195314545189236651 29257912792971817783854977)
      ·
        refine ⟨21943434594728863337891233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29257912792971817783854977 21943434594728863337891233)
        ·
          refine ⟨16457575946046647503418425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21943434594728863337891233 16457575946046647503418425)
          ·
            refine ⟨12343181959534985627563819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16457575946046647503418425 12343181959534985627563819)
            ·
              refine ⟨18514772939302478441345729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12343181959534985627563819 18514772939302478441345729)
              ·
                refine ⟨13886079704476858831009297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18514772939302478441345729 13886079704476858831009297)
                ·
                  refine ⟨10414559778357644123256973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13886079704476858831009297 10414559778357644123256973)
                  ·
                    refine ⟨3905459916884116546221365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10414559778357644123256973 3905459916884116546221365)
                    ·
                      refine ⟨366136867207885926208253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3905459916884116546221365 366136867207885926208253)
                      ·
                        rfl

theorem cell23_713049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_713049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713049 prefixEnd_713049 := by exact prefixLift 713049
  have htrace : WordTrace (prefixWord ++ tailWord_713049) baseStart_713049 baseEnd_713049 := by
    simpa [prefixWord, tailWord_713049, baseEnd_713049] using wordTrace_append hprefix tailTrace_713049
  have hstable : (prefixWord ++ tailWord_713049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713049).length < 2 ^ (prefixWord ++ tailWord_713049).sum := by decide
  have hdescent : baseEnd_713049 < baseStart_713049 := by decide
  rcases family_descends (prefixWord ++ tailWord_713049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713063 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_713063 : Nat := 118140960795 + 713063 * 2 ^ 59
def prefixEnd_713063 : Nat := 4983230072969 + 3 ^ 40 * 713063 * 2
def baseEnd_713063 : Nat := 366144055937048871433189

theorem tailTrace_713063 : CollatzResearch.WordTrace tailWord_713063 prefixEnd_713063 366144055937048871433189 := by
  unfold tailWord_713063
  simp only [CollatzResearch.WordTrace]
  refine ⟨26007544215702007309991843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17338362810468004873327895 26007544215702007309991843)
  ·
    refine ⟨39011316323553010964987765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26007544215702007309991843 39011316323553010964987765)
    ·
      refine ⟨3657310905333094777967603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39011316323553010964987765 3657310905333094777967603)
      ·
        refine ⟨5485966357999642166951405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657310905333094777967603 5485966357999642166951405)
        ·
          refine ⟨2057237384249865812606777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5485966357999642166951405 2057237384249865812606777)
          ·
            refine ⟨1542928038187399359455083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057237384249865812606777 1542928038187399359455083)
            ·
              refine ⟨2314392057281099039182625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542928038187399359455083 2314392057281099039182625)
              ·
                refine ⟨1735794042960824279386969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2314392057281099039182625 1735794042960824279386969)
                ·
                  refine ⟨1301845532220618209540227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1735794042960824279386969 1301845532220618209540227)
                  ·
                    refine ⟨1952768298330927314310341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1301845532220618209540227 1952768298330927314310341)
                    ·
                      refine ⟨366144055937048871433189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1952768298330927314310341 366144055937048871433189)
                      ·
                        rfl

theorem cell23_713063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_713063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713063 prefixEnd_713063 := by exact prefixLift 713063
  have htrace : WordTrace (prefixWord ++ tailWord_713063) baseStart_713063 baseEnd_713063 := by
    simpa [prefixWord, tailWord_713063, baseEnd_713063] using wordTrace_append hprefix tailTrace_713063
  have hstable : (prefixWord ++ tailWord_713063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713063).length < 2 ^ (prefixWord ++ tailWord_713063).sum := by decide
  have hdescent : baseEnd_713063 < baseStart_713063 := by decide
  rcases family_descends (prefixWord ++ tailWord_713063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713164 : List Nat := [2, 2, 1, 4, 3, 1, 2, 3, 1, 1, 3]
def baseStart_713164 : Nat := 118140960795 + 713164 * 2 ^ 59
def prefixEnd_713164 : Nat := 4983230072969 + 3 ^ 40 * 713164 * 2
def baseEnd_713164 : Nat := 366195917483152976270225

theorem tailTrace_713164 : CollatzResearch.WordTrace tailWord_713164 prefixEnd_713164 366195917483152976270225 := by
  unfold tailWord_713164
  simp only [CollatzResearch.WordTrace]
  refine ⟨13005613994168050779709273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17340818658890734372945697 13005613994168050779709273)
  ·
    refine ⟨9754210495626038084781955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13005613994168050779709273 9754210495626038084781955)
    ·
      refine ⟨14631315743439057127172933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9754210495626038084781955 14631315743439057127172933)
      ·
        refine ⟨2743371701894823211344925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14631315743439057127172933 2743371701894823211344925)
        ·
          refine ⟨1028764388210558704254347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2743371701894823211344925 1028764388210558704254347)
          ·
            refine ⟨1543146582315838056381521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028764388210558704254347 1543146582315838056381521)
            ·
              refine ⟨1157359936736878542286141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543146582315838056381521 1157359936736878542286141)
              ·
                refine ⟨434009976276329453357303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157359936736878542286141 434009976276329453357303)
                ·
                  refine ⟨651014964414494180035955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434009976276329453357303 651014964414494180035955)
                  ·
                    refine ⟨976522446621741270053933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 651014964414494180035955 976522446621741270053933)
                    ·
                      refine ⟨366195917483152976270225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 976522446621741270053933 366195917483152976270225)
                      ·
                        rfl

theorem cell23_713164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_713164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713164 prefixEnd_713164 := by exact prefixLift 713164
  have htrace : WordTrace (prefixWord ++ tailWord_713164) baseStart_713164 baseEnd_713164 := by
    simpa [prefixWord, tailWord_713164, baseEnd_713164] using wordTrace_append hprefix tailTrace_713164
  have hstable : (prefixWord ++ tailWord_713164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713164).length < 2 ^ (prefixWord ++ tailWord_713164).sum := by decide
  have hdescent : baseEnd_713164 < baseStart_713164 := by decide
  rcases family_descends (prefixWord ++ tailWord_713164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713166 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_713166 : Nat := 118140960795 + 713166 * 2 ^ 59
def prefixEnd_713166 : Nat := 4983230072969 + 3 ^ 40 * 713166 * 2
def baseEnd_713166 : Nat := 366196944444461968445215

theorem tailTrace_713166 : CollatzResearch.WordTrace tailWord_713166 prefixEnd_713166 366196944444461968445215 := by
  unfold tailWord_713166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251412616791106987623919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17340867289552570600660901 3251412616791106987623919)
  ·
    refine ⟨4877118925186660481435879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3251412616791106987623919 4877118925186660481435879)
    ·
      refine ⟨7315678387779990722153819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877118925186660481435879 7315678387779990722153819)
      ·
        refine ⟨10973517581669986083230729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7315678387779990722153819 10973517581669986083230729)
        ·
          refine ⟨8230138186252489562423047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10973517581669986083230729 8230138186252489562423047)
          ·
            refine ⟨12345207279378734343634571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230138186252489562423047 12345207279378734343634571)
            ·
              refine ⟨18517810919068101515451857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12345207279378734343634571 18517810919068101515451857)
              ·
                refine ⟨13888358189301076136588893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18517810919068101515451857 13888358189301076136588893)
                ·
                  refine ⟨5208134320987903551220835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13888358189301076136588893 5208134320987903551220835)
                  ·
                    refine ⟨7812201481481855326831253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208134320987903551220835 7812201481481855326831253)
                    ·
                      refine ⟨366196944444461968445215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7812201481481855326831253 366196944444461968445215)
                      ·
                        rfl

theorem cell23_713166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_713166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713166 prefixEnd_713166 := by exact prefixLift 713166
  have htrace : WordTrace (prefixWord ++ tailWord_713166) baseStart_713166 baseEnd_713166 := by
    simpa [prefixWord, tailWord_713166, baseEnd_713166] using wordTrace_append hprefix tailTrace_713166
  have hstable : (prefixWord ++ tailWord_713166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713166).length < 2 ^ (prefixWord ++ tailWord_713166).sum := by decide
  have hdescent : baseEnd_713166 < baseStart_713166 := by decide
  rcases family_descends (prefixWord ++ tailWord_713166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713277 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_713277 : Nat := 118140960795 + 713277 * 2 ^ 59
def prefixEnd_713277 : Nat := 4983230072969 + 3 ^ 40 * 713277 * 2
def baseEnd_713277 : Nat := 366253940797111034157205

theorem tailTrace_713277 : CollatzResearch.WordTrace tailWord_713277 prefixEnd_713277 366253940797111034157205 := by
  unfold tailWord_713277
  simp only [CollatzResearch.WordTrace]
  refine ⟨26015349436926721858282085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17343566291284481238854723 26015349436926721858282085)
  ·
    refine ⟨4877878019423760348427891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26015349436926721858282085 4877878019423760348427891)
    ·
      refine ⟨7316817029135640522641837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877878019423760348427891 7316817029135640522641837)
      ·
        refine ⟨2743806385925865195990689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7316817029135640522641837 2743806385925865195990689)
        ·
          refine ⟨2057854789444398896993017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2743806385925865195990689 2057854789444398896993017)
          ·
            refine ⟨1543391092083299172744763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2057854789444398896993017 1543391092083299172744763)
            ·
              refine ⟨2315086638124948759117145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543391092083299172744763 2315086638124948759117145)
              ·
                refine ⟨1736314978593711569337859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315086638124948759117145 1736314978593711569337859)
                ·
                  refine ⟨2604472467890567354006789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736314978593711569337859 2604472467890567354006789)
                  ·
                    refine ⟨488338587729481378876273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604472467890567354006789 488338587729481378876273)
                    ·
                      refine ⟨366253940797111034157205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488338587729481378876273 366253940797111034157205)
                      ·
                        rfl

theorem cell23_713277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_713277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713277 prefixEnd_713277 := by exact prefixLift 713277
  have htrace : WordTrace (prefixWord ++ tailWord_713277) baseStart_713277 baseEnd_713277 := by
    simpa [prefixWord, tailWord_713277, baseEnd_713277] using wordTrace_append hprefix tailTrace_713277
  have hstable : (prefixWord ++ tailWord_713277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713277).length < 2 ^ (prefixWord ++ tailWord_713277).sum := by decide
  have hdescent : baseEnd_713277 < baseStart_713277 := by decide
  rcases family_descends (prefixWord ++ tailWord_713277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713330 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_713330 : Nat := 118140960795 + 713330 * 2 ^ 59
def prefixEnd_713330 : Nat := 4983230072969 + 3 ^ 40 * 713330 * 2
def baseEnd_713330 : Nat := 122093718423933108931487

theorem tailTrace_713330 : CollatzResearch.WordTrace tailWord_713330 prefixEnd_713330 122093718423933108931487 := by
  unfold tailWord_713330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504320626433677977490361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17344855003823141273307629 6504320626433677977490361)
  ·
    refine ⟨4878240469825258483117771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6504320626433677977490361 4878240469825258483117771)
    ·
      refine ⟨7317360704737887724676657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4878240469825258483117771 7317360704737887724676657)
      ·
        refine ⟨5488020528553415793507493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7317360704737887724676657 5488020528553415793507493)
        ·
          refine ⟨1029003849103765461282655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5488020528553415793507493 1029003849103765461282655)
          ·
            refine ⟨1543505773655648191923983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029003849103765461282655 1543505773655648191923983)
            ·
              refine ⟨2315258660483472287885975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543505773655648191923983 2315258660483472287885975)
              ·
                refine ⟨3472887990725208431828963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2315258660483472287885975 3472887990725208431828963)
                ·
                  refine ⟨5209331986087812647743445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472887990725208431828963 5209331986087812647743445)
                  ·
                    refine ⟨122093718423933108931487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5209331986087812647743445 122093718423933108931487)
                    ·
                      rfl

theorem cell23_713330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_713330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713330 prefixEnd_713330 := by exact prefixLift 713330
  have htrace : WordTrace (prefixWord ++ tailWord_713330) baseStart_713330 baseEnd_713330 := by
    simpa [prefixWord, tailWord_713330, baseEnd_713330] using wordTrace_append hprefix tailTrace_713330
  have hstable : (prefixWord ++ tailWord_713330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713330).length < 2 ^ (prefixWord ++ tailWord_713330).sum := by decide
  have hdescent : baseEnd_713330 < baseStart_713330 := by decide
  rcases family_descends (prefixWord ++ tailWord_713330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713334 : List Nat := [5, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_713334 : Nat := 118140960795 + 713334 * 2 ^ 59
def prefixEnd_713334 : Nat := 4983230072969 + 3 ^ 40 * 713334 * 2
def baseEnd_713334 : Nat := 40698134354935256793827

theorem tailTrace_713334 : CollatzResearch.WordTrace tailWord_713334 prefixEnd_713334 40698134354935256793827 := by
  unfold tailWord_713334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626089274857513787069191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17344952265146813728738037 1626089274857513787069191)
  ·
    refine ⟨2439133912286270680603787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1626089274857513787069191 2439133912286270680603787)
    ·
      refine ⟨3658700868429406020905681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2439133912286270680603787 3658700868429406020905681)
      ·
        refine ⟨2744025651322054515679261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3658700868429406020905681 2744025651322054515679261)
        ·
          refine ⟨1029009619245770443379723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2744025651322054515679261 1029009619245770443379723)
          ·
            refine ⟨1543514428868655665069585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029009619245770443379723 1543514428868655665069585)
            ·
              refine ⟨1157635821651491748802189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543514428868655665069585 1157635821651491748802189)
              ·
                refine ⟨434113433119309405800821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157635821651491748802189 434113433119309405800821)
                ·
                  refine ⟨40698134354935256793827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 434113433119309405800821 40698134354935256793827)
                  ·
                    rfl

theorem cell23_713334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_713334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713334 prefixEnd_713334 := by exact prefixLift 713334
  have htrace : WordTrace (prefixWord ++ tailWord_713334) baseStart_713334 baseEnd_713334 := by
    simpa [prefixWord, tailWord_713334, baseEnd_713334] using wordTrace_append hprefix tailTrace_713334
  have hstable : (prefixWord ++ tailWord_713334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713334).length < 2 ^ (prefixWord ++ tailWord_713334).sum := by decide
  have hdescent : baseEnd_713334 < baseStart_713334 := by decide
  rcases family_descends (prefixWord ++ tailWord_713334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713403 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 7, 5]
def baseStart_713403 : Nat := 118140960795 + 713403 * 2 ^ 59
def prefixEnd_713403 : Nat := 4983230072969 + 3 ^ 40 * 713403 * 2
def baseEnd_713403 : Nat := 122106213119859180393875

theorem tailTrace_713403 : CollatzResearch.WordTrace tailWord_713403 prefixEnd_713403 122106213119859180393875 := by
  unfold tailWord_713403
  simp only [CollatzResearch.WordTrace]
  refine ⟨26019945034470245377368863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17346630022980163584912575 26019945034470245377368863)
  ·
    refine ⟨39029917551705368066053295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26019945034470245377368863 39029917551705368066053295)
    ·
      refine ⟨58544876327558052099079943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39029917551705368066053295 58544876327558052099079943)
      ·
        refine ⟨87817314491337078148619915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58544876327558052099079943 87817314491337078148619915)
        ·
          refine ⟨131725971737005617222929873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87817314491337078148619915 131725971737005617222929873)
          ·
            refine ⟨98794478802754212917197405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131725971737005617222929873 98794478802754212917197405)
            ·
              refine ⟨37047929551032829843949027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98794478802754212917197405 37047929551032829843949027)
              ·
                refine ⟨55571894326549244765923541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37047929551032829843949027 55571894326549244765923541)
                ·
                  refine ⟨1302466273278497924201333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 55571894326549244765923541 1302466273278497924201333)
                  ·
                    refine ⟨122106213119859180393875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1302466273278497924201333 122106213119859180393875)
                    ·
                      rfl

theorem cell23_713403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 5].length) (baseStart_713403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713403 prefixEnd_713403 := by exact prefixLift 713403
  have htrace : WordTrace (prefixWord ++ tailWord_713403) baseStart_713403 baseEnd_713403 := by
    simpa [prefixWord, tailWord_713403, baseEnd_713403] using wordTrace_append hprefix tailTrace_713403
  have hstable : (prefixWord ++ tailWord_713403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713403).length < 2 ^ (prefixWord ++ tailWord_713403).sum := by decide
  have hdescent : baseEnd_713403 < baseStart_713403 := by decide
  rcases family_descends (prefixWord ++ tailWord_713403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713423 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_713423 : Nat := 118140960795 + 713423 * 2 ^ 59
def prefixEnd_713423 : Nat := 4983230072969 + 3 ^ 40 * 713423 * 2
def baseEnd_713423 : Nat := 366328908972667462931533

theorem tailTrace_713423 : CollatzResearch.WordTrace tailWord_713423 prefixEnd_713423 366328908972667462931533 := by
  unfold tailWord_713423
  simp only [CollatzResearch.WordTrace]
  refine ⟨26020674494397788793096923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17347116329598525862064615 26020674494397788793096923)
  ·
    refine ⟨39031011741596683189645385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26020674494397788793096923 39031011741596683189645385)
    ·
      refine ⟨29273258806197512392234039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39031011741596683189645385 29273258806197512392234039)
      ·
        refine ⟨43909888209296268588351059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29273258806197512392234039 43909888209296268588351059)
        ·
          refine ⟨65864832313944402882526589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43909888209296268588351059 65864832313944402882526589)
          ·
            refine ⟨24699312117729151080947471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65864832313944402882526589 24699312117729151080947471)
            ·
              refine ⟨37048968176593726621421207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24699312117729151080947471 37048968176593726621421207)
              ·
                refine ⟨55573452264890589932131811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37048968176593726621421207 55573452264890589932131811)
                ·
                  refine ⟨83360178397335884898197717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55573452264890589932131811 83360178397335884898197717)
                  ·
                    refine ⟨1953754181187559802301509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83360178397335884898197717 1953754181187559802301509)
                    ·
                      refine ⟨366328908972667462931533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1953754181187559802301509 366328908972667462931533)
                      ·
                        rfl

theorem cell23_713423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_713423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713423 prefixEnd_713423 := by exact prefixLift 713423
  have htrace : WordTrace (prefixWord ++ tailWord_713423) baseStart_713423 baseEnd_713423 := by
    simpa [prefixWord, tailWord_713423, baseEnd_713423] using wordTrace_append hprefix tailTrace_713423
  have hstable : (prefixWord ++ tailWord_713423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713423).length < 2 ^ (prefixWord ++ tailWord_713423).sum := by decide
  have hdescent : baseEnd_713423 < baseStart_713423 := by decide
  rcases family_descends (prefixWord ++ tailWord_713423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713444 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_713444 : Nat := 118140960795 + 713444 * 2 ^ 59
def prefixEnd_713444 : Nat := 4983230072969 + 3 ^ 40 * 713444 * 2
def baseEnd_713444 : Nat := 366339692066411880768937

theorem tailTrace_713444 : CollatzResearch.WordTrace tailWord_713444 prefixEnd_713444 366339692066411880768937 := by
  unfold tailWord_713444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13010720213660854689805693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17347626951547806253074257 13010720213660854689805693)
  ·
    refine ⟨4879020080122820508677135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13010720213660854689805693 4879020080122820508677135)
    ·
      refine ⟨7318530120184230763015703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4879020080122820508677135 7318530120184230763015703)
      ·
        refine ⟨10977795180276346144523555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7318530120184230763015703 10977795180276346144523555)
        ·
          refine ⟨16466692770414519216785333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10977795180276346144523555 16466692770414519216785333)
          ·
            refine ⟨1543752447226361176573625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16466692770414519216785333 1543752447226361176573625)
            ·
              refine ⟨1157814335419770882430219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1543752447226361176573625 1157814335419770882430219)
              ·
                refine ⟨1736721503129656323645329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157814335419770882430219 1736721503129656323645329)
                ·
                  refine ⟨1302541127347242242733997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736721503129656323645329 1302541127347242242733997)
                  ·
                    refine ⟨488452922755215841025249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302541127347242242733997 488452922755215841025249)
                    ·
                      refine ⟨366339692066411880768937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488452922755215841025249 366339692066411880768937)
                      ·
                        rfl

theorem cell23_713444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_713444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713444 prefixEnd_713444 := by exact prefixLift 713444
  have htrace : WordTrace (prefixWord ++ tailWord_713444) baseStart_713444 baseEnd_713444 := by
    simpa [prefixWord, tailWord_713444, baseEnd_713444] using wordTrace_append hprefix tailTrace_713444
  have hstable : (prefixWord ++ tailWord_713444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713444).length < 2 ^ (prefixWord ++ tailWord_713444).sum := by decide
  have hdescent : baseEnd_713444 < baseStart_713444 := by decide
  rcases family_descends (prefixWord ++ tailWord_713444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713454 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_713454 : Nat := 118140960795 + 713454 * 2 ^ 59
def prefixEnd_713454 : Nat := 4983230072969 + 3 ^ 40 * 713454 * 2
def baseEnd_713454 : Nat := 122114942290985613881297

theorem tailTrace_713454 : CollatzResearch.WordTrace tailWord_713454 prefixEnd_713454 122114942290985613881297 := by
  unfold tailWord_713454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3252725644660685135934427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17347870104856987391650277 3252725644660685135934427)
  ·
    refine ⟨4879088466991027703901641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3252725644660685135934427 4879088466991027703901641)
    ·
      refine ⟨3659316350243270777926231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4879088466991027703901641 3659316350243270777926231)
      ·
        refine ⟨5488974525364906166889347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659316350243270777926231 5488974525364906166889347)
        ·
          refine ⟨8233461788047359250334021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5488974525364906166889347 8233461788047359250334021)
          ·
            refine ⟨1543774085258879859437629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8233461788047359250334021 1543774085258879859437629)
            ·
              refine ⟨578915281972079947289111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1543774085258879859437629 578915281972079947289111)
              ·
                refine ⟨868372922958119920933667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578915281972079947289111 868372922958119920933667)
                ·
                  refine ⟨1302559384437179881400501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868372922958119920933667 1302559384437179881400501)
                  ·
                    refine ⟨122114942290985613881297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1302559384437179881400501 122114942290985613881297)
                    ·
                      rfl

theorem cell23_713454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_713454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713454 prefixEnd_713454 := by exact prefixLift 713454
  have htrace : WordTrace (prefixWord ++ tailWord_713454) baseStart_713454 baseEnd_713454 := by
    simpa [prefixWord, tailWord_713454, baseEnd_713454] using wordTrace_append hprefix tailTrace_713454
  have hstable : (prefixWord ++ tailWord_713454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713454).length < 2 ^ (prefixWord ++ tailWord_713454).sum := by decide
  have hdescent : baseEnd_713454 < baseStart_713454 := by decide
  rcases family_descends (prefixWord ++ tailWord_713454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713468 : List Nat := [2, 2, 2, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_713468 : Nat := 118140960795 + 713468 * 2 ^ 59
def prefixEnd_713468 : Nat := 4983230072969 + 3 ^ 40 * 713468 * 2
def baseEnd_713468 : Nat := 366352015602119786868827

theorem tailTrace_713468 : CollatzResearch.WordTrace tailWord_713468 prefixEnd_713468 366352015602119786868827 := by
  unfold tailWord_713468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011157889617380739242529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17348210519489840985656705 13011157889617380739242529)
  ·
    refine ⟨9758368417213035554431897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13011157889617380739242529 9758368417213035554431897)
    ·
      refine ⟨7318776312909776665823923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9758368417213035554431897 7318776312909776665823923)
      ·
        refine ⟨10978164469364664998735885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7318776312909776665823923 10978164469364664998735885)
        ·
          refine ⟨4116811676011749374525957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10978164469364664998735885 4116811676011749374525957)
          ·
            refine ⟨771902189252203007723617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4116811676011749374525957 771902189252203007723617)
            ·
              refine ⟨578926641939152255792713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771902189252203007723617 578926641939152255792713)
              ·
                refine ⟨434194981454364191844535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578926641939152255792713 434194981454364191844535)
                ·
                  refine ⟨651292472181546287766803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434194981454364191844535 651292472181546287766803)
                  ·
                    refine ⟨976938708272319431650205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 651292472181546287766803 976938708272319431650205)
                    ·
                      refine ⟨366352015602119786868827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 976938708272319431650205 366352015602119786868827)
                      ·
                        rfl

theorem cell23_713468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_713468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713468 prefixEnd_713468 := by exact prefixLift 713468
  have htrace : WordTrace (prefixWord ++ tailWord_713468) baseStart_713468 baseEnd_713468 := by
    simpa [prefixWord, tailWord_713468, baseEnd_713468] using wordTrace_append hprefix tailTrace_713468
  have hstable : (prefixWord ++ tailWord_713468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713468).length < 2 ^ (prefixWord ++ tailWord_713468).sum := by decide
  have hdescent : baseEnd_713468 < baseStart_713468 := by decide
  rcases family_descends (prefixWord ++ tailWord_713468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713480 : List Nat := [2, 1, 3, 2, 2, 2, 3, 8]
def baseStart_713480 : Nat := 118140960795 + 713480 * 2 ^ 59
def prefixEnd_713480 : Nat := 4983230072969 + 3 ^ 40 * 713480 * 2
def baseEnd_713480 : Nat := 13568821384073101478473

theorem tailTrace_713480 : CollatzResearch.WordTrace tailWord_713480 prefixEnd_713480 13568821384073101478473 := by
  unfold tailWord_713480
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011376727595643763960947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17348502303460858351947929 13011376727595643763960947)
  ·
    refine ⟨19517065091393465645941421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13011376727595643763960947 19517065091393465645941421)
    ·
      refine ⟨7318899409272549617228033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19517065091393465645941421 7318899409272549617228033)
      ·
        refine ⟨5489174556954412212921025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7318899409272549617228033 5489174556954412212921025)
        ·
          refine ⟨4116880917715809159690769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489174556954412212921025 4116880917715809159690769)
          ·
            refine ⟨3087660688286856869768077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4116880917715809159690769 3087660688286856869768077)
            ·
              refine ⟨1157872758107571326163029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3087660688286856869768077 1157872758107571326163029)
              ·
                refine ⟨13568821384073101478473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1157872758107571326163029 13568821384073101478473)
                ·
                  rfl

theorem cell23_713480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 8].length) (baseStart_713480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713480 prefixEnd_713480 := by exact prefixLift 713480
  have htrace : WordTrace (prefixWord ++ tailWord_713480) baseStart_713480 baseEnd_713480 := by
    simpa [prefixWord, tailWord_713480, baseEnd_713480] using wordTrace_append hprefix tailTrace_713480
  have hstable : (prefixWord ++ tailWord_713480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713480).length < 2 ^ (prefixWord ++ tailWord_713480).sum := by decide
  have hdescent : baseEnd_713480 < baseStart_713480 := by decide
  rcases family_descends (prefixWord ++ tailWord_713480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713507 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 3]
def baseStart_713507 : Nat := 118140960795 + 713507 * 2 ^ 59
def prefixEnd_713507 : Nat := 4983230072969 + 3 ^ 40 * 713507 * 2
def baseEnd_713507 : Nat := 366372041347645134281147

theorem tailTrace_713507 : CollatzResearch.WordTrace tailWord_713507 prefixEnd_713507 366372041347645134281147 := by
  unfold tailWord_713507
  simp only [CollatzResearch.WordTrace]
  refine ⟨26023738226093471139154775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17349158817395647426103183 26023738226093471139154775)
  ·
    refine ⟨39035607339140206708732163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26023738226093471139154775 39035607339140206708732163)
    ·
      refine ⟨58553411008710310063098245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39035607339140206708732163 58553411008710310063098245)
      ·
        refine ⟨10978764564133183136830921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58553411008710310063098245 10978764564133183136830921)
        ·
          refine ⟨8234073423099887352623191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10978764564133183136830921 8234073423099887352623191)
          ·
            refine ⟨12351110134649831028934787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234073423099887352623191 12351110134649831028934787)
            ·
              refine ⟨18526665201974746543402181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351110134649831028934787 18526665201974746543402181)
              ·
                refine ⟨3473749725370264976887909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18526665201974746543402181 3473749725370264976887909)
                ·
                  refine ⟨651328073506924683166483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3473749725370264976887909 651328073506924683166483)
                  ·
                    refine ⟨976992110260387024749725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 651328073506924683166483 976992110260387024749725)
                    ·
                      refine ⟨366372041347645134281147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 976992110260387024749725 366372041347645134281147)
                      ·
                        rfl

theorem cell23_713507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_713507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713507 prefixEnd_713507 := by exact prefixLift 713507
  have htrace : WordTrace (prefixWord ++ tailWord_713507) baseStart_713507 baseEnd_713507 := by
    simpa [prefixWord, tailWord_713507, baseEnd_713507] using wordTrace_append hprefix tailTrace_713507
  have hstable : (prefixWord ++ tailWord_713507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713507).length < 2 ^ (prefixWord ++ tailWord_713507).sum := by decide
  have hdescent : baseEnd_713507 < baseStart_713507 := by decide
  rcases family_descends (prefixWord ++ tailWord_713507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713508 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_713508 : Nat := 118140960795 + 713508 * 2 ^ 59
def prefixEnd_713508 : Nat := 4983230072969 + 3 ^ 40 * 713508 * 2
def baseEnd_713508 : Nat := 366372554828299630368643

theorem tailTrace_713508 : CollatzResearch.WordTrace tailWord_713508 prefixEnd_713508 366372554828299630368643 := by
  unfold tailWord_713508
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011887349544924154970589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17349183132726565539960785 13011887349544924154970589)
  ·
    refine ⟨4879457756079346558113971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13011887349544924154970589 4879457756079346558113971)
    ·
      refine ⟨7319186634119019837170957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4879457756079346558113971 7319186634119019837170957)
      ·
        refine ⟨2744694987794632438939109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7319186634119019837170957 2744694987794632438939109)
        ·
          refine ⟨514630310211493582301083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2744694987794632438939109 514630310211493582301083)
          ·
            refine ⟨771945465317240373451625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514630310211493582301083 771945465317240373451625)
            ·
              refine ⟨578959098987930280088719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771945465317240373451625 578959098987930280088719)
              ·
                refine ⟨868438648481895420133079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578959098987930280088719 868438648481895420133079)
                ·
                  refine ⟨1302657972722843130199619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868438648481895420133079 1302657972722843130199619)
                  ·
                    refine ⟨1953986959084264695299429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1302657972722843130199619 1953986959084264695299429)
                    ·
                      refine ⟨366372554828299630368643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1953986959084264695299429 366372554828299630368643)
                      ·
                        rfl

theorem cell23_713508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_713508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713508 prefixEnd_713508 := by exact prefixLift 713508
  have htrace : WordTrace (prefixWord ++ tailWord_713508) baseStart_713508 baseEnd_713508 := by
    simpa [prefixWord, tailWord_713508, baseEnd_713508] using wordTrace_append hprefix tailTrace_713508
  have hstable : (prefixWord ++ tailWord_713508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713508).length < 2 ^ (prefixWord ++ tailWord_713508).sum := by decide
  have hdescent : baseEnd_713508 < baseStart_713508 := by decide
  rcases family_descends (prefixWord ++ tailWord_713508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713550 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_713550 : Nat := 118140960795 + 713550 * 2 ^ 59
def prefixEnd_713550 : Nat := 4983230072969 + 3 ^ 40 * 713550 * 2
def baseEnd_713550 : Nat := 366394121015788466043449

theorem tailTrace_713550 : CollatzResearch.WordTrace tailWord_713550 prefixEnd_713550 366394121015788466043449 := by
  unfold tailWord_713550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253163320617211185371263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17350204376625126321980069 3253163320617211185371263)
  ·
    refine ⟨4879744980925816778056895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3253163320617211185371263 4879744980925816778056895)
    ·
      refine ⟨7319617471388725167085343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4879744980925816778056895 7319617471388725167085343)
      ·
        refine ⟨10979426207083087750628015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7319617471388725167085343 10979426207083087750628015)
        ·
          refine ⟨16469139310624631625942023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10979426207083087750628015 16469139310624631625942023)
          ·
            refine ⟨24703708965936947438913035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16469139310624631625942023 24703708965936947438913035)
            ·
              refine ⟨37055563448905421158369553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24703708965936947438913035 37055563448905421158369553)
              ·
                refine ⟨27791672586679065868777165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37055563448905421158369553 27791672586679065868777165)
                ·
                  refine ⟨10421877220004649700791437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27791672586679065868777165 10421877220004649700791437)
                  ·
                    refine ⟨3908203957501743637796789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10421877220004649700791437 3908203957501743637796789)
                    ·
                      refine ⟨366394121015788466043449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3908203957501743637796789 366394121015788466043449)
                      ·
                        rfl

theorem cell23_713550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_713550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713550 prefixEnd_713550 := by exact prefixLift 713550
  have htrace : WordTrace (prefixWord ++ tailWord_713550) baseStart_713550 baseEnd_713550 := by
    simpa [prefixWord, tailWord_713550, baseEnd_713550] using wordTrace_append hprefix tailTrace_713550
  have hstable : (prefixWord ++ tailWord_713550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713550).length < 2 ^ (prefixWord ++ tailWord_713550).sum := by decide
  have hdescent : baseEnd_713550 < baseStart_713550 := by decide
  rcases family_descends (prefixWord ++ tailWord_713550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713560 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_713560 : Nat := 118140960795 + 713560 * 2 ^ 59
def prefixEnd_713560 : Nat := 4983230072969 + 3 ^ 40 * 713560 * 2
def baseEnd_713560 : Nat := 366399255822333426918403

theorem tailTrace_713560 : CollatzResearch.WordTrace tailWord_713560 prefixEnd_713560 366399255822333426918403 := by
  unfold tailWord_713560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012835647450730595417067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17350447529934307460556089 13012835647450730595417067)
  ·
    refine ⟨19519253471176095893125601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13012835647450730595417067 19519253471176095893125601)
    ·
      refine ⟨14639440103382071919844201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19519253471176095893125601 14639440103382071919844201)
      ·
        refine ⟨10979580077536553939883151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14639440103382071919844201 10979580077536553939883151)
        ·
          refine ⟨16469370116304830909824727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10979580077536553939883151 16469370116304830909824727)
          ·
            refine ⟨24704055174457246364737091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16469370116304830909824727 24704055174457246364737091)
            ·
              refine ⟨37056082761685869547105637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24704055174457246364737091 37056082761685869547105637)
              ·
                refine ⟨6948015517816100540082307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37056082761685869547105637 6948015517816100540082307)
                ·
                  refine ⟨10422023276724150810123461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6948015517816100540082307 10422023276724150810123461)
                  ·
                    refine ⟨1954129364385778276898149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10422023276724150810123461 1954129364385778276898149)
                    ·
                      refine ⟨366399255822333426918403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1954129364385778276898149 366399255822333426918403)
                      ·
                        rfl

theorem cell23_713560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_713560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713560 prefixEnd_713560 := by exact prefixLift 713560
  have htrace : WordTrace (prefixWord ++ tailWord_713560) baseStart_713560 baseEnd_713560 := by
    simpa [prefixWord, tailWord_713560, baseEnd_713560] using wordTrace_append hprefix tailTrace_713560
  have hstable : (prefixWord ++ tailWord_713560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713560).length < 2 ^ (prefixWord ++ tailWord_713560).sum := by decide
  have hdescent : baseEnd_713560 < baseStart_713560 := by decide
  rcases family_descends (prefixWord ++ tailWord_713560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713580 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_713580 : Nat := 118140960795 + 713580 * 2 ^ 59
def prefixEnd_713580 : Nat := 4983230072969 + 3 ^ 40 * 713580 * 2
def baseEnd_713580 : Nat := 366409525435423348668311

theorem tailTrace_713580 : CollatzResearch.WordTrace tailWord_713580 prefixEnd_713580 366409525435423348668311 := by
  unfold tailWord_713580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13013200377414502303281097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17350933836552669737708129 13013200377414502303281097)
  ·
    refine ⟨9759900283060876727460823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13013200377414502303281097 9759900283060876727460823)
    ·
      refine ⟨14639850424591315091191235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9759900283060876727460823 14639850424591315091191235)
      ·
        refine ⟨21959775636886972636786853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14639850424591315091191235 21959775636886972636786853)
        ·
          refine ⟨4117457931916307369397535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21959775636886972636786853 4117457931916307369397535)
          ·
            refine ⟨6176186897874461054096303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117457931916307369397535 6176186897874461054096303)
            ·
              refine ⟨9264280346811691581144455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6176186897874461054096303 9264280346811691581144455)
              ·
                refine ⟨13896420520217537371716683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9264280346811691581144455 13896420520217537371716683)
                ·
                  refine ⟨20844630780326306057575025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13896420520217537371716683 20844630780326306057575025)
                  ·
                    refine ⟨15633473085244729543181269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20844630780326306057575025 15633473085244729543181269)
                    ·
                      refine ⟨366409525435423348668311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15633473085244729543181269 366409525435423348668311)
                      ·
                        rfl

theorem cell23_713580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_713580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713580 prefixEnd_713580 := by exact prefixLift 713580
  have htrace : WordTrace (prefixWord ++ tailWord_713580) baseStart_713580 baseEnd_713580 := by
    simpa [prefixWord, tailWord_713580, baseEnd_713580] using wordTrace_append hprefix tailTrace_713580
  have hstable : (prefixWord ++ tailWord_713580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713580).length < 2 ^ (prefixWord ++ tailWord_713580).sum := by decide
  have hdescent : baseEnd_713580 < baseStart_713580 := by decide
  rcases family_descends (prefixWord ++ tailWord_713580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713581 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_713581 : Nat := 118140960795 + 713581 * 2 ^ 59
def prefixEnd_713581 : Nat := 4983230072969 + 3 ^ 40 * 713581 * 2
def baseEnd_713581 : Nat := 366410038916077844755807

theorem tailTrace_713581 : CollatzResearch.WordTrace tailWord_713581 prefixEnd_713581 366410038916077844755807 := by
  unfold tailWord_713581
  simp only [CollatzResearch.WordTrace]
  refine ⟨26026437227825381777348597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17350958151883587851565731 26026437227825381777348597)
  ·
    refine ⟨2439978490108629541626431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26026437227825381777348597 2439978490108629541626431)
    ·
      refine ⟨3659967735162944312439647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2439978490108629541626431 3659967735162944312439647)
      ·
        refine ⟨5489951602744416468659471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659967735162944312439647 5489951602744416468659471)
        ·
          refine ⟨8234927404116624702989207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489951602744416468659471 8234927404116624702989207)
          ·
            refine ⟨12352391106174937054483811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234927404116624702989207 12352391106174937054483811)
            ·
              refine ⟨18528586659262405581725717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12352391106174937054483811 18528586659262405581725717)
              ·
                refine ⟨868527499652925261643393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18528586659262405581725717 868527499652925261643393)
                ·
                  refine ⟨651395624739693946232545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 868527499652925261643393 651395624739693946232545)
                  ·
                    refine ⟨488546718554770459674409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 651395624739693946232545 488546718554770459674409)
                    ·
                      refine ⟨366410038916077844755807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488546718554770459674409 366410038916077844755807)
                      ·
                        rfl

theorem cell23_713581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_713581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713581 prefixEnd_713581 := by exact prefixLift 713581
  have htrace : WordTrace (prefixWord ++ tailWord_713581) baseStart_713581 baseEnd_713581 := by
    simpa [prefixWord, tailWord_713581, baseEnd_713581] using wordTrace_append hprefix tailTrace_713581
  have hstable : (prefixWord ++ tailWord_713581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713581).length < 2 ^ (prefixWord ++ tailWord_713581).sum := by decide
  have hdescent : baseEnd_713581 < baseStart_713581 := by decide
  rcases family_descends (prefixWord ++ tailWord_713581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713587 : List Nat := [1, 1, 1, 2, 2, 1, 4, 6, 5]
def baseStart_713587 : Nat := 118140960795 + 713587 * 2 ^ 59
def prefixEnd_713587 : Nat := 4983230072969 + 3 ^ 40 * 713587 * 2
def baseEnd_713587 : Nat := 40712568866667202364531

theorem tailTrace_713587 : CollatzResearch.WordTrace tailWord_713587 prefixEnd_713587 40712568866667202364531 := by
  unfold tailWord_713587
  simp only [CollatzResearch.WordTrace]
  refine ⟨26026656065803644802067015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17351104043869096534711343 26026656065803644802067015)
  ·
    refine ⟨39039984098705467203100523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26026656065803644802067015 39039984098705467203100523)
    ·
      refine ⟨58559976148058200804650785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39039984098705467203100523 58559976148058200804650785)
      ·
        refine ⟨43919982111043650603488089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58559976148058200804650785 43919982111043650603488089)
        ·
          refine ⟨32939986583282737952616067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43919982111043650603488089 32939986583282737952616067)
          ·
            refine ⟨49409979874924106928924101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32939986583282737952616067 49409979874924106928924101)
            ·
              refine ⟨9264371226548270049173269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49409979874924106928924101 9264371226548270049173269)
              ·
                refine ⟨434267401244450158554997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9264371226548270049173269 434267401244450158554997)
                ·
                  refine ⟨40712568866667202364531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 434267401244450158554997 40712568866667202364531)
                  ·
                    rfl

theorem cell23_713587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 5].length) (baseStart_713587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713587 prefixEnd_713587 := by exact prefixLift 713587
  have htrace : WordTrace (prefixWord ++ tailWord_713587) baseStart_713587 baseEnd_713587 := by
    simpa [prefixWord, tailWord_713587, baseEnd_713587] using wordTrace_append hprefix tailTrace_713587
  have hstable : (prefixWord ++ tailWord_713587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713587).length < 2 ^ (prefixWord ++ tailWord_713587).sum := by decide
  have hdescent : baseEnd_713587 < baseStart_713587 := by decide
  rcases family_descends (prefixWord ++ tailWord_713587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713597 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_713597 : Nat := 118140960795 + 713597 * 2 ^ 59
def prefixEnd_713597 : Nat := 4983230072969 + 3 ^ 40 * 713597 * 2
def baseEnd_713597 : Nat := 366418254606549782155733

theorem tailTrace_713597 : CollatzResearch.WordTrace tailWord_713597 prefixEnd_713597 366418254606549782155733 := by
  unfold tailWord_713597
  simp only [CollatzResearch.WordTrace]
  refine ⟨26027020795767416509931045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17351347197178277673287363 26027020795767416509931045)
  ·
    refine ⟨4880066399206390595612071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26027020795767416509931045 4880066399206390595612071)
    ·
      refine ⟨7320099598809585893418107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4880066399206390595612071 7320099598809585893418107)
      ·
        refine ⟨10980149398214378840127161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7320099598809585893418107 10980149398214378840127161)
        ·
          refine ⟨8235112048660784130095371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10980149398214378840127161 8235112048660784130095371)
          ·
            refine ⟨12352668072991176195143057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235112048660784130095371 12352668072991176195143057)
            ·
              refine ⟨9264501054743382146357293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12352668072991176195143057 9264501054743382146357293)
              ·
                refine ⟨3474187895528768304883985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9264501054743382146357293 3474187895528768304883985)
                ·
                  refine ⟨2605640921646576228662989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3474187895528768304883985 2605640921646576228662989)
                  ·
                    refine ⟨977115345617466085748621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2605640921646576228662989 977115345617466085748621)
                    ·
                      refine ⟨366418254606549782155733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 977115345617466085748621 366418254606549782155733)
                      ·
                        rfl

theorem cell23_713597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_713597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713597 prefixEnd_713597 := by exact prefixLift 713597
  have htrace : WordTrace (prefixWord ++ tailWord_713597) baseStart_713597 baseEnd_713597 := by
    simpa [prefixWord, tailWord_713597, baseEnd_713597] using wordTrace_append hprefix tailTrace_713597
  have hstable : (prefixWord ++ tailWord_713597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713597).length < 2 ^ (prefixWord ++ tailWord_713597).sum := by decide
  have hdescent : baseEnd_713597 < baseStart_713597 := by decide
  rcases family_descends (prefixWord ++ tailWord_713597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713600 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 1, 7]
def baseStart_713600 : Nat := 118140960795 + 713600 * 2 ^ 59
def prefixEnd_713600 : Nat := 4983230072969 + 3 ^ 40 * 713600 * 2
def baseEnd_713600 : Nat := 122139931682837756806073

theorem tailTrace_713600 : CollatzResearch.WordTrace tailWord_713600 prefixEnd_713600 122139931682837756806073 := by
  unfold tailWord_713600
  simp only [CollatzResearch.WordTrace]
  refine ⟨13013565107378274011145127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17351420143171032014860169 13013565107378274011145127)
  ·
    refine ⟨19520347661067411016717691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13013565107378274011145127 19520347661067411016717691)
    ·
      refine ⟨29280521491601116525076537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19520347661067411016717691 29280521491601116525076537)
      ·
        refine ⟨21960391118700837393807403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29280521491601116525076537 21960391118700837393807403)
        ·
          refine ⟨32940586678051256090711105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21960391118700837393807403 32940586678051256090711105)
          ·
            refine ⟨24705440008538442068033329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32940586678051256090711105 24705440008538442068033329)
            ·
              refine ⟨18529080006403831551024997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24705440008538442068033329 18529080006403831551024997)
              ·
                refine ⟨3474202501200718415817187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18529080006403831551024997 3474202501200718415817187)
                ·
                  refine ⟨5211303751801077623725781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474202501200718415817187 5211303751801077623725781)
                  ·
                    refine ⟨122139931682837756806073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5211303751801077623725781 122139931682837756806073)
                    ·
                      rfl

theorem cell23_713600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_713600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713600 prefixEnd_713600 := by exact prefixLift 713600
  have htrace : WordTrace (prefixWord ++ tailWord_713600) baseStart_713600 baseEnd_713600 := by
    simpa [prefixWord, tailWord_713600, baseEnd_713600] using wordTrace_append hprefix tailTrace_713600
  have hstable : (prefixWord ++ tailWord_713600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713600).length < 2 ^ (prefixWord ++ tailWord_713600).sum := by decide
  have hdescent : baseEnd_713600 < baseStart_713600 := by decide
  rcases family_descends (prefixWord ++ tailWord_713600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713602 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_713602 : Nat := 118140960795 + 713602 * 2 ^ 59
def prefixEnd_713602 : Nat := 4983230072969 + 3 ^ 40 * 713602 * 2
def baseEnd_713602 : Nat := 366420822009822262593211

theorem tailTrace_713602 : CollatzResearch.WordTrace tailWord_713602 prefixEnd_713602 366420822009822262593211 := by
  unfold tailWord_713602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6506800790187325590965765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17351468773832868242575373 6506800790187325590965765)
  ·
    refine ⟨1220025148160123548306081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6506800790187325590965765 1220025148160123548306081)
    ·
      refine ⟨915018861120092661229561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1220025148160123548306081 915018861120092661229561)
      ·
        refine ⟨686264145840069495922171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 915018861120092661229561 686264145840069495922171)
        ·
          refine ⟨1029396218760104243883257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686264145840069495922171 1029396218760104243883257)
          ·
            refine ⟨772047164070078182912443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1029396218760104243883257 772047164070078182912443)
            ·
              refine ⟨1158070746105117274368665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772047164070078182912443 1158070746105117274368665)
              ·
                refine ⟨868553059578837955776499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158070746105117274368665 868553059578837955776499)
                ·
                  refine ⟨1302829589368256933664749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868553059578837955776499 1302829589368256933664749)
                  ·
                    refine ⟨488561096013096350124281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1302829589368256933664749 488561096013096350124281)
                    ·
                      refine ⟨366420822009822262593211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488561096013096350124281 366420822009822262593211)
                      ·
                        rfl

theorem cell23_713602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_713602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713602 prefixEnd_713602 := by exact prefixLift 713602
  have htrace : WordTrace (prefixWord ++ tailWord_713602) baseStart_713602 baseEnd_713602 := by
    simpa [prefixWord, tailWord_713602, baseEnd_713602] using wordTrace_append hprefix tailTrace_713602
  have hstable : (prefixWord ++ tailWord_713602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713602).length < 2 ^ (prefixWord ++ tailWord_713602).sum := by decide
  have hdescent : baseEnd_713602 < baseStart_713602 := by decide
  rcases family_descends (prefixWord ++ tailWord_713602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713634 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_713634 : Nat := 118140960795 + 713634 * 2 ^ 59
def prefixEnd_713634 : Nat := 4983230072969 + 3 ^ 40 * 713634 * 2
def baseEnd_713634 : Nat := 122145751130255379131021

theorem tailTrace_713634 : CollatzResearch.WordTrace tailWord_713634 prefixEnd_713634 122145751130255379131021 := by
  unfold tailWord_713634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507092574158342957256989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17352246864422247886018637 6507092574158342957256989)
  ·
    refine ⟨2440159715309378608971371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6507092574158342957256989 2440159715309378608971371)
    ·
      refine ⟨3660239572964067913457057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2440159715309378608971371 3660239572964067913457057)
      ·
        refine ⟨2745179679723050935092793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3660239572964067913457057 2745179679723050935092793)
        ·
          refine ⟨2058884759792288201319595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2745179679723050935092793 2058884759792288201319595)
          ·
            refine ⟨3088327139688432301979393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058884759792288201319595 3088327139688432301979393)
            ·
              refine ⟨2316245354766324226484545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3088327139688432301979393 2316245354766324226484545)
              ·
                refine ⟨1737184016074743169863409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316245354766324226484545 1737184016074743169863409)
                ·
                  refine ⟨1302888012056057377397557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1737184016074743169863409 1302888012056057377397557)
                  ·
                    refine ⟨122145751130255379131021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1302888012056057377397557 122145751130255379131021)
                    ·
                      rfl

theorem cell23_713634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_713634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713634 prefixEnd_713634 := by exact prefixLift 713634
  have htrace : WordTrace (prefixWord ++ tailWord_713634) baseStart_713634 baseEnd_713634 := by
    simpa [prefixWord, tailWord_713634, baseEnd_713634] using wordTrace_append hprefix tailTrace_713634
  have hstable : (prefixWord ++ tailWord_713634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713634).length < 2 ^ (prefixWord ++ tailWord_713634).sum := by decide
  have hdescent : baseEnd_713634 < baseStart_713634 := by decide
  rcases family_descends (prefixWord ++ tailWord_713634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713664 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 3, 4]
def baseStart_713664 : Nat := 118140960795 + 713664 * 2 ^ 59
def prefixEnd_713664 : Nat := 4983230072969 + 3 ^ 40 * 713664 * 2
def baseEnd_713664 : Nat := 122150885936800340005975

theorem tailTrace_713664 : CollatzResearch.WordTrace tailWord_713664 prefixEnd_713664 122150885936800340005975 := by
  unfold tailWord_713664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13014732243262343476310023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17352976324349791301746697 13014732243262343476310023)
  ·
    refine ⟨19522098364893515214465035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13014732243262343476310023 19522098364893515214465035)
    ·
      refine ⟨29283147547340272821697553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19522098364893515214465035 29283147547340272821697553)
      ·
        refine ⟨21962360660505204616273165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29283147547340272821697553 21962360660505204616273165)
        ·
          refine ⟨8235885247689451731102437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21962360660505204616273165 8235885247689451731102437)
          ·
            refine ⟨1544228483941772199581707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8235885247689451731102437 1544228483941772199581707)
            ·
              refine ⟨2316342725912658299372561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544228483941772199581707 2316342725912658299372561)
              ·
                refine ⟨1737257044434493724529421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316342725912658299372561 1737257044434493724529421)
                ·
                  refine ⟨651471391662935146698533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1737257044434493724529421 651471391662935146698533)
                  ·
                    refine ⟨122150885936800340005975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651471391662935146698533 122150885936800340005975)
                    ·
                      rfl

theorem cell23_713664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_713664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713664 prefixEnd_713664 := by exact prefixLift 713664
  have htrace : WordTrace (prefixWord ++ tailWord_713664) baseStart_713664 baseEnd_713664 := by
    simpa [prefixWord, tailWord_713664, baseEnd_713664] using wordTrace_append hprefix tailTrace_713664
  have hstable : (prefixWord ++ tailWord_713664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713664).length < 2 ^ (prefixWord ++ tailWord_713664).sum := by decide
  have hdescent : baseEnd_713664 < baseStart_713664 := by decide
  rcases family_descends (prefixWord ++ tailWord_713664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713668 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_713668 : Nat := 118140960795 + 713668 * 2 ^ 59
def prefixEnd_713668 : Nat := 4983230072969 + 3 ^ 40 * 713668 * 2
def baseEnd_713668 : Nat := 122151570577673001455969

theorem tailTrace_713668 : CollatzResearch.WordTrace tailWord_713668 prefixEnd_713668 122151570577673001455969 := by
  unfold tailWord_713668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13014805189255097817882829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17353073585673463757177105 13014805189255097817882829)
  ·
    refine ⟨4880551945970661681706061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13014805189255097817882829 4880551945970661681706061)
    ·
      refine ⟨1830206979738998130639773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4880551945970661681706061 1830206979738998130639773)
      ·
        refine ⟨686327617402124298989915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1830206979738998130639773 686327617402124298989915)
        ·
          refine ⟨1029491426103186448484873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686327617402124298989915 1029491426103186448484873)
          ·
            refine ⟨772118569577389836363655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1029491426103186448484873 772118569577389836363655)
            ·
              refine ⟨1158177854366084754545483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772118569577389836363655 1158177854366084754545483)
              ·
                refine ⟨1737266781549127131818225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158177854366084754545483 1737266781549127131818225)
                ·
                  refine ⟨1302950086161845348863669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1737266781549127131818225 1302950086161845348863669)
                  ·
                    refine ⟨122151570577673001455969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1302950086161845348863669 122151570577673001455969)
                    ·
                      rfl

theorem cell23_713668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_713668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713668 prefixEnd_713668 := by exact prefixLift 713668
  have htrace : WordTrace (prefixWord ++ tailWord_713668) baseStart_713668 baseEnd_713668 := by
    simpa [prefixWord, tailWord_713668, baseEnd_713668] using wordTrace_append hprefix tailTrace_713668
  have hstable : (prefixWord ++ tailWord_713668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713668).length < 2 ^ (prefixWord ++ tailWord_713668).sum := by decide
  have hdescent : baseEnd_713668 < baseStart_713668 := by decide
  rcases family_descends (prefixWord ++ tailWord_713668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713681 : List Nat := [1, 2, 2, 1, 2, 1, 6, 3, 1, 4]
def baseStart_713681 : Nat := 118140960795 + 713681 * 2 ^ 59
def prefixEnd_713681 : Nat := 4983230072969 + 3 ^ 40 * 713681 * 2
def baseEnd_713681 : Nat := 122153795660509151168449

theorem tailTrace_713681 : CollatzResearch.WordTrace tailWord_713681 prefixEnd_713681 122153795660509151168449 := by
  unfold tailWord_713681
  simp only [CollatzResearch.WordTrace]
  refine ⟨26030084527463098855988897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17353389684975399237325931 26030084527463098855988897)
  ·
    refine ⟨19522563395597324141991673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26030084527463098855988897 19522563395597324141991673)
    ·
      refine ⟨14641922546697993106493755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19522563395597324141991673 14641922546697993106493755)
      ·
        refine ⟨21962883820046989659740633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14641922546697993106493755 21962883820046989659740633)
        ·
          refine ⟨16472162865035242244805475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21962883820046989659740633 16472162865035242244805475)
          ·
            refine ⟨24708244297552863367208213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16472162865035242244805475 24708244297552863367208213)
            ·
              refine ⟨1158198951447790470337885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24708244297552863367208213 1158198951447790470337885)
              ·
                refine ⟨434324606792921426376707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1158198951447790470337885 434324606792921426376707)
                ·
                  refine ⟨651486910189382139565061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434324606792921426376707 651486910189382139565061)
                  ·
                    refine ⟨122153795660509151168449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651486910189382139565061 122153795660509151168449)
                    ·
                      rfl

theorem cell23_713681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_713681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713681 prefixEnd_713681 := by exact prefixLift 713681
  have htrace : WordTrace (prefixWord ++ tailWord_713681) baseStart_713681 baseEnd_713681 := by
    simpa [prefixWord, tailWord_713681, baseEnd_713681] using wordTrace_append hprefix tailTrace_713681
  have hstable : (prefixWord ++ tailWord_713681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713681).length < 2 ^ (prefixWord ++ tailWord_713681).sum := by decide
  have hdescent : baseEnd_713681 < baseStart_713681 := by decide
  rcases family_descends (prefixWord ++ tailWord_713681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713698 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_713698 : Nat := 118140960795 + 713698 * 2 ^ 59
def prefixEnd_713698 : Nat := 4983230072969 + 3 ^ 40 * 713698 * 2
def baseEnd_713698 : Nat := 122156705384217962330923

theorem tailTrace_713698 : CollatzResearch.WordTrace tailWord_713698 prefixEnd_713698 122156705384217962330923 := by
  unfold tailWord_713698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507676142100377689839437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17353803045601007172905165 6507676142100377689839437)
  ·
    refine ⟨2440378553287641633689789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6507676142100377689839437 2440378553287641633689789)
    ·
      refine ⟨915141957482865612633671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2440378553287641633689789 915141957482865612633671)
      ·
        refine ⟨1372712936224298418950507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915141957482865612633671 1372712936224298418950507)
        ·
          refine ⟨2059069404336447628425761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372712936224298418950507 2059069404336447628425761)
          ·
            refine ⟨1544302053252335721319321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2059069404336447628425761 1544302053252335721319321)
            ·
              refine ⟨1158226539939251790989491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544302053252335721319321 1158226539939251790989491)
              ·
                refine ⟨1737339809908877686484237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158226539939251790989491 1737339809908877686484237)
                ·
                  refine ⟨651502428715829132431589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1737339809908877686484237 651502428715829132431589)
                  ·
                    refine ⟨122156705384217962330923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651502428715829132431589 122156705384217962330923)
                    ·
                      rfl

theorem cell23_713698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_713698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713698 prefixEnd_713698 := by exact prefixLift 713698
  have htrace : WordTrace (prefixWord ++ tailWord_713698) baseStart_713698 baseEnd_713698 := by
    simpa [prefixWord, tailWord_713698, baseEnd_713698] using wordTrace_append hprefix tailTrace_713698
  have hstable : (prefixWord ++ tailWord_713698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713698).length < 2 ^ (prefixWord ++ tailWord_713698).sum := by decide
  have hdescent : baseEnd_713698 < baseStart_713698 := by decide
  rcases family_descends (prefixWord ++ tailWord_713698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713724 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_713724 : Nat := 118140960795 + 713724 * 2 ^ 59
def prefixEnd_713724 : Nat := 4983230072969 + 3 ^ 40 * 713724 * 2
def baseEnd_713724 : Nat := 122161155549890261755883

theorem tailTrace_713724 : CollatzResearch.WordTrace tailWord_713724 prefixEnd_713724 122161155549890261755883 := by
  unfold tailWord_713724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13015826433153658599902113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17354435244204878133202817 13015826433153658599902113)
  ·
    refine ⟨9761869824865243949926585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13015826433153658599902113 9761869824865243949926585)
    ·
      refine ⟨7321402368648932962444939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9761869824865243949926585 7321402368648932962444939)
      ·
        refine ⟨10982103552973399443667409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7321402368648932962444939 10982103552973399443667409)
        ·
          refine ⟨8236577664730049582750557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10982103552973399443667409 8236577664730049582750557)
          ·
            refine ⟨3088716624273768593531459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8236577664730049582750557 3088716624273768593531459)
            ·
              refine ⟨4633074936410652890297189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088716624273768593531459 4633074936410652890297189)
              ·
                refine ⟨868701550576997416930723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4633074936410652890297189 868701550576997416930723)
                ·
                  refine ⟨1303052325865496125396085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868701550576997416930723 1303052325865496125396085)
                  ·
                    refine ⟨122161155549890261755883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1303052325865496125396085 122161155549890261755883)
                    ·
                      rfl

theorem cell23_713724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_713724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713724 prefixEnd_713724 := by exact prefixLift 713724
  have htrace : WordTrace (prefixWord ++ tailWord_713724) baseStart_713724 baseEnd_713724 := by
    simpa [prefixWord, tailWord_713724, baseEnd_713724] using wordTrace_append hprefix tailTrace_713724
  have hstable : (prefixWord ++ tailWord_713724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713724).length < 2 ^ (prefixWord ++ tailWord_713724).sum := by decide
  have hdescent : baseEnd_713724 < baseStart_713724 := by decide
  rcases family_descends (prefixWord ++ tailWord_713724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713737 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 1, 6]
def baseStart_713737 : Nat := 118140960795 + 713737 * 2 ^ 59
def prefixEnd_713737 : Nat := 4983230072969 + 3 ^ 40 * 713737 * 2
def baseEnd_713737 : Nat := 122163380632726411468363

theorem tailTrace_713737 : CollatzResearch.WordTrace tailWord_713737 prefixEnd_713737 122163380632726411468363 := by
  unfold tailWord_713737
  simp only [CollatzResearch.WordTrace]
  refine ⟨26032127015260220420027465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17354751343506813613351643 26032127015260220420027465)
  ·
    refine ⟨19524095261445165315020599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26032127015260220420027465 19524095261445165315020599)
    ·
      refine ⟨29286142892167747972530899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19524095261445165315020599 29286142892167747972530899)
      ·
        refine ⟨43929214338251621958796349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29286142892167747972530899 43929214338251621958796349)
        ·
          refine ⟨16473455376844358234548631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43929214338251621958796349 16473455376844358234548631)
          ·
            refine ⟨24710183065266537351822947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16473455376844358234548631 24710183065266537351822947)
            ·
              refine ⟨37065274597899806027734421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24710183065266537351822947 37065274597899806027734421)
              ·
                refine ⟨1737434746776553407550051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37065274597899806027734421 1737434746776553407550051)
                ·
                  refine ⟨2606152120164830111325077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737434746776553407550051 2606152120164830111325077)
                  ·
                    refine ⟨122163380632726411468363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2606152120164830111325077 122163380632726411468363)
                    ·
                      rfl

theorem cell23_713737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_713737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713737 prefixEnd_713737 := by exact prefixLift 713737
  have htrace : WordTrace (prefixWord ++ tailWord_713737) baseStart_713737 baseEnd_713737 := by
    simpa [prefixWord, tailWord_713737, baseEnd_713737] using wordTrace_append hprefix tailTrace_713737
  have hstable : (prefixWord ++ tailWord_713737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713737).length < 2 ^ (prefixWord ++ tailWord_713737).sum := by decide
  have hdescent : baseEnd_713737 < baseStart_713737 := by decide
  rcases family_descends (prefixWord ++ tailWord_713737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713754 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_713754 : Nat := 118140960795 + 713754 * 2 ^ 59
def prefixEnd_713754 : Nat := 4983230072969 + 3 ^ 40 * 713754 * 2
def baseEnd_713754 : Nat := 122166290356435222630837

theorem tailTrace_713754 : CollatzResearch.WordTrace tailWord_713754 prefixEnd_713754 122166290356435222630837 := by
  unfold tailWord_713754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508186764049658080849079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17355164704132421548930877 6508186764049658080849079)
  ·
    refine ⟨9762280146074487121273619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6508186764049658080849079 9762280146074487121273619)
    ·
      refine ⟨14643420219111730681910429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9762280146074487121273619 14643420219111730681910429)
      ·
        refine ⟨5491282582166899005716411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14643420219111730681910429 5491282582166899005716411)
        ·
          refine ⟨8236923873250348508574617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491282582166899005716411 8236923873250348508574617)
          ·
            refine ⟨6177692904937761381430963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8236923873250348508574617 6177692904937761381430963)
            ·
              refine ⟨9266539357406642072146445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177692904937761381430963 9266539357406642072146445)
              ·
                refine ⟨3474952259027490777054917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9266539357406642072146445 3474952259027490777054917)
                ·
                  refine ⟨651553548567654520697797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3474952259027490777054917 651553548567654520697797)
                  ·
                    refine ⟨122166290356435222630837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651553548567654520697797 122166290356435222630837)
                    ·
                      rfl

theorem cell23_713754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_713754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713754 prefixEnd_713754 := by exact prefixLift 713754
  have htrace : WordTrace (prefixWord ++ tailWord_713754) baseStart_713754 baseEnd_713754 := by
    simpa [prefixWord, tailWord_713754, baseEnd_713754] using wordTrace_append hprefix tailTrace_713754
  have hstable : (prefixWord ++ tailWord_713754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713754).length < 2 ^ (prefixWord ++ tailWord_713754).sum := by decide
  have hdescent : baseEnd_713754 < baseStart_713754 := by decide
  rcases family_descends (prefixWord ++ tailWord_713754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713774 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_713774 : Nat := 118140960795 + 713774 * 2 ^ 59
def prefixEnd_713774 : Nat := 4983230072969 + 3 ^ 40 * 713774 * 2
def baseEnd_713774 : Nat := 366509140682395589642419

theorem tailTrace_713774 : CollatzResearch.WordTrace tailWord_713774 prefixEnd_713774 366509140682395589642419 := by
  unfold tailWord_713774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254184564515771967390547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17355651010750783826082917 3254184564515771967390547)
  ·
    refine ⟨4881276846773657951085821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254184564515771967390547 4881276846773657951085821)
    ·
      refine ⟨1830478817540121731657183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4881276846773657951085821 1830478817540121731657183)
      ·
        refine ⟨2745718226310182597485775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830478817540121731657183 2745718226310182597485775)
        ·
          refine ⟨4118577339465273896228663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745718226310182597485775 4118577339465273896228663)
          ·
            refine ⟨6177866009197910844342995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118577339465273896228663 6177866009197910844342995)
            ·
              refine ⟨9266799013796866266514493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177866009197910844342995 9266799013796866266514493)
              ·
                refine ⟨3475049630173824849942935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9266799013796866266514493 3475049630173824849942935)
                ·
                  refine ⟨5212574445260737274914403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475049630173824849942935 5212574445260737274914403)
                  ·
                    refine ⟨7818861667891105912371605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5212574445260737274914403 7818861667891105912371605)
                    ·
                      refine ⟨366509140682395589642419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7818861667891105912371605 366509140682395589642419)
                      ·
                        rfl

theorem cell23_713774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_713774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713774 prefixEnd_713774 := by exact prefixLift 713774
  have htrace : WordTrace (prefixWord ++ tailWord_713774) baseStart_713774 baseEnd_713774 := by
    simpa [prefixWord, tailWord_713774, baseEnd_713774] using wordTrace_append hprefix tailTrace_713774
  have hstable : (prefixWord ++ tailWord_713774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713774).length < 2 ^ (prefixWord ++ tailWord_713774).sum := by decide
  have hdescent : baseEnd_713774 < baseStart_713774 := by decide
  rcases family_descends (prefixWord ++ tailWord_713774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713798 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_713798 : Nat := 118140960795 + 713798 * 2 ^ 59
def prefixEnd_713798 : Nat := 4983230072969 + 3 ^ 40 * 713798 * 2
def baseEnd_713798 : Nat := 366521464218103495742309

theorem tailTrace_713798 : CollatzResearch.WordTrace tailWord_713798 prefixEnd_713798 366521464218103495742309 := by
  unfold tailWord_713798
  simp only [CollatzResearch.WordTrace]
  refine ⟨813573495876225869937439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17356234578692818558665365 813573495876225869937439)
  ·
    refine ⟨1220360243814338804906159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 813573495876225869937439 1220360243814338804906159)
    ·
      refine ⟨1830540365721508207359239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1220360243814338804906159 1830540365721508207359239)
      ·
        refine ⟨2745810548582262311038859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830540365721508207359239 2745810548582262311038859)
        ·
          refine ⟨4118715822873393466558289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745810548582262311038859 4118715822873393466558289)
          ·
            refine ⟨3089036867155045099918717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4118715822873393466558289 3089036867155045099918717)
            ·
              refine ⟨1158388825183141912469519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3089036867155045099918717 1158388825183141912469519)
              ·
                refine ⟨1737583237774712868704279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158388825183141912469519 1737583237774712868704279)
                ·
                  refine ⟨2606374856662069303056419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737583237774712868704279 2606374856662069303056419)
                  ·
                    refine ⟨3909562284993103954584629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606374856662069303056419 3909562284993103954584629)
                    ·
                      refine ⟨366521464218103495742309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3909562284993103954584629 366521464218103495742309)
                      ·
                        rfl

theorem cell23_713798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_713798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713798 prefixEnd_713798 := by exact prefixLift 713798
  have htrace : WordTrace (prefixWord ++ tailWord_713798) baseStart_713798 baseEnd_713798 := by
    simpa [prefixWord, tailWord_713798, baseEnd_713798] using wordTrace_append hprefix tailTrace_713798
  have hstable : (prefixWord ++ tailWord_713798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713798).length < 2 ^ (prefixWord ++ tailWord_713798).sum := by decide
  have hdescent : baseEnd_713798 < baseStart_713798 := by decide
  rcases family_descends (prefixWord ++ tailWord_713798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713811 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 3]
def baseStart_713811 : Nat := 118140960795 + 713811 * 2 ^ 59
def prefixEnd_713811 : Nat := 4983230072969 + 3 ^ 40 * 713811 * 2
def baseEnd_713811 : Nat := 366528139466611944879749

theorem tailTrace_713811 : CollatzResearch.WordTrace tailWord_713811 prefixEnd_713811 366528139466611944879749 := by
  unfold tailWord_713811
  simp only [CollatzResearch.WordTrace]
  refine ⟨26034826016992131058221287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17356550677994754038814191 26034826016992131058221287)
  ·
    refine ⟨39052239025488196587331931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26034826016992131058221287 39052239025488196587331931)
    ·
      refine ⟨58578358538232294880997897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39052239025488196587331931 58578358538232294880997897)
      ·
        refine ⟨43933768903674221160748423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58578358538232294880997897 43933768903674221160748423)
        ·
          refine ⟨65900653355511331741122635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43933768903674221160748423 65900653355511331741122635)
          ·
            refine ⟨98850980033266997611683953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65900653355511331741122635 98850980033266997611683953)
            ·
              refine ⟨74138235024950248208762965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98850980033266997611683953 74138235024950248208762965)
              ·
                refine ⟨868807441698635721196441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 74138235024950248208762965 868807441698635721196441)
                ·
                  refine ⟨651605581273976790897331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 868807441698635721196441 651605581273976790897331)
                  ·
                    refine ⟨977408371910965186345997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 651605581273976790897331 977408371910965186345997)
                    ·
                      refine ⟨366528139466611944879749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 977408371910965186345997 366528139466611944879749)
                      ·
                        rfl

theorem cell23_713811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 1, 3].length) (baseStart_713811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713811 prefixEnd_713811 := by exact prefixLift 713811
  have htrace : WordTrace (prefixWord ++ tailWord_713811) baseStart_713811 baseEnd_713811 := by
    simpa [prefixWord, tailWord_713811, baseEnd_713811] using wordTrace_append hprefix tailTrace_713811
  have hstable : (prefixWord ++ tailWord_713811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713811).length < 2 ^ (prefixWord ++ tailWord_713811).sum := by decide
  have hdescent : baseEnd_713811 < baseStart_713811 := by decide
  rcases family_descends (prefixWord ++ tailWord_713811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713812 : List Nat := [2, 4, 1, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_713812 : Nat := 118140960795 + 713812 * 2 ^ 59
def prefixEnd_713812 : Nat := 4983230072969 + 3 ^ 40 * 713812 * 2
def baseEnd_713812 : Nat := 366528652947266440967245

theorem tailTrace_713812 : CollatzResearch.WordTrace tailWord_713812 prefixEnd_713812 366528652947266440967245 := by
  unfold tailWord_713812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017431244994254114503845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17356574993325672152671793 13017431244994254114503845)
  ·
    refine ⟨2440768358436422646469471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13017431244994254114503845 2440768358436422646469471)
    ·
      refine ⟨3661152537654633969704207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2440768358436422646469471 3661152537654633969704207)
      ·
        refine ⟨5491728806481950954556311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661152537654633969704207 5491728806481950954556311)
        ·
          refine ⟨8237593209722926431834467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491728806481950954556311 8237593209722926431834467)
          ·
            refine ⟨12356389814584389647751701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8237593209722926431834467 12356389814584389647751701)
            ·
              refine ⟨579205772558643264738361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12356389814584389647751701 579205772558643264738361)
              ·
                refine ⟨434404329418982448553771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579205772558643264738361 434404329418982448553771)
                ·
                  refine ⟨651606494128473672830657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434404329418982448553771 651606494128473672830657)
                  ·
                    refine ⟨488704870596355254622993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 651606494128473672830657 488704870596355254622993)
                    ·
                      refine ⟨366528652947266440967245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488704870596355254622993 366528652947266440967245)
                      ·
                        rfl

theorem cell23_713812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_713812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713812 prefixEnd_713812 := by exact prefixLift 713812
  have htrace : WordTrace (prefixWord ++ tailWord_713812) baseStart_713812 baseEnd_713812 := by
    simpa [prefixWord, tailWord_713812, baseEnd_713812] using wordTrace_append hprefix tailTrace_713812
  have hstable : (prefixWord ++ tailWord_713812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713812).length < 2 ^ (prefixWord ++ tailWord_713812).sum := by decide
  have hdescent : baseEnd_713812 < baseStart_713812 := by decide
  rcases family_descends (prefixWord ++ tailWord_713812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713838 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_713838 : Nat := 118140960795 + 713838 * 2 ^ 59
def prefixEnd_713838 : Nat := 4983230072969 + 3 ^ 40 * 713838 * 2
def baseEnd_713838 : Nat := 366542003444283339242125

theorem tailTrace_713838 : CollatzResearch.WordTrace tailWord_713838 prefixEnd_713838 366542003444283339242125 := by
  unfold tailWord_713838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254476348486789333681771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17357207191929543112969445 3254476348486789333681771)
  ·
    refine ⟨4881714522730184000522657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254476348486789333681771 4881714522730184000522657)
    ·
      refine ⟨3661285892047638000391993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4881714522730184000522657 3661285892047638000391993)
      ·
        refine ⟨2745964419035728500293995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3661285892047638000391993 2745964419035728500293995)
        ·
          refine ⟨4118946628553592750440993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745964419035728500293995 4118946628553592750440993)
          ·
            refine ⟨3089209971415194562830745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4118946628553592750440993 3089209971415194562830745)
            ·
              refine ⟨2316907478561395922123059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089209971415194562830745 2316907478561395922123059)
              ·
                refine ⟨3475361217842093883184589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316907478561395922123059 3475361217842093883184589)
                ·
                  refine ⟨1303260456690785206194221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3475361217842093883184589 1303260456690785206194221)
                  ·
                    refine ⟨488722671259044452322833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1303260456690785206194221 488722671259044452322833)
                    ·
                      refine ⟨366542003444283339242125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488722671259044452322833 366542003444283339242125)
                      ·
                        rfl

theorem cell23_713838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_713838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713838 prefixEnd_713838 := by exact prefixLift 713838
  have htrace : WordTrace (prefixWord ++ tailWord_713838) baseStart_713838 baseEnd_713838 := by
    simpa [prefixWord, tailWord_713838, baseEnd_713838] using wordTrace_append hprefix tailTrace_713838
  have hstable : (prefixWord ++ tailWord_713838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713838).length < 2 ^ (prefixWord ++ tailWord_713838).sum := by decide
  have hdescent : baseEnd_713838 < baseStart_713838 := by decide
  rcases family_descends (prefixWord ++ tailWord_713838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713914 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_713914 : Nat := 118140960795 + 713914 * 2 ^ 59
def prefixEnd_713914 : Nat := 4983230072969 + 3 ^ 40 * 713914 * 2
def baseEnd_713914 : Nat := 366581027974025041891775

theorem tailTrace_713914 : CollatzResearch.WordTrace tailWord_713914 prefixEnd_713914 366581027974025041891775 := by
  unfold tailWord_713914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6509645683904744912305199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17359055157079319766147197 6509645683904744912305199)
  ·
    refine ⟨9764468525857117368457799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6509645683904744912305199 9764468525857117368457799)
    ·
      refine ⟨14646702788785676052686699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9764468525857117368457799 14646702788785676052686699)
      ·
        refine ⟨21970054183178514079030049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14646702788785676052686699 21970054183178514079030049)
        ·
          refine ⟨16477540637383885559272537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21970054183178514079030049 16477540637383885559272537)
          ·
            refine ⟨12358155478037914169454403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16477540637383885559272537 12358155478037914169454403)
            ·
              refine ⟨18537233217056871254181605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12358155478037914169454403 18537233217056871254181605)
              ·
                refine ⟨3475731228198163360159051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18537233217056871254181605 3475731228198163360159051)
                ·
                  refine ⟨5213596842297245040238577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475731228198163360159051 5213596842297245040238577)
                  ·
                    refine ⟨3910197631722933780178933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5213596842297245040238577 3910197631722933780178933)
                    ·
                      refine ⟨366581027974025041891775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3910197631722933780178933 366581027974025041891775)
                      ·
                        rfl

theorem cell23_713914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_713914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713914 prefixEnd_713914 := by exact prefixLift 713914
  have htrace : WordTrace (prefixWord ++ tailWord_713914) baseStart_713914 baseEnd_713914 := by
    simpa [prefixWord, tailWord_713914, baseEnd_713914] using wordTrace_append hprefix tailTrace_713914
  have hstable : (prefixWord ++ tailWord_713914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713914).length < 2 ^ (prefixWord ++ tailWord_713914).sum := by decide
  have hdescent : baseEnd_713914 < baseStart_713914 := by decide
  rcases family_descends (prefixWord ++ tailWord_713914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713951 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 3, 4]
def baseStart_713951 : Nat := 118140960795 + 713951 * 2 ^ 59
def prefixEnd_713951 : Nat := 4983230072969 + 3 ^ 40 * 713951 * 2
def baseEnd_713951 : Nat := 122200008919413799043035

theorem tailTrace_713951 : CollatzResearch.WordTrace tailWord_713951 prefixEnd_713951 122200008919413799043035 := by
  unfold tailWord_713951
  simp only [CollatzResearch.WordTrace]
  refine ⟨26039932236484934968317707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17359954824323289978878471 26039932236484934968317707)
  ·
    refine ⟨39059898354727402452476561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26039932236484934968317707 39059898354727402452476561)
    ·
      refine ⟨29294923766045551839357421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39059898354727402452476561 29294923766045551839357421)
      ·
        refine ⟨10985596412267081939759033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29294923766045551839357421 10985596412267081939759033)
        ·
          refine ⟨8239197309200311454819275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10985596412267081939759033 8239197309200311454819275)
          ·
            refine ⟨12358795963800467182228913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8239197309200311454819275 12358795963800467182228913)
            ·
              refine ⟨9269096972850350386671685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12358795963800467182228913 9269096972850350386671685)
              ·
                refine ⟨1737955682409440697500941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9269096972850350386671685 1737955682409440697500941)
                ·
                  refine ⟨651733380903540261562853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1737955682409440697500941 651733380903540261562853)
                  ·
                    refine ⟨122200008919413799043035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651733380903540261562853 122200008919413799043035)
                    ·
                      rfl

theorem cell23_713951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_713951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713951 prefixEnd_713951 := by exact prefixLift 713951
  have htrace : WordTrace (prefixWord ++ tailWord_713951) baseStart_713951 baseEnd_713951 := by
    simpa [prefixWord, tailWord_713951, baseEnd_713951] using wordTrace_append hprefix tailTrace_713951
  have hstable : (prefixWord ++ tailWord_713951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713951).length < 2 ^ (prefixWord ++ tailWord_713951).sum := by decide
  have hdescent : baseEnd_713951 < baseStart_713951 := by decide
  rcases family_descends (prefixWord ++ tailWord_713951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713984 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_713984 : Nat := 118140960795 + 713984 * 2 ^ 59
def prefixEnd_713984 : Nat := 4983230072969 + 3 ^ 40 * 713984 * 2
def baseEnd_713984 : Nat := 366616971619839768016453

theorem tailTrace_713984 : CollatzResearch.WordTrace tailWord_713984 prefixEnd_713984 366616971619839768016453 := by
  unfold tailWord_713984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13020567922682690802134503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17360757230243587736179337 13020567922682690802134503)
  ·
    refine ⟨19530851884024036203201755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13020567922682690802134503 19530851884024036203201755)
    ·
      refine ⟨29296277826036054304802633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19530851884024036203201755 29296277826036054304802633)
      ·
        refine ⟨21972208369527040728601975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29296277826036054304802633 21972208369527040728601975)
        ·
          refine ⟨32958312554290561092902963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21972208369527040728601975 32958312554290561092902963)
          ·
            refine ⟨49437468831435841639354445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32958312554290561092902963 49437468831435841639354445)
            ·
              refine ⟨18539050811788440614757917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49437468831435841639354445 18539050811788440614757917)
              ·
                refine ⟨6952144054420665230534219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18539050811788440614757917 6952144054420665230534219)
                ·
                  refine ⟨10428216081630997845801329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6952144054420665230534219 10428216081630997845801329)
                  ·
                    refine ⟨7821162061223248384350997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10428216081630997845801329 7821162061223248384350997)
                    ·
                      refine ⟨366616971619839768016453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7821162061223248384350997 366616971619839768016453)
                      ·
                        rfl

theorem cell23_713984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_713984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713984 prefixEnd_713984 := by exact prefixLift 713984
  have htrace : WordTrace (prefixWord ++ tailWord_713984) baseStart_713984 baseEnd_713984 := by
    simpa [prefixWord, tailWord_713984, baseEnd_713984] using wordTrace_append hprefix tailTrace_713984
  have hstable : (prefixWord ++ tailWord_713984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713984).length < 2 ^ (prefixWord ++ tailWord_713984).sum := by decide
  have hdescent : baseEnd_713984 < baseStart_713984 := by decide
  rcases family_descends (prefixWord ++ tailWord_713984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713985 : List Nat := [1, 2, 4, 1, 1, 4, 1, 4, 1, 4]
def baseStart_713985 : Nat := 118140960795 + 713985 * 2 ^ 59
def prefixEnd_713985 : Nat := 4983230072969 + 3 ^ 40 * 713985 * 2
def baseEnd_713985 : Nat := 122205828366831421367983

theorem tailTrace_713985 : CollatzResearch.WordTrace tailWord_713985 prefixEnd_713985 122205828366831421367983 := by
  unfold tailWord_713985
  simp only [CollatzResearch.WordTrace]
  refine ⟨26041172318361758775055409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17360781545574505850036939 26041172318361758775055409)
  ·
    refine ⟨19530879238771319081291557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26041172318361758775055409 19530879238771319081291557)
    ·
      refine ⟨3662039857269622327742167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19530879238771319081291557 3662039857269622327742167)
      ·
        refine ⟨5493059785904433491613251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3662039857269622327742167 5493059785904433491613251)
        ·
          refine ⟨8239589678856650237419877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493059785904433491613251 8239589678856650237419877)
          ·
            refine ⟨1544923064785621919516227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8239589678856650237419877 1544923064785621919516227)
            ·
              refine ⟨2317384597178432879274341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544923064785621919516227 2317384597178432879274341)
              ·
                refine ⟨434509611970956164863939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2317384597178432879274341 434509611970956164863939)
                ·
                  refine ⟨651764417956434247295909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434509611970956164863939 651764417956434247295909)
                  ·
                    refine ⟨122205828366831421367983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651764417956434247295909 122205828366831421367983)
                    ·
                      rfl

theorem cell23_713985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_713985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_713985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_713985 prefixEnd_713985 := by exact prefixLift 713985
  have htrace : WordTrace (prefixWord ++ tailWord_713985) baseStart_713985 baseEnd_713985 := by
    simpa [prefixWord, tailWord_713985, baseEnd_713985] using wordTrace_append hprefix tailTrace_713985
  have hstable : (prefixWord ++ tailWord_713985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713985).length < 2 ^ (prefixWord ++ tailWord_713985).sum := by decide
  have hdescent : baseEnd_713985 < baseStart_713985 := by decide
  rcases family_descends (prefixWord ++ tailWord_713985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714002 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_714002 : Nat := 118140960795 + 714002 * 2 ^ 59
def prefixEnd_714002 : Nat := 4983230072969 + 3 ^ 40 * 714002 * 2
def baseEnd_714002 : Nat := 122208738090540232530457

theorem tailTrace_714002 : CollatzResearch.WordTrace tailWord_714002 prefixEnd_714002 122208738090540232530457 := by
  unfold tailWord_714002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6510448089825042669606065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17361194906200113785616173 6510448089825042669606065)
  ·
    refine ⟨4882836067368782002204549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6510448089825042669606065 4882836067368782002204549)
    ·
      refine ⟨915531762631646625413353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4882836067368782002204549 915531762631646625413353)
      ·
        refine ⟨686648821973734969060015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 915531762631646625413353 686648821973734969060015)
        ·
          refine ⟨1029973232960602453590023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686648821973734969060015 1029973232960602453590023)
          ·
            refine ⟨1544959849440903680385035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029973232960602453590023 1544959849440903680385035)
            ·
              refine ⟨2317439774161355520577553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544959849440903680385035 2317439774161355520577553)
              ·
                refine ⟨1738079830621016640433165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317439774161355520577553 1738079830621016640433165)
                ·
                  refine ⟨651779936482881240162437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1738079830621016640433165 651779936482881240162437)
                  ·
                    refine ⟨122208738090540232530457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651779936482881240162437 122208738090540232530457)
                    ·
                      rfl

theorem cell23_714002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_714002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714002 prefixEnd_714002 := by exact prefixLift 714002
  have htrace : WordTrace (prefixWord ++ tailWord_714002) baseStart_714002 baseEnd_714002 := by
    simpa [prefixWord, tailWord_714002, baseEnd_714002] using wordTrace_append hprefix tailTrace_714002
  have hstable : (prefixWord ++ tailWord_714002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714002).length < 2 ^ (prefixWord ++ tailWord_714002).sum := by decide
  have hdescent : baseEnd_714002 < baseStart_714002 := by decide
  rcases family_descends (prefixWord ++ tailWord_714002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714008 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_714008 : Nat := 118140960795 + 714008 * 2 ^ 59
def prefixEnd_714008 : Nat := 4983230072969 + 3 ^ 40 * 714008 * 2
def baseEnd_714008 : Nat := 366629295155547674116343

theorem tailTrace_714008 : CollatzResearch.WordTrace tailWord_714008 prefixEnd_714008 366629295155547674116343 := by
  unfold tailWord_714008
  simp only [CollatzResearch.WordTrace]
  refine ⟨13021005598639216851571339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17361340798185622468761785 13021005598639216851571339)
  ·
    refine ⟨19531508397958825277357009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13021005598639216851571339 19531508397958825277357009)
    ·
      refine ⟨14648631298469118958017757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19531508397958825277357009 14648631298469118958017757)
      ·
        refine ⟨5493236736925919609256659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14648631298469118958017757 5493236736925919609256659)
        ·
          refine ⟨8239855105388879413884989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493236736925919609256659 8239855105388879413884989)
          ·
            refine ⟨3089945664520829780206871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8239855105388879413884989 3089945664520829780206871)
            ·
              refine ⟨4634918496781244670310307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089945664520829780206871 4634918496781244670310307)
              ·
                refine ⟨6952377745171867005465461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634918496781244670310307 6952377745171867005465461)
                ·
                  refine ⟨651785413609862531762387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6952377745171867005465461 651785413609862531762387)
                  ·
                    refine ⟨977678120414793797643581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 651785413609862531762387 977678120414793797643581)
                    ·
                      refine ⟨366629295155547674116343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 977678120414793797643581 366629295155547674116343)
                      ·
                        rfl

theorem cell23_714008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_714008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714008 prefixEnd_714008 := by exact prefixLift 714008
  have htrace : WordTrace (prefixWord ++ tailWord_714008) baseStart_714008 baseEnd_714008 := by
    simpa [prefixWord, tailWord_714008, baseEnd_714008] using wordTrace_append hprefix tailTrace_714008
  have hstable : (prefixWord ++ tailWord_714008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714008).length < 2 ^ (prefixWord ++ tailWord_714008).sum := by decide
  have hdescent : baseEnd_714008 < baseStart_714008 := by decide
  rcases family_descends (prefixWord ++ tailWord_714008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714011 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 1, 5]
def baseStart_714011 : Nat := 118140960795 + 714011 * 2 ^ 59
def prefixEnd_714011 : Nat := 4983230072969 + 3 ^ 40 * 714011 * 2
def baseEnd_714011 : Nat := 122210278532503720792943

theorem tailTrace_714011 : CollatzResearch.WordTrace tailWord_714011 prefixEnd_714011 122210278532503720792943 := by
  unfold tailWord_714011
  simp only [CollatzResearch.WordTrace]
  refine ⟨26042120616267565215501887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17361413744178376810334591 26042120616267565215501887)
  ·
    refine ⟨39063180924401347823252831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26042120616267565215501887 39063180924401347823252831)
    ·
      refine ⟨58594771386602021734879247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39063180924401347823252831 58594771386602021734879247)
      ·
        refine ⟨87892157079903032602318871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58594771386602021734879247 87892157079903032602318871)
        ·
          refine ⟨131838235619854548903478307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87892157079903032602318871 131838235619854548903478307)
          ·
            refine ⟨197757353429781823355217461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131838235619854548903478307 197757353429781823355217461)
            ·
              refine ⟨18539751884042045939551637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197757353429781823355217461 18539751884042045939551637)
              ·
                refine ⟨869050869564470903416483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18539751884042045939551637 869050869564470903416483)
                ·
                  refine ⟨1303576304346706355124725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869050869564470903416483 1303576304346706355124725)
                  ·
                    refine ⟨122210278532503720792943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1303576304346706355124725 122210278532503720792943)
                    ·
                      rfl

theorem cell23_714011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 5].length) (baseStart_714011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714011 prefixEnd_714011 := by exact prefixLift 714011
  have htrace : WordTrace (prefixWord ++ tailWord_714011) baseStart_714011 baseEnd_714011 := by
    simpa [prefixWord, tailWord_714011, baseEnd_714011] using wordTrace_append hprefix tailTrace_714011
  have hstable : (prefixWord ++ tailWord_714011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714011).length < 2 ^ (prefixWord ++ tailWord_714011).sum := by decide
  have hdescent : baseEnd_714011 < baseStart_714011 := by decide
  rcases family_descends (prefixWord ++ tailWord_714011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714058 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_714058 : Nat := 118140960795 + 714058 * 2 ^ 59
def prefixEnd_714058 : Nat := 4983230072969 + 3 ^ 40 * 714058 * 2
def baseEnd_714058 : Nat := 122218323062757492830371

theorem tailTrace_714058 : CollatzResearch.WordTrace tailWord_714058 prefixEnd_714058 122218323062757492830371 := by
  unfold tailWord_714058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6510958711774323060615707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17362556564731528161641885 6510958711774323060615707)
  ·
    refine ⟨9766438067661484590923561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6510958711774323060615707 9766438067661484590923561)
    ·
      refine ⟨7324828550746113443192671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9766438067661484590923561 7324828550746113443192671)
      ·
        refine ⟨10987242826119170164789007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324828550746113443192671 10987242826119170164789007)
        ·
          refine ⟨16480864239178755247183511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10987242826119170164789007 16480864239178755247183511)
          ·
            refine ⟨24721296358768132870775267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16480864239178755247183511 24721296358768132870775267)
            ·
              refine ⟨37081944538152199306162901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24721296358768132870775267 37081944538152199306162901)
              ·
                refine ⟨869108075112942171238193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37081944538152199306162901 869108075112942171238193)
                ·
                  refine ⟨651831056334706628428645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869108075112942171238193 651831056334706628428645)
                  ·
                    refine ⟨122218323062757492830371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651831056334706628428645 122218323062757492830371)
                    ·
                      rfl

theorem cell23_714058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_714058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714058 prefixEnd_714058 := by exact prefixLift 714058
  have htrace : WordTrace (prefixWord ++ tailWord_714058) baseStart_714058 baseEnd_714058 := by
    simpa [prefixWord, tailWord_714058, baseEnd_714058] using wordTrace_append hprefix tailTrace_714058
  have hstable : (prefixWord ++ tailWord_714058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714058).length < 2 ^ (prefixWord ++ tailWord_714058).sum := by decide
  have hdescent : baseEnd_714058 < baseStart_714058 := by decide
  rcases family_descends (prefixWord ++ tailWord_714058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714065 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 3, 2, 2]
def baseStart_714065 : Nat := 118140960795 + 714065 * 2 ^ 59
def prefixEnd_714065 : Nat := 4983230072969 + 3 ^ 40 * 714065 * 2
def baseEnd_714065 : Nat := 366658563552853951103581

theorem tailTrace_714065 : CollatzResearch.WordTrace tailWord_714065 prefixEnd_714065 366658563552853951103581 := by
  unfold tailWord_714065
  simp only [CollatzResearch.WordTrace]
  refine ⟨26044090158071932437967649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17362726772047954958645099 26044090158071932437967649)
  ·
    refine ⟨19533067618553949328475737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26044090158071932437967649 19533067618553949328475737)
    ·
      refine ⟨14649800713915461996356803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19533067618553949328475737 14649800713915461996356803)
      ·
        refine ⟨21974701070873192994535205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14649800713915461996356803 21974701070873192994535205)
        ·
          refine ⟨4120256450788723686475351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21974701070873192994535205 4120256450788723686475351)
          ·
            refine ⟨6180384676183085529713027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4120256450788723686475351 6180384676183085529713027)
            ·
              refine ⟨9270577014274628294569541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6180384676183085529713027 9270577014274628294569541)
              ·
                refine ⟨1738233190176492805231789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9270577014274628294569541 1738233190176492805231789)
                ·
                  refine ⟨651837446316184801961921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1738233190176492805231789 651837446316184801961921)
                  ·
                    refine ⟨488878084737138601471441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 651837446316184801961921 488878084737138601471441)
                    ·
                      refine ⟨366658563552853951103581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 488878084737138601471441 366658563552853951103581)
                      ·
                        rfl

theorem cell23_714065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_714065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714065 prefixEnd_714065 := by exact prefixLift 714065
  have htrace : WordTrace (prefixWord ++ tailWord_714065) baseStart_714065 baseEnd_714065 := by
    simpa [prefixWord, tailWord_714065, baseEnd_714065] using wordTrace_append hprefix tailTrace_714065
  have hstable : (prefixWord ++ tailWord_714065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714065).length < 2 ^ (prefixWord ++ tailWord_714065).sum := by decide
  have hdescent : baseEnd_714065 < baseStart_714065 := by decide
  rcases family_descends (prefixWord ++ tailWord_714065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714070 : List Nat := [5, 2, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_714070 : Nat := 118140960795 + 714070 * 2 ^ 59
def prefixEnd_714070 : Nat := 4983230072969 + 3 ^ 40 * 714070 * 2
def baseEnd_714070 : Nat := 122220376985375477180353

theorem tailTrace_714070 : CollatzResearch.WordTrace tailWord_714070 prefixEnd_714070 122220376985375477180353 := by
  unfold tailWord_714070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627767032690863643243729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17362848348702545527933109 1627767032690863643243729)
  ·
    refine ⟨1220825274518147732432797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1627767032690863643243729 1220825274518147732432797)
    ·
      refine ⟨457809477944305399662299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1220825274518147732432797 457809477944305399662299)
      ·
        refine ⟨686714216916458099493449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457809477944305399662299 686714216916458099493449)
        ·
          refine ⟨515035662687343574620087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686714216916458099493449 515035662687343574620087)
          ·
            refine ⟨772553494031015361930131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515035662687343574620087 772553494031015361930131)
            ·
              refine ⟨1158830241046523042895197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772553494031015361930131 1158830241046523042895197)
              ·
                refine ⟨434561340392446141085699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1158830241046523042895197 434561340392446141085699)
                ·
                  refine ⟨651842010588669211628549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434561340392446141085699 651842010588669211628549)
                  ·
                    refine ⟨122220376985375477180353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 651842010588669211628549 122220376985375477180353)
                    ·
                      rfl

theorem cell23_714070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_714070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714070 prefixEnd_714070 := by exact prefixLift 714070
  have htrace : WordTrace (prefixWord ++ tailWord_714070) baseStart_714070 baseEnd_714070 := by
    simpa [prefixWord, tailWord_714070, baseEnd_714070] using wordTrace_append hprefix tailTrace_714070
  have hstable : (prefixWord ++ tailWord_714070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714070).length < 2 ^ (prefixWord ++ tailWord_714070).sum := by decide
  have hdescent : baseEnd_714070 < baseStart_714070 := by decide
  rcases family_descends (prefixWord ++ tailWord_714070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714071 : List Nat := [1, 1, 3, 2, 3, 3, 1, 9]
def baseStart_714071 : Nat := 118140960795 + 714071 * 2 ^ 59
def prefixEnd_714071 : Nat := 4983230072969 + 3 ^ 40 * 714071 * 2
def baseEnd_714071 : Nat := 13580060905065960282539

theorem tailTrace_714071 : CollatzResearch.WordTrace tailWord_714071 prefixEnd_714071 13580060905065960282539 := by
  unfold tailWord_714071
  simp only [CollatzResearch.WordTrace]
  refine ⟨26044308996050195462686067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17362872664033463641790711 26044308996050195462686067)
  ·
    refine ⟨39066463494075293194029101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26044308996050195462686067 39066463494075293194029101)
    ·
      refine ⟨14649923810278234947760913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39066463494075293194029101 14649923810278234947760913)
      ·
        refine ⟨10987442857708676210820685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14649923810278234947760913 10987442857708676210820685)
        ·
          refine ⟨4120291071640753579057757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10987442857708676210820685 4120291071640753579057757)
          ·
            refine ⟨1545109151865282592146659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4120291071640753579057757 1545109151865282592146659)
            ·
              refine ⟨2317663727797923888219989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545109151865282592146659 2317663727797923888219989)
              ·
                refine ⟨13580060905065960282539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2317663727797923888219989 13580060905065960282539)
                ·
                  rfl

theorem cell23_714071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 9].length) (baseStart_714071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714071 prefixEnd_714071 := by exact prefixLift 714071
  have htrace : WordTrace (prefixWord ++ tailWord_714071) baseStart_714071 baseEnd_714071 := by
    simpa [prefixWord, tailWord_714071, baseEnd_714071] using wordTrace_append hprefix tailTrace_714071
  have hstable : (prefixWord ++ tailWord_714071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714071).length < 2 ^ (prefixWord ++ tailWord_714071).sum := by decide
  have hdescent : baseEnd_714071 < baseStart_714071 := by decide
  rcases family_descends (prefixWord ++ tailWord_714071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714088 : List Nat := [2, 1, 4, 2, 3, 2, 9]
def baseStart_714088 : Nat := 118140960795 + 714088 * 2 ^ 59
def prefixEnd_714088 : Nat := 4983230072969 + 3 ^ 40 * 714088 * 2
def baseEnd_714088 : Nat := 4526794735900090877975

theorem tailTrace_714088 : CollatzResearch.WordTrace tailWord_714088 prefixEnd_714088 4526794735900090877975 := by
  unfold tailWord_714088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13022464518494303683027459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17363286024659071577369945 13022464518494303683027459)
  ·
    refine ⟨19533696777741455524541189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13022464518494303683027459 19533696777741455524541189)
    ·
      refine ⟨3662568145826522910851473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19533696777741455524541189 3662568145826522910851473)
      ·
        refine ⟨2746926109369892183138605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3662568145826522910851473 2746926109369892183138605)
        ·
          refine ⟨1030097291013709568676977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2746926109369892183138605 1030097291013709568676977)
          ·
            refine ⟨772572968260282176507733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030097291013709568676977 772572968260282176507733)
            ·
              refine ⟨4526794735900090877975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 772572968260282176507733 4526794735900090877975)
              ·
                rfl

theorem cell23_714088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 9].length) (baseStart_714088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714088 prefixEnd_714088 := by exact prefixLift 714088
  have htrace : WordTrace (prefixWord ++ tailWord_714088) baseStart_714088 baseEnd_714088 := by
    simpa [prefixWord, tailWord_714088, baseEnd_714088] using wordTrace_append hprefix tailTrace_714088
  have hstable : (prefixWord ++ tailWord_714088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714088).length < 2 ^ (prefixWord ++ tailWord_714088).sum := by decide
  have hdescent : baseEnd_714088 < baseStart_714088 := by decide
  rcases family_descends (prefixWord ++ tailWord_714088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714205 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_714205 : Nat := 118140960795 + 714205 * 2 ^ 59
def prefixEnd_714205 : Nat := 4983230072969 + 3 ^ 40 * 714205 * 2
def baseEnd_714205 : Nat := 366730450844483403352937

theorem tailTrace_714205 : CollatzResearch.WordTrace tailWord_714205 prefixEnd_714205 366730450844483403352937 := by
  unfold tailWord_714205
  simp only [CollatzResearch.WordTrace]
  refine ⟨26049196377564736348064069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17366130918376490898709379 26049196377564736348064069)
  ·
    refine ⟨4884224320793388065262013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26049196377564736348064069 4884224320793388065262013)
    ·
      refine ⟨1831584120297520524473255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4884224320793388065262013 1831584120297520524473255)
      ·
        refine ⟨2747376180446280786709883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831584120297520524473255 2747376180446280786709883)
        ·
          refine ⟨4121064270669421180064825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747376180446280786709883 4121064270669421180064825)
          ·
            refine ⟨3090798203002065885048619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4121064270669421180064825 3090798203002065885048619)
            ·
              refine ⟨4636197304503098827572929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090798203002065885048619 4636197304503098827572929)
              ·
                refine ⟨3477147978377324120679697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4636197304503098827572929 3477147978377324120679697)
                ·
                  refine ⟨2607860983782993090509773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3477147978377324120679697 2607860983782993090509773)
                  ·
                    refine ⟨977947868918622408941165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2607860983782993090509773 977947868918622408941165)
                    ·
                      refine ⟨366730450844483403352937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 977947868918622408941165 366730450844483403352937)
                      ·
                        rfl

theorem cell23_714205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_714205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714205 prefixEnd_714205 := by exact prefixLift 714205
  have htrace : WordTrace (prefixWord ++ tailWord_714205) baseStart_714205 baseEnd_714205 := by
    simpa [prefixWord, tailWord_714205, baseEnd_714205] using wordTrace_append hprefix tailTrace_714205
  have hstable : (prefixWord ++ tailWord_714205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714205).length < 2 ^ (prefixWord ++ tailWord_714205).sum := by decide
  have hdescent : baseEnd_714205 < baseStart_714205 := by decide
  rcases family_descends (prefixWord ++ tailWord_714205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714268 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 8]
def baseStart_714268 : Nat := 118140960795 + 714268 * 2 ^ 59
def prefixEnd_714268 : Nat := 4983230072969 + 3 ^ 40 * 714268 * 2
def baseEnd_714268 : Nat := 40751422236190739651683

theorem tailTrace_714268 : CollatzResearch.WordTrace tailWord_714268 prefixEnd_714268 40751422236190739651683 := by
  unfold tailWord_714268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13025747088168249053803729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17367662784224332071738305 13025747088168249053803729)
  ·
    refine ⟨9769310316126186790352797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13025747088168249053803729 9769310316126186790352797)
    ·
      refine ⟨3663491368547320046382299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9769310316126186790352797 3663491368547320046382299)
      ·
        refine ⟨5495237052820980069573449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663491368547320046382299 5495237052820980069573449)
        ·
          refine ⟨4121427789615735052180087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495237052820980069573449 4121427789615735052180087)
          ·
            refine ⟨6182141684423602578270131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121427789615735052180087 6182141684423602578270131)
            ·
              refine ⟨9273212526635403867405197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182141684423602578270131 9273212526635403867405197)
              ·
                refine ⟨3477454697488276450276949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9273212526635403867405197 3477454697488276450276949)
                ·
                  refine ⟨40751422236190739651683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3477454697488276450276949 40751422236190739651683)
                  ·
                    rfl

theorem cell23_714268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_714268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714268 prefixEnd_714268 := by exact prefixLift 714268
  have htrace : WordTrace (prefixWord ++ tailWord_714268) baseStart_714268 baseEnd_714268 := by
    simpa [prefixWord, tailWord_714268, baseEnd_714268] using wordTrace_append hprefix tailTrace_714268
  have hstable : (prefixWord ++ tailWord_714268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714268).length < 2 ^ (prefixWord ++ tailWord_714268).sum := by decide
  have hdescent : baseEnd_714268 < baseStart_714268 := by decide
  rcases family_descends (prefixWord ++ tailWord_714268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714272 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 3, 4]
def baseStart_714272 : Nat := 118140960795 + 714272 * 2 ^ 59
def prefixEnd_714272 : Nat := 4983230072969 + 3 ^ 40 * 714272 * 2
def baseEnd_714272 : Nat := 122254951349444880405043

theorem tailTrace_714272 : CollatzResearch.WordTrace tailWord_714272 prefixEnd_714272 122254951349444880405043 := by
  unfold tailWord_714272
  simp only [CollatzResearch.WordTrace]
  refine ⟨13025820034161003395376535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17367760045548004527168713 13025820034161003395376535)
  ·
    refine ⟨19538730051241505093064803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13025820034161003395376535 19538730051241505093064803)
    ·
      refine ⟨29308095076862257639597205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19538730051241505093064803 29308095076862257639597205)
      ·
        refine ⟨1373816956727918326856119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29308095076862257639597205 1373816956727918326856119)
        ·
          refine ⟨2060725435091877490284179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373816956727918326856119 2060725435091877490284179)
          ·
            refine ⟨3091088152637816235426269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060725435091877490284179 3091088152637816235426269)
            ·
              refine ⟨1159158057239181088284851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3091088152637816235426269 1159158057239181088284851)
              ·
                refine ⟨1738737085858771632427277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159158057239181088284851 1738737085858771632427277)
                ·
                  refine ⟨652026407197039362160229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1738737085858771632427277 652026407197039362160229)
                  ·
                    refine ⟨122254951349444880405043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652026407197039362160229 122254951349444880405043)
                    ·
                      rfl

theorem cell23_714272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_714272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714272 prefixEnd_714272 := by exact prefixLift 714272
  have htrace : WordTrace (prefixWord ++ tailWord_714272) baseStart_714272 baseEnd_714272 := by
    simpa [prefixWord, tailWord_714272, baseEnd_714272] using wordTrace_append hprefix tailTrace_714272
  have hstable : (prefixWord ++ tailWord_714272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714272).length < 2 ^ (prefixWord ++ tailWord_714272).sum := by decide
  have hdescent : baseEnd_714272 < baseStart_714272 := by decide
  rcases family_descends (prefixWord ++ tailWord_714272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714328 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 5, 6]
def baseStart_714328 : Nat := 118140960795 + 714328 * 2 ^ 59
def prefixEnd_714328 : Nat := 4983230072969 + 3 ^ 40 * 714328 * 2
def baseEnd_714328 : Nat := 122264536321662140704957

theorem tailTrace_714328 : CollatzResearch.WordTrace tailWord_714328 prefixEnd_714328 122264536321662140704957 := by
  unfold tailWord_714328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13026841278059564177395819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17369121704079418903194425 13026841278059564177395819)
  ·
    refine ⟨19540261917089346266093729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13026841278059564177395819 19540261917089346266093729)
    ·
      refine ⟨14655196437817009699570297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19540261917089346266093729 14655196437817009699570297)
      ·
        refine ⟨10991397328362757274677723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14655196437817009699570297 10991397328362757274677723)
        ·
          refine ⟨16487095992544135912016585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10991397328362757274677723 16487095992544135912016585)
          ·
            refine ⟨12365321994408101934012439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16487095992544135912016585 12365321994408101934012439)
            ·
              refine ⟨18547982991612152901018659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12365321994408101934012439 18547982991612152901018659)
              ·
                refine ⟨27821974487418229351527989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18547982991612152901018659 27821974487418229351527989)
                ·
                  refine ⟨2608310108195459001705749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27821974487418229351527989 2608310108195459001705749)
                  ·
                    refine ⟨122264536321662140704957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2608310108195459001705749 122264536321662140704957)
                    ·
                      rfl

theorem cell23_714328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_714328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714328 prefixEnd_714328 := by exact prefixLift 714328
  have htrace : WordTrace (prefixWord ++ tailWord_714328) baseStart_714328 baseEnd_714328 := by
    simpa [prefixWord, tailWord_714328, baseEnd_714328] using wordTrace_append hprefix tailTrace_714328
  have hstable : (prefixWord ++ tailWord_714328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714328).length < 2 ^ (prefixWord ++ tailWord_714328).sum := by decide
  have hdescent : baseEnd_714328 < baseStart_714328 := by decide
  rcases family_descends (prefixWord ++ tailWord_714328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714335 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 4, 6, 2]
def baseStart_714335 : Nat := 118140960795 + 714335 * 2 ^ 59
def prefixEnd_714335 : Nat := 4983230072969 + 3 ^ 40 * 714335 * 2
def baseEnd_714335 : Nat := 366797203329567894727339

theorem tailTrace_714335 : CollatzResearch.WordTrace tailWord_714335 prefixEnd_714335 366797203329567894727339 := by
  unfold tailWord_714335
  simp only [CollatzResearch.WordTrace]
  refine ⟨26053937867093768550296459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17369291911395845700197639 26053937867093768550296459)
  ·
    refine ⟨39080906800640652825444689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26053937867093768550296459 39080906800640652825444689)
    ·
      refine ⟨29310680100480489619083517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39080906800640652825444689 29310680100480489619083517)
      ·
        refine ⟨10991505037680183607156319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29310680100480489619083517 10991505037680183607156319)
        ·
          refine ⟨16487257556520275410734479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10991505037680183607156319 16487257556520275410734479)
          ·
            refine ⟨24730886334780413116101719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16487257556520275410734479 24730886334780413116101719)
            ·
              refine ⟨37096329502170619674152579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24730886334780413116101719 37096329502170619674152579)
              ·
                refine ⟨55644494253255929511228869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37096329502170619674152579 55644494253255929511228869)
                ·
                  refine ⟨10433342672485486783355413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55644494253255929511228869 10433342672485486783355413)
                  ·
                    refine ⟨489062937772757192969785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10433342672485486783355413 489062937772757192969785)
                    ·
                      refine ⟨366797203329567894727339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489062937772757192969785 366797203329567894727339)
                      ·
                        rfl

theorem cell23_714335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_714335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714335 prefixEnd_714335 := by exact prefixLift 714335
  have htrace : WordTrace (prefixWord ++ tailWord_714335) baseStart_714335 baseEnd_714335 := by
    simpa [prefixWord, tailWord_714335, baseEnd_714335] using wordTrace_append hprefix tailTrace_714335
  have hstable : (prefixWord ++ tailWord_714335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714335).length < 2 ^ (prefixWord ++ tailWord_714335).sum := by decide
  have hdescent : baseEnd_714335 < baseStart_714335 := by decide
  rcases family_descends (prefixWord ++ tailWord_714335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714369 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_714369 : Nat := 118140960795 + 714369 * 2 ^ 59
def prefixEnd_714369 : Nat := 4983230072969 + 3 ^ 40 * 714369 * 2
def baseEnd_714369 : Nat := 366814661671820761702183

theorem tailTrace_714369 : CollatzResearch.WordTrace tailWord_714369 prefixEnd_714369 366814661671820761702183 := by
  unfold tailWord_714369
  simp only [CollatzResearch.WordTrace]
  refine ⟨26055177948970592357034161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17370118632647061571356107 26055177948970592357034161)
  ·
    refine ⟨19541383461727944267775621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26055177948970592357034161 19541383461727944267775621)
    ·
      refine ⟨3664009399073989550207929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19541383461727944267775621 3664009399073989550207929)
      ·
        refine ⟨2748007049305492162655947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3664009399073989550207929 2748007049305492162655947)
        ·
          refine ⟨4122010573958238243983921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748007049305492162655947 4122010573958238243983921)
          ·
            refine ⟨3091507930468678682987941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4122010573958238243983921 3091507930468678682987941)
            ·
              refine ⟨579657736962877253060239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3091507930468678682987941 579657736962877253060239)
              ·
                refine ⟨869486605444315879590359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579657736962877253060239 869486605444315879590359)
                ·
                  refine ⟨1304229908166473819385539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869486605444315879590359 1304229908166473819385539)
                  ·
                    refine ⟨1956344862249710729078309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1304229908166473819385539 1956344862249710729078309)
                    ·
                      refine ⟨366814661671820761702183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1956344862249710729078309 366814661671820761702183)
                      ·
                        rfl

theorem cell23_714369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_714369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714369 prefixEnd_714369 := by exact prefixLift 714369
  have htrace : WordTrace (prefixWord ++ tailWord_714369) baseStart_714369 baseEnd_714369 := by
    simpa [prefixWord, tailWord_714369, baseEnd_714369] using wordTrace_append hprefix tailTrace_714369
  have hstable : (prefixWord ++ tailWord_714369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714369).length < 2 ^ (prefixWord ++ tailWord_714369).sum := by decide
  have hdescent : baseEnd_714369 < baseStart_714369 := by decide
  rcases family_descends (prefixWord ++ tailWord_714369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714396 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_714396 : Nat := 118140960795 + 714396 * 2 ^ 59
def prefixEnd_714396 : Nat := 4983230072969 + 3 ^ 40 * 714396 * 2
def baseEnd_714396 : Nat := 122276175216497385354853

theorem tailTrace_714396 : CollatzResearch.WordTrace tailWord_714396 prefixEnd_714396 122276175216497385354853 := by
  unfold tailWord_714396
  simp only [CollatzResearch.WordTrace]
  refine ⟨13028081359936387984133521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17370775146581850645511361 13028081359936387984133521)
  ·
    refine ⟨9771061019952290988100141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13028081359936387984133521 9771061019952290988100141)
    ·
      refine ⟨3664147882482109120537553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9771061019952290988100141 3664147882482109120537553)
      ·
        refine ⟨2748110911861581840403165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3664147882482109120537553 2748110911861581840403165)
        ·
          refine ⟨1030541591948093190151187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2748110911861581840403165 1030541591948093190151187)
          ·
            refine ⟨1545812387922139785226781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030541591948093190151187 1545812387922139785226781)
            ·
              refine ⟨579679645470802419460043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1545812387922139785226781 579679645470802419460043)
              ·
                refine ⟨869519468206203629190065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579679645470802419460043 869519468206203629190065)
                ·
                  refine ⟨652139601154652721892549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869519468206203629190065 652139601154652721892549)
                  ·
                    refine ⟨122276175216497385354853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652139601154652721892549 122276175216497385354853)
                    ·
                      rfl

theorem cell23_714396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_714396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714396 prefixEnd_714396 := by exact prefixLift 714396
  have htrace : WordTrace (prefixWord ++ tailWord_714396) baseStart_714396 baseEnd_714396 := by
    simpa [prefixWord, tailWord_714396, baseEnd_714396] using wordTrace_append hprefix tailTrace_714396
  have hstable : (prefixWord ++ tailWord_714396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714396).length < 2 ^ (prefixWord ++ tailWord_714396).sum := by decide
  have hdescent : baseEnd_714396 < baseStart_714396 := by decide
  rcases family_descends (prefixWord ++ tailWord_714396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714429 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_714429 : Nat := 118140960795 + 714429 * 2 ^ 59
def prefixEnd_714429 : Nat := 4983230072969 + 3 ^ 40 * 714429 * 2
def baseEnd_714429 : Nat := 366845470511090526951907

theorem tailTrace_714429 : CollatzResearch.WordTrace tailWord_714429 prefixEnd_714429 366845470511090526951907 := by
  unfold tailWord_714429
  simp only [CollatzResearch.WordTrace]
  refine ⟨26057366328753222604218341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17371577552502148402812227 26057366328753222604218341)
  ·
    refine ⟨4885756186641229238290939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26057366328753222604218341 4885756186641229238290939)
    ·
      refine ⟨7328634279961843857436409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4885756186641229238290939 7328634279961843857436409)
      ·
        refine ⟨5496475709971382893077307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7328634279961843857436409 5496475709971382893077307)
        ·
          refine ⟨8244713564957074339615961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5496475709971382893077307 8244713564957074339615961)
          ·
            refine ⟨6183535173717805754711971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8244713564957074339615961 6183535173717805754711971)
            ·
              refine ⟨9275302760576708632067957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6183535173717805754711971 9275302760576708632067957)
              ·
                refine ⟨869559633804066434256371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9275302760576708632067957 869559633804066434256371)
                ·
                  refine ⟨1304339450706099651384557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869559633804066434256371 1304339450706099651384557)
                  ·
                    refine ⟨489127294014787369269209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304339450706099651384557 489127294014787369269209)
                    ·
                      refine ⟨366845470511090526951907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489127294014787369269209 366845470511090526951907)
                      ·
                        rfl

theorem cell23_714429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_714429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714429 prefixEnd_714429 := by exact prefixLift 714429
  have htrace : WordTrace (prefixWord ++ tailWord_714429) baseStart_714429 baseEnd_714429 := by
    simpa [prefixWord, tailWord_714429, baseEnd_714429] using wordTrace_append hprefix tailTrace_714429
  have hstable : (prefixWord ++ tailWord_714429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714429).length < 2 ^ (prefixWord ++ tailWord_714429).sum := by decide
  have hdescent : baseEnd_714429 < baseStart_714429 := by decide
  rcases family_descends (prefixWord ++ tailWord_714429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714455 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_714455 : Nat := 118140960795 + 714455 * 2 ^ 59
def prefixEnd_714455 : Nat := 4983230072969 + 3 ^ 40 * 714455 * 2
def baseEnd_714455 : Nat := 366858821008107425226787

theorem tailTrace_714455 : CollatzResearch.WordTrace tailWord_714455 prefixEnd_714455 366858821008107425226787 := by
  unfold tailWord_714455
  simp only [CollatzResearch.WordTrace]
  refine ⟨26058314626659029044664819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17372209751106019363109879 26058314626659029044664819)
  ·
    refine ⟨39087471939988543566997229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26058314626659029044664819 39087471939988543566997229)
    ·
      refine ⟨14657801977495703837623961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39087471939988543566997229 14657801977495703837623961)
      ·
        refine ⟨10993351483121777878217971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14657801977495703837623961 10993351483121777878217971)
        ·
          refine ⟨16490027224682666817326957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10993351483121777878217971 16490027224682666817326957)
          ·
            refine ⟨6183760209256000056497609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16490027224682666817326957 6183760209256000056497609)
            ·
              refine ⟨4637820156942000042373207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6183760209256000056497609 4637820156942000042373207)
              ·
                refine ⟨6956730235413000063559811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4637820156942000042373207 6956730235413000063559811)
                ·
                  refine ⟨10435095353119500095339717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6956730235413000063559811 10435095353119500095339717)
                  ·
                    refine ⟨1956580378709906267876197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10435095353119500095339717 1956580378709906267876197)
                    ·
                      refine ⟨366858821008107425226787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1956580378709906267876197 366858821008107425226787)
                      ·
                        rfl

theorem cell23_714455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_714455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714455 prefixEnd_714455 := by exact prefixLift 714455
  have htrace : WordTrace (prefixWord ++ tailWord_714455) baseStart_714455 baseEnd_714455 := by
    simpa [prefixWord, tailWord_714455, baseEnd_714455] using wordTrace_append hprefix tailTrace_714455
  have hstable : (prefixWord ++ tailWord_714455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714455).length < 2 ^ (prefixWord ++ tailWord_714455).sum := by decide
  have hdescent : baseEnd_714455 < baseStart_714455 := by decide
  rcases family_descends (prefixWord ++ tailWord_714455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714492 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_714492 : Nat := 118140960795 + 714492 * 2 ^ 59
def prefixEnd_714492 : Nat := 4983230072969 + 3 ^ 40 * 714492 * 2
def baseEnd_714492 : Nat := 366877819792323780464117

theorem tailTrace_714492 : CollatzResearch.WordTrace tailWord_714492 prefixEnd_714492 366877819792323780464117 := by
  unfold tailWord_714492
  simp only [CollatzResearch.WordTrace]
  refine ⟨13029832063762492181880865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17373109418349989575841153 13029832063762492181880865)
  ·
    refine ⟨9772374047821869136410649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13029832063762492181880865 9772374047821869136410649)
    ·
      refine ⟨7329280535866401852307987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9772374047821869136410649 7329280535866401852307987)
      ·
        refine ⟨10993920803799602778461981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7329280535866401852307987 10993920803799602778461981)
        ·
          refine ⟨4122720301424851041923243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10993920803799602778461981 4122720301424851041923243)
          ·
            refine ⟨6184080452137276562884865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122720301424851041923243 6184080452137276562884865)
            ·
              refine ⟨4638060339102957422163649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6184080452137276562884865 4638060339102957422163649)
              ·
                refine ⟨3478545254327218066622737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638060339102957422163649 3478545254327218066622737)
                ·
                  refine ⟨2608908940745413549967053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3478545254327218066622737 2608908940745413549967053)
                  ·
                    refine ⟨978340852779530081237645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2608908940745413549967053 978340852779530081237645)
                    ·
                      refine ⟨366877819792323780464117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 978340852779530081237645 366877819792323780464117)
                      ·
                        rfl

theorem cell23_714492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_714492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714492 prefixEnd_714492 := by exact prefixLift 714492
  have htrace : WordTrace (prefixWord ++ tailWord_714492) baseStart_714492 baseEnd_714492 := by
    simpa [prefixWord, tailWord_714492, baseEnd_714492] using wordTrace_append hprefix tailTrace_714492
  have hstable : (prefixWord ++ tailWord_714492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714492).length < 2 ^ (prefixWord ++ tailWord_714492).sum := by decide
  have hdescent : baseEnd_714492 < baseStart_714492 := by decide
  rcases family_descends (prefixWord ++ tailWord_714492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714499 : List Nat := [1, 1, 1, 3, 2, 2, 6, 2, 5]
def baseStart_714499 : Nat := 118140960795 + 714499 * 2 ^ 59
def prefixEnd_714499 : Nat := 4983230072969 + 3 ^ 40 * 714499 * 2
def baseEnd_714499 : Nat := 40764601572989472564065

theorem tailTrace_714499 : CollatzResearch.WordTrace tailWord_714499 prefixEnd_714499 40764601572989472564065 := by
  unfold tailWord_714499
  simp only [CollatzResearch.WordTrace]
  refine ⟨26059919438499624559266551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17373279625666416372844367 26059919438499624559266551)
  ·
    refine ⟨39089879157749436838899827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26059919438499624559266551 39089879157749436838899827)
    ·
      refine ⟨58634818736624155258349741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39089879157749436838899827 58634818736624155258349741)
      ·
        refine ⟨21988057026234058221881153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58634818736624155258349741 21988057026234058221881153)
        ·
          refine ⟨16491042769675543666410865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21988057026234058221881153 16491042769675543666410865)
          ·
            refine ⟨12368282077256657749808149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16491042769675543666410865 12368282077256657749808149)
            ·
              refine ⟨579763222371405832022257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12368282077256657749808149 579763222371405832022257)
              ·
                refine ⟨434822416778554374016693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579763222371405832022257 434822416778554374016693)
                ·
                  refine ⟨40764601572989472564065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 434822416778554374016693 40764601572989472564065)
                  ·
                    rfl

theorem cell23_714499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 5].length) (baseStart_714499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714499 prefixEnd_714499 := by exact prefixLift 714499
  have htrace : WordTrace (prefixWord ++ tailWord_714499) baseStart_714499 baseEnd_714499 := by
    simpa [prefixWord, tailWord_714499, baseEnd_714499] using wordTrace_append hprefix tailTrace_714499
  have hstable : (prefixWord ++ tailWord_714499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714499).length < 2 ^ (prefixWord ++ tailWord_714499).sum := by decide
  have hdescent : baseEnd_714499 < baseStart_714499 := by decide
  rcases family_descends (prefixWord ++ tailWord_714499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714529 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 2, 5]
def baseStart_714529 : Nat := 118140960795 + 714529 * 2 ^ 59
def prefixEnd_714529 : Nat := 4983230072969 + 3 ^ 40 * 714529 * 2
def baseEnd_714529 : Nat := 122298939525513378567149

theorem tailTrace_714529 : CollatzResearch.WordTrace tailWord_714529 prefixEnd_714529 122298939525513378567149 := by
  unfold tailWord_714529
  simp only [CollatzResearch.WordTrace]
  refine ⟨26061013628390939682858641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17374009085593959788572427 26061013628390939682858641)
  ·
    refine ⟨19545760221293204762143981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26061013628390939682858641 19545760221293204762143981)
    ·
      refine ⟨7329660082984951785803993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19545760221293204762143981 7329660082984951785803993)
      ·
        refine ⟨5497245062238713839352995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7329660082984951785803993 5497245062238713839352995)
        ·
          refine ⟨8245867593358070759029493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497245062238713839352995 8245867593358070759029493)
          ·
            refine ⟨773050086877319133659015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8245867593358070759029493 773050086877319133659015)
            ·
              refine ⟨1159575130315978700488523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773050086877319133659015 1159575130315978700488523)
              ·
                refine ⟨1739362695473968050732785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159575130315978700488523 1739362695473968050732785)
                ·
                  refine ⟨1304522021605476038049589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1739362695473968050732785 1304522021605476038049589)
                  ·
                    refine ⟨122298939525513378567149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1304522021605476038049589 122298939525513378567149)
                    ·
                      rfl

theorem cell23_714529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_714529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714529 prefixEnd_714529 := by exact prefixLift 714529
  have htrace : WordTrace (prefixWord ++ tailWord_714529) baseStart_714529 baseEnd_714529 := by
    simpa [prefixWord, tailWord_714529, baseEnd_714529] using wordTrace_append hprefix tailTrace_714529
  have hstable : (prefixWord ++ tailWord_714529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714529).length < 2 ^ (prefixWord ++ tailWord_714529).sum := by decide
  have hdescent : baseEnd_714529 < baseStart_714529 := by decide
  rcases family_descends (prefixWord ++ tailWord_714529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714566 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_714566 : Nat := 118140960795 + 714566 * 2 ^ 59
def prefixEnd_714566 : Nat := 4983230072969 + 3 ^ 40 * 714566 * 2
def baseEnd_714566 : Nat := 366915817360756490938777

theorem tailTrace_714566 : CollatzResearch.WordTrace tailWord_714566 prefixEnd_714566 366915817360756490938777 := by
  unfold tailWord_714566
  simp only [CollatzResearch.WordTrace]
  refine ⟨814448847789277968811111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17374908752837930001303701 814448847789277968811111)
  ·
    refine ⟨1221673271683916953216667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 814448847789277968811111 1221673271683916953216667)
    ·
      refine ⟨1832509907525875429825001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1221673271683916953216667 1832509907525875429825001)
      ·
        refine ⟨1374382430644406572368751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1832509907525875429825001 1374382430644406572368751)
        ·
          refine ⟨2061573645966609858553127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374382430644406572368751 2061573645966609858553127)
          ·
            refine ⟨3092360468949914787829691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061573645966609858553127 3092360468949914787829691)
            ·
              refine ⟨4638540703424872181744537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092360468949914787829691 4638540703424872181744537)
              ·
                refine ⟨3478905527568654136308403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4638540703424872181744537 3478905527568654136308403)
                ·
                  refine ⟨5218358291352981204462605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478905527568654136308403 5218358291352981204462605)
                  ·
                    refine ⟨1956884359257367951673477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5218358291352981204462605 1956884359257367951673477)
                    ·
                      refine ⟨366915817360756490938777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1956884359257367951673477 366915817360756490938777)
                      ·
                        rfl

theorem cell23_714566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_714566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714566 prefixEnd_714566 := by exact prefixLift 714566
  have htrace : WordTrace (prefixWord ++ tailWord_714566) baseStart_714566 baseEnd_714566 := by
    simpa [prefixWord, tailWord_714566, baseEnd_714566] using wordTrace_append hprefix tailTrace_714566
  have hstable : (prefixWord ++ tailWord_714566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714566).length < 2 ^ (prefixWord ++ tailWord_714566).sum := by decide
  have hdescent : baseEnd_714566 < baseStart_714566 := by decide
  rcases family_descends (prefixWord ++ tailWord_714566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714686 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_714686 : Nat := 118140960795 + 714686 * 2 ^ 59
def prefixEnd_714686 : Nat := 4983230072969 + 3 ^ 40 * 714686 * 2
def baseEnd_714686 : Nat := 366977435039296021438225

theorem tailTrace_714686 : CollatzResearch.WordTrace tailWord_714686 prefixEnd_714686 366977435039296021438225 := by
  unfold tailWord_714686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258342486102769437040489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17377826592548103664215941 3258342486102769437040489)
  ·
    refine ⟨2443756864577077077780367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3258342486102769437040489 2443756864577077077780367)
    ·
      refine ⟨3665635296865615616670551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443756864577077077780367 3665635296865615616670551)
      ·
        refine ⟨5498452945298423425005827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665635296865615616670551 5498452945298423425005827)
        ·
          refine ⟨8247679417947635137508741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498452945298423425005827 8247679417947635137508741)
          ·
            refine ⟨1546439890865181588282889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8247679417947635137508741 1546439890865181588282889)
            ·
              refine ⟨1159829918148886191212167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546439890865181588282889 1159829918148886191212167)
              ·
                refine ⟨1739744877223329286818251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159829918148886191212167 1739744877223329286818251)
                ·
                  refine ⟨2609617315834993930227377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1739744877223329286818251 2609617315834993930227377)
                  ·
                    refine ⟨1957212986876245447670533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2609617315834993930227377 1957212986876245447670533)
                    ·
                      refine ⟨366977435039296021438225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1957212986876245447670533 366977435039296021438225)
                      ·
                        rfl

theorem cell23_714686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_714686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714686 prefixEnd_714686 := by exact prefixLift 714686
  have htrace : WordTrace (prefixWord ++ tailWord_714686) baseStart_714686 baseEnd_714686 := by
    simpa [prefixWord, tailWord_714686, baseEnd_714686] using wordTrace_append hprefix tailTrace_714686
  have hstable : (prefixWord ++ tailWord_714686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714686).length < 2 ^ (prefixWord ++ tailWord_714686).sum := by decide
  have hdescent : baseEnd_714686 < baseStart_714686 := by decide
  rcases family_descends (prefixWord ++ tailWord_714686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714710 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_714710 : Nat := 118140960795 + 714710 * 2 ^ 59
def prefixEnd_714710 : Nat := 4983230072969 + 3 ^ 40 * 714710 * 2
def baseEnd_714710 : Nat := 366989758575003927538115

theorem tailTrace_714710 : CollatzResearch.WordTrace tailWord_714710 prefixEnd_714710 366989758575003927538115 := by
  unfold tailWord_714710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629225952545950474699849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17378410160490138396798389 1629225952545950474699849)
  ·
    refine ⟨1221919464409462856024887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1629225952545950474699849 1221919464409462856024887)
    ·
      refine ⟨1832879196614194284037331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1221919464409462856024887 1832879196614194284037331)
      ·
        refine ⟨2749318794921291426055997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832879196614194284037331 2749318794921291426055997)
        ·
          refine ⟨1030994548095484284770999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2749318794921291426055997 1030994548095484284770999)
          ·
            refine ⟨1546491822143226427156499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030994548095484284770999 1546491822143226427156499)
            ·
              refine ⟨2319737733214839640734749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546491822143226427156499 2319737733214839640734749)
              ·
                refine ⟨869901649955564865275531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2319737733214839640734749 869901649955564865275531)
                ·
                  refine ⟨1304852474933347297913297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869901649955564865275531 1304852474933347297913297)
                  ·
                    refine ⟨978639356200010473434973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1304852474933347297913297 978639356200010473434973)
                    ·
                      refine ⟨366989758575003927538115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 978639356200010473434973 366989758575003927538115)
                      ·
                        rfl

theorem cell23_714710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_714710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714710 prefixEnd_714710 := by exact prefixLift 714710
  have htrace : WordTrace (prefixWord ++ tailWord_714710) baseStart_714710 baseEnd_714710 := by
    simpa [prefixWord, tailWord_714710, baseEnd_714710] using wordTrace_append hprefix tailTrace_714710
  have hstable : (prefixWord ++ tailWord_714710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714710).length < 2 ^ (prefixWord ++ tailWord_714710).sum := by decide
  have hdescent : baseEnd_714710 < baseStart_714710 := by decide
  rcases family_descends (prefixWord ++ tailWord_714710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714723 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 3]
def baseStart_714723 : Nat := 118140960795 + 714723 * 2 ^ 59
def prefixEnd_714723 : Nat := 4983230072969 + 3 ^ 40 * 714723 * 2
def baseEnd_714723 : Nat := 366996433823512376675555

theorem tailTrace_714723 : CollatzResearch.WordTrace tailWord_714723 prefixEnd_714723 366996433823512376675555 := by
  unfold tailWord_714723
  simp only [CollatzResearch.WordTrace]
  refine ⟨26068089389688110815420823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17378726259792073876947215 26068089389688110815420823)
  ·
    refine ⟨39102134084532166223131235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26068089389688110815420823 39102134084532166223131235)
    ·
      refine ⟨58653201126798249334696853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39102134084532166223131235 58653201126798249334696853)
      ·
        refine ⟨2749368802818667937563915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58653201126798249334696853 2749368802818667937563915)
        ·
          refine ⟨4124053204228001906345873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749368802818667937563915 4124053204228001906345873)
          ·
            refine ⟨3093039903171001429759405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4124053204228001906345873 3093039903171001429759405)
            ·
              refine ⟨1159889963689125536159777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3093039903171001429759405 1159889963689125536159777)
              ·
                refine ⟨869917472766844152119833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159889963689125536159777 869917472766844152119833)
                ·
                  refine ⟨652438104575133114089875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869917472766844152119833 652438104575133114089875)
                  ·
                    refine ⟨978657156862699671134813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 652438104575133114089875 978657156862699671134813)
                    ·
                      refine ⟨366996433823512376675555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 978657156862699671134813 366996433823512376675555)
                      ·
                        rfl

theorem cell23_714723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_714723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714723 prefixEnd_714723 := by exact prefixLift 714723
  have htrace : WordTrace (prefixWord ++ tailWord_714723) baseStart_714723 baseEnd_714723 := by
    simpa [prefixWord, tailWord_714723, baseEnd_714723] using wordTrace_append hprefix tailTrace_714723
  have hstable : (prefixWord ++ tailWord_714723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714723).length < 2 ^ (prefixWord ++ tailWord_714723).sum := by decide
  have hdescent : baseEnd_714723 < baseStart_714723 := by decide
  rcases family_descends (prefixWord ++ tailWord_714723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714729 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 10, 2]
def baseStart_714729 : Nat := 118140960795 + 714729 * 2 ^ 59
def prefixEnd_714729 : Nat := 4983230072969 + 3 ^ 40 * 714729 * 2
def baseEnd_714729 : Nat := 366999514707439353200527

theorem tailTrace_714729 : CollatzResearch.WordTrace tailWord_714729 prefixEnd_714729 366999514707439353200527 := by
  unfold tailWord_714729
  simp only [CollatzResearch.WordTrace]
  refine ⟨26068308227666373840139241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17378872151777582560092827 26068308227666373840139241)
  ·
    refine ⟨19551231170749780380104431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26068308227666373840139241 19551231170749780380104431)
    ·
      refine ⟨29326846756124670570156647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19551231170749780380104431 29326846756124670570156647)
      ·
        refine ⟨43990270134187005855234971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29326846756124670570156647 43990270134187005855234971)
        ·
          refine ⟨65985405201280508782852457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43990270134187005855234971 65985405201280508782852457)
          ·
            refine ⟨49489053900960381587139343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65985405201280508782852457 49489053900960381587139343)
            ·
              refine ⟨74233580851440572380709015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49489053900960381587139343 74233580851440572380709015)
              ·
                refine ⟨111350371277160858571063523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74233580851440572380709015 111350371277160858571063523)
                ·
                  refine ⟨167025556915741287856595285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111350371277160858571063523 167025556915741287856595285)
                  ·
                    refine ⟨489332686276585804267369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 167025556915741287856595285 489332686276585804267369)
                    ·
                      refine ⟨366999514707439353200527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489332686276585804267369 366999514707439353200527)
                      ·
                        rfl

theorem cell23_714729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 10, 2].length) (baseStart_714729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714729 prefixEnd_714729 := by exact prefixLift 714729
  have htrace : WordTrace (prefixWord ++ tailWord_714729) baseStart_714729 baseEnd_714729 := by
    simpa [prefixWord, tailWord_714729, baseEnd_714729] using wordTrace_append hprefix tailTrace_714729
  have hstable : (prefixWord ++ tailWord_714729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714729).length < 2 ^ (prefixWord ++ tailWord_714729).sum := by decide
  have hdescent : baseEnd_714729 < baseStart_714729 := by decide
  rcases family_descends (prefixWord ++ tailWord_714729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714749 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_714749 : Nat := 118140960795 + 714749 * 2 ^ 59
def prefixEnd_714749 : Nat := 4983230072969 + 3 ^ 40 * 714749 * 2
def baseEnd_714749 : Nat := 367009784320529274950435

theorem tailTrace_714749 : CollatzResearch.WordTrace tailWord_714749 prefixEnd_714749 367009784320529274950435 := by
  unfold tailWord_714749
  simp only [CollatzResearch.WordTrace]
  refine ⟨26069037687593917255867301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17379358458395944837244867 26069037687593917255867301)
  ·
    refine ⟨4887944566423859485475119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26069037687593917255867301 4887944566423859485475119)
    ·
      refine ⟨7331916849635789228212679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4887944566423859485475119 7331916849635789228212679)
      ·
        refine ⟨10997875274453683842319019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7331916849635789228212679 10997875274453683842319019)
        ·
          refine ⟨16496812911680525763478529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10997875274453683842319019 16496812911680525763478529)
          ·
            refine ⟨12372609683760394322608897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16496812911680525763478529 12372609683760394322608897)
            ·
              refine ⟨9279457262820295741956673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12372609683760394322608897 9279457262820295741956673)
              ·
                refine ⟨6959592947115221806467505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9279457262820295741956673 6959592947115221806467505)
                ·
                  refine ⟨5219694710336416354850629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6959592947115221806467505 5219694710336416354850629)
                  ·
                    refine ⟨978692758188078066534493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5219694710336416354850629 978692758188078066534493)
                    ·
                      refine ⟨367009784320529274950435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 978692758188078066534493 367009784320529274950435)
                      ·
                        rfl

theorem cell23_714749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_714749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714749 prefixEnd_714749 := by exact prefixLift 714749
  have htrace : WordTrace (prefixWord ++ tailWord_714749) baseStart_714749 baseEnd_714749 := by
    simpa [prefixWord, tailWord_714749, baseEnd_714749] using wordTrace_append hprefix tailTrace_714749
  have hstable : (prefixWord ++ tailWord_714749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714749).length < 2 ^ (prefixWord ++ tailWord_714749).sum := by decide
  have hdescent : baseEnd_714749 < baseStart_714749 := by decide
  rcases family_descends (prefixWord ++ tailWord_714749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714750 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_714750 : Nat := 118140960795 + 714750 * 2 ^ 59
def prefixEnd_714750 : Nat := 4983230072969 + 3 ^ 40 * 714750 * 2
def baseEnd_714750 : Nat := 367010297801183771037931

theorem tailTrace_714750 : CollatzResearch.WordTrace tailWord_714750 prefixEnd_714750 367010297801183771037931 := by
  unfold tailWord_714750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258634270073786803331713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17379382773726862951102469 3258634270073786803331713)
  ·
    refine ⟨2443975702555340102498785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3258634270073786803331713 2443975702555340102498785)
    ·
      refine ⟨1832981776916505076874089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2443975702555340102498785 1832981776916505076874089)
      ·
        refine ⟨1374736332687378807655567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1832981776916505076874089 1374736332687378807655567)
        ·
          refine ⟨2062104499031068211483351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374736332687378807655567 2062104499031068211483351)
          ·
            refine ⟨3093156748546602317225027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062104499031068211483351 3093156748546602317225027)
            ·
              refine ⟨4639735122819903475837541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093156748546602317225027 4639735122819903475837541)
              ·
                refine ⟨869950335528731901719539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4639735122819903475837541 869950335528731901719539)
                ·
                  refine ⟨1304925503293097852579309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869950335528731901719539 1304925503293097852579309)
                  ·
                    refine ⟨489347063734911694717241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1304925503293097852579309 489347063734911694717241)
                    ·
                      refine ⟨367010297801183771037931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489347063734911694717241 367010297801183771037931)
                      ·
                        rfl

theorem cell23_714750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_714750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714750 prefixEnd_714750 := by exact prefixLift 714750
  have htrace : WordTrace (prefixWord ++ tailWord_714750) baseStart_714750 baseEnd_714750 := by
    simpa [prefixWord, tailWord_714750, baseEnd_714750] using wordTrace_append hprefix tailTrace_714750
  have hstable : (prefixWord ++ tailWord_714750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714750).length < 2 ^ (prefixWord ++ tailWord_714750).sum := by decide
  have hdescent : baseEnd_714750 < baseStart_714750 := by decide
  rcases family_descends (prefixWord ++ tailWord_714750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714752 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 9]
def baseStart_714752 : Nat := 118140960795 + 714752 * 2 ^ 59
def prefixEnd_714752 : Nat := 4983230072969 + 3 ^ 40 * 714752 * 2
def baseEnd_714752 : Nat := 40779036084721418134769

theorem tailTrace_714752 : CollatzResearch.WordTrace tailWord_714752 prefixEnd_714752 40779036084721418134769 := by
  unfold tailWord_714752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13034573553291524384113255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17379431404388699178817673 13034573553291524384113255)
  ·
    refine ⟨19551860329937286576169883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13034573553291524384113255 19551860329937286576169883)
    ·
      refine ⟨29327790494905929864254825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19551860329937286576169883 29327790494905929864254825)
      ·
        refine ⟨21995842871179447398191119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29327790494905929864254825 21995842871179447398191119)
        ·
          refine ⟨32993764306769171097286679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21995842871179447398191119 32993764306769171097286679)
          ·
            refine ⟨49490646460153756645930019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32993764306769171097286679 49490646460153756645930019)
            ·
              refine ⟨74235969690230634968895029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49490646460153756645930019 74235969690230634968895029)
              ·
                refine ⟨6959622158459122028333909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74235969690230634968895029 6959622158459122028333909)
                ·
                  refine ⟨40779036084721418134769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6959622158459122028333909 40779036084721418134769)
                  ·
                    rfl

theorem cell23_714752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_714752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714752 prefixEnd_714752 := by exact prefixLift 714752
  have htrace : WordTrace (prefixWord ++ tailWord_714752) baseStart_714752 baseEnd_714752 := by
    simpa [prefixWord, tailWord_714752, baseEnd_714752] using wordTrace_append hprefix tailTrace_714752
  have hstable : (prefixWord ++ tailWord_714752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714752).length < 2 ^ (prefixWord ++ tailWord_714752).sum := by decide
  have hdescent : baseEnd_714752 < baseStart_714752 := by decide
  rcases family_descends (prefixWord ++ tailWord_714752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714779 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 3]
def baseStart_714779 : Nat := 118140960795 + 714779 * 2 ^ 59
def prefixEnd_714779 : Nat := 4983230072969 + 3 ^ 40 * 714779 * 2
def baseEnd_714779 : Nat := 367025188740164157575297

theorem tailTrace_714779 : CollatzResearch.WordTrace tailWord_714779 prefixEnd_714779 367025188740164157575297 := by
  unfold tailWord_714779
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070131877485232379459391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17380087918323488252972927 26070131877485232379459391)
  ·
    refine ⟨39105197816227848569189087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26070131877485232379459391 39105197816227848569189087)
    ·
      refine ⟨58657796724341772853783631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39105197816227848569189087 58657796724341772853783631)
      ·
        refine ⟨87986695086512659280675447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58657796724341772853783631 87986695086512659280675447)
        ·
          refine ⟨131980042629768988921013171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87986695086512659280675447 131980042629768988921013171)
          ·
            refine ⟨197970063944653483381519757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131980042629768988921013171 197970063944653483381519757)
            ·
              refine ⟨74238773979245056268069909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197970063944653483381519757 74238773979245056268069909)
              ·
                refine ⟨3479942530277112012565777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74238773979245056268069909 3479942530277112012565777)
                ·
                  refine ⟨2609956897707834009424333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3479942530277112012565777 2609956897707834009424333)
                  ·
                    refine ⟨978733836640437753534125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2609956897707834009424333 978733836640437753534125)
                    ·
                      refine ⟨367025188740164157575297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 978733836640437753534125 367025188740164157575297)
                      ·
                        rfl

theorem cell23_714779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 3].length) (baseStart_714779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714779 prefixEnd_714779 := by exact prefixLift 714779
  have htrace : WordTrace (prefixWord ++ tailWord_714779) baseStart_714779 baseEnd_714779 := by
    simpa [prefixWord, tailWord_714779, baseEnd_714779] using wordTrace_append hprefix tailTrace_714779
  have hstable : (prefixWord ++ tailWord_714779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714779).length < 2 ^ (prefixWord ++ tailWord_714779).sum := by decide
  have hdescent : baseEnd_714779 < baseStart_714779 := by decide
  rcases family_descends (prefixWord ++ tailWord_714779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714816 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 2, 5]
def baseStart_714816 : Nat := 118140960795 + 714816 * 2 ^ 59
def prefixEnd_714816 : Nat := 4983230072969 + 3 ^ 40 * 714816 * 2
def baseEnd_714816 : Nat := 122348062508126837604209

theorem tailTrace_714816 : CollatzResearch.WordTrace tailWord_714816 prefixEnd_714816 122348062508126837604209 := by
  unfold tailWord_714816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035740689175593849278151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17380987585567458465704201 13035740689175593849278151)
  ·
    refine ⟨19553611033763390773917227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13035740689175593849278151 19553611033763390773917227)
    ·
      refine ⟨29330416550645086160875841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553611033763390773917227 29330416550645086160875841)
      ·
        refine ⟨21997812412983814620656881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29330416550645086160875841 21997812412983814620656881)
        ·
          refine ⟨16498359309737860965492661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21997812412983814620656881 16498359309737860965492661)
          ·
            refine ⟨1546721185287924465514937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16498359309737860965492661 1546721185287924465514937)
            ·
              refine ⟨1160040888965943349136203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546721185287924465514937 1160040888965943349136203)
              ·
                refine ⟨1740061333448915023704305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160040888965943349136203 1740061333448915023704305)
                ·
                  refine ⟨1305046000086686267778229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740061333448915023704305 1305046000086686267778229)
                  ·
                    refine ⟨122348062508126837604209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1305046000086686267778229 122348062508126837604209)
                    ·
                      rfl

theorem cell23_714816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_714816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714816 prefixEnd_714816 := by exact prefixLift 714816
  have htrace : WordTrace (prefixWord ++ tailWord_714816) baseStart_714816 baseEnd_714816 := by
    simpa [prefixWord, tailWord_714816, baseEnd_714816] using wordTrace_append hprefix tailTrace_714816
  have hstable : (prefixWord ++ tailWord_714816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714816).length < 2 ^ (prefixWord ++ tailWord_714816).sum := by decide
  have hdescent : baseEnd_714816 < baseStart_714816 := by decide
  rcases family_descends (prefixWord ++ tailWord_714816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714849 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_714849 : Nat := 118140960795 + 714849 * 2 ^ 59
def prefixEnd_714849 : Nat := 4983230072969 + 3 ^ 40 * 714849 * 2
def baseEnd_714849 : Nat := 367061132385978883699975

theorem tailTrace_714849 : CollatzResearch.WordTrace tailWord_714849 prefixEnd_714849 367061132385978883699975 := by
  unfold tailWord_714849
  simp only [CollatzResearch.WordTrace]
  refine ⟨26072684987231634334507601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17381789991487756223005067 26072684987231634334507601)
  ·
    refine ⟨19554513740423725750880701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26072684987231634334507601 19554513740423725750880701)
    ·
      refine ⟨7332942652658897156580263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19554513740423725750880701 7332942652658897156580263)
      ·
        refine ⟨10999413978988345734870395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7332942652658897156580263 10999413978988345734870395)
        ·
          refine ⟨16499120968482518602305593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10999413978988345734870395 16499120968482518602305593)
          ·
            refine ⟨12374340726361888951729195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16499120968482518602305593 12374340726361888951729195)
            ·
              refine ⟨18561511089542833427593793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12374340726361888951729195 18561511089542833427593793)
              ·
                refine ⟨13921133317157125070695345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18561511089542833427593793 13921133317157125070695345)
                ·
                  refine ⟨10440849987867843803021509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13921133317157125070695345 10440849987867843803021509)
                  ·
                    refine ⟨1957659372725220713066533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10440849987867843803021509 1957659372725220713066533)
                    ·
                      refine ⟨367061132385978883699975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1957659372725220713066533 367061132385978883699975)
                      ·
                        rfl

theorem cell23_714849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_714849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714849 prefixEnd_714849 := by exact prefixLift 714849
  have htrace : WordTrace (prefixWord ++ tailWord_714849) baseStart_714849 baseEnd_714849 := by
    simpa [prefixWord, tailWord_714849, baseEnd_714849] using wordTrace_append hprefix tailTrace_714849
  have hstable : (prefixWord ++ tailWord_714849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714849).length < 2 ^ (prefixWord ++ tailWord_714849).sum := by decide
  have hdescent : baseEnd_714849 < baseStart_714849 := by decide
  rcases family_descends (prefixWord ++ tailWord_714849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714853 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 2, 4, 2]
def baseStart_714853 : Nat := 118140960795 + 714853 * 2 ^ 59
def prefixEnd_714853 : Nat := 4983230072969 + 3 ^ 40 * 714853 * 2
def baseEnd_714853 : Nat := 367063186308596868049957

theorem tailTrace_714853 : CollatzResearch.WordTrace tailWord_714853 prefixEnd_714853 367063186308596868049957 := by
  unfold tailWord_714853
  simp only [CollatzResearch.WordTrace]
  refine ⟨26072830879217143017653213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17381887252811428678435475 26072830879217143017653213)
  ·
    refine ⟨9777311579706428631619955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26072830879217143017653213 9777311579706428631619955)
    ·
      refine ⟨14665967369559642947429933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9777311579706428631619955 14665967369559642947429933)
      ·
        refine ⟨5499737763584866105286225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14665967369559642947429933 5499737763584866105286225)
        ·
          refine ⟨4124803322688649578964669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5499737763584866105286225 4124803322688649578964669)
          ·
            refine ⟨1546801246008243592111751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4124803322688649578964669 1546801246008243592111751)
            ·
              refine ⟨2320201869012365388167627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546801246008243592111751 2320201869012365388167627)
              ·
                refine ⟨3480302803518548082251441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320201869012365388167627 3480302803518548082251441)
                ·
                  refine ⟨2610227102638911061688581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3480302803518548082251441 2610227102638911061688581)
                  ·
                    refine ⟨489417581744795824066609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2610227102638911061688581 489417581744795824066609)
                    ·
                      refine ⟨367063186308596868049957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489417581744795824066609 367063186308596868049957)
                      ·
                        rfl

theorem cell23_714853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_714853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714853 prefixEnd_714853 := by exact prefixLift 714853
  have htrace : WordTrace (prefixWord ++ tailWord_714853) baseStart_714853 baseEnd_714853 := by
    simpa [prefixWord, tailWord_714853, baseEnd_714853] using wordTrace_append hprefix tailTrace_714853
  have hstable : (prefixWord ++ tailWord_714853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714853).length < 2 ^ (prefixWord ++ tailWord_714853).sum := by decide
  have hdescent : baseEnd_714853 < baseStart_714853 := by decide
  rcases family_descends (prefixWord ++ tailWord_714853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714870 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_714870 : Nat := 118140960795 + 714870 * 2 ^ 59
def prefixEnd_714870 : Nat := 4983230072969 + 3 ^ 40 * 714870 * 2
def baseEnd_714870 : Nat := 367071915479723301537379

theorem tailTrace_714870 : CollatzResearch.WordTrace tailWord_714870 prefixEnd_714870 367071915479723301537379 := by
  unfold tailWord_714870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629590682509722182563879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17382300613437036614014709 1629590682509722182563879)
  ·
    refine ⟨2444386023764583273845819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1629590682509722182563879 2444386023764583273845819)
    ·
      refine ⟨3666579035646874910768729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444386023764583273845819 3666579035646874910768729)
      ·
        refine ⟨2749934276735156183076547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3666579035646874910768729 2749934276735156183076547)
        ·
          refine ⟨4124901415102734274614821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749934276735156183076547 4124901415102734274614821)
          ·
            refine ⟨773419015331762676490279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4124901415102734274614821 773419015331762676490279)
            ·
              refine ⟨1160128522997644014735419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773419015331762676490279 1160128522997644014735419)
              ·
                refine ⟨1740192784496466022103129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160128522997644014735419 1740192784496466022103129)
                ·
                  refine ⟨1305144588372349516577347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740192784496466022103129 1305144588372349516577347)
                  ·
                    refine ⟨1957716882558524274866021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305144588372349516577347 1957716882558524274866021)
                    ·
                      refine ⟨367071915479723301537379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1957716882558524274866021 367071915479723301537379)
                      ·
                        rfl

theorem cell23_714870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_714870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714870 prefixEnd_714870 := by exact prefixLift 714870
  have htrace : WordTrace (prefixWord ++ tailWord_714870) baseStart_714870 baseEnd_714870 := by
    simpa [prefixWord, tailWord_714870, baseEnd_714870] using wordTrace_append hprefix tailTrace_714870
  have hstable : (prefixWord ++ tailWord_714870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714870).length < 2 ^ (prefixWord ++ tailWord_714870).sum := by decide
  have hdescent : baseEnd_714870 < baseStart_714870 := by decide
  rcases family_descends (prefixWord ++ tailWord_714870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714873 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 3]
def baseStart_714873 : Nat := 118140960795 + 714873 * 2 ^ 59
def prefixEnd_714873 : Nat := 4983230072969 + 3 ^ 40 * 714873 * 2
def baseEnd_714873 : Nat := 367073455921686789799865

theorem tailTrace_714873 : CollatzResearch.WordTrace tailWord_714873 prefixEnd_714873 367073455921686789799865 := by
  unfold tailWord_714873
  simp only [CollatzResearch.WordTrace]
  refine ⟨26073560339144686433381273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17382373559429790955587515 26073560339144686433381273)
  ·
    refine ⟨19555170254358514825035955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26073560339144686433381273 19555170254358514825035955)
    ·
      refine ⟨29332755381537772237553933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19555170254358514825035955 29332755381537772237553933)
      ·
        refine ⟨10999783268076664589082725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29332755381537772237553933 10999783268076664589082725)
        ·
          refine ⟨2062459362764374610453011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10999783268076664589082725 2062459362764374610453011)
          ·
            refine ⟨3093689044146561915679517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062459362764374610453011 3093689044146561915679517)
            ·
              refine ⟨1160133391554960718379819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3093689044146561915679517 1160133391554960718379819)
              ·
                refine ⟨1740200087332441077569729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160133391554960718379819 1740200087332441077569729)
                ·
                  refine ⟨1305150065499330808177297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740200087332441077569729 1305150065499330808177297)
                  ·
                    refine ⟨978862549124498106132973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1305150065499330808177297 978862549124498106132973)
                    ·
                      refine ⟨367073455921686789799865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 978862549124498106132973 367073455921686789799865)
                      ·
                        rfl

theorem cell23_714873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_714873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714873 prefixEnd_714873 := by exact prefixLift 714873
  have htrace : WordTrace (prefixWord ++ tailWord_714873) baseStart_714873 baseEnd_714873 := by
    simpa [prefixWord, tailWord_714873, baseEnd_714873] using wordTrace_append hprefix tailTrace_714873
  have hstable : (prefixWord ++ tailWord_714873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714873).length < 2 ^ (prefixWord ++ tailWord_714873).sum := by decide
  have hdescent : baseEnd_714873 < baseStart_714873 := by decide
  rcases family_descends (prefixWord ++ tailWord_714873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714913 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_714913 : Nat := 118140960795 + 714913 * 2 ^ 59
def prefixEnd_714913 : Nat := 4983230072969 + 3 ^ 40 * 714913 * 2
def baseEnd_714913 : Nat := 367093995147866633299681

theorem tailTrace_714913 : CollatzResearch.WordTrace tailWord_714913 prefixEnd_714913 367093995147866633299681 := by
  unfold tailWord_714913
  simp only [CollatzResearch.WordTrace]
  refine ⟨26075019258999773264837393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17383346172666515509891595 26075019258999773264837393)
  ·
    refine ⟨19556264444249829948628045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26075019258999773264837393 19556264444249829948628045)
    ·
      refine ⟨7333599166593686230735517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19556264444249829948628045 7333599166593686230735517)
      ·
        refine ⟨2750099687472632336525819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7333599166593686230735517 2750099687472632336525819)
        ·
          refine ⟨4125149531208948504788729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750099687472632336525819 4125149531208948504788729)
          ·
            refine ⟨3093862148406711378591547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125149531208948504788729 3093862148406711378591547)
            ·
              refine ⟨4640793222610067067887321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093862148406711378591547 4640793222610067067887321)
              ·
                refine ⟨3480594916957550300915491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4640793222610067067887321 3480594916957550300915491)
                ·
                  refine ⟨5220892375436325451373237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480594916957550300915491 5220892375436325451373237)
                  ·
                    refine ⟨489458660197155511066241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5220892375436325451373237 489458660197155511066241)
                    ·
                      refine ⟨367093995147866633299681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489458660197155511066241 367093995147866633299681)
                      ·
                        rfl

theorem cell23_714913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_714913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714913 prefixEnd_714913 := by exact prefixLift 714913
  have htrace : WordTrace (prefixWord ++ tailWord_714913) baseStart_714913 baseEnd_714913 := by
    simpa [prefixWord, tailWord_714913, baseEnd_714913] using wordTrace_append hprefix tailTrace_714913
  have hstable : (prefixWord ++ tailWord_714913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714913).length < 2 ^ (prefixWord ++ tailWord_714913).sum := by decide
  have hdescent : baseEnd_714913 < baseStart_714913 := by decide
  rcases family_descends (prefixWord ++ tailWord_714913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714936 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 6, 4]
def baseStart_714936 : Nat := 118140960795 + 714936 * 2 ^ 59
def prefixEnd_714936 : Nat := 4983230072969 + 3 ^ 40 * 714936 * 2
def baseEnd_714936 : Nat := 122368601734306681104025

theorem tailTrace_714936 : CollatzResearch.WordTrace tailWord_714936 prefixEnd_714936 122368601734306681104025 := by
  unfold tailWord_714936
  simp only [CollatzResearch.WordTrace]
  refine ⟨13037929068958224096462331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17383905425277632128616441 13037929068958224096462331)
  ·
    refine ⟨19556893603437336144693497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13037929068958224096462331 19556893603437336144693497)
    ·
      refine ⟨14667670202578002108520123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19556893603437336144693497 14667670202578002108520123)
      ·
        refine ⟨22001505303867003162780185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14667670202578002108520123 22001505303867003162780185)
        ·
          refine ⟨16501128977900252372085139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22001505303867003162780185 16501128977900252372085139)
          ·
            refine ⟨24751693466850378558127709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16501128977900252372085139 24751693466850378558127709)
            ·
              refine ⟨9281885050068891959297891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24751693466850378558127709 9281885050068891959297891)
              ·
                refine ⟨13922827575103337938946837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9281885050068891959297891 13922827575103337938946837)
                ·
                  refine ⟨652632542582968965888133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13922827575103337938946837 652632542582968965888133)
                  ·
                    refine ⟨122368601734306681104025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652632542582968965888133 122368601734306681104025)
                    ·
                      rfl

theorem cell23_714936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_714936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714936 prefixEnd_714936 := by exact prefixLift 714936
  have htrace : WordTrace (prefixWord ++ tailWord_714936) baseStart_714936 baseEnd_714936 := by
    simpa [prefixWord, tailWord_714936, baseEnd_714936] using wordTrace_append hprefix tailTrace_714936
  have hstable : (prefixWord ++ tailWord_714936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714936).length < 2 ^ (prefixWord ++ tailWord_714936).sum := by decide
  have hdescent : baseEnd_714936 < baseStart_714936 := by decide
  rcases family_descends (prefixWord ++ tailWord_714936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714949 : List Nat := [1, 3, 1, 1, 1, 1, 15]
def baseStart_714949 : Nat := 118140960795 + 714949 * 2 ^ 59
def prefixEnd_714949 : Nat := 4983230072969 + 3 ^ 40 * 714949 * 2
def baseEnd_714949 : Nat := 4532252845079364104315

theorem tailTrace_714949 : CollatzResearch.WordTrace tailWord_714949 prefixEnd_714949 4532252845079364104315 := by
  unfold tailWord_714949
  simp only [CollatzResearch.WordTrace]
  refine ⟨26076332286869351413147901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17384221524579567608765267 26076332286869351413147901)
  ·
    refine ⟨9778624607576006779930463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26076332286869351413147901 9778624607576006779930463)
    ·
      refine ⟨14667936911364010169895695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9778624607576006779930463 14667936911364010169895695)
      ·
        refine ⟨22001905367046015254843543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14667936911364010169895695 22001905367046015254843543)
        ·
          refine ⟨33002858050569022882265315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22001905367046015254843543 33002858050569022882265315)
          ·
            refine ⟨49504287075853534323397973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33002858050569022882265315 49504287075853534323397973)
            ·
              refine ⟨4532252845079364104315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 49504287075853534323397973 4532252845079364104315)
              ·
                rfl

theorem cell23_714949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 15].length) (baseStart_714949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714949 prefixEnd_714949 := by exact prefixLift 714949
  have htrace : WordTrace (prefixWord ++ tailWord_714949) baseStart_714949 baseEnd_714949 := by
    simpa [prefixWord, tailWord_714949, baseEnd_714949] using wordTrace_append hprefix tailTrace_714949
  have hstable : (prefixWord ++ tailWord_714949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714949).length < 2 ^ (prefixWord ++ tailWord_714949).sum := by decide
  have hdescent : baseEnd_714949 < baseStart_714949 := by decide
  rcases family_descends (prefixWord ++ tailWord_714949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714970 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_714970 : Nat := 118140960795 + 714970 * 2 ^ 59
def prefixEnd_714970 : Nat := 4983230072969 + 3 ^ 40 * 714970 * 2
def baseEnd_714970 : Nat := 122374421181724303428973

theorem tailTrace_714970 : CollatzResearch.WordTrace tailWord_714970 prefixEnd_714970 122374421181724303428973 := by
  unfold tailWord_714970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519274554948317999915591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17384732146528847999774909 6519274554948317999915591)
  ·
    refine ⟨9778911832422476999873387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6519274554948317999915591 9778911832422476999873387)
    ·
      refine ⟨14668367748633715499810081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9778911832422476999873387 14668367748633715499810081)
      ·
        refine ⟨11001275811475286624857561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14668367748633715499810081 11001275811475286624857561)
        ·
          refine ⟨8250956858606464968643171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11001275811475286624857561 8250956858606464968643171)
          ·
            refine ⟨12376435287909697452964757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8250956858606464968643171 12376435287909697452964757)
            ·
              refine ⟨580145404120767068107723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12376435287909697452964757 580145404120767068107723)
              ·
                refine ⟨870218106181150602161585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580145404120767068107723 870218106181150602161585)
                ·
                  refine ⟨652663579635862951621189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 870218106181150602161585 652663579635862951621189)
                  ·
                    refine ⟨122374421181724303428973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652663579635862951621189 122374421181724303428973)
                    ·
                      rfl

theorem cell23_714970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_714970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714970 prefixEnd_714970 := by exact prefixLift 714970
  have htrace : WordTrace (prefixWord ++ tailWord_714970) baseStart_714970 baseEnd_714970 := by
    simpa [prefixWord, tailWord_714970, baseEnd_714970] using wordTrace_append hprefix tailTrace_714970
  have hstable : (prefixWord ++ tailWord_714970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714970).length < 2 ^ (prefixWord ++ tailWord_714970).sum := by decide
  have hdescent : baseEnd_714970 < baseStart_714970 := by decide
  rcases family_descends (prefixWord ++ tailWord_714970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714973 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_714973 : Nat := 118140960795 + 714973 * 2 ^ 59
def prefixEnd_714973 : Nat := 4983230072969 + 3 ^ 40 * 714973 * 2
def baseEnd_714973 : Nat := 367124803987136398549405

theorem tailTrace_714973 : CollatzResearch.WordTrace tailWord_714973 prefixEnd_714973 367124803987136398549405 := by
  unfold tailWord_714973
  simp only [CollatzResearch.WordTrace]
  refine ⟨26077207638782403512021573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17384805092521602341347715 26077207638782403512021573)
  ·
    refine ⟨4889476432271700658504045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26077207638782403512021573 4889476432271700658504045)
    ·
      refine ⟨1833553662101887746939017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4889476432271700658504045 1833553662101887746939017)
      ·
        refine ⟨1375165246576415810204263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1833553662101887746939017 1375165246576415810204263)
        ·
          refine ⟨2062747869864623715306395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375165246576415810204263 2062747869864623715306395)
          ·
            refine ⟨3094121804796935572959593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2062747869864623715306395 3094121804796935572959593)
            ·
              refine ⟨2320591353597701679719695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094121804796935572959593 2320591353597701679719695)
              ·
                refine ⟨3480887030396552519579543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320591353597701679719695 3480887030396552519579543)
                ·
                  refine ⟨5221330545594828779369315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3480887030396552519579543 5221330545594828779369315)
                  ·
                    refine ⟨7831995818392243169053973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5221330545594828779369315 7831995818392243169053973)
                    ·
                      refine ⟨367124803987136398549405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7831995818392243169053973 367124803987136398549405)
                      ·
                        rfl

theorem cell23_714973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_714973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714973 prefixEnd_714973 := by exact prefixLift 714973
  have htrace : WordTrace (prefixWord ++ tailWord_714973) baseStart_714973 baseEnd_714973 := by
    simpa [prefixWord, tailWord_714973, baseEnd_714973] using wordTrace_append hprefix tailTrace_714973
  have hstable : (prefixWord ++ tailWord_714973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714973).length < 2 ^ (prefixWord ++ tailWord_714973).sum := by decide
  have hdescent : baseEnd_714973 < baseStart_714973 := by decide
  rcases family_descends (prefixWord ++ tailWord_714973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714993 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_714993 : Nat := 118140960795 + 714993 * 2 ^ 59
def prefixEnd_714993 : Nat := 4983230072969 + 3 ^ 40 * 714993 * 2
def baseEnd_714993 : Nat := 367135073600226320299313

theorem tailTrace_714993 : CollatzResearch.WordTrace tailWord_714993 prefixEnd_714993 367135073600226320299313 := by
  unfold tailWord_714993
  simp only [CollatzResearch.WordTrace]
  refine ⟨26077937098709946927749633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17385291399139964618499755 26077937098709946927749633)
  ·
    refine ⟨19558452824032460195812225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26077937098709946927749633 19558452824032460195812225)
    ·
      refine ⟨14668839618024345146859169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19558452824032460195812225 14668839618024345146859169)
      ·
        refine ⟨11001629713518258860144377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14668839618024345146859169 11001629713518258860144377)
        ·
          refine ⟨8251222285138694145108283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11001629713518258860144377 8251222285138694145108283)
          ·
            refine ⟨12376833427708041217662425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251222285138694145108283 12376833427708041217662425)
            ·
              refine ⟨9282625070781030913246819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12376833427708041217662425 9282625070781030913246819)
              ·
                refine ⟨13923937606171546369870229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9282625070781030913246819 13923937606171546369870229)
                ·
                  refine ⟨652684575289291236087667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13923937606171546369870229 652684575289291236087667)
                  ·
                    refine ⟨979026862933936854131501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 652684575289291236087667 979026862933936854131501)
                    ·
                      refine ⟨367135073600226320299313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979026862933936854131501 367135073600226320299313)
                      ·
                        rfl

theorem cell23_714993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_714993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_714993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_714993 prefixEnd_714993 := by exact prefixLift 714993
  have htrace : WordTrace (prefixWord ++ tailWord_714993) baseStart_714993 baseEnd_714993 := by
    simpa [prefixWord, tailWord_714993, baseEnd_714993] using wordTrace_append hprefix tailTrace_714993
  have hstable : (prefixWord ++ tailWord_714993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714993).length < 2 ^ (prefixWord ++ tailWord_714993).sum := by decide
  have hdescent : baseEnd_714993 < baseStart_714993 := by decide
  rcases family_descends (prefixWord ++ tailWord_714993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715084 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 2, 2, 2]
def baseStart_715084 : Nat := 118140960795 + 715084 * 2 ^ 59
def prefixEnd_715084 : Nat := 4983230072969 + 3 ^ 40 * 715084 * 2
def baseEnd_715084 : Nat := 367181800339785464261395

theorem tailTrace_715084 : CollatzResearch.WordTrace tailWord_715084 prefixEnd_715084 367181800339785464261395 := by
  unfold tailWord_715084
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040628070690134734656153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17387504094253512979541537 13040628070690134734656153)
  ·
    refine ⟨9780471053017601050992115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13040628070690134734656153 9780471053017601050992115)
    ·
      refine ⟨14670706579526401576488173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9780471053017601050992115 14670706579526401576488173)
      ·
        refine ⟨5501514967322400591183065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14670706579526401576488173 5501514967322400591183065)
        ·
          refine ⟨4126136225491800443387299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5501514967322400591183065 4126136225491800443387299)
          ·
            refine ⟨6189204338237700665080949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4126136225491800443387299 6189204338237700665080949)
            ·
              refine ⟨580237906709784437351339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6189204338237700665080949 580237906709784437351339)
              ·
                refine ⟨870356860064676656027009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580237906709784437351339 870356860064676656027009)
                ·
                  refine ⟨652767645048507492020257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 870356860064676656027009 652767645048507492020257)
                  ·
                    refine ⟨489575733786380619015193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 652767645048507492020257 489575733786380619015193)
                    ·
                      refine ⟨367181800339785464261395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489575733786380619015193 367181800339785464261395)
                      ·
                        rfl

theorem cell23_715084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_715084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715084 prefixEnd_715084 := by exact prefixLift 715084
  have htrace : WordTrace (prefixWord ++ tailWord_715084) baseStart_715084 baseEnd_715084 := by
    simpa [prefixWord, tailWord_715084, baseEnd_715084] using wordTrace_append hprefix tailTrace_715084
  have hstable : (prefixWord ++ tailWord_715084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715084).length < 2 ^ (prefixWord ++ tailWord_715084).sum := by decide
  have hdescent : baseEnd_715084 < baseStart_715084 := by decide
  rcases family_descends (prefixWord ++ tailWord_715084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715096 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_715096 : Nat := 118140960795 + 715096 * 2 ^ 59
def prefixEnd_715096 : Nat := 4983230072969 + 3 ^ 40 * 715096 * 2
def baseEnd_715096 : Nat := 367187962107639417311339

theorem tailTrace_715096 : CollatzResearch.WordTrace tailWord_715096 prefixEnd_715096 367187962107639417311339 := by
  unfold tailWord_715096
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040846908668397759374571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17387795878224530345832761 13040846908668397759374571)
  ·
    refine ⟨19561270363002596639061857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13040846908668397759374571 19561270363002596639061857)
    ·
      refine ⟨14670952772251947479296393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19561270363002596639061857 14670952772251947479296393)
      ·
        refine ⟨11003214579188960609472295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14670952772251947479296393 11003214579188960609472295)
        ·
          refine ⟨16504821868783440914208443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11003214579188960609472295 16504821868783440914208443)
          ·
            refine ⟨24757232803175161371312665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16504821868783440914208443 24757232803175161371312665)
            ·
              refine ⟨18567924602381371028484499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24757232803175161371312665 18567924602381371028484499)
              ·
                refine ⟨27851886903572056542726749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18567924602381371028484499 27851886903572056542726749)
                ·
                  refine ⟨10444457588839521203522531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27851886903572056542726749 10444457588839521203522531)
                  ·
                    refine ⟨15666686383259281805283797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10444457588839521203522531 15666686383259281805283797)
                    ·
                      refine ⟨367187962107639417311339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15666686383259281805283797 367187962107639417311339)
                      ·
                        rfl

theorem cell23_715096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_715096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715096 prefixEnd_715096 := by exact prefixLift 715096
  have htrace : WordTrace (prefixWord ++ tailWord_715096) baseStart_715096 baseEnd_715096 := by
    simpa [prefixWord, tailWord_715096, baseEnd_715096] using wordTrace_append hprefix tailTrace_715096
  have hstable : (prefixWord ++ tailWord_715096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715096).length < 2 ^ (prefixWord ++ tailWord_715096).sum := by decide
  have hdescent : baseEnd_715096 < baseStart_715096 := by decide
  rcases family_descends (prefixWord ++ tailWord_715096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715123 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 4]
def baseStart_715123 : Nat := 118140960795 + 715123 * 2 ^ 59
def prefixEnd_715123 : Nat := 4983230072969 + 3 ^ 40 * 715123 * 2
def baseEnd_715123 : Nat := 367201826085310811673715

theorem tailTrace_715123 : CollatzResearch.WordTrace tailWord_715123 prefixEnd_715123 367201826085310811673715 := by
  unfold tailWord_715123
  simp only [CollatzResearch.WordTrace]
  refine ⟨26082678588238979129982023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17388452392159319419988015 26082678588238979129982023)
  ·
    refine ⟨39124017882358468694973035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26082678588238979129982023 39124017882358468694973035)
    ·
      refine ⟨58686026823537703042459553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39124017882358468694973035 58686026823537703042459553)
      ·
        refine ⟨44014520117653277281844665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58686026823537703042459553 44014520117653277281844665)
        ·
          refine ⟨33010890088239957961383499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44014520117653277281844665 33010890088239957961383499)
          ·
            refine ⟨49516335132359936942075249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33010890088239957961383499 49516335132359936942075249)
            ·
              refine ⟨37137251349269952706556437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49516335132359936942075249 37137251349269952706556437)
              ·
                refine ⟨1740808656997029033119833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37137251349269952706556437 1740808656997029033119833)
                ·
                  refine ⟨1305606492747771774839875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740808656997029033119833 1305606492747771774839875)
                  ·
                    refine ⟨1958409739121657662259813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1305606492747771774839875 1958409739121657662259813)
                    ·
                      refine ⟨367201826085310811673715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1958409739121657662259813 367201826085310811673715)
                      ·
                        rfl

theorem cell23_715123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_715123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715123 prefixEnd_715123 := by exact prefixLift 715123
  have htrace : WordTrace (prefixWord ++ tailWord_715123) baseStart_715123 baseEnd_715123 := by
    simpa [prefixWord, tailWord_715123, baseEnd_715123] using wordTrace_append hprefix tailTrace_715123
  have hstable : (prefixWord ++ tailWord_715123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715123).length < 2 ^ (prefixWord ++ tailWord_715123).sum := by decide
  have hdescent : baseEnd_715123 < baseStart_715123 := by decide
  rcases family_descends (prefixWord ++ tailWord_715123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715140 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_715140 : Nat := 118140960795 + 715140 * 2 ^ 59
def prefixEnd_715140 : Nat := 4983230072969 + 3 ^ 40 * 715140 * 2
def baseEnd_715140 : Nat := 367210555256437245161137

theorem tailTrace_715140 : CollatzResearch.WordTrace tailWord_715140 prefixEnd_715140 367210555256437245161137 := by
  unfold tailWord_715140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041649314588695516675437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17388865752784927355567249 13041649314588695516675437)
  ·
    refine ⟨4890618492970760818753289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13041649314588695516675437 4890618492970760818753289)
    ·
      refine ⟨3667963869728070614064967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4890618492970760818753289 3667963869728070614064967)
      ·
        refine ⟨5501945804592105921097451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3667963869728070614064967 5501945804592105921097451)
        ·
          refine ⟨8252918706888158881646177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5501945804592105921097451 8252918706888158881646177)
          ·
            refine ⟨6189689030166119161234633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8252918706888158881646177 6189689030166119161234633)
            ·
              refine ⟨4642266772624589370925975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6189689030166119161234633 4642266772624589370925975)
              ·
                refine ⟨6963400158936884056388963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642266772624589370925975 6963400158936884056388963)
                ·
                  refine ⟨10445100238405326084583445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6963400158936884056388963 10445100238405326084583445)
                  ·
                    refine ⟨489614073675249660214849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10445100238405326084583445 489614073675249660214849)
                    ·
                      refine ⟨367210555256437245161137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489614073675249660214849 367210555256437245161137)
                      ·
                        rfl

theorem cell23_715140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_715140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715140 prefixEnd_715140 := by exact prefixLift 715140
  have htrace : WordTrace (prefixWord ++ tailWord_715140) baseStart_715140 baseEnd_715140 := by
    simpa [prefixWord, tailWord_715140, baseEnd_715140] using wordTrace_append hprefix tailTrace_715140
  have hstable : (prefixWord ++ tailWord_715140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715140).length < 2 ^ (prefixWord ++ tailWord_715140).sum := by decide
  have hdescent : baseEnd_715140 < baseStart_715140 := by decide
  rcases family_descends (prefixWord ++ tailWord_715140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715167 : List Nat := [1, 1, 2, 5, 1, 1, 2, 5, 1, 4]
def baseStart_715167 : Nat := 118140960795 + 715167 * 2 ^ 59
def prefixEnd_715167 : Nat := 4983230072969 + 3 ^ 40 * 715167 * 2
def baseEnd_715167 : Nat := 122408139744702879841171

theorem tailTrace_715167 : CollatzResearch.WordTrace tailWord_715167 prefixEnd_715167 122408139744702879841171 := by
  unfold tailWord_715167
  simp only [CollatzResearch.WordTrace]
  refine ⟨26084283400079574644583755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17389522266719716429722503 26084283400079574644583755)
  ·
    refine ⟨39126425100119361966875633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26084283400079574644583755 39126425100119361966875633)
    ·
      refine ⟨29344818825089521475156725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39126425100119361966875633 29344818825089521475156725)
      ·
        refine ⟨2751076764852142638295943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29344818825089521475156725 2751076764852142638295943)
        ·
          refine ⟨4126615147278213957443915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751076764852142638295943 4126615147278213957443915)
          ·
            refine ⟨6189922720917320936165873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4126615147278213957443915 6189922720917320936165873)
            ·
              refine ⟨4642442040687990702124405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6189922720917320936165873 4642442040687990702124405)
              ·
                refine ⟨435228941314499128324163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4642442040687990702124405 435228941314499128324163)
                ·
                  refine ⟨652843411971748692486245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435228941314499128324163 652843411971748692486245)
                  ·
                    refine ⟨122408139744702879841171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652843411971748692486245 122408139744702879841171)
                    ·
                      rfl

theorem cell23_715167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 4].length) (baseStart_715167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715167 prefixEnd_715167 := by exact prefixLift 715167
  have htrace : WordTrace (prefixWord ++ tailWord_715167) baseStart_715167 baseEnd_715167 := by
    simpa [prefixWord, tailWord_715167, baseEnd_715167] using wordTrace_append hprefix tailTrace_715167
  have hstable : (prefixWord ++ tailWord_715167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715167).length < 2 ^ (prefixWord ++ tailWord_715167).sum := by decide
  have hdescent : baseEnd_715167 < baseStart_715167 := by decide
  rcases family_descends (prefixWord ++ tailWord_715167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715200 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 1, 5, 2]
def baseStart_715200 : Nat := 118140960795 + 715200 * 2 ^ 59
def prefixEnd_715200 : Nat := 4983230072969 + 3 ^ 40 * 715200 * 2
def baseEnd_715200 : Nat := 367241364095707010410861

theorem tailTrace_715200 : CollatzResearch.WordTrace tailWord_715200 prefixEnd_715200 367241364095707010410861 := by
  unfold tailWord_715200
  simp only [CollatzResearch.WordTrace]
  refine ⟨13042743504480010640267527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17390324672640014187023369 13042743504480010640267527)
  ·
    refine ⟨19564115256720015960401291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13042743504480010640267527 19564115256720015960401291)
    ·
      refine ⟨29346172885080023940601937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19564115256720015960401291 29346172885080023940601937)
      ·
        refine ⟨22009629663810017955451453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29346172885080023940601937 22009629663810017955451453)
        ·
          refine ⟨8253611123928756733294295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22009629663810017955451453 8253611123928756733294295)
          ·
            refine ⟨12380416685893135099941443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8253611123928756733294295 12380416685893135099941443)
            ·
              refine ⟨18570625028839702649912165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12380416685893135099941443 18570625028839702649912165)
              ·
                refine ⟨3481992192907444246858531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18570625028839702649912165 3481992192907444246858531)
                ·
                  refine ⟨5222988289361166370287797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3481992192907444246858531 5222988289361166370287797)
                  ·
                    refine ⟨489655152127609347214481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5222988289361166370287797 489655152127609347214481)
                    ·
                      refine ⟨367241364095707010410861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489655152127609347214481 367241364095707010410861)
                      ·
                        rfl

theorem cell23_715200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_715200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715200 prefixEnd_715200 := by exact prefixLift 715200
  have htrace : WordTrace (prefixWord ++ tailWord_715200) baseStart_715200 baseEnd_715200 := by
    simpa [prefixWord, tailWord_715200, baseEnd_715200] using wordTrace_append hprefix tailTrace_715200
  have hstable : (prefixWord ++ tailWord_715200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715200).length < 2 ^ (prefixWord ++ tailWord_715200).sum := by decide
  have hdescent : baseEnd_715200 < baseStart_715200 := by decide
  rcases family_descends (prefixWord ++ tailWord_715200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715201 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 3, 4]
def baseStart_715201 : Nat := 118140960795 + 715201 * 2 ^ 59
def prefixEnd_715201 : Nat := 4983230072969 + 3 ^ 40 * 715201 * 2
def baseEnd_715201 : Nat := 122413959192120502166119

theorem tailTrace_715201 : CollatzResearch.WordTrace tailWord_715201 prefixEnd_715201 122413959192120502166119 := by
  unfold tailWord_715201
  simp only [CollatzResearch.WordTrace]
  refine ⟨26085523481956398451321457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17390348987970932300880971 26085523481956398451321457)
  ·
    refine ⟨19564142611467298838491093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26085523481956398451321457 19564142611467298838491093)
    ·
      refine ⟨458534592456264816527135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19564142611467298838491093 458534592456264816527135)
      ·
        refine ⟨687801888684397224790703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458534592456264816527135 687801888684397224790703)
        ·
          refine ⟨1031702833026595837186055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687801888684397224790703 1031702833026595837186055)
          ·
            refine ⟨1547554249539893755779083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031702833026595837186055 1547554249539893755779083)
            ·
              refine ⟨2321331374309840633668625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547554249539893755779083 2321331374309840633668625)
              ·
                refine ⟨1740998530732380475251469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321331374309840633668625 1740998530732380475251469)
                ·
                  refine ⟨652874449024642678219301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1740998530732380475251469 652874449024642678219301)
                  ·
                    refine ⟨122413959192120502166119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652874449024642678219301 122413959192120502166119)
                    ·
                      rfl

theorem cell23_715201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_715201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715201 prefixEnd_715201 := by exact prefixLift 715201
  have htrace : WordTrace (prefixWord ++ tailWord_715201) baseStart_715201 baseEnd_715201 := by
    simpa [prefixWord, tailWord_715201, baseEnd_715201] using wordTrace_append hprefix tailTrace_715201
  have hstable : (prefixWord ++ tailWord_715201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715201).length < 2 ^ (prefixWord ++ tailWord_715201).sum := by decide
  have hdescent : baseEnd_715201 < baseStart_715201 := by decide
  rcases family_descends (prefixWord ++ tailWord_715201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715207 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_715207 : Nat := 118140960795 + 715207 * 2 ^ 59
def prefixEnd_715207 : Nat := 4983230072969 + 3 ^ 40 * 715207 * 2
def baseEnd_715207 : Nat := 367244958460288483023329

theorem tailTrace_715207 : CollatzResearch.WordTrace tailWord_715207 prefixEnd_715207 367244958460288483023329 := by
  unfold tailWord_715207
  simp only [CollatzResearch.WordTrace]
  refine ⟨26085742319934661476039875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17390494879956440984026583 26085742319934661476039875)
  ·
    refine ⟨39128613479901992214059813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26085742319934661476039875 39128613479901992214059813)
    ·
      refine ⟨7336615027481623540136215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39128613479901992214059813 7336615027481623540136215)
      ·
        refine ⟨11004922541222435310204323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7336615027481623540136215 11004922541222435310204323)
        ·
          refine ⟨16507383811833652965306485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11004922541222435310204323 16507383811833652965306485)
          ·
            refine ⟨1547567232359404965497483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16507383811833652965306485 1547567232359404965497483)
            ·
              refine ⟨2321350848539107448246225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547567232359404965497483 2321350848539107448246225)
              ·
                refine ⟨1741013136404330586184669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2321350848539107448246225 1741013136404330586184669)
                ·
                  refine ⟨652879926151623969819251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1741013136404330586184669 652879926151623969819251)
                  ·
                    refine ⟨979319889227435954728877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 652879926151623969819251 979319889227435954728877)
                    ·
                      refine ⟨367244958460288483023329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979319889227435954728877 367244958460288483023329)
                      ·
                        rfl

theorem cell23_715207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_715207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715207 prefixEnd_715207 := by exact prefixLift 715207
  have htrace : WordTrace (prefixWord ++ tailWord_715207) baseStart_715207 baseEnd_715207 := by
    simpa [prefixWord, tailWord_715207, baseEnd_715207] using wordTrace_append hprefix tailTrace_715207
  have hstable : (prefixWord ++ tailWord_715207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715207).length < 2 ^ (prefixWord ++ tailWord_715207).sum := by decide
  have hdescent : baseEnd_715207 < baseStart_715207 := by decide
  rcases family_descends (prefixWord ++ tailWord_715207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715210 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_715210 : Nat := 118140960795 + 715210 * 2 ^ 59
def prefixEnd_715210 : Nat := 4983230072969 + 3 ^ 40 * 715210 * 2
def baseEnd_715210 : Nat := 122415499634083990428605

theorem tailTrace_715210 : CollatzResearch.WordTrace tailWord_715210 prefixEnd_715210 122415499634083990428605 := by
  unfold tailWord_715210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521462934730948247099771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17390567825949195325599389 6521462934730948247099771)
  ·
    refine ⟨9782194402096422370649657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6521462934730948247099771 9782194402096422370649657)
    ·
      refine ⟨7336645801572316777987243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9782194402096422370649657 7336645801572316777987243)
      ·
        refine ⟨11004968702358475166980865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7336645801572316777987243 11004968702358475166980865)
        ·
          refine ⟨8253726526768856375235649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11004968702358475166980865 8253726526768856375235649)
          ·
            refine ⟨6190294895076642281426737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8253726526768856375235649 6190294895076642281426737)
            ·
              refine ⟨4642721171307481711070053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6190294895076642281426737 4642721171307481711070053)
              ·
                refine ⟨870510219620152820825635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4642721171307481711070053 870510219620152820825635)
                ·
                  refine ⟨1305765329430229231238453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870510219620152820825635 1305765329430229231238453)
                  ·
                    refine ⟨122415499634083990428605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1305765329430229231238453 122415499634083990428605)
                    ·
                      rfl

theorem cell23_715210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_715210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715210 prefixEnd_715210 := by exact prefixLift 715210
  have htrace : WordTrace (prefixWord ++ tailWord_715210) baseStart_715210 baseEnd_715210 := by
    simpa [prefixWord, tailWord_715210, baseEnd_715210] using wordTrace_append hprefix tailTrace_715210
  have hstable : (prefixWord ++ tailWord_715210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715210).length < 2 ^ (prefixWord ++ tailWord_715210).sum := by decide
  have hdescent : baseEnd_715210 < baseStart_715210 := by decide
  rcases family_descends (prefixWord ++ tailWord_715210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715243 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6]
def baseStart_715243 : Nat := 118140960795 + 715243 * 2 ^ 59
def prefixEnd_715243 : Nat := 4983230072969 + 3 ^ 40 * 715243 * 2
def baseEnd_715243 : Nat := 367263443763850342173163

theorem tailTrace_715243 : CollatzResearch.WordTrace tailWord_715243 prefixEnd_715243 367263443763850342173163 := by
  unfold tailWord_715243
  simp only [CollatzResearch.WordTrace]
  refine ⟨26087055347804239624350383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17391370231869493082900255 26087055347804239624350383)
  ·
    refine ⟨39130583021706359436525575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26087055347804239624350383 39130583021706359436525575)
    ·
      refine ⟨58695874532559539154788363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39130583021706359436525575 58695874532559539154788363)
      ·
        refine ⟨88043811798839308732182545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58695874532559539154788363 88043811798839308732182545)
        ·
          refine ⟨66032858849129481549136909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88043811798839308732182545 66032858849129481549136909)
          ·
            refine ⟨24762322068423555580926341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66032858849129481549136909 24762322068423555580926341)
            ·
              refine ⟨4642935387829416671423689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24762322068423555580926341 4642935387829416671423689)
              ·
                refine ⟨3482201540872062503567767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4642935387829416671423689 3482201540872062503567767)
                ·
                  refine ⟨5223302311308093755351651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3482201540872062503567767 5223302311308093755351651)
                  ·
                    refine ⟨7834953466962140633027477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5223302311308093755351651 7834953466962140633027477)
                    ·
                      refine ⟨367263443763850342173163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7834953466962140633027477 367263443763850342173163)
                      ·
                        rfl

theorem cell23_715243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_715243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715243 prefixEnd_715243 := by exact prefixLift 715243
  have htrace : WordTrace (prefixWord ++ tailWord_715243) baseStart_715243 baseEnd_715243 := by
    simpa [prefixWord, tailWord_715243, baseEnd_715243] using wordTrace_append hprefix tailTrace_715243
  have hstable : (prefixWord ++ tailWord_715243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715243).length < 2 ^ (prefixWord ++ tailWord_715243).sum := by decide
  have hdescent : baseEnd_715243 < baseStart_715243 := by decide
  rcases family_descends (prefixWord ++ tailWord_715243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715267 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 3]
def baseStart_715267 : Nat := 118140960795 + 715267 * 2 ^ 59
def prefixEnd_715267 : Nat := 4983230072969 + 3 ^ 40 * 715267 * 2
def baseEnd_715267 : Nat := 367275767299558248273053

theorem tailTrace_715267 : CollatzResearch.WordTrace tailWord_715267 prefixEnd_715267 367275767299558248273053 := by
  unfold tailWord_715267
  simp only [CollatzResearch.WordTrace]
  refine ⟨26087930699717291723224055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17391953799811527815482703 26087930699717291723224055)
  ·
    refine ⟨39131896049575937584836083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26087930699717291723224055 39131896049575937584836083)
    ·
      refine ⟨58697844074363906377254125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39131896049575937584836083 58697844074363906377254125)
      ·
        refine ⟨22011691527886464891470297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58697844074363906377254125 22011691527886464891470297)
        ·
          refine ⟨16508768645914848668602723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22011691527886464891470297 16508768645914848668602723)
          ·
            refine ⟨24763152968872273002904085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16508768645914848668602723 24763152968872273002904085)
            ·
              refine ⟨1160772795415887797011129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24763152968872273002904085 1160772795415887797011129)
              ·
                refine ⟨870579596561915847758347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160772795415887797011129 870579596561915847758347)
                ·
                  refine ⟨1305869394842873771637521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870579596561915847758347 1305869394842873771637521)
                  ·
                    refine ⟨979402046132155328728141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1305869394842873771637521 979402046132155328728141)
                    ·
                      refine ⟨367275767299558248273053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979402046132155328728141 367275767299558248273053)
                      ·
                        rfl

theorem cell23_715267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_715267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715267 prefixEnd_715267 := by exact prefixLift 715267
  have htrace : WordTrace (prefixWord ++ tailWord_715267) baseStart_715267 baseEnd_715267 := by
    simpa [prefixWord, tailWord_715267, baseEnd_715267] using wordTrace_append hprefix tailTrace_715267
  have hstable : (prefixWord ++ tailWord_715267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715267).length < 2 ^ (prefixWord ++ tailWord_715267).sum := by decide
  have hdescent : baseEnd_715267 < baseStart_715267 := by decide
  rcases family_descends (prefixWord ++ tailWord_715267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715284 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_715284 : Nat := 118140960795 + 715284 * 2 ^ 59
def prefixEnd_715284 : Nat := 4983230072969 + 3 ^ 40 * 715284 * 2
def baseEnd_715284 : Nat := 367284496470684681760475

theorem tailTrace_715284 : CollatzResearch.WordTrace tailWord_715284 prefixEnd_715284 367284496470684681760475 := by
  unfold tailWord_715284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13044275370327851813296453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17392367160437135751061937 13044275370327851813296453)
  ·
    refine ⟨2445801631936472214993085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13044275370327851813296453 2445801631936472214993085)
    ·
      refine ⟨917175611976177080622407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2445801631936472214993085 917175611976177080622407)
      ·
        refine ⟨1375763417964265620933611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917175611976177080622407 1375763417964265620933611)
        ·
          refine ⟨2063645126946398431400417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375763417964265620933611 2063645126946398431400417)
          ·
            refine ⟨1547733845209798823550313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2063645126946398431400417 1547733845209798823550313)
            ·
              refine ⟨1160800383907349117662735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547733845209798823550313 1160800383907349117662735)
              ·
                refine ⟨1741200575861023676494103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160800383907349117662735 1741200575861023676494103)
                ·
                  refine ⟨2611800863791535514741155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741200575861023676494103 2611800863791535514741155)
                  ·
                    refine ⟨3917701295687303272111733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2611800863791535514741155 3917701295687303272111733)
                    ·
                      refine ⟨367284496470684681760475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3917701295687303272111733 367284496470684681760475)
                      ·
                        rfl

theorem cell23_715284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_715284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715284 prefixEnd_715284 := by exact prefixLift 715284
  have htrace : WordTrace (prefixWord ++ tailWord_715284) baseStart_715284 baseEnd_715284 := by
    simpa [prefixWord, tailWord_715284, baseEnd_715284] using wordTrace_append hprefix tailTrace_715284
  have hstable : (prefixWord ++ tailWord_715284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715284).length < 2 ^ (prefixWord ++ tailWord_715284).sum := by decide
  have hdescent : baseEnd_715284 < baseStart_715284 := by decide
  rcases family_descends (prefixWord ++ tailWord_715284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715287 : List Nat := [1, 1, 3, 6, 1, 2, 9]
def baseStart_715287 : Nat := 118140960795 + 715287 * 2 ^ 59
def prefixEnd_715287 : Nat := 4983230072969 + 3 ^ 40 * 715287 * 2
def baseEnd_715287 : Nat := 4534395517440100864481

theorem tailTrace_715287 : CollatzResearch.WordTrace tailWord_715287 prefixEnd_715287 4534395517440100864481 := by
  unfold tailWord_715287
  simp only [CollatzResearch.WordTrace]
  refine ⟨26088660159644835138952115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17392440106429890092634743 26088660159644835138952115)
  ·
    refine ⟨39132990239467252708428173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26088660159644835138952115 39132990239467252708428173)
    ·
      refine ⟨14674871339800219765660565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39132990239467252708428173 14674871339800219765660565)
      ·
        refine ⟨687884594053135301515339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14674871339800219765660565 687884594053135301515339)
        ·
          refine ⟨1031826891079702952273009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687884594053135301515339 1031826891079702952273009)
          ·
            refine ⟨773870168309777214204757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031826891079702952273009 773870168309777214204757)
            ·
              refine ⟨4534395517440100864481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 773870168309777214204757 4534395517440100864481)
              ·
                rfl

theorem cell23_715287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 9].length) (baseStart_715287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715287 prefixEnd_715287 := by exact prefixLift 715287
  have htrace : WordTrace (prefixWord ++ tailWord_715287) baseStart_715287 baseEnd_715287 := by
    simpa [prefixWord, tailWord_715287, baseEnd_715287] using wordTrace_append hprefix tailTrace_715287
  have hstable : (prefixWord ++ tailWord_715287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715287).length < 2 ^ (prefixWord ++ tailWord_715287).sum := by decide
  have hdescent : baseEnd_715287 < baseStart_715287 := by decide
  rcases family_descends (prefixWord ++ tailWord_715287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715297 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_715297 : Nat := 118140960795 + 715297 * 2 ^ 59
def prefixEnd_715297 : Nat := 4983230072969 + 3 ^ 40 * 715297 * 2
def baseEnd_715297 : Nat := 367291171719193130897915

theorem tailTrace_715297 : CollatzResearch.WordTrace tailWord_715297 prefixEnd_715297 367291171719193130897915 := by
  unfold tailWord_715297
  simp only [CollatzResearch.WordTrace]
  refine ⟨26089024889608606846816145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17392683259739071231210763 26089024889608606846816145)
  ·
    refine ⟨19566768667206455135112109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26089024889608606846816145 19566768667206455135112109)
    ·
      refine ⟨7337538250202420675667041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19566768667206455135112109 7337538250202420675667041)
      ·
        refine ⟨5503153687651815506750281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7337538250202420675667041 5503153687651815506750281)
        ·
          refine ⟨4127365265738861630062711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5503153687651815506750281 4127365265738861630062711)
          ·
            refine ⟨6191047898608292445094067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127365265738861630062711 6191047898608292445094067)
            ·
              refine ⟨9286571847912438667641101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191047898608292445094067 9286571847912438667641101)
              ·
                refine ⟨3482464442967164500365413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9286571847912438667641101 3482464442967164500365413)
                ·
                  refine ⟨652962083056343343818515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3482464442967164500365413 652962083056343343818515)
                  ·
                    refine ⟨979443124584515015727773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 652962083056343343818515 979443124584515015727773)
                    ·
                      refine ⟨367291171719193130897915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979443124584515015727773 367291171719193130897915)
                      ·
                        rfl

theorem cell23_715297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_715297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715297 prefixEnd_715297 := by exact prefixLift 715297
  have htrace : WordTrace (prefixWord ++ tailWord_715297) baseStart_715297 baseEnd_715297 := by
    simpa [prefixWord, tailWord_715297, baseEnd_715297] using wordTrace_append hprefix tailTrace_715297
  have hstable : (prefixWord ++ tailWord_715297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715297).length < 2 ^ (prefixWord ++ tailWord_715297).sum := by decide
  have hdescent : baseEnd_715297 < baseStart_715297 := by decide
  rcases family_descends (prefixWord ++ tailWord_715297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715324 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_715324 : Nat := 118140960795 + 715324 * 2 ^ 59
def prefixEnd_715324 : Nat := 4983230072969 + 3 ^ 40 * 715324 * 2
def baseEnd_715324 : Nat := 367305035696864525260291

theorem tailTrace_715324 : CollatzResearch.WordTrace tailWord_715324 prefixEnd_715324 367305035696864525260291 := by
  unfold tailWord_715324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045004830255395229024513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17393339773673860305366017 13045004830255395229024513)
  ·
    refine ⟨9783753622691546421768385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13045004830255395229024513 9783753622691546421768385)
    ·
      refine ⟨7337815217018659816326289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9783753622691546421768385 7337815217018659816326289)
      ·
        refine ⟨5503361412763994862244717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7337815217018659816326289 5503361412763994862244717)
        ·
          refine ⟨2063760529786498073341769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5503361412763994862244717 2063760529786498073341769)
          ·
            refine ⟨1547820397339873555006327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2063760529786498073341769 1547820397339873555006327)
            ·
              refine ⟨2321730596009810332509491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547820397339873555006327 2321730596009810332509491)
              ·
                refine ⟨3482595894014715498764237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321730596009810332509491 3482595894014715498764237)
                ·
                  refine ⟨1305973460255518312036589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3482595894014715498764237 1305973460255518312036589)
                  ·
                    refine ⟨489740047595819367013721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1305973460255518312036589 489740047595819367013721)
                    ·
                      refine ⟨367305035696864525260291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489740047595819367013721 367305035696864525260291)
                      ·
                        rfl

theorem cell23_715324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_715324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715324 prefixEnd_715324 := by exact prefixLift 715324
  have htrace : WordTrace (prefixWord ++ tailWord_715324) baseStart_715324 baseEnd_715324 := by
    simpa [prefixWord, tailWord_715324, baseEnd_715324] using wordTrace_append hprefix tailTrace_715324
  have hstable : (prefixWord ++ tailWord_715324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715324).length < 2 ^ (prefixWord ++ tailWord_715324).sum := by decide
  have hdescent : baseEnd_715324 < baseStart_715324 := by decide
  rcases family_descends (prefixWord ++ tailWord_715324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715340 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_715340 : Nat := 118140960795 + 715340 * 2 ^ 59
def prefixEnd_715340 : Nat := 4983230072969 + 3 ^ 40 * 715340 * 2
def baseEnd_715340 : Nat := 367313251387336462660217

theorem tailTrace_715340 : CollatzResearch.WordTrace tailWord_715340 prefixEnd_715340 367313251387336462660217 := by
  unfold tailWord_715340
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045296614226412595315737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17393728818968550127087649 13045296614226412595315737)
  ·
    refine ⟨9783972460669809446486803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13045296614226412595315737 9783972460669809446486803)
    ·
      refine ⟨14675958691004714169730205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9783972460669809446486803 14675958691004714169730205)
      ·
        refine ⟨5503484509126767813648827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14675958691004714169730205 5503484509126767813648827)
        ·
          refine ⟨8255226763690151720473241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503484509126767813648827 8255226763690151720473241)
          ·
            refine ⟨6191420072767613790354931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8255226763690151720473241 6191420072767613790354931)
            ·
              refine ⟨9287130109151420685532397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191420072767613790354931 9287130109151420685532397)
              ·
                refine ⟨3482673790931782757074649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9287130109151420685532397 3482673790931782757074649)
                ·
                  refine ⟨2612005343198837067805987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3482673790931782757074649 2612005343198837067805987)
                  ·
                    refine ⟨3918008014798255601708981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612005343198837067805987 3918008014798255601708981)
                    ·
                      refine ⟨367313251387336462660217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3918008014798255601708981 367313251387336462660217)
                      ·
                        rfl

theorem cell23_715340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_715340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715340 prefixEnd_715340 := by exact prefixLift 715340
  have htrace : WordTrace (prefixWord ++ tailWord_715340) baseStart_715340 baseEnd_715340 := by
    simpa [prefixWord, tailWord_715340, baseEnd_715340] using wordTrace_append hprefix tailTrace_715340
  have hstable : (prefixWord ++ tailWord_715340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715340).length < 2 ^ (prefixWord ++ tailWord_715340).sum := by decide
  have hdescent : baseEnd_715340 < baseStart_715340 := by decide
  rcases family_descends (prefixWord ++ tailWord_715340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715427 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 1, 6, 2]
def baseStart_715427 : Nat := 118140960795 + 715427 * 2 ^ 59
def prefixEnd_715427 : Nat := 4983230072969 + 3 ^ 40 * 715427 * 2
def baseEnd_715427 : Nat := 367357924204277622272317

theorem tailTrace_715427 : CollatzResearch.WordTrace tailWord_715427 prefixEnd_715427 367357924204277622272317 := by
  unfold tailWord_715427
  simp only [CollatzResearch.WordTrace]
  refine ⟨26093766379137639049048535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17395844252758426032699023 26093766379137639049048535)
  ·
    refine ⟨39140649568706458573572803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26093766379137639049048535 39140649568706458573572803)
    ·
      refine ⟨58710974353059687860359205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39140649568706458573572803 58710974353059687860359205)
      ·
        refine ⟨11008307691198691473817351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58710974353059687860359205 11008307691198691473817351)
        ·
          refine ⟨16512461536798037210726027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11008307691198691473817351 16512461536798037210726027)
          ·
            refine ⟨24768692305197055816089041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16512461536798037210726027 24768692305197055816089041)
            ·
              refine ⟨18576519228897791862066781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24768692305197055816089041 18576519228897791862066781)
              ·
                refine ⟨6966194710836671948275043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18576519228897791862066781 6966194710836671948275043)
                ·
                  refine ⟨10449292066255007922412565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6966194710836671948275043 10449292066255007922412565)
                  ·
                    refine ⟨489810565605703496363089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10449292066255007922412565 489810565605703496363089)
                    ·
                      refine ⟨367357924204277622272317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489810565605703496363089 367357924204277622272317)
                      ·
                        rfl

theorem cell23_715427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_715427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715427 prefixEnd_715427 := by exact prefixLift 715427
  have htrace : WordTrace (prefixWord ++ tailWord_715427) baseStart_715427 baseEnd_715427 := by
    simpa [prefixWord, tailWord_715427, baseEnd_715427] using wordTrace_append hprefix tailTrace_715427
  have hstable : (prefixWord ++ tailWord_715427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715427).length < 2 ^ (prefixWord ++ tailWord_715427).sum := by decide
  have hdescent : baseEnd_715427 < baseStart_715427 := by decide
  rcases family_descends (prefixWord ++ tailWord_715427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715440 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_715440 : Nat := 118140960795 + 715440 * 2 ^ 59
def prefixEnd_715440 : Nat := 4983230072969 + 3 ^ 40 * 715440 * 2
def baseEnd_715440 : Nat := 367364599452786071409757

theorem tailTrace_715440 : CollatzResearch.WordTrace tailWord_715440 prefixEnd_715440 367364599452786071409757 := by
  unfold tailWord_715440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13047120264045271134635887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17396160352060361512847849 13047120264045271134635887)
  ·
    refine ⟨19570680396067906701953831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13047120264045271134635887 19570680396067906701953831)
    ·
      refine ⟨29356020594101860052930747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19570680396067906701953831 29356020594101860052930747)
      ·
        refine ⟨44034030891152790079396121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29356020594101860052930747 44034030891152790079396121)
        ·
          refine ⟨33025523168364592559547091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44034030891152790079396121 33025523168364592559547091)
          ·
            refine ⟨49538284752546888839320637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33025523168364592559547091 49538284752546888839320637)
            ·
              refine ⟨18576856782205083314745239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49538284752546888839320637 18576856782205083314745239)
              ·
                refine ⟨27865285173307624972117859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18576856782205083314745239 27865285173307624972117859)
                ·
                  refine ⟨41797927759961437458176789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27865285173307624972117859 41797927759961437458176789)
                  ·
                    refine ⟨1959277863748192380852037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41797927759961437458176789 1959277863748192380852037)
                    ·
                      refine ⟨367364599452786071409757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1959277863748192380852037 367364599452786071409757)
                      ·
                        rfl

theorem cell23_715440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_715440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715440 prefixEnd_715440 := by exact prefixLift 715440
  have htrace : WordTrace (prefixWord ++ tailWord_715440) baseStart_715440 baseEnd_715440 := by
    simpa [prefixWord, tailWord_715440, baseEnd_715440] using wordTrace_append hprefix tailTrace_715440
  have hstable : (prefixWord ++ tailWord_715440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715440).length < 2 ^ (prefixWord ++ tailWord_715440).sum := by decide
  have hdescent : baseEnd_715440 < baseStart_715440 := by decide
  rcases family_descends (prefixWord ++ tailWord_715440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715450 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 10]
def baseStart_715450 : Nat := 118140960795 + 715450 * 2 ^ 59
def prefixEnd_715450 : Nat := 4983230072969 + 3 ^ 40 * 715450 * 2
def baseEnd_715450 : Nat := 40818859362147892476079

theorem tailTrace_715450 : CollatzResearch.WordTrace tailWord_715450 prefixEnd_715450 40818859362147892476079 := by
  unfold tailWord_715450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6523651314513578494283951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17396403505369542651423869 6523651314513578494283951)
  ·
    refine ⟨9785476971770367741425927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6523651314513578494283951 9785476971770367741425927)
    ·
      refine ⟨14678215457655551612138891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9785476971770367741425927 14678215457655551612138891)
      ·
        refine ⟨22017323186483327418208337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14678215457655551612138891 22017323186483327418208337)
        ·
          refine ⟨16512992389862495563656253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22017323186483327418208337 16512992389862495563656253)
          ·
            refine ⟨6192372146198435836371095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16512992389862495563656253 6192372146198435836371095)
            ·
              refine ⟨9288558219297653754556643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6192372146198435836371095 9288558219297653754556643)
              ·
                refine ⟨13932837328946480631834965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9288558219297653754556643 13932837328946480631834965)
                ·
                  refine ⟨40818859362147892476079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 13932837328946480631834965 40818859362147892476079)
                  ·
                    rfl

theorem cell23_715450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_715450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715450 prefixEnd_715450 := by exact prefixLift 715450
  have htrace : WordTrace (prefixWord ++ tailWord_715450) baseStart_715450 baseEnd_715450 := by
    simpa [prefixWord, tailWord_715450, baseEnd_715450] using wordTrace_append hprefix tailTrace_715450
  have hstable : (prefixWord ++ tailWord_715450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715450).length < 2 ^ (prefixWord ++ tailWord_715450).sum := by decide
  have hdescent : baseEnd_715450 < baseStart_715450 := by decide
  rcases family_descends (prefixWord ++ tailWord_715450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715464 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_715464 : Nat := 118140960795 + 715464 * 2 ^ 59
def prefixEnd_715464 : Nat := 4983230072969 + 3 ^ 40 * 715464 * 2
def baseEnd_715464 : Nat := 367376922988493977509647

theorem tailTrace_715464 : CollatzResearch.WordTrace tailWord_715464 prefixEnd_715464 367376922988493977509647 := by
  unfold tailWord_715464
  simp only [CollatzResearch.WordTrace]
  refine ⟨13047557940001797184072723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17396743920002396245430297 13047557940001797184072723)
  ·
    refine ⟨19571336910002695776109085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13047557940001797184072723 19571336910002695776109085)
    ·
      refine ⟨7339251341251010916040907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19571336910002695776109085 7339251341251010916040907)
      ·
        refine ⟨11008877011876516374061361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7339251341251010916040907 11008877011876516374061361)
        ·
          refine ⟨8256657758907387280546021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11008877011876516374061361 8256657758907387280546021)
          ·
            refine ⟨1548123329795135115102379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8256657758907387280546021 1548123329795135115102379)
            ·
              refine ⟨2322184994692702672653569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548123329795135115102379 2322184994692702672653569)
              ·
                refine ⟨1741638746019527004490177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322184994692702672653569 1741638746019527004490177)
                ·
                  refine ⟨1306229059514645253367633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741638746019527004490177 1306229059514645253367633)
                  ·
                    refine ⟨979671794635983940025725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306229059514645253367633 979671794635983940025725)
                    ·
                      refine ⟨367376922988493977509647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979671794635983940025725 367376922988493977509647)
                      ·
                        rfl

theorem cell23_715464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_715464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715464 prefixEnd_715464 := by exact prefixLift 715464
  have htrace : WordTrace (prefixWord ++ tailWord_715464) baseStart_715464 baseEnd_715464 := by
    simpa [prefixWord, tailWord_715464, baseEnd_715464] using wordTrace_append hprefix tailTrace_715464
  have hstable : (prefixWord ++ tailWord_715464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715464).length < 2 ^ (prefixWord ++ tailWord_715464).sum := by decide
  have hdescent : baseEnd_715464 < baseStart_715464 := by decide
  rcases family_descends (prefixWord ++ tailWord_715464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715511 : List Nat := [1, 1, 3, 1, 1, 1, 3, 7, 1, 1, 3]
def baseStart_715511 : Nat := 118140960795 + 715511 * 2 ^ 59
def prefixEnd_715511 : Nat := 4983230072969 + 3 ^ 40 * 715511 * 2
def baseEnd_715511 : Nat := 367401056579255293621931

theorem tailTrace_715511 : CollatzResearch.WordTrace tailWord_715511 prefixEnd_715511 367401056579255293621931 := by
  unfold tailWord_715511
  simp only [CollatzResearch.WordTrace]
  refine ⟨26096830110833321395106387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17397886740555547596737591 26096830110833321395106387)
  ·
    refine ⟨39145245166249982092659581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26096830110833321395106387 39145245166249982092659581)
    ·
      refine ⟨14679466937343743284747343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39145245166249982092659581 14679466937343743284747343)
      ·
        refine ⟨22019200406015614927121015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14679466937343743284747343 22019200406015614927121015)
        ·
          refine ⟨33028800609023422390681523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22019200406015614927121015 33028800609023422390681523)
          ·
            refine ⟨49543200913535133586022285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33028800609023422390681523 49543200913535133586022285)
            ·
              refine ⟨18578700342575675094758357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49543200913535133586022285 18578700342575675094758357)
              ·
                refine ⟨435438289279117385033399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18578700342575675094758357 435438289279117385033399)
                ·
                  refine ⟨653157433918676077550099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435438289279117385033399 653157433918676077550099)
                  ·
                    refine ⟨979736150878014116325149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653157433918676077550099 979736150878014116325149)
                    ·
                      refine ⟨367401056579255293621931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979736150878014116325149 367401056579255293621931)
                      ·
                        rfl

theorem cell23_715511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_715511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715511 prefixEnd_715511 := by exact prefixLift 715511
  have htrace : WordTrace (prefixWord ++ tailWord_715511) baseStart_715511 baseEnd_715511 := by
    simpa [prefixWord, tailWord_715511, baseEnd_715511] using wordTrace_append hprefix tailTrace_715511
  have hstable : (prefixWord ++ tailWord_715511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715511).length < 2 ^ (prefixWord ++ tailWord_715511).sum := by decide
  have hdescent : baseEnd_715511 < baseStart_715511 := by decide
  rcases family_descends (prefixWord ++ tailWord_715511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715528 : List Nat := [2, 1, 3, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_715528 : Nat := 118140960795 + 715528 * 2 ^ 59
def prefixEnd_715528 : Nat := 4983230072969 + 3 ^ 40 * 715528 * 2
def baseEnd_715528 : Nat := 367409785750381727109353

theorem tailTrace_715528 : CollatzResearch.WordTrace tailWord_715528 prefixEnd_715528 367409785750381727109353 := by
  unfold tailWord_715528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13048725075885866649237619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17398300101181155532316825 13048725075885866649237619)
  ·
    refine ⟨19573087613828799973856429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13048725075885866649237619 19573087613828799973856429)
    ·
      refine ⟨7339907855185799990196161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19573087613828799973856429 7339907855185799990196161)
      ·
        refine ⟨5504930891389349992647121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7339907855185799990196161 5504930891389349992647121)
        ·
          refine ⟨4128698168542012494485341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5504930891389349992647121 4128698168542012494485341)
          ·
            refine ⟨1548261813203254685432003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4128698168542012494485341 1548261813203254685432003)
            ·
              refine ⟨2322392719804882028148005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548261813203254685432003 2322392719804882028148005)
              ·
                refine ⟨435448634963415380277751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2322392719804882028148005 435448634963415380277751)
                ·
                  refine ⟨653172952445123070416627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435448634963415380277751 653172952445123070416627)
                  ·
                    refine ⟨979759428667684605624941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653172952445123070416627 979759428667684605624941)
                    ·
                      refine ⟨367409785750381727109353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979759428667684605624941 367409785750381727109353)
                      ·
                        rfl

theorem cell23_715528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_715528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715528 prefixEnd_715528 := by exact prefixLift 715528
  have htrace : WordTrace (prefixWord ++ tailWord_715528) baseStart_715528 baseEnd_715528 := by
    simpa [prefixWord, tailWord_715528, baseEnd_715528] using wordTrace_append hprefix tailTrace_715528
  have hstable : (prefixWord ++ tailWord_715528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715528).length < 2 ^ (prefixWord ++ tailWord_715528).sum := by decide
  have hdescent : baseEnd_715528 < baseStart_715528 := by decide
  rcases family_descends (prefixWord ++ tailWord_715528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715534 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_715534 : Nat := 118140960795 + 715534 * 2 ^ 59
def prefixEnd_715534 : Nat := 4983230072969 + 3 ^ 40 * 715534 * 2
def baseEnd_715534 : Nat := 367412866634308703634325

theorem tailTrace_715534 : CollatzResearch.WordTrace tailWord_715534 prefixEnd_715534 367412866634308703634325 := by
  unfold tailWord_715534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262208623718749540399207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17398445993166664215462437 3262208623718749540399207)
  ·
    refine ⟨4893312935578124310598811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3262208623718749540399207 4893312935578124310598811)
    ·
      refine ⟨7339969403367186465898217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4893312935578124310598811 7339969403367186465898217)
      ·
        refine ⟨5504977052525389849423663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7339969403367186465898217 5504977052525389849423663)
        ·
          refine ⟨8257465578788084774135495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5504977052525389849423663 8257465578788084774135495)
          ·
            refine ⟨12386198368182127161203243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8257465578788084774135495 12386198368182127161203243)
            ·
              refine ⟨18579297552273190741804865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12386198368182127161203243 18579297552273190741804865)
              ·
                refine ⟨13934473164204893056353649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18579297552273190741804865 13934473164204893056353649)
                ·
                  refine ⟨10450854873153669792265237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13934473164204893056353649 10450854873153669792265237)
                  ·
                    refine ⟨489883822179078271512433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10450854873153669792265237 489883822179078271512433)
                    ·
                      refine ⟨367412866634308703634325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489883822179078271512433 367412866634308703634325)
                      ·
                        rfl

theorem cell23_715534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_715534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715534 prefixEnd_715534 := by exact prefixLift 715534
  have htrace : WordTrace (prefixWord ++ tailWord_715534) baseStart_715534 baseEnd_715534 := by
    simpa [prefixWord, tailWord_715534, baseEnd_715534] using wordTrace_append hprefix tailTrace_715534
  have hstable : (prefixWord ++ tailWord_715534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715534).length < 2 ^ (prefixWord ++ tailWord_715534).sum := by decide
  have hdescent : baseEnd_715534 < baseStart_715534 := by decide
  rcases family_descends (prefixWord ++ tailWord_715534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715537 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_715537 : Nat := 118140960795 + 715537 * 2 ^ 59
def prefixEnd_715537 : Nat := 4983230072969 + 3 ^ 40 * 715537 * 2
def baseEnd_715537 : Nat := 367414407076272191896811

theorem tailTrace_715537 : CollatzResearch.WordTrace tailWord_715537 prefixEnd_715537 367414407076272191896811 := by
  unfold tailWord_715537
  simp only [CollatzResearch.WordTrace]
  refine ⟨26097778408739127835552865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17398518939159418557035243 26097778408739127835552865)
  ·
    refine ⟨19573333806554345876664649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26097778408739127835552865 19573333806554345876664649)
    ·
      refine ⟨14680000354915759407498487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19573333806554345876664649 14680000354915759407498487)
      ·
        refine ⟨22020000532373639111247731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14680000354915759407498487 22020000532373639111247731)
        ·
          refine ⟨33030000798560458666871597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22020000532373639111247731 33030000798560458666871597)
          ·
            refine ⟨12386250299460172000076849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33030000798560458666871597 12386250299460172000076849)
            ·
              refine ⟨9289687724595129000057637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12386250299460172000076849 9289687724595129000057637)
              ·
                refine ⟨1741816448361586687510807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9289687724595129000057637 1741816448361586687510807)
                ·
                  refine ⟨2612724672542380031266211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741816448361586687510807 2612724672542380031266211)
                  ·
                    refine ⟨3919087008813570046899317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612724672542380031266211 3919087008813570046899317)
                    ·
                      refine ⟨367414407076272191896811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3919087008813570046899317 367414407076272191896811)
                      ·
                        rfl

theorem cell23_715537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_715537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715537 prefixEnd_715537 := by exact prefixLift 715537
  have htrace : WordTrace (prefixWord ++ tailWord_715537) baseStart_715537 baseEnd_715537 := by
    simpa [prefixWord, tailWord_715537, baseEnd_715537] using wordTrace_append hprefix tailTrace_715537
  have hstable : (prefixWord ++ tailWord_715537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715537).length < 2 ^ (prefixWord ++ tailWord_715537).sum := by decide
  have hdescent : baseEnd_715537 < baseStart_715537 := by decide
  rcases family_descends (prefixWord ++ tailWord_715537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715551 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 5, 2, 2]
def baseStart_715551 : Nat := 118140960795 + 715551 * 2 ^ 59
def prefixEnd_715551 : Nat := 4983230072969 + 3 ^ 40 * 715551 * 2
def baseEnd_715551 : Nat := 367421595805435137121747

theorem tailTrace_715551 : CollatzResearch.WordTrace tailWord_715551 prefixEnd_715551 367421595805435137121747 := by
  unfold tailWord_715551
  simp only [CollatzResearch.WordTrace]
  refine ⟨26098289030688408226562507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17398859353792272151041671 26098289030688408226562507)
  ·
    refine ⟨39147433546032612339843761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26098289030688408226562507 39147433546032612339843761)
    ·
      refine ⟨29360575159524459254882821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39147433546032612339843761 29360575159524459254882821)
      ·
        refine ⟨5505107842410836110290529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29360575159524459254882821 5505107842410836110290529)
        ·
          refine ⟨4128830881808127082717897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5505107842410836110290529 4128830881808127082717897)
          ·
            refine ⟨3096623161356095312038423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4128830881808127082717897 3096623161356095312038423)
            ·
              refine ⟨4644934742034142968057635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096623161356095312038423 4644934742034142968057635)
              ·
                refine ⟨6967402113051214452086453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4644934742034142968057635 6967402113051214452086453)
                ·
                  refine ⟨653193948098551354883105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6967402113051214452086453 653193948098551354883105)
                  ·
                    refine ⟨489895461073913516162329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 653193948098551354883105 489895461073913516162329)
                    ·
                      refine ⟨367421595805435137121747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489895461073913516162329 367421595805435137121747)
                      ·
                        rfl

theorem cell23_715551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_715551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715551 prefixEnd_715551 := by exact prefixLift 715551
  have htrace : WordTrace (prefixWord ++ tailWord_715551) baseStart_715551 baseEnd_715551 := by
    simpa [prefixWord, tailWord_715551, baseEnd_715551] using wordTrace_append hprefix tailTrace_715551
  have hstable : (prefixWord ++ tailWord_715551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715551).length < 2 ^ (prefixWord ++ tailWord_715551).sum := by decide
  have hdescent : baseEnd_715551 < baseStart_715551 := by decide
  rcases family_descends (prefixWord ++ tailWord_715551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715562 : List Nat := [3, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_715562 : Nat := 118140960795 + 715562 * 2 ^ 59
def prefixEnd_715562 : Nat := 4983230072969 + 3 ^ 40 * 715562 * 2
def baseEnd_715562 : Nat := 367427244092634594084197

theorem tailTrace_715562 : CollatzResearch.WordTrace tailWord_715562 prefixEnd_715562 367427244092634594084197 := by
  unfold tailWord_715562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524672558412139276303235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17399126822432371403475293 6524672558412139276303235)
  ·
    refine ⟨9787008837618208914454853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6524672558412139276303235 9787008837618208914454853)
    ·
      refine ⟨1835064157053414171460285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9787008837618208914454853 1835064157053414171460285)
      ·
        refine ⟨688149058895030314297607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1835064157053414171460285 688149058895030314297607)
        ·
          refine ⟨1032223588342545471446411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688149058895030314297607 1032223588342545471446411)
          ·
            refine ⟨1548335382513818207169617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032223588342545471446411 1548335382513818207169617)
            ·
              refine ⟨1161251536885363655377213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548335382513818207169617 1161251536885363655377213)
              ·
                refine ⟨435469326332011370766455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161251536885363655377213 435469326332011370766455)
                ·
                  refine ⟨653203989498017056149683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435469326332011370766455 653203989498017056149683)
                  ·
                    refine ⟨979805984247025584224525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653203989498017056149683 979805984247025584224525)
                    ·
                      refine ⟨367427244092634594084197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979805984247025584224525 367427244092634594084197)
                      ·
                        rfl

theorem cell23_715562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_715562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715562 prefixEnd_715562 := by exact prefixLift 715562
  have htrace : WordTrace (prefixWord ++ tailWord_715562) baseStart_715562 baseEnd_715562 := by
    simpa [prefixWord, tailWord_715562, baseEnd_715562] using wordTrace_append hprefix tailTrace_715562
  have hstable : (prefixWord ++ tailWord_715562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715562).length < 2 ^ (prefixWord ++ tailWord_715562).sum := by decide
  have hdescent : baseEnd_715562 < baseStart_715562 := by decide
  rcases family_descends (prefixWord ++ tailWord_715562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715571 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 3]
def baseStart_715571 : Nat := 118140960795 + 715571 * 2 ^ 59
def prefixEnd_715571 : Nat := 4983230072969 + 3 ^ 40 * 715571 * 2
def baseEnd_715571 : Nat := 367431865418525058871655

theorem tailTrace_715571 : CollatzResearch.WordTrace tailWord_715571 prefixEnd_715571 367431865418525058871655 := by
  unfold tailWord_715571
  simp only [CollatzResearch.WordTrace]
  refine ⟨26099018490615951642290567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17399345660410634428193711 26099018490615951642290567)
  ·
    refine ⟨39148527735923927463435851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26099018490615951642290567 39148527735923927463435851)
    ·
      refine ⟨58722791603885891195153777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39148527735923927463435851 58722791603885891195153777)
      ·
        refine ⟨44042093702914418396365333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58722791603885891195153777 44042093702914418396365333)
        ·
          refine ⟨2064473142324113362329625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44042093702914418396365333 2064473142324113362329625)
          ·
            refine ⟨1548354856743085021747219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064473142324113362329625 1548354856743085021747219)
            ·
              refine ⟨2322532285114627532620829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548354856743085021747219 2322532285114627532620829)
              ·
                refine ⟨870949606917985324732811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2322532285114627532620829 870949606917985324732811)
                ·
                  refine ⟨1306424410376977987099217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870949606917985324732811 1306424410376977987099217)
                  ·
                    refine ⟨979818307782733490324413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1306424410376977987099217 979818307782733490324413)
                    ·
                      refine ⟨367431865418525058871655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 979818307782733490324413 367431865418525058871655)
                      ·
                        rfl

theorem cell23_715571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_715571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715571 prefixEnd_715571 := by exact prefixLift 715571
  have htrace : WordTrace (prefixWord ++ tailWord_715571) baseStart_715571 baseEnd_715571 := by
    simpa [prefixWord, tailWord_715571, baseEnd_715571] using wordTrace_append hprefix tailTrace_715571
  have hstable : (prefixWord ++ tailWord_715571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715571).length < 2 ^ (prefixWord ++ tailWord_715571).sum := by decide
  have hdescent : baseEnd_715571 < baseStart_715571 := by decide
  rcases family_descends (prefixWord ++ tailWord_715571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715578 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_715578 : Nat := 118140960795 + 715578 * 2 ^ 59
def prefixEnd_715578 : Nat := 4983230072969 + 3 ^ 40 * 715578 * 2
def baseEnd_715578 : Nat := 122478486594368843828041

theorem tailTrace_715578 : CollatzResearch.WordTrace tailWord_715578 prefixEnd_715578 122478486594368843828041 := by
  unfold tailWord_715578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524818450397647959448847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17399515867727061225196925 6524818450397647959448847)
  ·
    refine ⟨9787227675596471939173271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6524818450397647959448847 9787227675596471939173271)
    ·
      refine ⟨14680841513394707908759907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9787227675596471939173271 14680841513394707908759907)
      ·
        refine ⟨22021262270092061863139861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14680841513394707908759907 22021262270092061863139861)
        ·
          refine ⟨1032246668910565399834681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22021262270092061863139861 1032246668910565399834681)
          ·
            refine ⟨774185001682924049876011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032246668910565399834681 774185001682924049876011)
            ·
              refine ⟨1161277502524386074814017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774185001682924049876011 1161277502524386074814017)
              ·
                refine ⟨870958126893289556110513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161277502524386074814017 870958126893289556110513)
                ·
                  refine ⟨653218595169967167082885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 870958126893289556110513 653218595169967167082885)
                  ·
                    refine ⟨122478486594368843828041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 653218595169967167082885 122478486594368843828041)
                    ·
                      rfl

theorem cell23_715578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_715578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715578 prefixEnd_715578 := by exact prefixLift 715578
  have htrace : WordTrace (prefixWord ++ tailWord_715578) baseStart_715578 baseEnd_715578 := by
    simpa [prefixWord, tailWord_715578, baseEnd_715578] using wordTrace_append hprefix tailTrace_715578
  have hstable : (prefixWord ++ tailWord_715578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715578).length < 2 ^ (prefixWord ++ tailWord_715578).sum := by decide
  have hdescent : baseEnd_715578 < baseStart_715578 := by decide
  rcases family_descends (prefixWord ++ tailWord_715578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715588 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_715588 : Nat := 118140960795 + 715588 * 2 ^ 59
def prefixEnd_715588 : Nat := 4983230072969 + 3 ^ 40 * 715588 * 2
def baseEnd_715588 : Nat := 367440594589651492359077

theorem tailTrace_715588 : CollatzResearch.WordTrace tailWord_715588 prefixEnd_715588 367440594589651492359077 := by
  unfold tailWord_715588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049819265777181772829709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17399759021036242363772945 13049819265777181772829709)
  ·
    refine ⟨4893682224666443164811141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13049819265777181772829709 4893682224666443164811141)
    ·
      refine ⟨917565417124958093402089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4893682224666443164811141 917565417124958093402089)
      ·
        refine ⟨688174062843718570051567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 917565417124958093402089 688174062843718570051567)
        ·
          refine ⟨1032261094265577855077351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688174062843718570051567 1032261094265577855077351)
          ·
            refine ⟨1548391641398366782616027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032261094265577855077351 1548391641398366782616027)
            ·
              refine ⟨2322587462097550173924041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1548391641398366782616027 2322587462097550173924041)
              ·
                refine ⟨1741940596573162630443031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322587462097550173924041 1741940596573162630443031)
                ·
                  refine ⟨2612910894859743945664547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1741940596573162630443031 2612910894859743945664547)
                  ·
                    refine ⟨3919366342289615918496821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2612910894859743945664547 3919366342289615918496821)
                    ·
                      refine ⟨367440594589651492359077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3919366342289615918496821 367440594589651492359077)
                      ·
                        rfl

theorem cell23_715588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_715588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715588 prefixEnd_715588 := by exact prefixLift 715588
  have htrace : WordTrace (prefixWord ++ tailWord_715588) baseStart_715588 baseEnd_715588 := by
    simpa [prefixWord, tailWord_715588, baseEnd_715588] using wordTrace_append hprefix tailTrace_715588
  have hstable : (prefixWord ++ tailWord_715588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715588).length < 2 ^ (prefixWord ++ tailWord_715588).sum := by decide
  have hdescent : baseEnd_715588 < baseStart_715588 := by decide
  rcases family_descends (prefixWord ++ tailWord_715588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715594 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_715594 : Nat := 118140960795 + 715594 * 2 ^ 59
def prefixEnd_715594 : Nat := 4983230072969 + 3 ^ 40 * 715594 * 2
def baseEnd_715594 : Nat := 367443675473578468884049

theorem tailTrace_715594 : CollatzResearch.WordTrace tailWord_715594 prefixEnd_715594 367443675473578468884049 := by
  unfold tailWord_715594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524964342383156642594459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17399904913021751046918557 6524964342383156642594459)
  ·
    refine ⟨9787446513574734963891689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6524964342383156642594459 9787446513574734963891689)
    ·
      refine ⟨7340584885181051222918767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9787446513574734963891689 7340584885181051222918767)
      ·
        refine ⟨11010877327771576834378151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340584885181051222918767 11010877327771576834378151)
        ·
          refine ⟨16516315991657365251567227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010877327771576834378151 16516315991657365251567227)
          ·
            refine ⟨24774473987486047877350841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16516315991657365251567227 24774473987486047877350841)
            ·
              refine ⟨18580855490614535908013131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24774473987486047877350841 18580855490614535908013131)
              ·
                refine ⟨27871283235921803862019697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18580855490614535908013131 27871283235921803862019697)
                ·
                  refine ⟨20903462426941352896514773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27871283235921803862019697 20903462426941352896514773)
                  ·
                    refine ⟨489924900631437958512065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20903462426941352896514773 489924900631437958512065)
                    ·
                      refine ⟨367443675473578468884049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489924900631437958512065 367443675473578468884049)
                      ·
                        rfl

theorem cell23_715594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_715594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715594 prefixEnd_715594 := by exact prefixLift 715594
  have htrace : WordTrace (prefixWord ++ tailWord_715594) baseStart_715594 baseEnd_715594 := by
    simpa [prefixWord, tailWord_715594, baseEnd_715594] using wordTrace_append hprefix tailTrace_715594
  have hstable : (prefixWord ++ tailWord_715594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715594).length < 2 ^ (prefixWord ++ tailWord_715594).sum := by decide
  have hdescent : baseEnd_715594 < baseStart_715594 := by decide
  rcases family_descends (prefixWord ++ tailWord_715594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715617 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 4, 6]
def baseStart_715617 : Nat := 118140960795 + 715617 * 2 ^ 59
def prefixEnd_715617 : Nat := 4983230072969 + 3 ^ 40 * 715617 * 2
def baseEnd_715617 : Nat := 122485161842877292965481

theorem tailTrace_715617 : CollatzResearch.WordTrace tailWord_715617 prefixEnd_715617 122485161842877292965481 := by
  unfold tailWord_715617
  simp only [CollatzResearch.WordTrace]
  refine ⟨26100696248449301498465105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17400464165632867665643403 26100696248449301498465105)
  ·
    refine ⟨19575522186336976123848829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26100696248449301498465105 19575522186336976123848829)
    ·
      refine ⟨7340820819876366046443311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19575522186336976123848829 7340820819876366046443311)
      ·
        refine ⟨11011231229814549069664967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340820819876366046443311 11011231229814549069664967)
        ·
          refine ⟨16516846844721823604497451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11011231229814549069664967 16516846844721823604497451)
          ·
            refine ⟨24775270267082735406746177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16516846844721823604497451 24775270267082735406746177)
            ·
              refine ⟨18581452700312051555059633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24775270267082735406746177 18581452700312051555059633)
              ·
                refine ⟨13936089525234038666294725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18581452700312051555059633 13936089525234038666294725)
                ·
                  refine ⟨2613016785981382249930261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13936089525234038666294725 2613016785981382249930261)
                  ·
                    refine ⟨122485161842877292965481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2613016785981382249930261 122485161842877292965481)
                    ·
                      rfl

theorem cell23_715617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_715617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715617 prefixEnd_715617 := by exact prefixLift 715617
  have htrace : WordTrace (prefixWord ++ tailWord_715617) baseStart_715617 baseEnd_715617 := by
    simpa [prefixWord, tailWord_715617, baseEnd_715617] using wordTrace_append hprefix tailTrace_715617
  have hstable : (prefixWord ++ tailWord_715617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715617).length < 2 ^ (prefixWord ++ tailWord_715617).sum := by decide
  have hdescent : baseEnd_715617 < baseStart_715617 := by decide
  rcases family_descends (prefixWord ++ tailWord_715617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715627 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5]
def baseStart_715627 : Nat := 118140960795 + 715627 * 2 ^ 59
def prefixEnd_715627 : Nat := 4983230072969 + 3 ^ 40 * 715627 * 2
def baseEnd_715627 : Nat := 367460620335176839771397

theorem tailTrace_715627 : CollatzResearch.WordTrace tailWord_715627 prefixEnd_715627 367460620335176839771397 := by
  unfold tailWord_715627
  simp only [CollatzResearch.WordTrace]
  refine ⟨26101060978413073206329135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17400707318942048804219423 26101060978413073206329135)
  ·
    refine ⟨39151591467619609809493703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26101060978413073206329135 39151591467619609809493703)
    ·
      refine ⟨58727387201429414714240555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39151591467619609809493703 58727387201429414714240555)
      ·
        refine ⟨88091080802144122071360833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58727387201429414714240555 88091080802144122071360833)
        ·
          refine ⟨66068310601608091553520625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88091080802144122071360833 66068310601608091553520625)
          ·
            refine ⟨49551232951206068665140469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66068310601608091553520625 49551232951206068665140469)
            ·
              refine ⟨4645428089175568937356919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49551232951206068665140469 4645428089175568937356919)
              ·
                refine ⟨6968142133763353406035379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4645428089175568937356919 6968142133763353406035379)
                ·
                  refine ⟨10452213200645030109053069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6968142133763353406035379 10452213200645030109053069)
                  ·
                    refine ⟨3919579950241886290894901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10452213200645030109053069 3919579950241886290894901)
                    ·
                      refine ⟨367460620335176839771397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3919579950241886290894901 367460620335176839771397)
                      ·
                        rfl

theorem cell23_715627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_715627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715627 prefixEnd_715627 := by exact prefixLift 715627
  have htrace : WordTrace (prefixWord ++ tailWord_715627) baseStart_715627 baseEnd_715627 := by
    simpa [prefixWord, tailWord_715627, baseEnd_715627] using wordTrace_append hprefix tailTrace_715627
  have hstable : (prefixWord ++ tailWord_715627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715627).length < 2 ^ (prefixWord ++ tailWord_715627).sum := by decide
  have hdescent : baseEnd_715627 < baseStart_715627 := by decide
  rcases family_descends (prefixWord ++ tailWord_715627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715701 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_715701 : Nat := 118140960795 + 715701 * 2 ^ 59
def prefixEnd_715701 : Nat := 4983230072969 + 3 ^ 40 * 715701 * 2
def baseEnd_715701 : Nat := 367498617903609550246057

theorem tailTrace_715701 : CollatzResearch.WordTrace tailWord_715701 prefixEnd_715701 367498617903609550246057 := by
  unfold tailWord_715701
  simp only [CollatzResearch.WordTrace]
  refine ⟨26103759980144983844522957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17402506653429989229681971 26103759980144983844522957)
  ·
    refine ⟨9788909992554368941696109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26103759980144983844522957 9788909992554368941696109)
    ·
      refine ⟨3670841247207888353136041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9788909992554368941696109 3670841247207888353136041)
      ·
        refine ⟨2753130935405916264852031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3670841247207888353136041 2753130935405916264852031)
        ·
          refine ⟨4129696403108874397278047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753130935405916264852031 4129696403108874397278047)
          ·
            refine ⟨6194544604663311595917071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129696403108874397278047 6194544604663311595917071)
            ·
              refine ⟨9291816906994967393875607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6194544604663311595917071 9291816906994967393875607)
              ·
                refine ⟨13937725360492451090813411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9291816906994967393875607 13937725360492451090813411)
                ·
                  refine ⟨20906588040738676636220117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13937725360492451090813411 20906588040738676636220117)
                  ·
                    refine ⟨489998157204812733661409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20906588040738676636220117 489998157204812733661409)
                    ·
                      refine ⟨367498617903609550246057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 489998157204812733661409 367498617903609550246057)
                      ·
                        rfl

theorem cell23_715701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_715701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715701 prefixEnd_715701 := by exact prefixLift 715701
  have htrace : WordTrace (prefixWord ++ tailWord_715701) baseStart_715701 baseEnd_715701 := by
    simpa [prefixWord, tailWord_715701, baseEnd_715701] using wordTrace_append hprefix tailTrace_715701
  have hstable : (prefixWord ++ tailWord_715701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715701).length < 2 ^ (prefixWord ++ tailWord_715701).sum := by decide
  have hdescent : baseEnd_715701 < baseStart_715701 := by decide
  rcases family_descends (prefixWord ++ tailWord_715701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715704 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_715704 : Nat := 118140960795 + 715704 * 2 ^ 59
def prefixEnd_715704 : Nat := 4983230072969 + 3 ^ 40 * 715704 * 2
def baseEnd_715704 : Nat := 367500158345573038508543

theorem tailTrace_715704 : CollatzResearch.WordTrace tailWord_715704 prefixEnd_715704 367500158345573038508543 := by
  unfold tailWord_715704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13051934699567057678441083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17402579599422743571254777 13051934699567057678441083)
  ·
    refine ⟨19577902049350586517661625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13051934699567057678441083 19577902049350586517661625)
    ·
      refine ⟨14683426537012939888246219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19577902049350586517661625 14683426537012939888246219)
      ·
        refine ⟨22025139805519409832369329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14683426537012939888246219 22025139805519409832369329)
        ·
          refine ⟨16518854854139557374276997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22025139805519409832369329 16518854854139557374276997)
          ·
            refine ⟨3097285285151167007676937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16518854854139557374276997 3097285285151167007676937)
            ·
              refine ⟨2322963963863375255757703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3097285285151167007676937 2322963963863375255757703)
              ·
                refine ⟨3484445945795062883636555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322963963863375255757703 3484445945795062883636555)
                ·
                  refine ⟨5226668918692594325454833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484445945795062883636555 5226668918692594325454833)
                  ·
                    refine ⟨3920001689019445744091125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5226668918692594325454833 3920001689019445744091125)
                    ·
                      refine ⟨367500158345573038508543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3920001689019445744091125 367500158345573038508543)
                      ·
                        rfl

theorem cell23_715704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_715704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715704 prefixEnd_715704 := by exact prefixLift 715704
  have htrace : WordTrace (prefixWord ++ tailWord_715704) baseStart_715704 baseEnd_715704 := by
    simpa [prefixWord, tailWord_715704, baseEnd_715704] using wordTrace_append hprefix tailTrace_715704
  have hstable : (prefixWord ++ tailWord_715704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715704).length < 2 ^ (prefixWord ++ tailWord_715704).sum := by decide
  have hdescent : baseEnd_715704 < baseStart_715704 := by decide
  rcases family_descends (prefixWord ++ tailWord_715704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715801 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 1, 5]
def baseStart_715801 : Nat := 118140960795 + 715801 * 2 ^ 59
def prefixEnd_715801 : Nat := 4983230072969 + 3 ^ 40 * 715801 * 2
def baseEnd_715801 : Nat := 122516655323019719665199

theorem tailTrace_715801 : CollatzResearch.WordTrace tailWord_715801 prefixEnd_715801 122516655323019719665199 := by
  unfold tailWord_715801
  simp only [CollatzResearch.WordTrace]
  refine ⟨26107407279782700923163257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17404938186521800615442171 26107407279782700923163257)
  ·
    refine ⟨19580555459837025692372443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26107407279782700923163257 19580555459837025692372443)
    ·
      refine ⟨29370833189755538538558665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19580555459837025692372443 29370833189755538538558665)
      ·
        refine ⟨22028124892316653903918999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29370833189755538538558665 22028124892316653903918999)
        ·
          refine ⟨33042187338474980855878499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22028124892316653903918999 33042187338474980855878499)
          ·
            refine ⟨49563281007712471283817749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33042187338474980855878499 49563281007712471283817749)
            ·
              refine ⟨2323278797236522091428957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49563281007712471283817749 2323278797236522091428957)
              ·
                refine ⟨871229548963695784285859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2323278797236522091428957 871229548963695784285859)
                ·
                  refine ⟨1306844323445543676428789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871229548963695784285859 1306844323445543676428789)
                  ·
                    refine ⟨122516655323019719665199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1306844323445543676428789 122516655323019719665199)
                    ·
                      rfl

theorem cell23_715801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_715801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715801 prefixEnd_715801 := by exact prefixLift 715801
  have htrace : WordTrace (prefixWord ++ tailWord_715801) baseStart_715801 baseEnd_715801 := by
    simpa [prefixWord, tailWord_715801, baseEnd_715801] using wordTrace_append hprefix tailTrace_715801
  have hstable : (prefixWord ++ tailWord_715801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715801).length < 2 ^ (prefixWord ++ tailWord_715801).sum := by decide
  have hdescent : baseEnd_715801 < baseStart_715801 := by decide
  rcases family_descends (prefixWord ++ tailWord_715801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715858 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_715858 : Nat := 118140960795 + 715858 * 2 ^ 59
def prefixEnd_715858 : Nat := 4983230072969 + 3 ^ 40 * 715858 * 2
def baseEnd_715858 : Nat := 367579234366365435982835

theorem tailTrace_715858 : CollatzResearch.WordTrace tailWord_715858 prefixEnd_715858 367579234366365435982835 := by
  unfold tailWord_715858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6527371560144049914497057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17406324160384133105325485 6527371560144049914497057)
  ·
    refine ⟨4895528670108037435872793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6527371560144049914497057 4895528670108037435872793)
    ·
      refine ⟨3671646502581028076904595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4895528670108037435872793 3671646502581028076904595)
      ·
        refine ⟨5507469753871542115356893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671646502581028076904595 5507469753871542115356893)
        ·
          refine ⟨2065301157701828293258835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5507469753871542115356893 2065301157701828293258835)
          ·
            refine ⟨3097951736552742439888253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065301157701828293258835 3097951736552742439888253)
            ·
              refine ⟨1161731901207278414958095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3097951736552742439888253 1161731901207278414958095)
              ·
                refine ⟨1742597851810917622437143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161731901207278414958095 1742597851810917622437143)
                ·
                  refine ⟨2613896777716376433655715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742597851810917622437143 2613896777716376433655715)
                  ·
                    refine ⟨3920845166574564650483573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2613896777716376433655715 3920845166574564650483573)
                    ·
                      refine ⟨367579234366365435982835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3920845166574564650483573 367579234366365435982835)
                      ·
                        rfl

theorem cell23_715858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_715858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715858 prefixEnd_715858 := by exact prefixLift 715858
  have htrace : WordTrace (prefixWord ++ tailWord_715858) baseStart_715858 baseEnd_715858 := by
    simpa [prefixWord, tailWord_715858, baseEnd_715858] using wordTrace_append hprefix tailTrace_715858
  have hstable : (prefixWord ++ tailWord_715858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715858).length < 2 ^ (prefixWord ++ tailWord_715858).sum := by decide
  have hdescent : baseEnd_715858 < baseStart_715858 := by decide
  rcases family_descends (prefixWord ++ tailWord_715858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715871 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 3]
def baseStart_715871 : Nat := 118140960795 + 715871 * 2 ^ 59
def prefixEnd_715871 : Nat := 4983230072969 + 3 ^ 40 * 715871 * 2
def baseEnd_715871 : Nat := 367585909614873885120275

theorem tailTrace_715871 : CollatzResearch.WordTrace tailWord_715871 prefixEnd_715871 367585909614873885120275 := by
  unfold tailWord_715871
  simp only [CollatzResearch.WordTrace]
  refine ⟨26109960389529102878211467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17406640259686068585474311 26109960389529102878211467)
  ·
    refine ⟨39164940584293654317317201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26109960389529102878211467 39164940584293654317317201)
    ·
      refine ⟨29373705438220240737987901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39164940584293654317317201 29373705438220240737987901)
      ·
        refine ⟨11015139539332590276745463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29373705438220240737987901 11015139539332590276745463)
        ·
          refine ⟨16522709308998885415118195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11015139539332590276745463 16522709308998885415118195)
          ·
            refine ⟨24784063963498328122677293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16522709308998885415118195 24784063963498328122677293)
            ·
              refine ⟨9294023986311873046003985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24784063963498328122677293 9294023986311873046003985)
              ·
                refine ⟨6970517989733904784502989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9294023986311873046003985 6970517989733904784502989)
                ·
                  refine ⟨2613944246150214294188621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6970517989733904784502989 2613944246150214294188621)
                  ·
                    refine ⟨980229092306330360320733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2613944246150214294188621 980229092306330360320733)
                    ·
                      refine ⟨367585909614873885120275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 980229092306330360320733 367585909614873885120275)
                      ·
                        rfl

theorem cell23_715871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_715871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715871 prefixEnd_715871 := by exact prefixLift 715871
  have htrace : WordTrace (prefixWord ++ tailWord_715871) baseStart_715871 baseEnd_715871 := by
    simpa [prefixWord, tailWord_715871, baseEnd_715871] using wordTrace_append hprefix tailTrace_715871
  have hstable : (prefixWord ++ tailWord_715871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715871).length < 2 ^ (prefixWord ++ tailWord_715871).sum := by decide
  have hdescent : baseEnd_715871 < baseStart_715871 := by decide
  rcases family_descends (prefixWord ++ tailWord_715871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715872 : List Nat := [2, 1, 1, 3, 2, 2, 3, 4, 1, 2, 2]
def baseStart_715872 : Nat := 118140960795 + 715872 * 2 ^ 59
def prefixEnd_715872 : Nat := 4983230072969 + 3 ^ 40 * 715872 * 2
def baseEnd_715872 : Nat := 367586423095528381207771

theorem tailTrace_715872 : CollatzResearch.WordTrace tailWord_715872 prefixEnd_715872 367586423095528381207771 := by
  unfold tailWord_715872
  simp only [CollatzResearch.WordTrace]
  refine ⟨13054998431262740024498935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17406664575016986699331913 13054998431262740024498935)
  ·
    refine ⟨19582497646894110036748403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13054998431262740024498935 19582497646894110036748403)
    ·
      refine ⟨29373746470341165055122605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19582497646894110036748403 29373746470341165055122605)
      ·
        refine ⟨11015154926377936895670977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29373746470341165055122605 11015154926377936895670977)
        ·
          refine ⟨8261366194783452671753233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11015154926377936895670977 8261366194783452671753233)
          ·
            refine ⟨6196024646087589503814925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8261366194783452671753233 6196024646087589503814925)
            ·
              refine ⟨2323509242282846063930597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6196024646087589503814925 2323509242282846063930597)
              ·
                refine ⟨435657982928033636986987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2323509242282846063930597 435657982928033636986987)
                ·
                  refine ⟨653486974392050455480481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435657982928033636986987 653486974392050455480481)
                  ·
                    refine ⟨490115230794037841610361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 653486974392050455480481 490115230794037841610361)
                    ·
                      refine ⟨367586423095528381207771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490115230794037841610361 367586423095528381207771)
                      ·
                        rfl

theorem cell23_715872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_715872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715872 prefixEnd_715872 := by exact prefixLift 715872
  have htrace : WordTrace (prefixWord ++ tailWord_715872) baseStart_715872 baseEnd_715872 := by
    simpa [prefixWord, tailWord_715872, baseEnd_715872] using wordTrace_append hprefix tailTrace_715872
  have hstable : (prefixWord ++ tailWord_715872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715872).length < 2 ^ (prefixWord ++ tailWord_715872).sum := by decide
  have hdescent : baseEnd_715872 < baseStart_715872 := by decide
  rcases family_descends (prefixWord ++ tailWord_715872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715888 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3]
def baseStart_715888 : Nat := 118140960795 + 715888 * 2 ^ 59
def prefixEnd_715888 : Nat := 4983230072969 + 3 ^ 40 * 715888 * 2
def baseEnd_715888 : Nat := 367594638786000318607697

theorem tailTrace_715888 : CollatzResearch.WordTrace tailWord_715888 prefixEnd_715888 367594638786000318607697 := by
  unfold tailWord_715888
  simp only [CollatzResearch.WordTrace]
  refine ⟨13055290215233757390790159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17407053620311676521053545 13055290215233757390790159)
  ·
    refine ⟨19582935322850636086185239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13055290215233757390790159 19582935322850636086185239)
    ·
      refine ⟨29374402984275954129277859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19582935322850636086185239 29374402984275954129277859)
      ·
        refine ⟨44061604476413931193916789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29374402984275954129277859 44061604476413931193916789)
        ·
          refine ⟨4130775419663806049429699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44061604476413931193916789 4130775419663806049429699)
          ·
            refine ⟨6196163129495709074144549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130775419663806049429699 6196163129495709074144549)
            ·
              refine ⟨1161780586780445451402103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6196163129495709074144549 1161780586780445451402103)
              ·
                refine ⟨1742670880170668177103155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161780586780445451402103 1742670880170668177103155)
                ·
                  refine ⟨2614006320256002265654733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742670880170668177103155 2614006320256002265654733)
                  ·
                    refine ⟨980252370096000849620525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2614006320256002265654733 980252370096000849620525)
                    ·
                      refine ⟨367594638786000318607697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 980252370096000849620525 367594638786000318607697)
                      ·
                        rfl

theorem cell23_715888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_715888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715888 prefixEnd_715888 := by exact prefixLift 715888
  have htrace : WordTrace (prefixWord ++ tailWord_715888) baseStart_715888 baseEnd_715888 := by
    simpa [prefixWord, tailWord_715888, baseEnd_715888] using wordTrace_append hprefix tailTrace_715888
  have hstable : (prefixWord ++ tailWord_715888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715888).length < 2 ^ (prefixWord ++ tailWord_715888).sum := by decide
  have hdescent : baseEnd_715888 < baseStart_715888 := by decide
  rcases family_descends (prefixWord ++ tailWord_715888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715901 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_715901 : Nat := 118140960795 + 715901 * 2 ^ 59
def prefixEnd_715901 : Nat := 4983230072969 + 3 ^ 40 * 715901 * 2
def baseEnd_715901 : Nat := 367601314034508767745137

theorem tailTrace_715901 : CollatzResearch.WordTrace tailWord_715901 prefixEnd_715901 367601314034508767745137 := by
  unfold tailWord_715901
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111054579420418001803557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17407369719613612001202371 26111054579420418001803557)
  ·
    refine ⟨4895822733641328375338167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26111054579420418001803557 4895822733641328375338167)
    ·
      refine ⟨7343734100461992563007251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4895822733641328375338167 7343734100461992563007251)
      ·
        refine ⟨11015601150692988844510877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7343734100461992563007251 11015601150692988844510877)
        ·
          refine ⟨4130850431509870816691579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11015601150692988844510877 4130850431509870816691579)
          ·
            refine ⟨6196275647264806225037369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130850431509870816691579 6196275647264806225037369)
            ·
              refine ⟨4647206735448604668778027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196275647264806225037369 4647206735448604668778027)
              ·
                refine ⟨6970810103172907003167041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647206735448604668778027 6970810103172907003167041)
                ·
                  refine ⟨5228107577379680252375281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6970810103172907003167041 5228107577379680252375281)
                  ·
                    refine ⟨3921080683034760189281461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5228107577379680252375281 3921080683034760189281461)
                    ·
                      refine ⟨367601314034508767745137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3921080683034760189281461 367601314034508767745137)
                      ·
                        rfl

theorem cell23_715901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_715901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715901 prefixEnd_715901 := by exact prefixLift 715901
  have htrace : WordTrace (prefixWord ++ tailWord_715901) baseStart_715901 baseEnd_715901 := by
    simpa [prefixWord, tailWord_715901, baseEnd_715901] using wordTrace_append hprefix tailTrace_715901
  have hstable : (prefixWord ++ tailWord_715901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715901).length < 2 ^ (prefixWord ++ tailWord_715901).sum := by decide
  have hdescent : baseEnd_715901 < baseStart_715901 := by decide
  rcases family_descends (prefixWord ++ tailWord_715901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715909 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 1, 2, 3]
def baseStart_715909 : Nat := 118140960795 + 715909 * 2 ^ 59
def prefixEnd_715909 : Nat := 4983230072969 + 3 ^ 40 * 715909 * 2
def baseEnd_715909 : Nat := 367605421879744736445101

theorem tailTrace_715909 : CollatzResearch.WordTrace tailWord_715909 prefixEnd_715909 367605421879744736445101 := by
  unfold tailWord_715909
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111346363391435368094781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17407564242260956912063187 26111346363391435368094781)
  ·
    refine ⟨9791754886271788263035543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26111346363391435368094781 9791754886271788263035543)
    ·
      refine ⟨14687632329407682394553315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9791754886271788263035543 14687632329407682394553315)
      ·
        refine ⟨22031448494111523591829973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14687632329407682394553315 22031448494111523591829973)
        ·
          refine ⟨516362074080738834183515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22031448494111523591829973 516362074080738834183515)
          ·
            refine ⟨774543111121108251275273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516362074080738834183515 774543111121108251275273)
            ·
              refine ⟨580907333340831188456455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774543111121108251275273 580907333340831188456455)
              ·
                refine ⟨871361000011246782684683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580907333340831188456455 871361000011246782684683)
                ·
                  refine ⟨1307041500016870174027025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871361000011246782684683 1307041500016870174027025)
                  ·
                    refine ⟨980281125012652630520269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1307041500016870174027025 980281125012652630520269)
                    ·
                      refine ⟨367605421879744736445101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 980281125012652630520269 367605421879744736445101)
                      ·
                        rfl

theorem cell23_715909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_715909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715909 prefixEnd_715909 := by exact prefixLift 715909
  have htrace : WordTrace (prefixWord ++ tailWord_715909) baseStart_715909 baseEnd_715909 := by
    simpa [prefixWord, tailWord_715909, baseEnd_715909] using wordTrace_append hprefix tailTrace_715909
  have hstable : (prefixWord ++ tailWord_715909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715909).length < 2 ^ (prefixWord ++ tailWord_715909).sum := by decide
  have hdescent : baseEnd_715909 < baseStart_715909 := by decide
  rcases family_descends (prefixWord ++ tailWord_715909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715922 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_715922 : Nat := 118140960795 + 715922 * 2 ^ 59
def prefixEnd_715922 : Nat := 4983230072969 + 3 ^ 40 * 715922 * 2
def baseEnd_715922 : Nat := 367612097128253185582541

theorem tailTrace_715922 : CollatzResearch.WordTrace tailWord_715922 prefixEnd_715922 367612097128253185582541 := by
  unfold tailWord_715922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6527955128086084647079505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17407880341562892392212013 6527955128086084647079505)
  ·
    refine ⟨4895966346064563485309629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6527955128086084647079505 4895966346064563485309629)
    ·
      refine ⟨1835987379774211306991111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4895966346064563485309629 1835987379774211306991111)
      ·
        refine ⟨2753981069661316960486667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835987379774211306991111 2753981069661316960486667)
        ·
          refine ⟨4130971604491975440730001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753981069661316960486667 4130971604491975440730001)
          ·
            refine ⟨3098228703368981580547501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130971604491975440730001 3098228703368981580547501)
            ·
              refine ⟨1161835763763368092705313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3098228703368981580547501 1161835763763368092705313)
              ·
                refine ⟨871376822822526069528985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161835763763368092705313 871376822822526069528985)
                ·
                  refine ⟨653532617116894552146739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 871376822822526069528985 653532617116894552146739)
                  ·
                    refine ⟨980298925675341828220109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653532617116894552146739 980298925675341828220109)
                    ·
                      refine ⟨367612097128253185582541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 980298925675341828220109 367612097128253185582541)
                      ·
                        rfl

theorem cell23_715922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_715922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715922 prefixEnd_715922 := by exact prefixLift 715922
  have htrace : WordTrace (prefixWord ++ tailWord_715922) baseStart_715922 baseEnd_715922 := by
    simpa [prefixWord, tailWord_715922, baseEnd_715922] using wordTrace_append hprefix tailTrace_715922
  have hstable : (prefixWord ++ tailWord_715922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715922).length < 2 ^ (prefixWord ++ tailWord_715922).sum := by decide
  have hdescent : baseEnd_715922 < baseStart_715922 := by decide
  rcases family_descends (prefixWord ++ tailWord_715922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715949 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_715949 : Nat := 118140960795 + 715949 * 2 ^ 59
def prefixEnd_715949 : Nat := 4983230072969 + 3 ^ 40 * 715949 * 2
def baseEnd_715949 : Nat := 367625961105924579944917

theorem tailTrace_715949 : CollatzResearch.WordTrace tailWord_715949 prefixEnd_715949 367625961105924579944917 := by
  unfold tailWord_715949
  simp only [CollatzResearch.WordTrace]
  refine ⟨26112805283246522199550901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17408536855497681466367267 26112805283246522199550901)
  ·
    refine ⟨2448075495304361456207897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26112805283246522199550901 2448075495304361456207897)
    ·
      refine ⟨1836056621478271092155923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2448075495304361456207897 1836056621478271092155923)
      ·
        refine ⟨2754084932217406638233885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836056621478271092155923 2754084932217406638233885)
        ·
          refine ⟨1032781849581527489337707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2754084932217406638233885 1032781849581527489337707)
          ·
            refine ⟨1549172774372291234006561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032781849581527489337707 1549172774372291234006561)
            ·
              refine ⟨1161879580779218425504921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549172774372291234006561 1161879580779218425504921)
              ·
                refine ⟨871409685584413819128691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161879580779218425504921 871409685584413819128691)
                ·
                  refine ⟨1307114528376620728693037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871409685584413819128691 1307114528376620728693037)
                  ·
                    refine ⟨490167948141232773259889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1307114528376620728693037 490167948141232773259889)
                    ·
                      refine ⟨367625961105924579944917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490167948141232773259889 367625961105924579944917)
                      ·
                        rfl

theorem cell23_715949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_715949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715949 prefixEnd_715949 := by exact prefixLift 715949
  have htrace : WordTrace (prefixWord ++ tailWord_715949) baseStart_715949 baseEnd_715949 := by
    simpa [prefixWord, tailWord_715949, baseEnd_715949] using wordTrace_append hprefix tailTrace_715949
  have hstable : (prefixWord ++ tailWord_715949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715949).length < 2 ^ (prefixWord ++ tailWord_715949).sum := by decide
  have hdescent : baseEnd_715949 < baseStart_715949 := by decide
  rcases family_descends (prefixWord ++ tailWord_715949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715951 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 7]
def baseStart_715951 : Nat := 118140960795 + 715951 * 2 ^ 59
def prefixEnd_715951 : Nat := 4983230072969 + 3 ^ 40 * 715951 * 2
def baseEnd_715951 : Nat := 40847443118581508013323

theorem tailTrace_715951 : CollatzResearch.WordTrace tailWord_715951 prefixEnd_715951 40847443118581508013323 := by
  unfold tailWord_715951
  simp only [CollatzResearch.WordTrace]
  refine ⟨26112878229239276541123707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17408585486159517694082471 26112878229239276541123707)
  ·
    refine ⟨39169317343858914811685561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26112878229239276541123707 39169317343858914811685561)
    ·
      refine ⟨29376988007894186108764171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39169317343858914811685561 29376988007894186108764171)
      ·
        refine ⟨44065482011841279163146257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29376988007894186108764171 44065482011841279163146257)
        ·
          refine ⟨33049111508880959372359693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44065482011841279163146257 33049111508880959372359693)
          ·
            refine ⟨12393416815830359764634885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33049111508880959372359693 12393416815830359764634885)
            ·
              refine ⟨2323765652968192455869041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12393416815830359764634885 2323765652968192455869041)
              ·
                refine ⟨1742824239726144341901781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2323765652968192455869041 1742824239726144341901781)
                ·
                  refine ⟨40847443118581508013323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1742824239726144341901781 40847443118581508013323)
                  ·
                    rfl

theorem cell23_715951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 7].length) (baseStart_715951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715951 prefixEnd_715951 := by exact prefixLift 715951
  have htrace : WordTrace (prefixWord ++ tailWord_715951) baseStart_715951 baseEnd_715951 := by
    simpa [prefixWord, tailWord_715951, baseEnd_715951] using wordTrace_append hprefix tailTrace_715951
  have hstable : (prefixWord ++ tailWord_715951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715951).length < 2 ^ (prefixWord ++ tailWord_715951).sum := by decide
  have hdescent : baseEnd_715951 < baseStart_715951 := by decide
  rcases family_descends (prefixWord ++ tailWord_715951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715991 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_715991 : Nat := 118140960795 + 715991 * 2 ^ 59
def prefixEnd_715991 : Nat := 4983230072969 + 3 ^ 40 * 715991 * 2
def baseEnd_715991 : Nat := 367647527293413415619723

theorem tailTrace_715991 : CollatzResearch.WordTrace tailWord_715991 prefixEnd_715991 367647527293413415619723 := by
  unfold tailWord_715991
  simp only [CollatzResearch.WordTrace]
  refine ⟨26114337149094363372579827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17409558099396242248386551 26114337149094363372579827)
  ·
    refine ⟨39171505723641545058869741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26114337149094363372579827 39171505723641545058869741)
    ·
      refine ⟨14689314646365579397076153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39171505723641545058869741 14689314646365579397076153)
      ·
        refine ⟨11016985984774184547807115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14689314646365579397076153 11016985984774184547807115)
        ·
          refine ⟨16525478977161276821710673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11016985984774184547807115 16525478977161276821710673)
          ·
            refine ⟨12394109232870957616283005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16525478977161276821710673 12394109232870957616283005)
            ·
              refine ⟨4647790962326609106106127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12394109232870957616283005 4647790962326609106106127)
              ·
                refine ⟨6971686443489913659159191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4647790962326609106106127 6971686443489913659159191)
                ·
                  refine ⟨10457529665234870488738787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6971686443489913659159191 10457529665234870488738787)
                  ·
                    refine ⟨15686294497852305733108181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10457529665234870488738787 15686294497852305733108181)
                    ·
                      refine ⟨367647527293413415619723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15686294497852305733108181 367647527293413415619723)
                      ·
                        rfl

theorem cell23_715991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_715991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_715991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_715991 prefixEnd_715991 := by exact prefixLift 715991
  have htrace : WordTrace (prefixWord ++ tailWord_715991) baseStart_715991 baseEnd_715991 := by
    simpa [prefixWord, tailWord_715991, baseEnd_715991] using wordTrace_append hprefix tailTrace_715991
  have hstable : (prefixWord ++ tailWord_715991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715991).length < 2 ^ (prefixWord ++ tailWord_715991).sum := by decide
  have hdescent : baseEnd_715991 < baseStart_715991 := by decide
  rcases family_descends (prefixWord ++ tailWord_715991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716015 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 2, 5]
def baseStart_716015 : Nat := 118140960795 + 716015 * 2 ^ 59
def prefixEnd_716015 : Nat := 4983230072969 + 3 ^ 40 * 716015 * 2
def baseEnd_716015 : Nat := 122553283609707107239871

theorem tailTrace_716015 : CollatzResearch.WordTrace tailWord_716015 prefixEnd_716015 122553283609707107239871 := by
  unfold tailWord_716015
  simp only [CollatzResearch.WordTrace]
  refine ⟨26115212501007415471453499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17410141667338276980968999 26115212501007415471453499)
  ·
    refine ⟨39172818751511123207180249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26115212501007415471453499 39172818751511123207180249)
    ·
      refine ⟨29379614063633342405385187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39172818751511123207180249 29379614063633342405385187)
      ·
        refine ⟨44069421095450013608077781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29379614063633342405385187 44069421095450013608077781)
        ·
          refine ⟨1032877056924609693939323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 44069421095450013608077781 1032877056924609693939323)
          ·
            refine ⟨1549315585386914540908985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032877056924609693939323 1549315585386914540908985)
            ·
              refine ⟨1161986689040185905681739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549315585386914540908985 1161986689040185905681739)
              ·
                refine ⟨1742980033560278858522609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161986689040185905681739 1742980033560278858522609)
                ·
                  refine ⟨1307235025170209143891957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1742980033560278858522609 1307235025170209143891957)
                  ·
                    refine ⟨122553283609707107239871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1307235025170209143891957 122553283609707107239871)
                    ·
                      rfl

theorem cell23_716015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_716015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716015 prefixEnd_716015 := by exact prefixLift 716015
  have htrace : WordTrace (prefixWord ++ tailWord_716015) baseStart_716015 baseEnd_716015 := by
    simpa [prefixWord, tailWord_716015, baseEnd_716015] using wordTrace_append hprefix tailTrace_716015
  have hstable : (prefixWord ++ tailWord_716015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716015).length < 2 ^ (prefixWord ++ tailWord_716015).sum := by decide
  have hdescent : baseEnd_716015 < baseStart_716015 := by decide
  rcases family_descends (prefixWord ++ tailWord_716015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716072 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_716072 : Nat := 118140960795 + 716072 * 2 ^ 59
def prefixEnd_716072 : Nat := 4983230072969 + 3 ^ 40 * 716072 * 2
def baseEnd_716072 : Nat := 367689119226427598706851

theorem tailTrace_716072 : CollatzResearch.WordTrace tailWord_716072 prefixEnd_716072 367689119226427598706851 := by
  unfold tailWord_716072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13058645730900457103139235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17411527641200609470852313 13058645730900457103139235)
  ·
    refine ⟨19587968596350685654708853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13058645730900457103139235 19587968596350685654708853)
    ·
      refine ⟨1836372055907876780128955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19587968596350685654708853 1836372055907876780128955)
      ·
        refine ⟨2754558083861815170193433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836372055907876780128955 2754558083861815170193433)
        ·
          refine ⟨2065918562896361377645075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2754558083861815170193433 2065918562896361377645075)
          ·
            refine ⟨3098877844344542066467613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2065918562896361377645075 3098877844344542066467613)
            ·
              refine ⟨1162079191629203274925355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3098877844344542066467613 1162079191629203274925355)
              ·
                refine ⟨1743118787443804912388033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162079191629203274925355 1743118787443804912388033)
                ·
                  refine ⟨1307339090582853684291025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1743118787443804912388033 1307339090582853684291025)
                  ·
                    refine ⟨980504317937140263218269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1307339090582853684291025 980504317937140263218269)
                    ·
                      refine ⟨367689119226427598706851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 980504317937140263218269 367689119226427598706851)
                      ·
                        rfl

theorem cell23_716072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_716072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716072 prefixEnd_716072 := by exact prefixLift 716072
  have htrace : WordTrace (prefixWord ++ tailWord_716072) baseStart_716072 baseEnd_716072 := by
    simpa [prefixWord, tailWord_716072, baseEnd_716072] using wordTrace_append hprefix tailTrace_716072
  have hstable : (prefixWord ++ tailWord_716072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716072).length < 2 ^ (prefixWord ++ tailWord_716072).sum := by decide
  have hdescent : baseEnd_716072 < baseStart_716072 := by decide
  rcases family_descends (prefixWord ++ tailWord_716072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716209 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_716209 : Nat := 118140960795 + 716209 * 2 ^ 59
def prefixEnd_716209 : Nat := 4983230072969 + 3 ^ 40 * 716209 * 2
def baseEnd_716209 : Nat := 367759466076093562693721

theorem tailTrace_716209 : CollatzResearch.WordTrace tailWord_716209 prefixEnd_716209 367759466076093562693721 := by
  unfold tailWord_716209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26122288262304586604015681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17414858841536391069343787 26122288262304586604015681)
  ·
    refine ⟨19591716196728439953011761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26122288262304586604015681 19591716196728439953011761)
    ·
      refine ⟨14693787147546329964758821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19591716196728439953011761 14693787147546329964758821)
      ·
        refine ⟨2755085090164936868392279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14693787147546329964758821 2755085090164936868392279)
        ·
          refine ⟨4132627635247405302588419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755085090164936868392279 4132627635247405302588419)
          ·
            refine ⟨6198941452871107953882629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132627635247405302588419 6198941452871107953882629)
            ·
              refine ⟨1162301522413332741352993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6198941452871107953882629 1162301522413332741352993)
              ·
                refine ⟨871726141809999556014745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162301522413332741352993 871726141809999556014745)
                ·
                  refine ⟨653794606357499667011059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 871726141809999556014745 653794606357499667011059)
                  ·
                    refine ⟨980691909536249500516589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 653794606357499667011059 980691909536249500516589)
                    ·
                      refine ⟨367759466076093562693721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 980691909536249500516589 367759466076093562693721)
                      ·
                        rfl

theorem cell23_716209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_716209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716209 prefixEnd_716209 := by exact prefixLift 716209
  have htrace : WordTrace (prefixWord ++ tailWord_716209) baseStart_716209 baseEnd_716209 := by
    simpa [prefixWord, tailWord_716209, baseEnd_716209] using wordTrace_append hprefix tailTrace_716209
  have hstable : (prefixWord ++ tailWord_716209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716209).length < 2 ^ (prefixWord ++ tailWord_716209).sum := by decide
  have hdescent : baseEnd_716209 < baseStart_716209 := by decide
  rcases family_descends (prefixWord ++ tailWord_716209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716245 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_716245 : Nat := 118140960795 + 716245 * 2 ^ 59
def prefixEnd_716245 : Nat := 4983230072969 + 3 ^ 40 * 716245 * 2
def baseEnd_716245 : Nat := 367777951379655421843555

theorem tailTrace_716245 : CollatzResearch.WordTrace tailWord_716245 prefixEnd_716245 367777951379655421843555 := by
  unfold tailWord_716245
  simp only [CollatzResearch.WordTrace]
  refine ⟨26123601290174164752326189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17415734193449443168217459 26123601290174164752326189)
  ·
    refine ⟨9796350483815311782122321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26123601290174164752326189 9796350483815311782122321)
    ·
      refine ⟨7347262862861483836591741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9796350483815311782122321 7347262862861483836591741)
      ·
        refine ⟨2755223573573056438721903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7347262862861483836591741 2755223573573056438721903)
        ·
          refine ⟨4132835360359584658082855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755223573573056438721903 4132835360359584658082855)
          ·
            refine ⟨6199253040539376987124283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132835360359584658082855 6199253040539376987124283)
            ·
              refine ⟨9298879560809065480686425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6199253040539376987124283 9298879560809065480686425)
              ·
                refine ⟨6974159670606799110514819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9298879560809065480686425 6974159670606799110514819)
                ·
                  refine ⟨10461239505910198665772229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6974159670606799110514819 10461239505910198665772229)
                  ·
                    refine ⟨1961482407358162249832293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10461239505910198665772229 1961482407358162249832293)
                    ·
                      refine ⟨367777951379655421843555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1961482407358162249832293 367777951379655421843555)
                      ·
                        rfl

theorem cell23_716245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_716245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716245 prefixEnd_716245 := by exact prefixLift 716245
  have htrace : WordTrace (prefixWord ++ tailWord_716245) baseStart_716245 baseEnd_716245 := by
    simpa [prefixWord, tailWord_716245, baseEnd_716245] using wordTrace_append hprefix tailTrace_716245
  have hstable : (prefixWord ++ tailWord_716245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716245).length < 2 ^ (prefixWord ++ tailWord_716245).sum := by decide
  have hdescent : baseEnd_716245 < baseStart_716245 := by decide
  rcases family_descends (prefixWord ++ tailWord_716245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716253 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_716253 : Nat := 118140960795 + 716253 * 2 ^ 59
def prefixEnd_716253 : Nat := 4983230072969 + 3 ^ 40 * 716253 * 2
def baseEnd_716253 : Nat := 367782059224891390543519

theorem tailTrace_716253 : CollatzResearch.WordTrace tailWord_716253 prefixEnd_716253 367782059224891390543519 := by
  unfold tailWord_716253
  simp only [CollatzResearch.WordTrace]
  refine ⟨26123893074145182118617413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17415928716096788079078275 26123893074145182118617413)
  ·
    refine ⟨4898229951402221647240765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26123893074145182118617413 4898229951402221647240765)
    ·
      refine ⟨1836836231775833117715287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4898229951402221647240765 1836836231775833117715287)
      ·
        refine ⟨2755254347663749676572931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836836231775833117715287 2755254347663749676572931)
        ·
          refine ⟨4132881521495624514859397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755254347663749676572931 4132881521495624514859397)
          ·
            refine ⟨774915285280429596536137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4132881521495624514859397 774915285280429596536137)
            ·
              refine ⟨581186463960322197402103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774915285280429596536137 581186463960322197402103)
              ·
                refine ⟨871779695940483296103155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581186463960322197402103 871779695940483296103155)
                ·
                  refine ⟨1307669543910724944154733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871779695940483296103155 1307669543910724944154733)
                  ·
                    refine ⟨490376078966521854058025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1307669543910724944154733 490376078966521854058025)
                    ·
                      refine ⟨367782059224891390543519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 490376078966521854058025 367782059224891390543519)
                      ·
                        rfl

theorem cell23_716253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_716253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_716253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_716253 prefixEnd_716253 := by exact prefixLift 716253
  have htrace : WordTrace (prefixWord ++ tailWord_716253) baseStart_716253 baseEnd_716253 := by
    simpa [prefixWord, tailWord_716253, baseEnd_716253] using wordTrace_append hprefix tailTrace_716253
  have hstable : (prefixWord ++ tailWord_716253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716253).length < 2 ^ (prefixWord ++ tailWord_716253).sum := by decide
  have hdescent : baseEnd_716253 < baseStart_716253 := by decide
  rcases family_descends (prefixWord ++ tailWord_716253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
