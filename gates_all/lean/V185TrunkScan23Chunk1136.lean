import V185TrunkScan23Chunk1135

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6728348 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6728348 : Nat := 118140960795 + 6728348 * 2 ^ 59
def prefixEnd_6728348 : Nat := 4983230072969 + 3 ^ 40 * 6728348 * 2
def baseEnd_6728348 : Nat := 3454876534717546541206897

theorem tailTrace_6728348 : CollatzResearch.WordTrace tailWord_6728348 prefixEnd_6728348 3454876534717546541206897 := by
  unfold tailWord_6728348
  simp only [CollatzResearch.WordTrace]
  refine ⟨122701506114175890599080849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163602008152234520798774465 122701506114175890599080849)
  ·
    refine ⟨92026129585631917949310637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122701506114175890599080849 92026129585631917949310637)
    ·
      refine ⟨34509798594611969230991489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92026129585631917949310637 34509798594611969230991489)
      ·
        refine ⟨25882348945958976923243617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34509798594611969230991489 25882348945958976923243617)
        ·
          refine ⟨19411761709469232692432713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25882348945958976923243617 19411761709469232692432713)
          ·
            refine ⟨14558821282101924519324535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19411761709469232692432713 14558821282101924519324535)
            ·
              refine ⟨21838231923152886778986803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14558821282101924519324535 21838231923152886778986803)
              ·
                refine ⟨32757347884729330168480205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21838231923152886778986803 32757347884729330168480205)
                ·
                  refine ⟨12284005456773498813180077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32757347884729330168480205 12284005456773498813180077)
                  ·
                    refine ⟨4606502046290062054942529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12284005456773498813180077 4606502046290062054942529)
                    ·
                      refine ⟨3454876534717546541206897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606502046290062054942529 3454876534717546541206897)
                      ·
                        rfl

theorem cell23_6728348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6728348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728348 prefixEnd_6728348 := by exact prefixLift 6728348
  have htrace : WordTrace (prefixWord ++ tailWord_6728348) baseStart_6728348 baseEnd_6728348 := by
    simpa [prefixWord, tailWord_6728348, baseEnd_6728348] using wordTrace_append hprefix tailTrace_6728348
  have hstable : (prefixWord ++ tailWord_6728348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728348).length < 2 ^ (prefixWord ++ tailWord_6728348).sum := by decide
  have hdescent : baseEnd_6728348 < baseStart_6728348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728474 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 10]
def baseStart_6728474 : Nat := 118140960795 + 6728474 * 2 ^ 59
def prefixEnd_6728474 : Nat := 4983230072969 + 3 ^ 40 * 6728474 * 2
def baseEnd_6728474 : Nat := 383882359253334783136813

theorem tailTrace_6728474 : CollatzResearch.WordTrace tailWord_6728474 prefixEnd_6728474 383882359253334783136813 := by
  unfold tailWord_6728474
  simp only [CollatzResearch.WordTrace]
  refine ⟨61351901956473826179312119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163605071883930203144832317 61351901956473826179312119)
  ·
    refine ⟨92027852934710739268968179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61351901956473826179312119 92027852934710739268968179)
    ·
      refine ⟨138041779402066108903452269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92027852934710739268968179 138041779402066108903452269)
      ·
        refine ⟨51765667275774790838794601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138041779402066108903452269 51765667275774790838794601)
        ·
          refine ⟨38824250456831093129095951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51765667275774790838794601 38824250456831093129095951)
          ·
            refine ⟨58236375685246639693643927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38824250456831093129095951 58236375685246639693643927)
            ·
              refine ⟨87354563527869959540465891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58236375685246639693643927 87354563527869959540465891)
              ·
                refine ⟨131031845291804939310698837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87354563527869959540465891 131031845291804939310698837)
                ·
                  refine ⟨383882359253334783136813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 131031845291804939310698837 383882359253334783136813)
                  ·
                    rfl

theorem cell23_6728474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_6728474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728474 prefixEnd_6728474 := by exact prefixLift 6728474
  have htrace : WordTrace (prefixWord ++ tailWord_6728474) baseStart_6728474 baseEnd_6728474 := by
    simpa [prefixWord, tailWord_6728474, baseEnd_6728474] using wordTrace_append hprefix tailTrace_6728474
  have hstable : (prefixWord ++ tailWord_6728474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728474).length < 2 ^ (prefixWord ++ tailWord_6728474).sum := by decide
  have hdescent : baseEnd_6728474 < baseStart_6728474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728488 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_6728488 : Nat := 118140960795 + 6728488 * 2 ^ 59
def prefixEnd_6728488 : Nat := 4983230072969 + 3 ^ 40 * 6728488 * 2
def baseEnd_6728488 : Nat := 3454948422009175993456253

theorem tailTrace_6728488 : CollatzResearch.WordTrace tailWord_6728488 prefixEnd_6728488 3454948422009175993456253 := by
  unfold tailWord_6728488
  simp only [CollatzResearch.WordTrace]
  refine ⟨122704059223922292554129059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163605412298563056738838745 122704059223922292554129059)
  ·
    refine ⟨184056088835883438831193589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122704059223922292554129059 184056088835883438831193589)
    ·
      refine ⟨17255258328364072390424399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184056088835883438831193589 17255258328364072390424399)
      ·
        refine ⟨25882887492546108585636599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17255258328364072390424399 25882887492546108585636599)
        ·
          refine ⟨38824331238819162878454899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25882887492546108585636599 38824331238819162878454899)
          ·
            refine ⟨58236496858228744317682349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38824331238819162878454899 58236496858228744317682349)
            ·
              refine ⟨21838686321835779119130881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58236496858228744317682349 21838686321835779119130881)
              ·
                refine ⟨16379014741376834339348161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21838686321835779119130881 16379014741376834339348161)
                ·
                  refine ⟨12284261056032625754511121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16379014741376834339348161 12284261056032625754511121)
                  ·
                    refine ⟨9213195792024469315883341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12284261056032625754511121 9213195792024469315883341)
                    ·
                      refine ⟨3454948422009175993456253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9213195792024469315883341 3454948422009175993456253)
                      ·
                        rfl

theorem cell23_6728488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_6728488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728488 prefixEnd_6728488 := by exact prefixLift 6728488
  have htrace : WordTrace (prefixWord ++ tailWord_6728488) baseStart_6728488 baseEnd_6728488 := by
    simpa [prefixWord, tailWord_6728488, baseEnd_6728488] using wordTrace_append hprefix tailTrace_6728488
  have hstable : (prefixWord ++ tailWord_6728488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728488).length < 2 ^ (prefixWord ++ tailWord_6728488).sum := by decide
  have hdescent : baseEnd_6728488 < baseStart_6728488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728521 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 3, 5]
def baseStart_6728521 : Nat := 118140960795 + 6728521 * 2 ^ 59
def prefixEnd_6728521 : Nat := 4983230072969 + 3 ^ 40 * 6728521 * 2
def baseEnd_6728521 : Nat := 1151655122290258121447867

theorem tailTrace_6728521 : CollatzResearch.WordTrace tailWord_6728521 prefixEnd_6728521 1151655122290258121447867 := by
  unfold tailWord_6728521
  simp only [CollatzResearch.WordTrace]
  refine ⟨245409322056725031744209417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163606214704483354496139611 245409322056725031744209417)
  ·
    refine ⟨184056991542543773808157063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245409322056725031744209417 184056991542543773808157063)
    ·
      refine ⟨276085487313815660712235595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184056991542543773808157063 276085487313815660712235595)
      ·
        refine ⟨414128230970723491068353393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276085487313815660712235595 414128230970723491068353393)
        ·
          refine ⟨310596173228042618301265045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414128230970723491068353393 310596173228042618301265045)
          ·
            refine ⟨14559195620064497732871799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 310596173228042618301265045 14559195620064497732871799)
            ·
              refine ⟨21838793430096746599307699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14559195620064497732871799 21838793430096746599307699)
              ·
                refine ⟨32758190145145119898961549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21838793430096746599307699 32758190145145119898961549)
                ·
                  refine ⟨12284321304429419962110581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32758190145145119898961549 12284321304429419962110581)
                  ·
                    refine ⟨1151655122290258121447867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12284321304429419962110581 1151655122290258121447867)
                    ·
                      rfl

theorem cell23_6728521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_6728521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728521 prefixEnd_6728521 := by exact prefixLift 6728521
  have htrace : WordTrace (prefixWord ++ tailWord_6728521) baseStart_6728521 baseEnd_6728521 := by
    simpa [prefixWord, tailWord_6728521, baseEnd_6728521] using wordTrace_append hprefix tailTrace_6728521
  have hstable : (prefixWord ++ tailWord_6728521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728521).length < 2 ^ (prefixWord ++ tailWord_6728521).sum := by decide
  have hdescent : baseEnd_6728521 < baseStart_6728521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728528 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 2, 3, 2]
def baseStart_6728528 : Nat := 118140960795 + 6728528 * 2 ^ 59
def prefixEnd_6728528 : Nat := 4983230072969 + 3 ^ 40 * 6728528 * 2
def baseEnd_6728528 : Nat := 3454968961235355836956069

theorem tailTrace_6728528 : CollatzResearch.WordTrace tailWord_6728528 prefixEnd_6728528 3454968961235355836956069 := by
  unfold tailWord_6728528
  simp only [CollatzResearch.WordTrace]
  refine ⟨122704788683849835969857119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163606384911799781293142825 122704788683849835969857119)
  ·
    refine ⟨184057183025774753954785679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122704788683849835969857119 184057183025774753954785679)
    ·
      refine ⟨276085774538662130932178519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184057183025774753954785679 276085774538662130932178519)
      ·
        refine ⟨414128661807993196398267779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276085774538662130932178519 414128661807993196398267779)
        ·
          refine ⟨621192992711989794597401669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414128661807993196398267779 621192992711989794597401669)
          ·
            refine ⟨116473686133498086487012813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 621192992711989794597401669 116473686133498086487012813)
            ·
              refine ⟨43677632300061782432629805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116473686133498086487012813 43677632300061782432629805)
              ·
                refine ⟨16379112112523168412236177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43677632300061782432629805 16379112112523168412236177)
                ·
                  refine ⟨12284334084392376309177133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16379112112523168412236177 12284334084392376309177133)
                  ·
                    refine ⟨4606625281647141115941425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12284334084392376309177133 4606625281647141115941425)
                    ·
                      refine ⟨3454968961235355836956069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606625281647141115941425 3454968961235355836956069)
                      ·
                        rfl

theorem cell23_6728528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 3, 2].length) (baseStart_6728528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728528 prefixEnd_6728528 := by exact prefixLift 6728528
  have htrace : WordTrace (prefixWord ++ tailWord_6728528) baseStart_6728528 baseEnd_6728528 := by
    simpa [prefixWord, tailWord_6728528, baseEnd_6728528] using wordTrace_append hprefix tailTrace_6728528
  have hstable : (prefixWord ++ tailWord_6728528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728528).length < 2 ^ (prefixWord ++ tailWord_6728528).sum := by decide
  have hdescent : baseEnd_6728528 < baseStart_6728528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728546 : List Nat := [3, 3, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_6728546 : Nat := 118140960795 + 6728546 * 2 ^ 59
def prefixEnd_6728546 : Nat := 4983230072969 + 3 ^ 40 * 6728546 * 2
def baseEnd_6728546 : Nat := 1151659401295712255510329

theorem tailTrace_6728546 : CollatzResearch.WordTrace tailWord_6728546 prefixEnd_6728546 1151659401295712255510329 := by
  unfold tailWord_6728546
  simp only [CollatzResearch.WordTrace]
  refine ⟨61352558470408615253467373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163606822587756307342579661 61352558470408615253467373)
  ·
    refine ⟨23007209426403230720050265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61352558470408615253467373 23007209426403230720050265)
    ·
      refine ⟨17255407069802423040037699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23007209426403230720050265 17255407069802423040037699)
      ·
        refine ⟨25883110604703634560056549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17255407069802423040037699 25883110604703634560056549)
        ·
          refine ⟨4853083238381931480010603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25883110604703634560056549 4853083238381931480010603)
          ·
            refine ⟨7279624857572897220015905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853083238381931480010603 7279624857572897220015905)
            ·
              refine ⟨5459718643179672915011929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7279624857572897220015905 5459718643179672915011929)
              ·
                refine ⟨4094788982384754686258947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5459718643179672915011929 4094788982384754686258947)
                ·
                  refine ⟨6142183473577132029388421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094788982384754686258947 6142183473577132029388421)
                  ·
                    refine ⟨1151659401295712255510329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6142183473577132029388421 1151659401295712255510329)
                    ·
                      rfl

theorem cell23_6728546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_6728546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728546 prefixEnd_6728546 := by exact prefixLift 6728546
  have htrace : WordTrace (prefixWord ++ tailWord_6728546) baseStart_6728546 baseEnd_6728546 := by
    simpa [prefixWord, tailWord_6728546, baseEnd_6728546] using wordTrace_append hprefix tailTrace_6728546
  have hstable : (prefixWord ++ tailWord_6728546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728546).length < 2 ^ (prefixWord ++ tailWord_6728546).sum := by decide
  have hdescent : baseEnd_6728546 < baseStart_6728546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728552 : List Nat := [2, 1, 4, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6728552 : Nat := 118140960795 + 6728552 * 2 ^ 59
def prefixEnd_6728552 : Nat := 4983230072969 + 3 ^ 40 * 6728552 * 2
def baseEnd_6728552 : Nat := 3454981284771063743055959

theorem tailTrace_6728552 : CollatzResearch.WordTrace tailWord_6728552 prefixEnd_6728552 3454981284771063743055959 := by
  unfold tailWord_6728552
  simp only [CollatzResearch.WordTrace]
  refine ⟨122705226359806362019293955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163606968479741816025725273 122705226359806362019293955)
  ·
    refine ⟨184057839539709543028940933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122705226359806362019293955 184057839539709543028940933)
    ·
      refine ⟨34510844913695539317926425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184057839539709543028940933 34510844913695539317926425)
      ·
        refine ⟨25883133685271654488444819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34510844913695539317926425 25883133685271654488444819)
        ·
          refine ⟨38824700527907481732667229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25883133685271654488444819 38824700527907481732667229)
          ·
            refine ⟨14559262697965305649750211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38824700527907481732667229 14559262697965305649750211)
            ·
              refine ⟨21838894046947958474625317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14559262697965305649750211 21838894046947958474625317)
              ·
                refine ⟨4094792633802742213992247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21838894046947958474625317 4094792633802742213992247)
                ·
                  refine ⟨6142188950704113320988371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094792633802742213992247 6142188950704113320988371)
                  ·
                    refine ⟨9213283426056169981482557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6142188950704113320988371 9213283426056169981482557)
                    ·
                      refine ⟨3454981284771063743055959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9213283426056169981482557 3454981284771063743055959)
                      ·
                        rfl

theorem cell23_6728552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6728552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728552 prefixEnd_6728552 := by exact prefixLift 6728552
  have htrace : WordTrace (prefixWord ++ tailWord_6728552) baseStart_6728552 baseEnd_6728552 := by
    simpa [prefixWord, tailWord_6728552, baseEnd_6728552] using wordTrace_append hprefix tailTrace_6728552
  have hstable : (prefixWord ++ tailWord_6728552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728552).length < 2 ^ (prefixWord ++ tailWord_6728552).sum := by decide
  have hdescent : baseEnd_6728552 < baseStart_6728552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728571 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4]
def baseStart_6728571 : Nat := 118140960795 + 6728571 * 2 ^ 59
def prefixEnd_6728571 : Nat := 4983230072969 + 3 ^ 40 * 6728571 * 2
def baseEnd_6728571 : Nat := 3454991040903499168718371

theorem tailTrace_6728571 : CollatzResearch.WordTrace tailWord_6728571 prefixEnd_6728571 3454991040903499168718371 := by
  unfold tailWord_6728571
  simp only [CollatzResearch.WordTrace]
  refine ⟨245411145706543890283529567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163607430471029260189019711 245411145706543890283529567)
  ·
    refine ⟨368116718559815835425294351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245411145706543890283529567 368116718559815835425294351)
    ·
      refine ⟨552175077839723753137941527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368116718559815835425294351 552175077839723753137941527)
      ·
        refine ⟨828262616759585629706912291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552175077839723753137941527 828262616759585629706912291)
        ·
          refine ⟨1242393925139378444560368437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828262616759585629706912291 1242393925139378444560368437)
          ·
            refine ⟨116474430481816729177534541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1242393925139378444560368437 116474430481816729177534541)
            ·
              refine ⟨43677911430681273441575453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116474430481816729177534541 43677911430681273441575453)
              ·
                refine ⟨16379216786505477540590795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43677911430681273441575453 16379216786505477540590795)
                ·
                  refine ⟨24568825179758216310886193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16379216786505477540590795 24568825179758216310886193)
                  ·
                    refine ⟨18426618884818662233164645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24568825179758216310886193 18426618884818662233164645)
                    ·
                      refine ⟨3454991040903499168718371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18426618884818662233164645 3454991040903499168718371)
                      ·
                        rfl

theorem cell23_6728571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4].length) (baseStart_6728571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728571 prefixEnd_6728571 := by exact prefixLift 6728571
  have htrace : WordTrace (prefixWord ++ tailWord_6728571) baseStart_6728571 baseEnd_6728571 := by
    simpa [prefixWord, tailWord_6728571, baseEnd_6728571] using wordTrace_append hprefix tailTrace_6728571
  have hstable : (prefixWord ++ tailWord_6728571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728571).length < 2 ^ (prefixWord ++ tailWord_6728571).sum := by decide
  have hdescent : baseEnd_6728571 < baseStart_6728571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728602 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_6728602 : Nat := 118140960795 + 6728602 * 2 ^ 59
def prefixEnd_6728602 : Nat := 4983230072969 + 3 ^ 40 * 6728602 * 2
def baseEnd_6728602 : Nat := 1151668986267929515810243

theorem tailTrace_6728602 : CollatzResearch.WordTrace tailWord_6728602 prefixEnd_6728602 1151668986267929515810243 := by
  unfold tailWord_6728602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61353069092357895644477015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163608184246287721718605373 61353069092357895644477015)
  ·
    refine ⟨92029603638536843466715523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61353069092357895644477015 92029603638536843466715523)
    ·
      refine ⟨138044405457805265200073285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92029603638536843466715523 138044405457805265200073285)
      ·
        refine ⟨25883326023338487225013741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138044405457805265200073285 25883326023338487225013741)
        ·
          refine ⟨9706247258751932709380153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25883326023338487225013741 9706247258751932709380153)
          ·
            refine ⟨7279685444063949532035115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9706247258751932709380153 7279685444063949532035115)
            ·
              refine ⟨10919528166095924298052673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279685444063949532035115 10919528166095924298052673)
              ·
                refine ⟨8189646124571943223539505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10919528166095924298052673 8189646124571943223539505)
                ·
                  refine ⟨6142234593428957417654629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8189646124571943223539505 6142234593428957417654629)
                  ·
                    refine ⟨1151668986267929515810243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6142234593428957417654629 1151668986267929515810243)
                    ·
                      rfl

theorem cell23_6728602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_6728602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728602 prefixEnd_6728602 := by exact prefixLift 6728602
  have htrace : WordTrace (prefixWord ++ tailWord_6728602) baseStart_6728602 baseEnd_6728602 := by
    simpa [prefixWord, tailWord_6728602, baseEnd_6728602] using wordTrace_append hprefix tailTrace_6728602
  have hstable : (prefixWord ++ tailWord_6728602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728602).length < 2 ^ (prefixWord ++ tailWord_6728602).sum := by decide
  have hdescent : baseEnd_6728602 < baseStart_6728602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728609 : List Nat := [1, 2, 3, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6728609 : Nat := 118140960795 + 6728609 * 2 ^ 59
def prefixEnd_6728609 : Nat := 4983230072969 + 3 ^ 40 * 6728609 * 2
def baseEnd_6728609 : Nat := 3455010553168370020043197

theorem tailTrace_6728609 : CollatzResearch.WordTrace tailWord_6728609 prefixEnd_6728609 3455010553168370020043197 := by
  unfold tailWord_6728609
  simp only [CollatzResearch.WordTrace]
  refine ⟨245412531680406222773412881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163608354453604148515608587 245412531680406222773412881)
  ·
    refine ⟨184059398760304667080059661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245412531680406222773412881 184059398760304667080059661)
    ·
      refine ⟨69022274535114250155022373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184059398760304667080059661 69022274535114250155022373)
      ·
        refine ⟨12941676475333921904066695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69022274535114250155022373 12941676475333921904066695)
        ·
          refine ⟨19412514713000882856100043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12941676475333921904066695 19412514713000882856100043)
          ·
            refine ⟨29118772069501324284150065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19412514713000882856100043 29118772069501324284150065)
            ·
              refine ⟨21839079052125993213112549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29118772069501324284150065 21839079052125993213112549)
              ·
                refine ⟨4094827322273623727458603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21839079052125993213112549 4094827322273623727458603)
                ·
                  refine ⟨6142240983410435591187905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094827322273623727458603 6142240983410435591187905)
                  ·
                    refine ⟨4606680737557826693390929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6142240983410435591187905 4606680737557826693390929)
                    ·
                      refine ⟨3455010553168370020043197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606680737557826693390929 3455010553168370020043197)
                      ·
                        rfl

theorem cell23_6728609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6728609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728609 prefixEnd_6728609 := by exact prefixLift 6728609
  have htrace : WordTrace (prefixWord ++ tailWord_6728609) baseStart_6728609 baseEnd_6728609 := by
    simpa [prefixWord, tailWord_6728609, baseEnd_6728609] using wordTrace_append hprefix tailTrace_6728609
  have hstable : (prefixWord ++ tailWord_6728609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728609).length < 2 ^ (prefixWord ++ tailWord_6728609).sum := by decide
  have hdescent : baseEnd_6728609 < baseStart_6728609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728631 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_6728631 : Nat := 118140960795 + 6728631 * 2 ^ 59
def prefixEnd_6728631 : Nat := 4983230072969 + 3 ^ 40 * 6728631 * 2
def baseEnd_6728631 : Nat := 3455021849742768933968095

theorem tailTrace_6728631 : CollatzResearch.WordTrace tailWord_6728631 prefixEnd_6728631 3455021849742768933968095 := by
  unfold tailWord_6728631
  simp only [CollatzResearch.WordTrace]
  refine ⟨245413334086326520530713747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163608889390884347020475831 245413334086326520530713747)
  ·
    refine ⟨368120001129489780796070621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245413334086326520530713747 368120001129489780796070621)
    ·
      refine ⟨138045000423558667798526483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368120001129489780796070621 138045000423558667798526483)
      ·
        refine ⟨207067500635338001697789725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138045000423558667798526483 207067500635338001697789725)
        ·
          refine ⟨77650312738251750636671147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207067500635338001697789725 77650312738251750636671147)
          ·
            refine ⟨116475469107377625955006721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77650312738251750636671147 116475469107377625955006721)
            ·
              refine ⟨87356601830533219466255041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116475469107377625955006721 87356601830533219466255041)
              ·
                refine ⟨65517451372899914599691281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87356601830533219466255041 65517451372899914599691281)
                ·
                  refine ⟨49138088529674935949768461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65517451372899914599691281 49138088529674935949768461)
                  ·
                    refine ⟨18426783198628100981163173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49138088529674935949768461 18426783198628100981163173)
                    ·
                      refine ⟨3455021849742768933968095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18426783198628100981163173 3455021849742768933968095)
                      ·
                        rfl

theorem cell23_6728631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_6728631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728631 prefixEnd_6728631 := by exact prefixLift 6728631
  have htrace : WordTrace (prefixWord ++ tailWord_6728631) baseStart_6728631 baseEnd_6728631 := by
    simpa [prefixWord, tailWord_6728631, baseEnd_6728631] using wordTrace_append hprefix tailTrace_6728631
  have hstable : (prefixWord ++ tailWord_6728631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728631).length < 2 ^ (prefixWord ++ tailWord_6728631).sum := by decide
  have hdescent : baseEnd_6728631 < baseStart_6728631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728646 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6728646 : Nat := 118140960795 + 6728646 * 2 ^ 59
def prefixEnd_6728646 : Nat := 4983230072969 + 3 ^ 40 * 6728646 * 2
def baseEnd_6728646 : Nat := 3455029551952586375280527

theorem tailTrace_6728646 : CollatzResearch.WordTrace tailWord_6728646 prefixEnd_6728646 3455029551952586375280527 := by
  unfold tailWord_6728646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7669183786914755565390931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163609254120848118728339861 7669183786914755565390931)
  ·
    refine ⟨11503775680372133348086397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7669183786914755565390931 11503775680372133348086397)
    ·
      refine ⟨4313915880139550005532399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11503775680372133348086397 4313915880139550005532399)
      ·
        refine ⟨6470873820209325008298599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4313915880139550005532399 6470873820209325008298599)
        ·
          refine ⟨9706310730313987512447899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6470873820209325008298599 9706310730313987512447899)
          ·
            refine ⟨14559466095470981268671849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9706310730313987512447899 14559466095470981268671849)
            ·
              refine ⟨10919599571603235951503887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14559466095470981268671849 10919599571603235951503887)
              ·
                refine ⟨16379399357404853927255831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10919599571603235951503887 16379399357404853927255831)
                ·
                  refine ⟨24569099036107280890883747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16379399357404853927255831 24569099036107280890883747)
                  ·
                    refine ⟨36853648554160921336325621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24569099036107280890883747 36853648554160921336325621)
                    ·
                      refine ⟨3455029551952586375280527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36853648554160921336325621 3455029551952586375280527)
                      ·
                        rfl

theorem cell23_6728646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6728646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728646 prefixEnd_6728646 := by exact prefixLift 6728646
  have htrace : WordTrace (prefixWord ++ tailWord_6728646) baseStart_6728646 baseEnd_6728646 := by
    simpa [prefixWord, tailWord_6728646, baseEnd_6728646] using wordTrace_append hprefix tailTrace_6728646
  have hstable : (prefixWord ++ tailWord_6728646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728646).length < 2 ^ (prefixWord ++ tailWord_6728646).sum := by decide
  have hdescent : baseEnd_6728646 < baseStart_6728646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728651 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5]
def baseStart_6728651 : Nat := 118140960795 + 6728651 * 2 ^ 59
def prefixEnd_6728651 : Nat := 4983230072969 + 3 ^ 40 * 6728651 * 2
def baseEnd_6728651 : Nat := 3455032119355858855718003

theorem tailTrace_6728651 : CollatzResearch.WordTrace tailWord_6728651 prefixEnd_6728651 3455032119355858855718003 := by
  unfold tailWord_6728651
  simp only [CollatzResearch.WordTrace]
  refine ⟨245414063546254063946441807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163609375697502709297627871 245414063546254063946441807)
  ·
    refine ⟨368121095319381095919662711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245414063546254063946441807 368121095319381095919662711)
    ·
      refine ⟨552181642979071643879494067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368121095319381095919662711 552181642979071643879494067)
      ·
        refine ⟨828272464468607465819241101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552181642979071643879494067 828272464468607465819241101)
        ·
          refine ⟨310602174175727799682215413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828272464468607465819241101 310602174175727799682215413)
          ·
            refine ⟨29118953828974481220207695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310602174175727799682215413 29118953828974481220207695)
            ·
              refine ⟨43678430743461721830311543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29118953828974481220207695 43678430743461721830311543)
              ·
                refine ⟨65517646115192582745467315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43678430743461721830311543 65517646115192582745467315)
                ·
                  refine ⟨98276469172788874118200973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65517646115192582745467315 98276469172788874118200973)
                  ·
                    refine ⟨36853675939795827794325365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98276469172788874118200973 36853675939795827794325365)
                    ·
                      refine ⟨3455032119355858855718003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36853675939795827794325365 3455032119355858855718003)
                      ·
                        rfl

theorem cell23_6728651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_6728651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728651 prefixEnd_6728651 := by exact prefixLift 6728651
  have htrace : WordTrace (prefixWord ++ tailWord_6728651) baseStart_6728651 baseEnd_6728651 := by
    simpa [prefixWord, tailWord_6728651, baseEnd_6728651] using wordTrace_append hprefix tailTrace_6728651
  have hstable : (prefixWord ++ tailWord_6728651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728651).length < 2 ^ (prefixWord ++ tailWord_6728651).sum := by decide
  have hdescent : baseEnd_6728651 < baseStart_6728651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728686 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_6728686 : Nat := 118140960795 + 6728686 * 2 ^ 59
def prefixEnd_6728686 : Nat := 4983230072969 + 3 ^ 40 * 6728686 * 2
def baseEnd_6728686 : Nat := 3455050091178766218780343

theorem tailTrace_6728686 : CollatzResearch.WordTrace tailWord_6728686 prefixEnd_6728686 3455050091178766218780343 := by
  unfold tailWord_6728686
  simp only [CollatzResearch.WordTrace]
  refine ⟨30676917512640908115495739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163610226734084843282643941 30676917512640908115495739)
  ·
    refine ⟨46015376268961362173243609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30676917512640908115495739 46015376268961362173243609)
    ·
      refine ⟨34511532201721021629932707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46015376268961362173243609 34511532201721021629932707)
      ·
        refine ⟨51767298302581532444899061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34511532201721021629932707 51767298302581532444899061)
        ·
          refine ⟨4853184215867018666709287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51767298302581532444899061 4853184215867018666709287)
          ·
            refine ⟨7279776323800528000063931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853184215867018666709287 7279776323800528000063931)
            ·
              refine ⟨10919664485700792000095897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279776323800528000063931 10919664485700792000095897)
              ·
                refine ⟨8189748364275594000071923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10919664485700792000095897 8189748364275594000071923)
                ·
                  refine ⟨12284622546413391000107885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8189748364275594000071923 12284622546413391000107885)
                  ·
                    refine ⟨4606733454905021625040457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12284622546413391000107885 4606733454905021625040457)
                    ·
                      refine ⟨3455050091178766218780343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606733454905021625040457 3455050091178766218780343)
                      ·
                        rfl

theorem cell23_6728686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_6728686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728686 prefixEnd_6728686 := by exact prefixLift 6728686
  have htrace : WordTrace (prefixWord ++ tailWord_6728686) baseStart_6728686 baseEnd_6728686 := by
    simpa [prefixWord, tailWord_6728686, baseEnd_6728686] using wordTrace_append hprefix tailTrace_6728686
  have hstable : (prefixWord ++ tailWord_6728686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728686).length < 2 ^ (prefixWord ++ tailWord_6728686).sum := by decide
  have hdescent : baseEnd_6728686 < baseStart_6728686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728725 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_6728725 : Nat := 118140960795 + 6728725 * 2 ^ 59
def prefixEnd_6728725 : Nat := 4983230072969 + 3 ^ 40 * 6728725 * 2
def baseEnd_6728725 : Nat := 3455070116924291566192663

theorem tailTrace_6728725 : CollatzResearch.WordTrace tailWord_6728725 prefixEnd_6728725 3455070116924291566192663 := by
  unfold tailWord_6728725
  simp only [CollatzResearch.WordTrace]
  refine ⟨245416762547985974584635629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163611175031990649723090419 245416762547985974584635629)
  ·
    refine ⟨92031285955494740469238361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245416762547985974584635629 92031285955494740469238361)
    ·
      refine ⟨69023464466621055351928771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92031285955494740469238361 69023464466621055351928771)
      ·
        refine ⟨103535196699931583027893157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69023464466621055351928771 103535196699931583027893157)
        ·
          refine ⟨19412849381237171817729967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103535196699931583027893157 19412849381237171817729967)
          ·
            refine ⟨29119274071855757726594951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19412849381237171817729967 29119274071855757726594951)
            ·
              refine ⟨43678911107783636589892427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29119274071855757726594951 43678911107783636589892427)
              ·
                refine ⟨65518366661675454884838641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43678911107783636589892427 65518366661675454884838641)
                ·
                  refine ⟨49138774996256591163628981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65518366661675454884838641 49138774996256591163628981)
                  ·
                    refine ⟨4606760155899055421590217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49138774996256591163628981 4606760155899055421590217)
                    ·
                      refine ⟨3455070116924291566192663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606760155899055421590217 3455070116924291566192663)
                      ·
                        rfl

theorem cell23_6728725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_6728725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728725 prefixEnd_6728725 := by exact prefixLift 6728725
  have htrace : WordTrace (prefixWord ++ tailWord_6728725) baseStart_6728725 baseEnd_6728725 := by
    simpa [prefixWord, tailWord_6728725, baseEnd_6728725] using wordTrace_append hprefix tailTrace_6728725
  have hstable : (prefixWord ++ tailWord_6728725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728725).length < 2 ^ (prefixWord ++ tailWord_6728725).sum := by decide
  have hdescent : baseEnd_6728725 < baseStart_6728725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728728 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_6728728 : Nat := 118140960795 + 6728728 * 2 ^ 59
def prefixEnd_6728728 : Nat := 4983230072969 + 3 ^ 40 * 6728728 * 2
def baseEnd_6728728 : Nat := 3455071657366255054455149

theorem tailTrace_6728728 : CollatzResearch.WordTrace tailWord_6728728 prefixEnd_6728728 3455071657366255054455149 := by
  unfold tailWord_6728728
  simp only [CollatzResearch.WordTrace]
  refine ⟨122708435983487553048497419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163611247977983404064663225 122708435983487553048497419)
  ·
    refine ⟨184062653975231329572746129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122708435983487553048497419 184062653975231329572746129)
    ·
      refine ⟨138046990481423497179559597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184062653975231329572746129 138046990481423497179559597)
      ·
        refine ⟨51767621430533811442334849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138046990481423497179559597 51767621430533811442334849)
        ·
          refine ⟨38825716072900358581751137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51767621430533811442334849 38825716072900358581751137)
          ·
            refine ⟨29119287054675268936313353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38825716072900358581751137 29119287054675268936313353)
            ·
              refine ⟨21839465291006451702235015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29119287054675268936313353 21839465291006451702235015)
              ·
                refine ⟨32759197936509677553352523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21839465291006451702235015 32759197936509677553352523)
                ·
                  refine ⟨49138796904764516330028785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32759197936509677553352523 49138796904764516330028785)
                  ·
                    refine ⟨36854097678573387247521589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49138796904764516330028785 36854097678573387247521589)
                    ·
                      refine ⟨3455071657366255054455149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36854097678573387247521589 3455071657366255054455149)
                      ·
                        rfl

theorem cell23_6728728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_6728728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728728 prefixEnd_6728728 := by exact prefixLift 6728728
  have htrace : WordTrace (prefixWord ++ tailWord_6728728) baseStart_6728728 baseEnd_6728728 := by
    simpa [prefixWord, tailWord_6728728, baseEnd_6728728] using wordTrace_append hprefix tailTrace_6728728
  have hstable : (prefixWord ++ tailWord_6728728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728728).length < 2 ^ (prefixWord ++ tailWord_6728728).sum := by decide
  have hdescent : baseEnd_6728728 < baseStart_6728728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728782 : List Nat := [4, 1, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_6728782 : Nat := 118140960795 + 6728782 * 2 ^ 59
def prefixEnd_6728782 : Nat := 4983230072969 + 3 ^ 40 * 6728782 * 2
def baseEnd_6728782 : Nat := 1151699795107199281059967

theorem tailTrace_6728782 : CollatzResearch.WordTrace tailWord_6728782 prefixEnd_6728782 1151699795107199281059967 := by
  unfold tailWord_6728782
  simp only [CollatzResearch.WordTrace]
  refine ⟨30677355188597434164932575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163612561005852982212973733 30677355188597434164932575)
  ·
    refine ⟨46016032782896151247398863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30677355188597434164932575 46016032782896151247398863)
    ·
      refine ⟨69024049174344226871098295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46016032782896151247398863 69024049174344226871098295)
      ·
        refine ⟨103536073761516340306647443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69024049174344226871098295 103536073761516340306647443)
        ·
          refine ⟨155304110642274510459971165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103536073761516340306647443 155304110642274510459971165)
          ·
            refine ⟨58239041490852941422489187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155304110642274510459971165 58239041490852941422489187)
            ·
              refine ⟨87358562236279412133733781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58239041490852941422489187 87358562236279412133733781)
              ·
                refine ⟨4094932604825597443768771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87358562236279412133733781 4094932604825597443768771)
                ·
                  refine ⟨6142398907238396165653157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094932604825597443768771 6142398907238396165653157)
                  ·
                    refine ⟨1151699795107199281059967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6142398907238396165653157 1151699795107199281059967)
                    ·
                      rfl

theorem cell23_6728782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_6728782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728782 prefixEnd_6728782 := by exact prefixLift 6728782
  have htrace : WordTrace (prefixWord ++ tailWord_6728782) baseStart_6728782 baseEnd_6728782 := by
    simpa [prefixWord, tailWord_6728782, baseEnd_6728782] using wordTrace_append hprefix tailTrace_6728782
  have hstable : (prefixWord ++ tailWord_6728782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728782).length < 2 ^ (prefixWord ++ tailWord_6728782).sum := by decide
  have hdescent : baseEnd_6728782 < baseStart_6728782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728815 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 1, 5, 2]
def baseStart_6728815 : Nat := 118140960795 + 6728815 * 2 ^ 59
def prefixEnd_6728815 : Nat := 4983230072969 + 3 ^ 40 * 6728815 * 2
def baseEnd_6728815 : Nat := 3455116330183196214067249

theorem tailTrace_6728815 : CollatzResearch.WordTrace tailWord_6728815 prefixEnd_6728815 3455116330183196214067249 := by
  unfold tailWord_6728815
  simp only [CollatzResearch.WordTrace]
  refine ⟨245420045117659919955411899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163613363411773279970274599 245420045117659919955411899)
  ·
    refine ⟨368130067676489879933117849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245420045117659919955411899 368130067676489879933117849)
    ·
      refine ⟨276097550757367409949838387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368130067676489879933117849 276097550757367409949838387)
      ·
        refine ⟨414146326136051114924757581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276097550757367409949838387 414146326136051114924757581)
        ·
          refine ⟨155304872301019168096784093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414146326136051114924757581 155304872301019168096784093)
          ·
            refine ⟨58239327112882188036294035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155304872301019168096784093 58239327112882188036294035)
            ·
              refine ⟨87358990669323282054441053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58239327112882188036294035 87358990669323282054441053)
              ·
                refine ⟨32759621500996230770415395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87358990669323282054441053 32759621500996230770415395)
                ·
                  refine ⟨49139432251494346155623093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32759621500996230770415395 49139432251494346155623093)
                  ·
                    refine ⟨4606821773577594952089665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49139432251494346155623093 4606821773577594952089665)
                    ·
                      refine ⟨3455116330183196214067249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606821773577594952089665 3455116330183196214067249)
                      ·
                        rfl

theorem cell23_6728815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5, 2].length) (baseStart_6728815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728815 prefixEnd_6728815 := by exact prefixLift 6728815
  have htrace : WordTrace (prefixWord ++ tailWord_6728815) baseStart_6728815 baseEnd_6728815 := by
    simpa [prefixWord, tailWord_6728815, baseEnd_6728815] using wordTrace_append hprefix tailTrace_6728815
  have hstable : (prefixWord ++ tailWord_6728815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728815).length < 2 ^ (prefixWord ++ tailWord_6728815).sum := by decide
  have hdescent : baseEnd_6728815 < baseStart_6728815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728848 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_6728848 : Nat := 118140960795 + 6728848 * 2 ^ 59
def prefixEnd_6728848 : Nat := 4983230072969 + 3 ^ 40 * 6728848 * 2
def baseEnd_6728848 : Nat := 3455133275044794584954597

theorem tailTrace_6728848 : CollatzResearch.WordTrace tailWord_6728848 prefixEnd_6728848 3455133275044794584954597 := by
  unfold tailWord_6728848
  simp only [CollatzResearch.WordTrace]
  refine ⟨122710624363270183295681599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163614165817693577727575465 122710624363270183295681599)
  ·
    refine ⟨184065936544905274943522399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122710624363270183295681599 184065936544905274943522399)
    ·
      refine ⟨276098904817357912415283599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184065936544905274943522399 276098904817357912415283599)
      ·
        refine ⟨414148357226036868622925399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276098904817357912415283599 414148357226036868622925399)
        ·
          refine ⟨621222535839055302934388099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414148357226036868622925399 621222535839055302934388099)
          ·
            refine ⟨931833803758582954401582149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621222535839055302934388099 931833803758582954401582149)
            ·
              refine ⟨174718838204734303950296653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 931833803758582954401582149 174718838204734303950296653)
              ·
                refine ⟨65519564326775363981361245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174718838204734303950296653 65519564326775363981361245)
                ·
                  refine ⟨24569836622540761493010467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65519564326775363981361245 24569836622540761493010467)
                  ·
                    refine ⟨36854754933811142239515701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24569836622540761493010467 36854754933811142239515701)
                    ·
                      refine ⟨3455133275044794584954597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36854754933811142239515701 3455133275044794584954597)
                      ·
                        rfl

theorem cell23_6728848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_6728848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728848 prefixEnd_6728848 := by exact prefixLift 6728848
  have htrace : WordTrace (prefixWord ++ tailWord_6728848) baseStart_6728848 baseEnd_6728848 := by
    simpa [prefixWord, tailWord_6728848, baseEnd_6728848] using wordTrace_append hprefix tailTrace_6728848
  have hstable : (prefixWord ++ tailWord_6728848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728848).length < 2 ^ (prefixWord ++ tailWord_6728848).sum := by decide
  have hdescent : baseEnd_6728848 < baseStart_6728848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728866 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_6728866 : Nat := 118140960795 + 6728866 * 2 ^ 59
def prefixEnd_6728866 : Nat := 4983230072969 + 3 ^ 40 * 6728866 * 2
def baseEnd_6728866 : Nat := 3455142517696575514529515

theorem tailTrace_6728866 : CollatzResearch.WordTrace tailWord_6728866 prefixEnd_6728866 3455142517696575514529515 := by
  unfold tailWord_6728866
  simp only [CollatzResearch.WordTrace]
  refine ⟨61355476310118788916379613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163614603493650103777012301 61355476310118788916379613)
  ·
    refine ⟨23008303616294545843642355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61355476310118788916379613 23008303616294545843642355)
    ·
      refine ⟨34512455424441818765463533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23008303616294545843642355 34512455424441818765463533)
      ·
        refine ⟨12942170784165682037048825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34512455424441818765463533 12942170784165682037048825)
        ·
          refine ⟨9706628088124261527786619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12942170784165682037048825 9706628088124261527786619)
          ·
            refine ⟨14559942132186392291679929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9706628088124261527786619 14559942132186392291679929)
            ·
              refine ⟨10919956599139794218759947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14559942132186392291679929 10919956599139794218759947)
              ·
                refine ⟨16379934898709691328139921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10919956599139794218759947 16379934898709691328139921)
                ·
                  refine ⟨12284951174032268496104941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16379934898709691328139921 12284951174032268496104941)
                  ·
                    refine ⟨4606856690262100686039353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12284951174032268496104941 4606856690262100686039353)
                    ·
                      refine ⟨3455142517696575514529515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606856690262100686039353 3455142517696575514529515)
                      ·
                        rfl

theorem cell23_6728866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_6728866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728866 prefixEnd_6728866 := by exact prefixLift 6728866
  have htrace : WordTrace (prefixWord ++ tailWord_6728866) baseStart_6728866 baseEnd_6728866 := by
    simpa [prefixWord, tailWord_6728866, baseEnd_6728866] using wordTrace_append hprefix tailTrace_6728866
  have hstable : (prefixWord ++ tailWord_6728866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728866).length < 2 ^ (prefixWord ++ tailWord_6728866).sum := by decide
  have hdescent : baseEnd_6728866 < baseStart_6728866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728882 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_6728882 : Nat := 118140960795 + 6728882 * 2 ^ 59
def prefixEnd_6728882 : Nat := 4983230072969 + 3 ^ 40 * 6728882 * 2
def baseEnd_6728882 : Nat := 3455150733387047451929441

theorem tailTrace_6728882 : CollatzResearch.WordTrace tailWord_6728882 prefixEnd_6728882 3455150733387047451929441 := by
  unfold tailWord_6728882
  simp only [CollatzResearch.WordTrace]
  refine ⟨61355622202104297599525225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163614992538944793598733933 61355622202104297599525225)
  ·
    refine ⟨46016716651578223199643919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61355622202104297599525225 46016716651578223199643919)
    ·
      refine ⟨69025074977367334799465879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46016716651578223199643919 69025074977367334799465879)
      ·
        refine ⟨103537612466051002199198819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69025074977367334799465879 103537612466051002199198819)
        ·
          refine ⟨155306418699076503298798229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103537612466051002199198819 155306418699076503298798229)
          ·
            refine ⟨7279988376519211092131167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155306418699076503298798229 7279988376519211092131167)
            ·
              refine ⟨10919982564778816638196751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279988376519211092131167 10919982564778816638196751)
              ·
                refine ⟨16379973847168224957295127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10919982564778816638196751 16379973847168224957295127)
                ·
                  refine ⟨24569960770752337435942691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16379973847168224957295127 24569960770752337435942691)
                  ·
                    refine ⟨36854941156128506153914037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24569960770752337435942691 36854941156128506153914037)
                    ·
                      refine ⟨3455150733387047451929441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36854941156128506153914037 3455150733387047451929441)
                      ·
                        rfl

theorem cell23_6728882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_6728882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728882 prefixEnd_6728882 := by exact prefixLift 6728882
  have htrace : WordTrace (prefixWord ++ tailWord_6728882) baseStart_6728882 baseEnd_6728882 := by
    simpa [prefixWord, tailWord_6728882, baseEnd_6728882] using wordTrace_append hprefix tailTrace_6728882
  have hstable : (prefixWord ++ tailWord_6728882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728882).length < 2 ^ (prefixWord ++ tailWord_6728882).sum := by decide
  have hdescent : baseEnd_6728882 < baseStart_6728882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728888 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_6728888 : Nat := 118140960795 + 6728888 * 2 ^ 59
def prefixEnd_6728888 : Nat := 4983230072969 + 3 ^ 40 * 6728888 * 2
def baseEnd_6728888 : Nat := 3455153814270974428454413

theorem tailTrace_6728888 : CollatzResearch.WordTrace tailWord_6728888 prefixEnd_6728888 3455153814270974428454413 := by
  unfold tailWord_6728888
  simp only [CollatzResearch.WordTrace]
  refine ⟨122711353823197726711409659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163615138430930302281879545 122711353823197726711409659)
  ·
    refine ⟨184067030734796590067114489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122711353823197726711409659 184067030734796590067114489)
    ·
      refine ⟨138050273051097442550335867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184067030734796590067114489 138050273051097442550335867)
      ·
        refine ⟨207075409576646163825503801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138050273051097442550335867 207075409576646163825503801)
        ·
          refine ⟨155306557182484622869127851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207075409576646163825503801 155306557182484622869127851)
          ·
            refine ⟨232959835773726934303691777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155306557182484622869127851 232959835773726934303691777)
            ·
              refine ⟨174719876830295200727768833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232959835773726934303691777 174719876830295200727768833)
              ·
                refine ⟨131039907622721400545826625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174719876830295200727768833 131039907622721400545826625)
                ·
                  refine ⟨98279930717041050409369969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131039907622721400545826625 98279930717041050409369969)
                  ·
                    refine ⟨73709948037780787807027477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98279930717041050409369969 73709948037780787807027477)
                    ·
                      refine ⟨3455153814270974428454413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73709948037780787807027477 3455153814270974428454413)
                      ·
                        rfl

theorem cell23_6728888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_6728888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728888 prefixEnd_6728888 := by exact prefixLift 6728888
  have htrace : WordTrace (prefixWord ++ tailWord_6728888) baseStart_6728888 baseEnd_6728888 := by
    simpa [prefixWord, tailWord_6728888, baseEnd_6728888] using wordTrace_append hprefix tailTrace_6728888
  have hstable : (prefixWord ++ tailWord_6728888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728888).length < 2 ^ (prefixWord ++ tailWord_6728888).sum := by decide
  have hdescent : baseEnd_6728888 < baseStart_6728888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728933 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 1, 2, 3]
def baseStart_6728933 : Nat := 118140960795 + 6728933 * 2 ^ 59
def prefixEnd_6728933 : Nat := 4983230072969 + 3 ^ 40 * 6728933 * 2
def baseEnd_6728933 : Nat := 3455176920900426752391707

theorem tailTrace_6728933 : CollatzResearch.WordTrace tailWord_6728933 prefixEnd_6728933 3455176920900426752391707 := by
  unfold tailWord_6728933
  simp only [CollatzResearch.WordTrace]
  refine ⟨245424348931232426108207453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163616232620821617405471635 245424348931232426108207453)
  ·
    refine ⟨92034130849212159790577795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245424348931232426108207453 92034130849212159790577795)
    ·
      refine ⟨138051196273818239685866693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92034130849212159790577795 138051196273818239685866693)
      ·
        refine ⟨25884599301340919941100005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138051196273818239685866693 25884599301340919941100005)
        ·
          refine ⟨4853362369001422488956251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25884599301340919941100005 4853362369001422488956251)
          ·
            refine ⟨7280043553502133733434377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853362369001422488956251 7280043553502133733434377)
            ·
              refine ⟨5460032665126600300075783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7280043553502133733434377 5460032665126600300075783)
              ·
                refine ⟨8190048997689900450113675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460032665126600300075783 8190048997689900450113675)
                ·
                  refine ⟨12285073496534850675170513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190048997689900450113675 12285073496534850675170513)
                  ·
                    refine ⟨9213805122401138006377885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12285073496534850675170513 9213805122401138006377885)
                    ·
                      refine ⟨3455176920900426752391707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9213805122401138006377885 3455176920900426752391707)
                      ·
                        rfl

theorem cell23_6728933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_6728933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728933 prefixEnd_6728933 := by exact prefixLift 6728933
  have htrace : WordTrace (prefixWord ++ tailWord_6728933) baseStart_6728933 baseEnd_6728933 := by
    simpa [prefixWord, tailWord_6728933, baseEnd_6728933] using wordTrace_append hprefix tailTrace_6728933
  have hstable : (prefixWord ++ tailWord_6728933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728933).length < 2 ^ (prefixWord ++ tailWord_6728933).sum := by decide
  have hdescent : baseEnd_6728933 < baseStart_6728933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728939 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 1, 3, 2]
def baseStart_6728939 : Nat := 118140960795 + 6728939 * 2 ^ 59
def prefixEnd_6728939 : Nat := 4983230072969 + 3 ^ 40 * 6728939 * 2
def baseEnd_6728939 : Nat := 3455180001784353728916679

theorem tailTrace_6728939 : CollatzResearch.WordTrace tailWord_6728939 prefixEnd_6728939 3455180001784353728916679 := by
  unfold tailWord_6728939
  simp only [CollatzResearch.WordTrace]
  refine ⟨245424567769210689132925871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163616378512807126088617247 245424567769210689132925871)
  ·
    refine ⟨368136851653816033699388807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245424567769210689132925871 368136851653816033699388807)
    ·
      refine ⟨552205277480724050549083211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368136851653816033699388807 552205277480724050549083211)
      ·
        refine ⟨828307916221086075823624817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552205277480724050549083211 828307916221086075823624817)
        ·
          refine ⟨621230937165814556867718613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828307916221086075823624817 621230937165814556867718613)
          ·
            refine ⟨14560100089823778676587155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 621230937165814556867718613 14560100089823778676587155)
            ·
              refine ⟨21840150134735668014880733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14560100089823778676587155 21840150134735668014880733)
              ·
                refine ⟨8190056300525875505580275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21840150134735668014880733 8190056300525875505580275)
                ·
                  refine ⟨12285084450788813258370413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190056300525875505580275 12285084450788813258370413)
                  ·
                    refine ⟨4606906669045804971888905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12285084450788813258370413 4606906669045804971888905)
                    ·
                      refine ⟨3455180001784353728916679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4606906669045804971888905 3455180001784353728916679)
                      ·
                        rfl

theorem cell23_6728939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 3, 2].length) (baseStart_6728939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728939 prefixEnd_6728939 := by exact prefixLift 6728939
  have htrace : WordTrace (prefixWord ++ tailWord_6728939) baseStart_6728939 baseEnd_6728939 := by
    simpa [prefixWord, tailWord_6728939, baseEnd_6728939] using wordTrace_append hprefix tailTrace_6728939
  have hstable : (prefixWord ++ tailWord_6728939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728939).length < 2 ^ (prefixWord ++ tailWord_6728939).sum := by decide
  have hdescent : baseEnd_6728939 < baseStart_6728939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6728965 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_6728965 : Nat := 118140960795 + 6728965 * 2 ^ 59
def prefixEnd_6728965 : Nat := 4983230072969 + 3 ^ 40 * 6728965 * 2
def baseEnd_6728965 : Nat := 3455193352281370627191559

theorem tailTrace_6728965 : CollatzResearch.WordTrace tailWord_6728965 prefixEnd_6728965 3455193352281370627191559 := by
  unfold tailWord_6728965
  simp only [CollatzResearch.WordTrace]
  refine ⟨245425516067116495573372349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163617010711410997048914899 245425516067116495573372349)
  ·
    refine ⟨92034568525168685840014631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245425516067116495573372349 92034568525168685840014631)
    ·
      refine ⟨138051852787753028760021947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92034568525168685840014631 138051852787753028760021947)
      ·
        refine ⟨207077779181629543140032921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138051852787753028760021947 207077779181629543140032921)
        ·
          refine ⟨155308334386222157355024691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207077779181629543140032921 155308334386222157355024691)
          ·
            refine ⟨232962501579333236032537037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155308334386222157355024691 232962501579333236032537037)
            ·
              refine ⟨87360938092249963512201389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232962501579333236032537037 87360938092249963512201389)
              ·
                refine ⟨32760351784593736317075521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87360938092249963512201389 32760351784593736317075521)
                ·
                  refine ⟨24570263838445302237806641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32760351784593736317075521 24570263838445302237806641)
                  ·
                    refine ⟨18427697878833976678354981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24570263838445302237806641 18427697878833976678354981)
                    ·
                      refine ⟨3455193352281370627191559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18427697878833976678354981 3455193352281370627191559)
                      ·
                        rfl

theorem cell23_6728965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_6728965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6728965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6728965 prefixEnd_6728965 := by exact prefixLift 6728965
  have htrace : WordTrace (prefixWord ++ tailWord_6728965) baseStart_6728965 baseEnd_6728965 := by
    simpa [prefixWord, tailWord_6728965, baseEnd_6728965] using wordTrace_append hprefix tailTrace_6728965
  have hstable : (prefixWord ++ tailWord_6728965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6728965).length < 2 ^ (prefixWord ++ tailWord_6728965).sum := by decide
  have hdescent : baseEnd_6728965 < baseStart_6728965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6728965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729022 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_6729022 : Nat := 118140960795 + 6729022 * 2 ^ 59
def prefixEnd_6729022 : Nat := 4983230072969 + 3 ^ 40 * 6729022 * 2
def baseEnd_6729022 : Nat := 1151740873559558968059599

theorem tailTrace_6729022 : CollatzResearch.WordTrace tailWord_6729022 prefixEnd_6729022 1151740873559558968059599 := by
  unfold tailWord_6729022
  simp only [CollatzResearch.WordTrace]
  refine ⟨30678449378488749288524665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163618396685273329538798213 30678449378488749288524665)
  ·
    refine ⟨23008837033866561966393499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30678449378488749288524665 23008837033866561966393499)
    ·
      refine ⟨34513255550799842949590249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23008837033866561966393499 34513255550799842949590249)
      ·
        refine ⟨25884941663099882212192687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34513255550799842949590249 25884941663099882212192687)
        ·
          refine ⟨38827412494649823318289031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25884941663099882212192687 38827412494649823318289031)
          ·
            refine ⟨58241118741974734977433547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38827412494649823318289031 58241118741974734977433547)
            ·
              refine ⟨87361678112962102466150321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58241118741974734977433547 87361678112962102466150321)
              ·
                refine ⟨65521258584721576849612741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87361678112962102466150321 65521258584721576849612741)
                ·
                  refine ⟨12285235984635295659302389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65521258584721576849612741 12285235984635295659302389)
                  ·
                    refine ⟨1151740873559558968059599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12285235984635295659302389 1151740873559558968059599)
                    ·
                      rfl

theorem cell23_6729022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_6729022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729022 prefixEnd_6729022 := by exact prefixLift 6729022
  have htrace : WordTrace (prefixWord ++ tailWord_6729022) baseStart_6729022 baseEnd_6729022 := by
    simpa [prefixWord, tailWord_6729022, baseEnd_6729022] using wordTrace_append hprefix tailTrace_6729022
  have hstable : (prefixWord ++ tailWord_6729022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729022).length < 2 ^ (prefixWord ++ tailWord_6729022).sum := by decide
  have hdescent : baseEnd_6729022 < baseStart_6729022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729055 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_6729055 : Nat := 118140960795 + 6729055 * 2 ^ 59
def prefixEnd_6729055 : Nat := 4983230072969 + 3 ^ 40 * 6729055 * 2
def baseEnd_6729055 : Nat := 3455239565540275275066145

theorem tailTrace_6729055 : CollatzResearch.WordTrace tailWord_6729055 prefixEnd_6729055 3455239565540275275066145 := by
  unfold tailWord_6729055
  simp only [CollatzResearch.WordTrace]
  refine ⟨245428798636790440944148619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163619199091193627296099079 245428798636790440944148619)
  ·
    refine ⟨368143197955185661416222929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245428798636790440944148619 368143197955185661416222929)
    ·
      refine ⟨276107398466389246062167197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368143197955185661416222929 276107398466389246062167197)
      ·
        refine ⟨103540274424895967273312699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276107398466389246062167197 103540274424895967273312699)
        ·
          refine ⟨155310411637343950909969049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103540274424895967273312699 155310411637343950909969049)
          ·
            refine ⟨116482808728007963182476787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155310411637343950909969049 116482808728007963182476787)
            ·
              refine ⟨174724213092011944773715181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116482808728007963182476787 174724213092011944773715181)
              ·
                refine ⟨65521579909504479290143193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174724213092011944773715181 65521579909504479290143193)
                ·
                  refine ⟨49141184932128359467607395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65521579909504479290143193 49141184932128359467607395)
                  ·
                    refine ⟨73711777398192539201411093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49141184932128359467607395 73711777398192539201411093)
                    ·
                      refine ⟨3455239565540275275066145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73711777398192539201411093 3455239565540275275066145)
                      ·
                        rfl

theorem cell23_6729055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_6729055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729055 prefixEnd_6729055 := by exact prefixLift 6729055
  have htrace : WordTrace (prefixWord ++ tailWord_6729055) baseStart_6729055 baseEnd_6729055 := by
    simpa [prefixWord, tailWord_6729055, baseEnd_6729055] using wordTrace_append hprefix tailTrace_6729055
  have hstable : (prefixWord ++ tailWord_6729055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729055).length < 2 ^ (prefixWord ++ tailWord_6729055).sum := by decide
  have hdescent : baseEnd_6729055 < baseStart_6729055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729096 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6729096 : Nat := 118140960795 + 6729096 * 2 ^ 59
def prefixEnd_6729096 : Nat := 4983230072969 + 3 ^ 40 * 6729096 * 2
def baseEnd_6729096 : Nat := 3455260618247109614653457

theorem tailTrace_6729096 : CollatzResearch.WordTrace tailWord_6729096 prefixEnd_6729096 3455260618247109614653457 := by
  unfold tailWord_6729096
  simp only [CollatzResearch.WordTrace]
  refine ⟨122715147014820952473195571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163620196019761269964260761 122715147014820952473195571)
  ·
    refine ⟨184072720522231428709793357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122715147014820952473195571 184072720522231428709793357)
    ·
      refine ⟨69027270195836785766172509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184072720522231428709793357 69027270195836785766172509)
      ·
        refine ⟨25885226323438794662314691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69027270195836785766172509 25885226323438794662314691)
        ·
          refine ⟨38827839485158191993472037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25885226323438794662314691 38827839485158191993472037)
          ·
            refine ⟨7280219903467160998776007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38827839485158191993472037 7280219903467160998776007)
            ·
              refine ⟨10920329855200741498164011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7280219903467160998776007 10920329855200741498164011)
              ·
                refine ⟨16380494782801112247246017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10920329855200741498164011 16380494782801112247246017)
                ·
                  refine ⟨12285371087100834185434513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16380494782801112247246017 12285371087100834185434513)
                  ·
                    refine ⟨9214028315325625639075885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12285371087100834185434513 9214028315325625639075885)
                    ·
                      refine ⟨3455260618247109614653457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9214028315325625639075885 3455260618247109614653457)
                      ·
                        rfl

theorem cell23_6729096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6729096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729096 prefixEnd_6729096 := by exact prefixLift 6729096
  have htrace : WordTrace (prefixWord ++ tailWord_6729096) baseStart_6729096 baseEnd_6729096 := by
    simpa [prefixWord, tailWord_6729096, baseEnd_6729096] using wordTrace_append hprefix tailTrace_6729096
  have hstable : (prefixWord ++ tailWord_6729096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729096).length < 2 ^ (prefixWord ++ tailWord_6729096).sum := by decide
  have hdescent : baseEnd_6729096 < baseStart_6729096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729105 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_6729105 : Nat := 118140960795 + 6729105 * 2 ^ 59
def prefixEnd_6729105 : Nat := 4983230072969 + 3 ^ 40 * 6729105 * 2
def baseEnd_6729105 : Nat := 3455265239573000079440915

theorem tailTrace_6729105 : CollatzResearch.WordTrace tailWord_6729105 prefixEnd_6729105 3455265239573000079440915 := by
  unfold tailWord_6729105
  simp only [CollatzResearch.WordTrace]
  refine ⟨245430622286609299483468769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163620414857739532988979179 245430622286609299483468769)
  ·
    refine ⟨184072966714956974612601577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245430622286609299483468769 184072966714956974612601577)
    ·
      refine ⟨138054725036217730959451183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184072966714956974612601577 138054725036217730959451183)
      ·
        refine ⟨207082087554326596439176775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138054725036217730959451183 207082087554326596439176775)
        ·
          refine ⟨310623131331489894658765163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207082087554326596439176775 310623131331489894658765163)
          ·
            refine ⟨465934696997234841988147745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310623131331489894658765163 465934696997234841988147745)
            ·
              refine ⟨349451022747926131491110809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465934696997234841988147745 349451022747926131491110809)
              ·
                refine ⟨262088267060944598618333107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349451022747926131491110809 262088267060944598618333107)
                ·
                  refine ⟨393132400591416897927499661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262088267060944598618333107 393132400591416897927499661)
                  ·
                    refine ⟨147424650221781336722812373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393132400591416897927499661 147424650221781336722812373)
                    ·
                      refine ⟨3455265239573000079440915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147424650221781336722812373 3455265239573000079440915)
                      ·
                        rfl

theorem cell23_6729105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_6729105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729105 prefixEnd_6729105 := by exact prefixLift 6729105
  have htrace : WordTrace (prefixWord ++ tailWord_6729105) baseStart_6729105 baseEnd_6729105 := by
    simpa [prefixWord, tailWord_6729105, baseEnd_6729105] using wordTrace_append hprefix tailTrace_6729105
  have hstable : (prefixWord ++ tailWord_6729105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729105).length < 2 ^ (prefixWord ++ tailWord_6729105).sum := by decide
  have hdescent : baseEnd_6729105 < baseStart_6729105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729132 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_6729132 : Nat := 118140960795 + 6729132 * 2 ^ 59
def prefixEnd_6729132 : Nat := 4983230072969 + 3 ^ 40 * 6729132 * 2
def baseEnd_6729132 : Nat := 3455279103550671473803291

theorem tailTrace_6729132 : CollatzResearch.WordTrace tailWord_6729132 prefixEnd_6729132 3455279103550671473803291 := by
  unfold tailWord_6729132
  simp only [CollatzResearch.WordTrace]
  refine ⟨122715803528755741547350825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163621071371674322063134433 122715803528755741547350825)
  ·
    refine ⟨92036852646566806160513119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122715803528755741547350825 92036852646566806160513119)
    ·
      refine ⟨138055278969850209240769679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92036852646566806160513119 138055278969850209240769679)
      ·
        refine ⟨207082918454775313861154519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138055278969850209240769679 207082918454775313861154519)
        ·
          refine ⟨310624377682162970791731779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207082918454775313861154519 310624377682162970791731779)
          ·
            refine ⟨465936566523244456187597669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310624377682162970791731779 465936566523244456187597669)
            ·
              refine ⟨87363106223108335535174563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465936566523244456187597669 87363106223108335535174563)
              ·
                refine ⟨131044659334662503302761845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87363106223108335535174563 131044659334662503302761845)
                ·
                  refine ⟨12285436812624609684633923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131044659334662503302761845 12285436812624609684633923)
                  ·
                    refine ⟨18428155218936914526950885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12285436812624609684633923 18428155218936914526950885)
                    ·
                      refine ⟨3455279103550671473803291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18428155218936914526950885 3455279103550671473803291)
                      ·
                        rfl

theorem cell23_6729132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_6729132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729132 prefixEnd_6729132 := by exact prefixLift 6729132
  have htrace : WordTrace (prefixWord ++ tailWord_6729132) baseStart_6729132 baseEnd_6729132 := by
    simpa [prefixWord, tailWord_6729132, baseEnd_6729132] using wordTrace_append hprefix tailTrace_6729132
  have hstable : (prefixWord ++ tailWord_6729132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729132).length < 2 ^ (prefixWord ++ tailWord_6729132).sum := by decide
  have hdescent : baseEnd_6729132 < baseStart_6729132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729149 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_6729149 : Nat := 118140960795 + 6729149 * 2 ^ 59
def prefixEnd_6729149 : Nat := 4983230072969 + 3 ^ 40 * 6729149 * 2
def baseEnd_6729149 : Nat := 3455287832721797907290713

theorem tailTrace_6729149 : CollatzResearch.WordTrace tailWord_6729149 prefixEnd_6729149 3455287832721797907290713 := by
  unfold tailWord_6729149
  simp only [CollatzResearch.WordTrace]
  refine ⟨245432227098449894998070501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163621484732299929998713667 245432227098449894998070501)
  ·
    refine ⟨46018542580959355312138219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245432227098449894998070501 46018542580959355312138219)
    ·
      refine ⟨69027813871439032968207329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46018542580959355312138219 69027813871439032968207329)
      ·
        refine ⟨51770860403579274726155497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69027813871439032968207329 51770860403579274726155497)
        ·
          refine ⟨38828145302684456044616623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51770860403579274726155497 38828145302684456044616623)
          ·
            refine ⟨58242217954026684066924935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38828145302684456044616623 58242217954026684066924935)
            ·
              refine ⟨87363326931040026100387403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58242217954026684066924935 87363326931040026100387403)
              ·
                refine ⟨131044990396560039150581105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87363326931040026100387403 131044990396560039150581105)
                ·
                  refine ⟨98283742797420029362935829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131044990396560039150581105 98283742797420029362935829)
                  ·
                    refine ⟨4607050443629063876387617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98283742797420029362935829 4607050443629063876387617)
                    ·
                      refine ⟨3455287832721797907290713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607050443629063876387617 3455287832721797907290713)
                      ·
                        rfl

theorem cell23_6729149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_6729149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729149 prefixEnd_6729149 := by exact prefixLift 6729149
  have htrace : WordTrace (prefixWord ++ tailWord_6729149) baseStart_6729149 baseEnd_6729149 := by
    simpa [prefixWord, tailWord_6729149, baseEnd_6729149] using wordTrace_append hprefix tailTrace_6729149
  have hstable : (prefixWord ++ tailWord_6729149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729149).length < 2 ^ (prefixWord ++ tailWord_6729149).sum := by decide
  have hdescent : baseEnd_6729149 < baseStart_6729149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729166 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_6729166 : Nat := 118140960795 + 6729166 * 2 ^ 59
def prefixEnd_6729166 : Nat := 4983230072969 + 3 ^ 40 * 6729166 * 2
def baseEnd_6729166 : Nat := 3455296561892924340778135

theorem tailTrace_6729166 : CollatzResearch.WordTrace tailWord_6729166 prefixEnd_6729166 3455296561892924340778135 := by
  unfold tailWord_6729166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30679105892423538362679919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163621898092925537934292901 30679105892423538362679919)
  ·
    refine ⟨46018658838635307544019879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30679105892423538362679919 46018658838635307544019879)
    ·
      refine ⟨69027988257952961316029819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46018658838635307544019879 69027988257952961316029819)
      ·
        refine ⟨103541982386929441974044729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69027988257952961316029819 103541982386929441974044729)
        ·
          refine ⟨77656486790197081480533547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103541982386929441974044729 77656486790197081480533547)
          ·
            refine ⟨116484730185295622220800321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77656486790197081480533547 116484730185295622220800321)
            ·
              refine ⟨87363547638971716665600241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116484730185295622220800321 87363547638971716665600241)
              ·
                refine ⟨65522660729228787499200181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87363547638971716665600241 65522660729228787499200181)
                ·
                  refine ⟨6142749443365198828050017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65522660729228787499200181 6142749443365198828050017)
                  ·
                    refine ⟨4607062082523899121037513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6142749443365198828050017 4607062082523899121037513)
                    ·
                      refine ⟨3455296561892924340778135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607062082523899121037513 3455296561892924340778135)
                      ·
                        rfl

theorem cell23_6729166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_6729166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729166 prefixEnd_6729166 := by exact prefixLift 6729166
  have htrace : WordTrace (prefixWord ++ tailWord_6729166) baseStart_6729166 baseEnd_6729166 := by
    simpa [prefixWord, tailWord_6729166, baseEnd_6729166] using wordTrace_append hprefix tailTrace_6729166
  have hstable : (prefixWord ++ tailWord_6729166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729166).length < 2 ^ (prefixWord ++ tailWord_6729166).sum := by decide
  have hdescent : baseEnd_6729166 < baseStart_6729166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729189 : List Nat := [1, 3, 1, 5, 1, 2, 2, 8]
def baseStart_6729189 : Nat := 118140960795 + 6729189 * 2 ^ 59
def prefixEnd_6729189 : Nat := 4983230072969 + 3 ^ 40 * 6729189 * 2
def baseEnd_6729189 : Nat := 127974384146221398177427

theorem tailTrace_6729189 : CollatzResearch.WordTrace tailWord_6729189 prefixEnd_6729189 127974384146221398177427 := by
  unfold tailWord_6729189
  simp only [CollatzResearch.WordTrace]
  refine ⟨245433686018304981829526621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163622457345536654553017747 245433686018304981829526621)
  ·
    refine ⟨92037632256864368186072483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245433686018304981829526621 92037632256864368186072483)
    ·
      refine ⟨138056448385296552279108725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92037632256864368186072483 138056448385296552279108725)
      ·
        refine ⟨12942792036121551776166443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138056448385296552279108725 12942792036121551776166443)
        ·
          refine ⟨19414188054182327664249665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12942792036121551776166443 19414188054182327664249665)
          ·
            refine ⟨14560641040636745748187249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19414188054182327664249665 14560641040636745748187249)
            ·
              refine ⟨10920480780477559311140437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14560641040636745748187249 10920480780477559311140437)
              ·
                refine ⟨127974384146221398177427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10920480780477559311140437 127974384146221398177427)
                ·
                  rfl

theorem cell23_6729189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 8].length) (baseStart_6729189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729189 prefixEnd_6729189 := by exact prefixLift 6729189
  have htrace : WordTrace (prefixWord ++ tailWord_6729189) baseStart_6729189 baseEnd_6729189 := by
    simpa [prefixWord, tailWord_6729189, baseEnd_6729189] using wordTrace_append hprefix tailTrace_6729189
  have hstable : (prefixWord ++ tailWord_6729189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729189).length < 2 ^ (prefixWord ++ tailWord_6729189).sum := by decide
  have hdescent : baseEnd_6729189 < baseStart_6729189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729192 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6729192 : Nat := 118140960795 + 6729192 * 2 ^ 59
def prefixEnd_6729192 : Nat := 4983230072969 + 3 ^ 40 * 6729192 * 2
def baseEnd_6729192 : Nat := 3455309912389941239053015

theorem tailTrace_6729192 : CollatzResearch.WordTrace tailWord_6729192 prefixEnd_6729192 3455309912389941239053015 := by
  unfold tailWord_6729192
  simp only [CollatzResearch.WordTrace]
  refine ⟨122716897718647056670942915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163622530291529408894590553 122716897718647056670942915)
  ·
    refine ⟨184075346577970585006414373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122716897718647056670942915 184075346577970585006414373)
    ·
      refine ⟨34514127483369484688702695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184075346577970585006414373 34514127483369484688702695)
      ·
        refine ⟨51771191225054227033054043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34514127483369484688702695 51771191225054227033054043)
        ·
          refine ⟨77656786837581340549581065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51771191225054227033054043 77656786837581340549581065)
          ·
            refine ⟨58242590128186005412185799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77656786837581340549581065 58242590128186005412185799)
            ·
              refine ⟨87363885192279008118278699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58242590128186005412185799 87363885192279008118278699)
              ·
                refine ⟨131045827788418512177418049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87363885192279008118278699 131045827788418512177418049)
                ·
                  refine ⟨98284370841313884133063537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131045827788418512177418049 98284370841313884133063537)
                  ·
                    refine ⟨73713278130985413099797653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98284370841313884133063537 73713278130985413099797653)
                    ·
                      refine ⟨3455309912389941239053015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73713278130985413099797653 3455309912389941239053015)
                      ·
                        rfl

theorem cell23_6729192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6729192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729192 prefixEnd_6729192 := by exact prefixLift 6729192
  have htrace : WordTrace (prefixWord ++ tailWord_6729192) baseStart_6729192 baseEnd_6729192 := by
    simpa [prefixWord, tailWord_6729192, baseEnd_6729192] using wordTrace_append hprefix tailTrace_6729192
  have hstable : (prefixWord ++ tailWord_6729192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729192).length < 2 ^ (prefixWord ++ tailWord_6729192).sum := by decide
  have hdescent : baseEnd_6729192 < baseStart_6729192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729212 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_6729212 : Nat := 118140960795 + 6729212 * 2 ^ 59
def prefixEnd_6729212 : Nat := 4983230072969 + 3 ^ 40 * 6729212 * 2
def baseEnd_6729212 : Nat := 3455320182003031160802923

theorem tailTrace_6729212 : CollatzResearch.WordTrace tailWord_6729212 prefixEnd_6729212 3455320182003031160802923 := by
  unfold tailWord_6729212
  simp only [CollatzResearch.WordTrace]
  refine ⟨122717262448610828378806945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163623016598147771171742593 122717262448610828378806945)
  ·
    refine ⟨92037946836458121284105209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122717262448610828378806945 92037946836458121284105209)
    ·
      refine ⟨69028460127343590963078907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92037946836458121284105209 69028460127343590963078907)
      ·
        refine ⟨103542690191015386444618361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69028460127343590963078907 103542690191015386444618361)
        ·
          refine ⟨77657017643261539833463771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103542690191015386444618361 77657017643261539833463771)
          ·
            refine ⟨116485526464892309750195657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77657017643261539833463771 116485526464892309750195657)
            ·
              refine ⟨87364144848669232312646743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116485526464892309750195657 87364144848669232312646743)
              ·
                refine ⟨131046217273003848468970115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87364144848669232312646743 131046217273003848468970115)
                ·
                  refine ⟨196569325909505772703455173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131046217273003848468970115 196569325909505772703455173)
                  ·
                    refine ⟨36856748608032332381897845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196569325909505772703455173 36856748608032332381897845)
                    ·
                      refine ⟨3455320182003031160802923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36856748608032332381897845 3455320182003031160802923)
                      ·
                        rfl

theorem cell23_6729212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_6729212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729212 prefixEnd_6729212 := by exact prefixLift 6729212
  have htrace : WordTrace (prefixWord ++ tailWord_6729212) baseStart_6729212 baseEnd_6729212 := by
    simpa [prefixWord, tailWord_6729212, baseEnd_6729212] using wordTrace_append hprefix tailTrace_6729212
  have hstable : (prefixWord ++ tailWord_6729212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729212).length < 2 ^ (prefixWord ++ tailWord_6729212).sum := by decide
  have hdescent : baseEnd_6729212 < baseStart_6729212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729220 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6729220 : Nat := 118140960795 + 6729220 * 2 ^ 59
def prefixEnd_6729220 : Nat := 4983230072969 + 3 ^ 40 * 6729220 * 2
def baseEnd_6729220 : Nat := 3455324289848267129502887

theorem tailTrace_6729220 : CollatzResearch.WordTrace tailWord_6729220 prefixEnd_6729220 3455324289848267129502887 := by
  unfold tailWord_6729220
  simp only [CollatzResearch.WordTrace]
  refine ⟨122717408340596337061952557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163623211120795116082603409 122717408340596337061952557)
  ·
    refine ⟨46019028127723626398232209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122717408340596337061952557 46019028127723626398232209)
    ·
      refine ⟨34514271095792719798674157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46019028127723626398232209 34514271095792719798674157)
      ·
        refine ⟨12942851660922269924502809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34514271095792719798674157 12942851660922269924502809)
        ·
          refine ⟨9707138745691702443377107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12942851660922269924502809 9707138745691702443377107)
          ·
            refine ⟨14560708118537553665065661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707138745691702443377107 14560708118537553665065661)
            ·
              refine ⟨5460265544451582624399623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14560708118537553665065661 5460265544451582624399623)
              ·
                refine ⟨8190398316677373936599435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460265544451582624399623 8190398316677373936599435)
                ·
                  refine ⟨12285597475016060904899153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190398316677373936599435 12285597475016060904899153)
                  ·
                    refine ⟨9214198106262045678674365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12285597475016060904899153 9214198106262045678674365)
                    ·
                      refine ⟨3455324289848267129502887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9214198106262045678674365 3455324289848267129502887)
                      ·
                        rfl

theorem cell23_6729220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6729220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729220 prefixEnd_6729220 := by exact prefixLift 6729220
  have htrace : WordTrace (prefixWord ++ tailWord_6729220) baseStart_6729220 baseEnd_6729220 := by
    simpa [prefixWord, tailWord_6729220, baseEnd_6729220] using wordTrace_append hprefix tailTrace_6729220
  have hstable : (prefixWord ++ tailWord_6729220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729220).length < 2 ^ (prefixWord ++ tailWord_6729220).sum := by decide
  have hdescent : baseEnd_6729220 < baseStart_6729220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729249 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 2, 6]
def baseStart_6729249 : Nat := 118140960795 + 6729249 * 2 ^ 59
def prefixEnd_6729249 : Nat := 4983230072969 + 3 ^ 40 * 6729249 * 2
def baseEnd_6729249 : Nat := 1151779726929082505346751

theorem tailTrace_6729249 : CollatzResearch.WordTrace tailWord_6729249 prefixEnd_6729249 1151779726929082505346751 := by
  unfold tailWord_6729249
  simp only [CollatzResearch.WordTrace]
  refine ⟨245435874398087612076710801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163623916265391741384473867 245435874398087612076710801)
  ·
    refine ⟨184076905798565709057533101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245435874398087612076710801 184076905798565709057533101)
    ·
      refine ⟨69028839674462140896574913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184076905798565709057533101 69028839674462140896574913)
      ·
        refine ⟨51771629755846605672431185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69028839674462140896574913 51771629755846605672431185)
        ·
          refine ⟨38828722316884954254323389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51771629755846605672431185 38828722316884954254323389)
          ·
            refine ⟨14560770868831857845371271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38828722316884954254323389 14560770868831857845371271)
            ·
              refine ⟨21841156303247786768056907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14560770868831857845371271 21841156303247786768056907)
              ·
                refine ⟨32761734454871680152085361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21841156303247786768056907 32761734454871680152085361)
                ·
                  refine ⟨24571300841153760114064021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32761734454871680152085361 24571300841153760114064021)
                  ·
                    refine ⟨1151779726929082505346751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24571300841153760114064021 1151779726929082505346751)
                    ·
                      rfl

theorem cell23_6729249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_6729249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729249 prefixEnd_6729249 := by exact prefixLift 6729249
  have htrace : WordTrace (prefixWord ++ tailWord_6729249) baseStart_6729249 baseEnd_6729249 := by
    simpa [prefixWord, tailWord_6729249, baseEnd_6729249] using wordTrace_append hprefix tailTrace_6729249
  have hstable : (prefixWord ++ tailWord_6729249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729249).length < 2 ^ (prefixWord ++ tailWord_6729249).sum := by decide
  have hdescent : baseEnd_6729249 < baseStart_6729249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729277 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_6729277 : Nat := 118140960795 + 6729277 * 2 ^ 59
def prefixEnd_6729277 : Nat := 4983230072969 + 3 ^ 40 * 6729277 * 2
def baseEnd_6729277 : Nat := 3455353558245573406490125

theorem tailTrace_6729277 : CollatzResearch.WordTrace tailWord_6729277 prefixEnd_6729277 3455353558245573406490125 := by
  unfold tailWord_6729277
  simp only [CollatzResearch.WordTrace]
  refine ⟨245436895641986172858730085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163624597094657448572486723 245436895641986172858730085)
  ·
    refine ⟨46019417932872407411011891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245436895641986172858730085 46019417932872407411011891)
    ·
      refine ⟨69029126899308611116517837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46019417932872407411011891 69029126899308611116517837)
      ·
        refine ⟨25885922587240729168694189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69029126899308611116517837 25885922587240729168694189)
        ·
          refine ⟨9707220970215273438260321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25885922587240729168694189 9707220970215273438260321)
          ·
            refine ⟨7280415727661455078695241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9707220970215273438260321 7280415727661455078695241)
            ·
              refine ⟨5460311795746091309021431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7280415727661455078695241 5460311795746091309021431)
              ·
                refine ⟨8190467693619136963532147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460311795746091309021431 8190467693619136963532147)
                ·
                  refine ⟨12285701540428705445298221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190467693619136963532147 12285701540428705445298221)
                  ·
                    refine ⟨4607138077660764541986833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12285701540428705445298221 4607138077660764541986833)
                    ·
                      refine ⟨3455353558245573406490125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607138077660764541986833 3455353558245573406490125)
                      ·
                        rfl

theorem cell23_6729277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_6729277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729277 prefixEnd_6729277 := by exact prefixLift 6729277
  have htrace : WordTrace (prefixWord ++ tailWord_6729277) baseStart_6729277 baseEnd_6729277 := by
    simpa [prefixWord, tailWord_6729277, baseEnd_6729277] using wordTrace_append hprefix tailTrace_6729277
  have hstable : (prefixWord ++ tailWord_6729277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729277).length < 2 ^ (prefixWord ++ tailWord_6729277).sum := by decide
  have hdescent : baseEnd_6729277 < baseStart_6729277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729329 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_6729329 : Nat := 118140960795 + 6729329 * 2 ^ 59
def prefixEnd_6729329 : Nat := 4983230072969 + 3 ^ 40 * 6729329 * 2
def baseEnd_6729329 : Nat := 3455380259239607203039885

theorem tailTrace_6729329 : CollatzResearch.WordTrace tailWord_6729329 prefixEnd_6729329 3455380259239607203039885 := by
  unfold tailWord_6729329
  simp only [CollatzResearch.WordTrace]
  refine ⟨245438792237797785739623041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163625861491865190493082027 245438792237797785739623041)
  ·
    refine ⟨184079094178348339304717281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245438792237797785739623041 184079094178348339304717281)
    ·
      refine ⟨138059320633761254478537961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184079094178348339304717281 138059320633761254478537961)
      ·
        refine ⟨103544490475320940858903471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138059320633761254478537961 103544490475320940858903471)
        ·
          refine ⟨155316735712981411288355207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103544490475320940858903471 155316735712981411288355207)
          ·
            refine ⟨232975103569472116932532811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155316735712981411288355207 232975103569472116932532811)
            ·
              refine ⟨349462655354208175398799217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232975103569472116932532811 349462655354208175398799217)
              ·
                refine ⟨262096991515656131549099413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349462655354208175398799217 262096991515656131549099413)
                ·
                  refine ⟨12285796477296381166364035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 262096991515656131549099413 12285796477296381166364035)
                  ·
                    refine ⟨18428694715944571749546053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12285796477296381166364035 18428694715944571749546053)
                    ·
                      refine ⟨3455380259239607203039885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18428694715944571749546053 3455380259239607203039885)
                      ·
                        rfl

theorem cell23_6729329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_6729329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729329 prefixEnd_6729329 := by exact prefixLift 6729329
  have htrace : WordTrace (prefixWord ++ tailWord_6729329) baseStart_6729329 baseEnd_6729329 := by
    simpa [prefixWord, tailWord_6729329, baseEnd_6729329] using wordTrace_append hprefix tailTrace_6729329
  have hstable : (prefixWord ++ tailWord_6729329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729329).length < 2 ^ (prefixWord ++ tailWord_6729329).sum := by decide
  have hdescent : baseEnd_6729329 < baseStart_6729329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729449 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_6729449 : Nat := 118140960795 + 6729449 * 2 ^ 59
def prefixEnd_6729449 : Nat := 4983230072969 + 3 ^ 40 * 6729449 * 2
def baseEnd_6729449 : Nat := 3455441876918146733539333

theorem tailTrace_6729449 : CollatzResearch.WordTrace tailWord_6729449 prefixEnd_6729449 3455441876918146733539333 := by
  unfold tailWord_6729449
  simp only [CollatzResearch.WordTrace]
  refine ⟨245443168997363046233991401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163628779331575364155994267 245443168997363046233991401)
  ·
    refine ⟨184082376748022284675493551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245443168997363046233991401 184082376748022284675493551)
    ·
      refine ⟨276123565122033427013240327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184082376748022284675493551 276123565122033427013240327)
      ·
        refine ⟨414185347683050140519860491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276123565122033427013240327 414185347683050140519860491)
        ·
          refine ⟨621278021524575210779790737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414185347683050140519860491 621278021524575210779790737)
          ·
            refine ⟨465958516143431408084843053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621278021524575210779790737 465958516143431408084843053)
            ·
              refine ⟨174734443553786778031816145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465958516143431408084843053 174734443553786778031816145)
              ·
                refine ⟨131050832665340083523862109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174734443553786778031816145 131050832665340083523862109)
                ·
                  refine ⟨49144062249502531321448291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131050832665340083523862109 49144062249502531321448291)
                  ·
                    refine ⟨73716093374253796982172437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49144062249502531321448291 73716093374253796982172437)
                    ·
                      refine ⟨3455441876918146733539333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73716093374253796982172437 3455441876918146733539333)
                      ·
                        rfl

theorem cell23_6729449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_6729449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729449 prefixEnd_6729449 := by exact prefixLift 6729449
  have htrace : WordTrace (prefixWord ++ tailWord_6729449) baseStart_6729449 baseEnd_6729449 := by
    simpa [prefixWord, tailWord_6729449, baseEnd_6729449] using wordTrace_append hprefix tailTrace_6729449
  have hstable : (prefixWord ++ tailWord_6729449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729449).length < 2 ^ (prefixWord ++ tailWord_6729449).sum := by decide
  have hdescent : baseEnd_6729449 < baseStart_6729449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729456 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3]
def baseStart_6729456 : Nat := 118140960795 + 6729456 * 2 ^ 59
def prefixEnd_6729456 : Nat := 4983230072969 + 3 ^ 40 * 6729456 * 2
def baseEnd_6729456 : Nat := 3455445471282728206151801

theorem tailTrace_6729456 : CollatzResearch.WordTrace tailWord_6729456 prefixEnd_6729456 3455445471282728206151801 := by
  unfold tailWord_6729456
  simp only [CollatzResearch.WordTrace]
  refine ⟨122721712154168843214748111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163628949538891790952997481 122721712154168843214748111)
  ·
    refine ⟨184082568231253264822122167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122721712154168843214748111 184082568231253264822122167)
    ·
      refine ⟨276123852346879897233183251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184082568231253264822122167 276123852346879897233183251)
      ·
        refine ⟨414185778520319845849774877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276123852346879897233183251 414185778520319845849774877)
        ·
          refine ⟨155319666945119942193665579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414185778520319845849774877 155319666945119942193665579)
          ·
            refine ⟨232979500417679913290498369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155319666945119942193665579 232979500417679913290498369)
            ·
              refine ⟨174734625313259934967873777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232979500417679913290498369 174734625313259934967873777)
              ·
                refine ⟨131050968984944951225905333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174734625313259934967873777 131050968984944951225905333)
                ·
                  refine ⟨12286028342338589177428625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131050968984944951225905333 12286028342338589177428625)
                  ·
                    refine ⟨9214521256753941883071469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12286028342338589177428625 9214521256753941883071469)
                    ·
                      refine ⟨3455445471282728206151801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9214521256753941883071469 3455445471282728206151801)
                      ·
                        rfl

theorem cell23_6729456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_6729456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729456 prefixEnd_6729456 := by exact prefixLift 6729456
  have htrace : WordTrace (prefixWord ++ tailWord_6729456) baseStart_6729456 baseEnd_6729456 := by
    simpa [prefixWord, tailWord_6729456, baseEnd_6729456] using wordTrace_append hprefix tailTrace_6729456
  have hstable : (prefixWord ++ tailWord_6729456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729456).length < 2 ^ (prefixWord ++ tailWord_6729456).sum := by decide
  have hdescent : baseEnd_6729456 < baseStart_6729456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729463 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 2, 4]
def baseStart_6729463 : Nat := 118140960795 + 6729463 * 2 ^ 59
def prefixEnd_6729463 : Nat := 4983230072969 + 3 ^ 40 * 6729463 * 2
def baseEnd_6729463 : Nat := 1151816355215769892921423

theorem tailTrace_6729463 : CollatzResearch.WordTrace tailWord_6729463 prefixEnd_6729463 1151816355215769892921423 := by
  unfold tailWord_6729463
  simp only [CollatzResearch.WordTrace]
  refine ⟨245443679619312326625001043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163629119746208217750000695 245443679619312326625001043)
  ·
    refine ⟨368165519428968489937501565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245443679619312326625001043 368165519428968489937501565)
    ·
      refine ⟨138062069785863183726563087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368165519428968489937501565 138062069785863183726563087)
      ·
        refine ⟨207093104678794775589844631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138062069785863183726563087 207093104678794775589844631)
        ·
          refine ⟨310639657018192163384766947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207093104678794775589844631 310639657018192163384766947)
          ·
            refine ⟨465959485527288245077150421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310639657018192163384766947 465959485527288245077150421)
            ·
              refine ⟨10920925442045818243995713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 465959485527288245077150421 10920925442045818243995713)
              ·
                refine ⟨8190694081534363682996785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10920925442045818243995713 8190694081534363682996785)
                ·
                  refine ⟨6143020561150772762247589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8190694081534363682996785 6143020561150772762247589)
                  ·
                    refine ⟨1151816355215769892921423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6143020561150772762247589 1151816355215769892921423)
                    ·
                      rfl

theorem cell23_6729463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_6729463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729463 prefixEnd_6729463 := by exact prefixLift 6729463
  have htrace : WordTrace (prefixWord ++ tailWord_6729463) baseStart_6729463 baseEnd_6729463 := by
    simpa [prefixWord, tailWord_6729463, baseEnd_6729463] using wordTrace_append hprefix tailTrace_6729463
  have hstable : (prefixWord ++ tailWord_6729463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729463).length < 2 ^ (prefixWord ++ tailWord_6729463).sum := by decide
  have hdescent : baseEnd_6729463 < baseStart_6729463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729480 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 2, 4]
def baseStart_6729480 : Nat := 118140960795 + 6729480 * 2 ^ 59
def prefixEnd_6729480 : Nat := 4983230072969 + 3 ^ 40 * 6729480 * 2
def baseEnd_6729480 : Nat := 1151819264939478704083897

theorem tailTrace_6729480 : CollatzResearch.WordTrace tailWord_6729480 prefixEnd_6729480 1151819264939478704083897 := by
  unfold tailWord_6729480
  simp only [CollatzResearch.WordTrace]
  refine ⟨122722149830125369264184947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163629533106833825685579929 122722149830125369264184947)
  ·
    refine ⟨184083224745188053896277421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122722149830125369264184947 184083224745188053896277421)
    ·
      refine ⟨69031209279445520211104033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184083224745188053896277421 69031209279445520211104033)
      ·
        refine ⟨51773406959584140158328025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69031209279445520211104033 51773406959584140158328025)
        ·
          refine ⟨38830055219688105118746019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51773406959584140158328025 38830055219688105118746019)
          ·
            refine ⟨58245082829532157678119029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38830055219688105118746019 58245082829532157678119029)
            ·
              refine ⟨5460476515268639782323659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58245082829532157678119029 5460476515268639782323659)
              ·
                refine ⟨8190714772902959673485489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460476515268639782323659 8190714772902959673485489)
                ·
                  refine ⟨6143036079677219755114117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8190714772902959673485489 6143036079677219755114117)
                  ·
                    refine ⟨1151819264939478704083897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6143036079677219755114117 1151819264939478704083897)
                    ·
                      rfl

theorem cell23_6729480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_6729480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729480 prefixEnd_6729480 := by exact prefixLift 6729480
  have htrace : WordTrace (prefixWord ++ tailWord_6729480) baseStart_6729480 baseEnd_6729480 := by
    simpa [prefixWord, tailWord_6729480, baseEnd_6729480] using wordTrace_append hprefix tailTrace_6729480
  have hstable : (prefixWord ++ tailWord_6729480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729480).length < 2 ^ (prefixWord ++ tailWord_6729480).sum := by decide
  have hdescent : baseEnd_6729480 < baseStart_6729480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729493 : List Nat := [1, 3, 2, 1, 2, 5, 2, 7]
def baseStart_6729493 : Nat := 118140960795 + 6729493 * 2 ^ 59
def prefixEnd_6729493 : Nat := 4983230072969 + 3 ^ 40 * 6729493 * 2
def baseEnd_6729493 : Nat := 127980165558034983755153

theorem tailTrace_6729493 : CollatzResearch.WordTrace tailWord_6729493 prefixEnd_6729493 127980165558034983755153 := by
  unfold tailWord_6729493
  simp only [CollatzResearch.WordTrace]
  refine ⟨245444773809203641748593133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163629849206135761165728755 245444773809203641748593133)
  ·
    refine ⟨92041790178451365655722425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245444773809203641748593133 92041790178451365655722425)
    ·
      refine ⟨69031342633838524241791819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92041790178451365655722425 69031342633838524241791819)
      ·
        refine ⟨103547013950757786362687729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69031342633838524241791819 103547013950757786362687729)
        ·
          refine ⟨77660260463068339772015797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103547013950757786362687729 77660260463068339772015797)
          ·
            refine ⟨7280649418412656853626481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77660260463068339772015797 7280649418412656853626481)
            ·
              refine ⟨5460487063809492640219861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7280649418412656853626481 5460487063809492640219861)
              ·
                refine ⟨127980165558034983755153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5460487063809492640219861 127980165558034983755153)
                ·
                  rfl

theorem cell23_6729493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 7].length) (baseStart_6729493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729493 prefixEnd_6729493 := by exact prefixLift 6729493
  have htrace : WordTrace (prefixWord ++ tailWord_6729493) baseStart_6729493 baseEnd_6729493 := by
    simpa [prefixWord, tailWord_6729493, baseEnd_6729493] using wordTrace_append hprefix tailTrace_6729493
  have hstable : (prefixWord ++ tailWord_6729493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729493).length < 2 ^ (prefixWord ++ tailWord_6729493).sum := by decide
  have hdescent : baseEnd_6729493 < baseStart_6729493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729503 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 3]
def baseStart_6729503 : Nat := 118140960795 + 6729503 * 2 ^ 59
def prefixEnd_6729503 : Nat := 4983230072969 + 3 ^ 40 * 6729503 * 2
def baseEnd_6729503 : Nat := 3455469604873489522264085

theorem tailTrace_6729503 : CollatzResearch.WordTrace tailWord_6729503 prefixEnd_6729503 3455469604873489522264085 := by
  unfold tailWord_6729503
  simp only [CollatzResearch.WordTrace]
  refine ⟨245445138539167413456457163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163630092359444942304304775 245445138539167413456457163)
  ·
    refine ⟨368167707808751120184685745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245445138539167413456457163 368167707808751120184685745)
    ·
      refine ⟨276125780856563340138514309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368167707808751120184685745 276125780856563340138514309)
      ·
        refine ⟨51773583910605626275971433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276125780856563340138514309 51773583910605626275971433)
        ·
          refine ⟨38830187932954219706978575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51773583910605626275971433 38830187932954219706978575)
          ·
            refine ⟨58245281899431329560467863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38830187932954219706978575 58245281899431329560467863)
            ·
              refine ⟨87367922849146994340701795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58245281899431329560467863 87367922849146994340701795)
              ·
                refine ⟨131051884273720491511052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87367922849146994340701795 131051884273720491511052693)
                ·
                  refine ⟨6143057075330648039580595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131051884273720491511052693 6143057075330648039580595)
                  ·
                    refine ⟨9214585612995972059370893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6143057075330648039580595 9214585612995972059370893)
                    ·
                      refine ⟨3455469604873489522264085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9214585612995972059370893 3455469604873489522264085)
                      ·
                        rfl

theorem cell23_6729503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_6729503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729503 prefixEnd_6729503 := by exact prefixLift 6729503
  have htrace : WordTrace (prefixWord ++ tailWord_6729503) baseStart_6729503 baseEnd_6729503 := by
    simpa [prefixWord, tailWord_6729503, baseEnd_6729503] using wordTrace_append hprefix tailTrace_6729503
  have hstable : (prefixWord ++ tailWord_6729503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729503).length < 2 ^ (prefixWord ++ tailWord_6729503).sum := by decide
  have hdescent : baseEnd_6729503 < baseStart_6729503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729546 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_6729546 : Nat := 118140960795 + 6729546 * 2 ^ 59
def prefixEnd_6729546 : Nat := 4983230072969 + 3 ^ 40 * 6729546 * 2
def baseEnd_6729546 : Nat := 3455491684541632854026387

theorem tailTrace_6729546 : CollatzResearch.WordTrace tailWord_6729546 prefixEnd_6729546 3455491684541632854026387 := by
  unfold tailWord_6729546
  simp only [CollatzResearch.WordTrace]
  refine ⟨61361676719502907950068123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163631137918674421200181661 61361676719502907950068123)
  ·
    refine ⟨92042515079254361925102185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61361676719502907950068123 92042515079254361925102185)
    ·
      refine ⟨69031886309440771443826639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92042515079254361925102185 69031886309440771443826639)
      ·
        refine ⟨103547829464161157165739959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69031886309440771443826639 103547829464161157165739959)
        ·
          refine ⟨155321744196241735748609939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103547829464161157165739959 155321744196241735748609939)
          ·
            refine ⟨232982616294362603622914909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155321744196241735748609939 232982616294362603622914909)
            ·
              refine ⟨87368481110385976358593091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232982616294362603622914909 87368481110385976358593091)
              ·
                refine ⟨131052721665578964537889637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87368481110385976358593091 131052721665578964537889637)
                ·
                  refine ⟨24572385312296055850854307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131052721665578964537889637 24572385312296055850854307)
                  ·
                    refine ⟨36858577968444083776281461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24572385312296055850854307 36858577968444083776281461)
                    ·
                      refine ⟨3455491684541632854026387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36858577968444083776281461 3455491684541632854026387)
                      ·
                        rfl

theorem cell23_6729546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_6729546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729546 prefixEnd_6729546 := by exact prefixLift 6729546
  have htrace : WordTrace (prefixWord ++ tailWord_6729546) baseStart_6729546 baseEnd_6729546 := by
    simpa [prefixWord, tailWord_6729546, baseEnd_6729546] using wordTrace_append hprefix tailTrace_6729546
  have hstable : (prefixWord ++ tailWord_6729546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729546).length < 2 ^ (prefixWord ++ tailWord_6729546).sum := by decide
  have hdescent : baseEnd_6729546 < baseStart_6729546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729586 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_6729586 : Nat := 118140960795 + 6729586 * 2 ^ 59
def prefixEnd_6729586 : Nat := 4983230072969 + 3 ^ 40 * 6729586 * 2
def baseEnd_6729586 : Nat := 3455512223767812697526203

theorem tailTrace_6729586 : CollatzResearch.WordTrace tailWord_6729586 prefixEnd_6729586 3455512223767812697526203 := by
  unfold tailWord_6729586
  simp only [CollatzResearch.WordTrace]
  refine ⟨61362041449466679657932153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163632110531911145754485741 61362041449466679657932153)
  ·
    refine ⟨46021531087100009743449115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61362041449466679657932153 46021531087100009743449115)
    ·
      refine ⟨69032296630650014615173673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46021531087100009743449115 69032296630650014615173673)
      ·
        refine ⟨51774222472987510961380255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69032296630650014615173673 51774222472987510961380255)
        ·
          refine ⟨77661333709481266442070383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51774222472987510961380255 77661333709481266442070383)
          ·
            refine ⟨116492000564221899663105575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77661333709481266442070383 116492000564221899663105575)
            ·
              refine ⟨174738000846332849494658363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116492000564221899663105575 174738000846332849494658363)
              ·
                refine ⟨262107001269499274241987545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174738000846332849494658363 262107001269499274241987545)
                ·
                  refine ⟨196580250952124455681490659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262107001269499274241987545 196580250952124455681490659)
                  ·
                    refine ⟨294870376428186683522235989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196580250952124455681490659 294870376428186683522235989)
                    ·
                      refine ⟨3455512223767812697526203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 294870376428186683522235989 3455512223767812697526203)
                      ·
                        rfl

theorem cell23_6729586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_6729586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729586 prefixEnd_6729586 := by exact prefixLift 6729586
  have htrace : WordTrace (prefixWord ++ tailWord_6729586) baseStart_6729586 baseEnd_6729586 := by
    simpa [prefixWord, tailWord_6729586, baseEnd_6729586] using wordTrace_append hprefix tailTrace_6729586
  have hstable : (prefixWord ++ tailWord_6729586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729586).length < 2 ^ (prefixWord ++ tailWord_6729586).sum := by decide
  have hdescent : baseEnd_6729586 < baseStart_6729586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729593 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 3]
def baseStart_6729593 : Nat := 118140960795 + 6729593 * 2 ^ 59
def prefixEnd_6729593 : Nat := 4983230072969 + 3 ^ 40 * 6729593 * 2
def baseEnd_6729593 : Nat := 3455515818132394170138671

theorem tailTrace_6729593 : CollatzResearch.WordTrace tailWord_6729593 prefixEnd_6729593 3455515818132394170138671 := by
  unfold tailWord_6729593
  simp only [CollatzResearch.WordTrace]
  refine ⟨245448421108841358827233433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163632280739227572551488955 245448421108841358827233433)
  ·
    refine ⟨184086315831631019120425075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245448421108841358827233433 184086315831631019120425075)
    ·
      refine ⟨276129473747446528680637613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184086315831631019120425075 276129473747446528680637613)
      ·
        refine ⟨103548552655292448255239105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276129473747446528680637613 103548552655292448255239105)
        ·
          refine ⟨77661414491469336191429329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103548552655292448255239105 77661414491469336191429329)
          ·
            refine ⟨58246060868602002143571997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77661414491469336191429329 58246060868602002143571997)
            ·
              refine ⟨21842272825725750803839499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58246060868602002143571997 21842272825725750803839499)
              ·
                refine ⟨32763409238588626205759249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21842272825725750803839499 32763409238588626205759249)
                ·
                  refine ⟨24572556928941469654319437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32763409238588626205759249 24572556928941469654319437)
                  ·
                    refine ⟨9214708848353051120369789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24572556928941469654319437 9214708848353051120369789)
                    ·
                      refine ⟨3455515818132394170138671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9214708848353051120369789 3455515818132394170138671)
                      ·
                        rfl

theorem cell23_6729593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_6729593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729593 prefixEnd_6729593 := by exact prefixLift 6729593
  have htrace : WordTrace (prefixWord ++ tailWord_6729593) baseStart_6729593 baseEnd_6729593 := by
    simpa [prefixWord, tailWord_6729593, baseEnd_6729593] using wordTrace_append hprefix tailTrace_6729593
  have hstable : (prefixWord ++ tailWord_6729593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729593).length < 2 ^ (prefixWord ++ tailWord_6729593).sum := by decide
  have hdescent : baseEnd_6729593 < baseStart_6729593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729720 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 1, 5]
def baseStart_6729720 : Nat := 118140960795 + 6729720 * 2 ^ 59
def prefixEnd_6729720 : Nat := 4983230072969 + 3 ^ 40 * 6729720 * 2
def baseEnd_6729720 : Nat := 1151860343391838391083529

theorem tailTrace_6729720 : CollatzResearch.WordTrace tailWord_6729720 prefixEnd_6729720 1151860343391838391083529 := by
  unfold tailWord_6729720
  simp only [CollatzResearch.WordTrace]
  refine ⟨122726526589690629758553307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163635368786254173011404409 122726526589690629758553307)
  ·
    refine ⟨184089789884535944637829961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122726526589690629758553307 184089789884535944637829961)
    ·
      refine ⟨138067342413401958478372471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184089789884535944637829961 138067342413401958478372471)
      ·
        refine ⟨207101013620102937717558707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138067342413401958478372471 207101013620102937717558707)
        ·
          refine ⟨310651520430154406576338061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207101013620102937717558707 310651520430154406576338061)
          ·
            refine ⟨116494320161307902466126773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310651520430154406576338061 116494320161307902466126773)
            ·
              refine ⟨10921342515122615856199385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116494320161307902466126773 10921342515122615856199385)
              ·
                refine ⟨8191006886341961892149539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10921342515122615856199385 8191006886341961892149539)
                ·
                  refine ⟨12286510329512942838224309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8191006886341961892149539 12286510329512942838224309)
                  ·
                    refine ⟨1151860343391838391083529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12286510329512942838224309 1151860343391838391083529)
                    ·
                      rfl

theorem cell23_6729720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_6729720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729720 prefixEnd_6729720 := by exact prefixLift 6729720
  have htrace : WordTrace (prefixWord ++ tailWord_6729720) baseStart_6729720 baseEnd_6729720 := by
    simpa [prefixWord, tailWord_6729720, baseEnd_6729720] using wordTrace_append hprefix tailTrace_6729720
  have hstable : (prefixWord ++ tailWord_6729720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729720).length < 2 ^ (prefixWord ++ tailWord_6729720).sum := by decide
  have hdescent : baseEnd_6729720 < baseStart_6729720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729733 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_6729733 : Nat := 118140960795 + 6729733 * 2 ^ 59
def prefixEnd_6729733 : Nat := 4983230072969 + 3 ^ 40 * 6729733 * 2
def baseEnd_6729733 : Nat := 1151862568474674540796009

theorem tailTrace_6729733 : CollatzResearch.WordTrace tailWord_6729733 prefixEnd_6729733 1151862568474674540796009 := by
  unfold tailWord_6729733
  simp only [CollatzResearch.WordTrace]
  refine ⟨245453527328334162737329853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163635684885556108491553235 245453527328334162737329853)
  ·
    refine ⟨92045072748125311026498695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245453527328334162737329853 92045072748125311026498695)
    ·
      refine ⟨138067609122187966539748043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92045072748125311026498695 138067609122187966539748043)
      ·
        refine ⟨207101413683281949809622065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138067609122187966539748043 207101413683281949809622065)
        ·
          refine ⟨155326060262461462357216549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207101413683281949809622065 155326060262461462357216549)
          ·
            refine ⟨29123636299211524191978103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155326060262461462357216549 29123636299211524191978103)
            ·
              refine ⟨43685454448817286287967155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29123636299211524191978103 43685454448817286287967155)
              ·
                refine ⟨65528181673225929431950733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43685454448817286287967155 65528181673225929431950733)
                ·
                  refine ⟨24573068127459723536981525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65528181673225929431950733 24573068127459723536981525)
                  ·
                    refine ⟨1151862568474674540796009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24573068127459723536981525 1151862568474674540796009)
                    ·
                      rfl

theorem cell23_6729733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_6729733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729733 prefixEnd_6729733 := by exact prefixLift 6729733
  have htrace : WordTrace (prefixWord ++ tailWord_6729733) baseStart_6729733 baseEnd_6729733 := by
    simpa [prefixWord, tailWord_6729733, baseEnd_6729733] using wordTrace_append hprefix tailTrace_6729733
  have hstable : (prefixWord ++ tailWord_6729733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729733).length < 2 ^ (prefixWord ++ tailWord_6729733).sum := by decide
  have hdescent : baseEnd_6729733 < baseStart_6729733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729741 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6729741 : Nat := 118140960795 + 6729741 * 2 ^ 59
def prefixEnd_6729741 : Nat := 4983230072969 + 3 ^ 40 * 6729741 * 2
def baseEnd_6729741 : Nat := 383954645918806621231999

theorem tailTrace_6729741 : CollatzResearch.WordTrace tailWord_6729741 prefixEnd_6729741 383954645918806621231999 := by
  unfold tailWord_6729741
  simp only [CollatzResearch.WordTrace]
  refine ⟨245453819112305180103621077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163635879408203453402414051 245453819112305180103621077)
  ·
    refine ⟨5752823885444652658678619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 245453819112305180103621077 5752823885444652658678619)
    ·
      refine ⟨8629235828166978988017929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752823885444652658678619 8629235828166978988017929)
      ·
        refine ⟨6471926871125234241013447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8629235828166978988017929 6471926871125234241013447)
        ·
          refine ⟨9707890306687851361520171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6471926871125234241013447 9707890306687851361520171)
          ·
            refine ⟨14561835460031777042280257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707890306687851361520171 14561835460031777042280257)
            ·
              refine ⟨10921376595023832781710193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14561835460031777042280257 10921376595023832781710193)
              ·
                refine ⟨8191032446267874586282645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10921376595023832781710193 8191032446267874586282645)
                ·
                  refine ⟨383954645918806621231999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8191032446267874586282645 383954645918806621231999)
                  ·
                    rfl

theorem cell23_6729741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6729741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729741 prefixEnd_6729741 := by exact prefixLift 6729741
  have htrace : WordTrace (prefixWord ++ tailWord_6729741) baseStart_6729741 baseEnd_6729741 := by
    simpa [prefixWord, tailWord_6729741, baseEnd_6729741] using wordTrace_append hprefix tailTrace_6729741
  have hstable : (prefixWord ++ tailWord_6729741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729741).length < 2 ^ (prefixWord ++ tailWord_6729741).sum := by decide
  have hdescent : baseEnd_6729741 < baseStart_6729741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729751 : List Nat := [1, 1, 3, 5, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6729751 : Nat := 118140960795 + 6729751 * 2 ^ 59
def prefixEnd_6729751 : Nat := 4983230072969 + 3 ^ 40 * 6729751 * 2
def baseEnd_6729751 : Nat := 3455596948075804551962945

theorem tailTrace_6729751 : CollatzResearch.WordTrace tailWord_6729751 prefixEnd_6729751 3455596948075804551962945 := by
  unfold tailWord_6729751
  simp only [CollatzResearch.WordTrace]
  refine ⟨245454183842268951811485107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163636122561512634540990071 245454183842268951811485107)
  ·
    refine ⟨368181275763403427717227661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245454183842268951811485107 368181275763403427717227661)
    ·
      refine ⟨138067978411276285393960373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368181275763403427717227661 138067978411276285393960373)
      ·
        refine ⟨12943872976057151755683785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138067978411276285393960373 12943872976057151755683785)
        ·
          refine ⟨9707904732042863816762839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12943872976057151755683785 9707904732042863816762839)
          ·
            refine ⟨14561857098064295725144259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707904732042863816762839 14561857098064295725144259)
            ·
              refine ⟨21842785647096443587716389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14561857098064295725144259 21842785647096443587716389)
              ·
                refine ⟨4095522308830583172696823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21842785647096443587716389 4095522308830583172696823)
                ·
                  refine ⟨6143283463245874759045235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095522308830583172696823 6143283463245874759045235)
                  ·
                    refine ⟨9214925194868812138567853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6143283463245874759045235 9214925194868812138567853)
                    ·
                      refine ⟨3455596948075804551962945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9214925194868812138567853 3455596948075804551962945)
                      ·
                        rfl

theorem cell23_6729751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6729751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729751 prefixEnd_6729751 := by exact prefixLift 6729751
  have htrace : WordTrace (prefixWord ++ tailWord_6729751) baseStart_6729751 baseEnd_6729751 := by
    simpa [prefixWord, tailWord_6729751, baseEnd_6729751] using wordTrace_append hprefix tailTrace_6729751
  have hstable : (prefixWord ++ tailWord_6729751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729751).length < 2 ^ (prefixWord ++ tailWord_6729751).sum := by decide
  have hdescent : baseEnd_6729751 < baseStart_6729751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729753 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_6729753 : Nat := 118140960795 + 6729753 * 2 ^ 59
def prefixEnd_6729753 : Nat := 4983230072969 + 3 ^ 40 * 6729753 * 2
def baseEnd_6729753 : Nat := 3455597975037113544137935

theorem tailTrace_6729753 : CollatzResearch.WordTrace tailWord_6729753 prefixEnd_6729753 3455597975037113544137935 := by
  unfold tailWord_6729753
  simp only [CollatzResearch.WordTrace]
  refine ⟨245454256788261706153057913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163636171192174470768705275 245454256788261706153057913)
  ·
    refine ⟨184090692591196279614793435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245454256788261706153057913 184090692591196279614793435)
    ·
      refine ⟨276136038886794419422190153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184090692591196279614793435 276136038886794419422190153)
      ·
        refine ⟨207102029165095814566642615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276136038886794419422190153 207102029165095814566642615)
        ·
          refine ⟨310653043747643721849963923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207102029165095814566642615 310653043747643721849963923)
          ·
            refine ⟨465979565621465582774945885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310653043747643721849963923 465979565621465582774945885)
            ·
              refine ⟨174742337108049593540604707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465979565621465582774945885 174742337108049593540604707)
              ·
                refine ⟨262113505662074390310907061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174742337108049593540604707 262113505662074390310907061)
                ·
                  refine ⟨24573141155819474091647537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262113505662074390310907061 24573141155819474091647537)
                  ·
                    refine ⟨18429855866864605568735653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24573141155819474091647537 18429855866864605568735653)
                    ·
                      refine ⟨3455597975037113544137935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18429855866864605568735653 3455597975037113544137935)
                      ·
                        rfl

theorem cell23_6729753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_6729753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729753 prefixEnd_6729753 := by exact prefixLift 6729753
  have htrace : WordTrace (prefixWord ++ tailWord_6729753) baseStart_6729753 baseEnd_6729753 := by
    simpa [prefixWord, tailWord_6729753, baseEnd_6729753] using wordTrace_append hprefix tailTrace_6729753
  have hstable : (prefixWord ++ tailWord_6729753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729753).length < 2 ^ (prefixWord ++ tailWord_6729753).sum := by decide
  have hdescent : baseEnd_6729753 < baseStart_6729753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729774 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_6729774 : Nat := 118140960795 + 6729774 * 2 ^ 59
def prefixEnd_6729774 : Nat := 4983230072969 + 3 ^ 40 * 6729774 * 2
def baseEnd_6729774 : Nat := 3455608758130857961975339

theorem tailTrace_6729774 : CollatzResearch.WordTrace tailWord_6729774 prefixEnd_6729774 3455608758130857961975339 := by
  unfold tailWord_6729774
  simp only [CollatzResearch.WordTrace]
  refine ⟨30681877840148203342446547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163636681814123751159714917 30681877840148203342446547)
  ·
    refine ⟨46022816760222305013669821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30681877840148203342446547 46022816760222305013669821)
    ·
      refine ⟨17258556285083364380126183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46022816760222305013669821 17258556285083364380126183)
      ·
        refine ⟨25887834427625046570189275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17258556285083364380126183 25887834427625046570189275)
        ·
          refine ⟨38831751641437569855283913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25887834427625046570189275 38831751641437569855283913)
          ·
            refine ⟨29123813731078177391462935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38831751641437569855283913 29123813731078177391462935)
            ·
              refine ⟨43685720596617266087194403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29123813731078177391462935 43685720596617266087194403)
              ·
                refine ⟨65528580894925899130791605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43685720596617266087194403 65528580894925899130791605)
                ·
                  refine ⟨6143304458899303043511713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65528580894925899130791605 6143304458899303043511713)
                  ·
                    refine ⟨4607478344174477282633785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6143304458899303043511713 4607478344174477282633785)
                    ·
                      refine ⟨3455608758130857961975339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607478344174477282633785 3455608758130857961975339)
                      ·
                        rfl

theorem cell23_6729774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_6729774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729774 prefixEnd_6729774 := by exact prefixLift 6729774
  have htrace : WordTrace (prefixWord ++ tailWord_6729774) baseStart_6729774 baseEnd_6729774 := by
    simpa [prefixWord, tailWord_6729774, baseEnd_6729774] using wordTrace_append hprefix tailTrace_6729774
  have hstable : (prefixWord ++ tailWord_6729774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729774).length < 2 ^ (prefixWord ++ tailWord_6729774).sum := by decide
  have hdescent : baseEnd_6729774 < baseStart_6729774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729803 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5]
def baseStart_6729803 : Nat := 118140960795 + 6729803 * 2 ^ 59
def prefixEnd_6729803 : Nat := 4983230072969 + 3 ^ 40 * 6729803 * 2
def baseEnd_6729803 : Nat := 3455623649069838348512705

theorem tailTrace_6729803 : CollatzResearch.WordTrace tailWord_6729803 prefixEnd_6729803 3455623649069838348512705 := by
  unfold tailWord_6729803
  simp only [CollatzResearch.WordTrace]
  refine ⟨245456080438080564692378063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163637386958720376461585375 245456080438080564692378063)
  ·
    refine ⟨368184120657120847038567095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245456080438080564692378063 368184120657120847038567095)
    ·
      refine ⟨552276180985681270557850643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368184120657120847038567095 552276180985681270557850643)
      ·
        refine ⟨828414271478521905836775965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552276180985681270557850643 828414271478521905836775965)
        ·
          refine ⟨310655351804445714688790987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828414271478521905836775965 310655351804445714688790987)
          ·
            refine ⟨465983027706668572033186481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310655351804445714688790987 465983027706668572033186481)
            ·
              refine ⟨349487270780001429024889861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465983027706668572033186481 349487270780001429024889861)
              ·
                refine ⟨65528863271250267942166849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349487270780001429024889861 65528863271250267942166849)
                ·
                  refine ⟨49146647453437700956625137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65528863271250267942166849 49146647453437700956625137)
                  ·
                    refine ⟨36859985590078275717468853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49146647453437700956625137 36859985590078275717468853)
                    ·
                      refine ⟨3455623649069838348512705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36859985590078275717468853 3455623649069838348512705)
                      ·
                        rfl

theorem cell23_6729803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_6729803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729803 prefixEnd_6729803 := by exact prefixLift 6729803
  have htrace : WordTrace (prefixWord ++ tailWord_6729803) baseStart_6729803 baseEnd_6729803 := by
    simpa [prefixWord, tailWord_6729803, baseEnd_6729803] using wordTrace_append hprefix tailTrace_6729803
  have hstable : (prefixWord ++ tailWord_6729803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729803).length < 2 ^ (prefixWord ++ tailWord_6729803).sum := by decide
  have hdescent : baseEnd_6729803 < baseStart_6729803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729823 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 1, 8]
def baseStart_6729823 : Nat := 118140960795 + 6729823 * 2 ^ 59
def prefixEnd_6729823 : Nat := 4983230072969 + 3 ^ 40 * 6729823 * 2
def baseEnd_6729823 : Nat := 1151877972894309423420871

theorem tailTrace_6729823 : CollatzResearch.WordTrace tailWord_6729823 prefixEnd_6729823 1151877972894309423420871 := by
  unfold tailWord_6729823
  simp only [CollatzResearch.WordTrace]
  refine ⟨245456809898008108108106123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163637873265338738738737415 245456809898008108108106123)
  ·
    refine ⟨368185214847012162162159185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245456809898008108108106123 368185214847012162162159185)
    ·
      refine ⟨276138911135259121621619389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368185214847012162162159185 276138911135259121621619389)
      ·
        refine ⟨103552091675722170608107271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276138911135259121621619389 103552091675722170608107271)
        ·
          refine ⟨155328137513583255912160907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103552091675722170608107271 155328137513583255912160907)
          ·
            refine ⟨232992206270374883868241361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155328137513583255912160907 232992206270374883868241361)
            ·
              refine ⟨174744154702781162901181021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232992206270374883868241361 174744154702781162901181021)
              ·
                refine ⟨65529058013542936087942883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174744154702781162901181021 65529058013542936087942883)
                ·
                  refine ⟨98293587020314404131914325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65529058013542936087942883 98293587020314404131914325)
                  ·
                    refine ⟨1151877972894309423420871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98293587020314404131914325 1151877972894309423420871)
                    ·
                      rfl

theorem cell23_6729823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_6729823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729823 prefixEnd_6729823 := by exact prefixLift 6729823
  have htrace : WordTrace (prefixWord ++ tailWord_6729823) baseStart_6729823 baseEnd_6729823 := by
    simpa [prefixWord, tailWord_6729823, baseEnd_6729823] using wordTrace_append hprefix tailTrace_6729823
  have hstable : (prefixWord ++ tailWord_6729823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729823).length < 2 ^ (prefixWord ++ tailWord_6729823).sum := by decide
  have hdescent : baseEnd_6729823 < baseStart_6729823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729921 : List Nat := [1, 2, 6, 1, 2, 1, 1, 4, 5]
def baseStart_6729921 : Nat := 118140960795 + 6729921 * 2 ^ 59
def prefixEnd_6729921 : Nat := 4983230072969 + 3 ^ 40 * 6729921 * 2
def baseEnd_6729921 : Nat := 383964915531896542981907

theorem tailTrace_6729921 : CollatzResearch.WordTrace tailWord_6729921 prefixEnd_6729921 383964915531896542981907 := by
  unfold tailWord_6729921
  simp only [CollatzResearch.WordTrace]
  refine ⟨245460384251653070845173617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163640256167768713896782411 245460384251653070845173617)
  ·
    refine ⟨184095288188739803133880213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245460384251653070845173617 184095288188739803133880213)
    ·
      refine ⟨8629466633847178271900635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184095288188739803133880213 8629466633847178271900635)
      ·
        refine ⟨12944199950770767407850953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8629466633847178271900635 12944199950770767407850953)
        ·
          refine ⟨9708149963078075555888215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12944199950770767407850953 9708149963078075555888215)
          ·
            refine ⟨14562224944617113333832323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9708149963078075555888215 14562224944617113333832323)
            ·
              refine ⟨21843337416925670000748485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14562224944617113333832323 21843337416925670000748485)
              ·
                refine ⟨4095625765673563125140341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21843337416925670000748485 4095625765673563125140341)
                ·
                  refine ⟨383964915531896542981907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4095625765673563125140341 383964915531896542981907)
                  ·
                    rfl

theorem cell23_6729921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 5].length) (baseStart_6729921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729921 prefixEnd_6729921 := by exact prefixLift 6729921
  have htrace : WordTrace (prefixWord ++ tailWord_6729921) baseStart_6729921 baseEnd_6729921 := by
    simpa [prefixWord, tailWord_6729921, baseEnd_6729921] using wordTrace_append hprefix tailTrace_6729921
  have hstable : (prefixWord ++ tailWord_6729921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729921).length < 2 ^ (prefixWord ++ tailWord_6729921).sum := by decide
  have hdescent : baseEnd_6729921 < baseStart_6729921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729924 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_6729924 : Nat := 118140960795 + 6729924 * 2 ^ 59
def prefixEnd_6729924 : Nat := 4983230072969 + 3 ^ 40 * 6729924 * 2
def baseEnd_6729924 : Nat := 3455685780229032375099649

theorem tailTrace_6729924 : CollatzResearch.WordTrace tailWord_6729924 prefixEnd_6729924 3455685780229032375099649 := by
  unfold tailWord_6729924
  simp only [CollatzResearch.WordTrace]
  refine ⟨122730246835321101178766413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163640329113761468238355217 122730246835321101178766413)
  ·
    refine ⟨46023842563245412942037405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122730246835321101178766413 46023842563245412942037405)
    ·
      refine ⟨17258940961217029853264027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46023842563245412942037405 17258940961217029853264027)
      ·
        refine ⟨25888411441825544779896041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17258940961217029853264027 25888411441825544779896041)
        ·
          refine ⟨19416308581369158584922031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25888411441825544779896041 19416308581369158584922031)
          ·
            refine ⟨29124462872053737877383047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19416308581369158584922031 29124462872053737877383047)
            ·
              refine ⟨43686694308080606816074571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29124462872053737877383047 43686694308080606816074571)
              ·
                refine ⟨65530041462120910224111857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43686694308080606816074571 65530041462120910224111857)
                ·
                  refine ⟨49147531096590682668083893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65530041462120910224111857 49147531096590682668083893)
                  ·
                    refine ⟨4607581040305376500132865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49147531096590682668083893 4607581040305376500132865)
                    ·
                      refine ⟨3455685780229032375099649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607581040305376500132865 3455685780229032375099649)
                      ·
                        rfl

theorem cell23_6729924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_6729924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729924 prefixEnd_6729924 := by exact prefixLift 6729924
  have htrace : WordTrace (prefixWord ++ tailWord_6729924) baseStart_6729924 baseEnd_6729924 := by
    simpa [prefixWord, tailWord_6729924, baseEnd_6729924] using wordTrace_append hprefix tailTrace_6729924
  have hstable : (prefixWord ++ tailWord_6729924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729924).length < 2 ^ (prefixWord ++ tailWord_6729924).sum := by decide
  have hdescent : baseEnd_6729924 < baseStart_6729924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729937 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 1, 6, 2]
def baseStart_6729937 : Nat := 118140960795 + 6729937 * 2 ^ 59
def prefixEnd_6729937 : Nat := 4983230072969 + 3 ^ 40 * 6729937 * 2
def baseEnd_6729937 : Nat := 3455692455477540824237089

theorem tailTrace_6729937 : CollatzResearch.WordTrace tailWord_6729937 prefixEnd_6729937 3455692455477540824237089 := by
  unfold tailWord_6729937
  simp only [CollatzResearch.WordTrace]
  refine ⟨245460967819595105577756065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163640645213063403718504043 245460967819595105577756065)
  ·
    refine ⟨184095725864696329183317049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245460967819595105577756065 184095725864696329183317049)
    ·
      refine ⟨138071794398522246887487787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184095725864696329183317049 138071794398522246887487787)
      ·
        refine ⟨207107691597783370331231681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138071794398522246887487787 207107691597783370331231681)
        ·
          refine ⟨155330768698337527748423761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207107691597783370331231681 155330768698337527748423761)
          ·
            refine ⟨116498076523753145811317821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155330768698337527748423761 116498076523753145811317821)
            ·
              refine ⟨43686778696407429679244183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116498076523753145811317821 43686778696407429679244183)
              ·
                refine ⟨65530168044611144518866275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43686778696407429679244183 65530168044611144518866275)
                ·
                  refine ⟨98295252066916716778299413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65530168044611144518866275 98295252066916716778299413)
                  ·
                    refine ⟨4607589940636721098982785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98295252066916716778299413 4607589940636721098982785)
                    ·
                      refine ⟨3455692455477540824237089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607589940636721098982785 3455692455477540824237089)
                      ·
                        rfl

theorem cell23_6729937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_6729937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729937 prefixEnd_6729937 := by exact prefixLift 6729937
  have htrace : WordTrace (prefixWord ++ tailWord_6729937) baseStart_6729937 baseEnd_6729937 := by
    simpa [prefixWord, tailWord_6729937, baseEnd_6729937] using wordTrace_append hprefix tailTrace_6729937
  have hstable : (prefixWord ++ tailWord_6729937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729937).length < 2 ^ (prefixWord ++ tailWord_6729937).sum := by decide
  have hdescent : baseEnd_6729937 < baseStart_6729937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6729974 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_6729974 : Nat := 118140960795 + 6729974 * 2 ^ 59
def prefixEnd_6729974 : Nat := 4983230072969 + 3 ^ 40 * 6729974 * 2
def baseEnd_6729974 : Nat := 3455711454261757179474419

theorem tailTrace_6729974 : CollatzResearch.WordTrace tailWord_6729974 prefixEnd_6729974 3455711454261757179474419 := by
  unfold tailWord_6729974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341394832528816306053311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163641544880307373931235317 15341394832528816306053311)
  ·
    refine ⟨23012092248793224459079967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15341394832528816306053311 23012092248793224459079967)
    ·
      refine ⟨34518138373189836688619951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23012092248793224459079967 34518138373189836688619951)
      ·
        refine ⟨51777207559784755032929927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34518138373189836688619951 51777207559784755032929927)
        ·
          refine ⟨77665811339677132549394891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51777207559784755032929927 77665811339677132549394891)
          ·
            refine ⟨116498717009515698824092337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77665811339677132549394891 116498717009515698824092337)
            ·
              refine ⟨87374037757136774118069253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116498717009515698824092337 87374037757136774118069253)
              ·
                refine ⟨16382632079463145147137985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87374037757136774118069253 16382632079463145147137985)
                ·
                  refine ⟨12286974059597358860353489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16382632079463145147137985 12286974059597358860353489)
                  ·
                    refine ⟨9215230544698019145265117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12286974059597358860353489 9215230544698019145265117)
                    ·
                      refine ⟨3455711454261757179474419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9215230544698019145265117 3455711454261757179474419)
                      ·
                        rfl

theorem cell23_6729974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_6729974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6729974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6729974 prefixEnd_6729974 := by exact prefixLift 6729974
  have htrace : WordTrace (prefixWord ++ tailWord_6729974) baseStart_6729974 baseEnd_6729974 := by
    simpa [prefixWord, tailWord_6729974, baseEnd_6729974] using wordTrace_append hprefix tailTrace_6729974
  have hstable : (prefixWord ++ tailWord_6729974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6729974).length < 2 ^ (prefixWord ++ tailWord_6729974).sum := by decide
  have hdescent : baseEnd_6729974 < baseStart_6729974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6729974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730047 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_6730047 : Nat := 118140960795 + 6730047 * 2 ^ 59
def prefixEnd_6730047 : Nat := 4983230072969 + 3 ^ 40 * 6730047 * 2
def baseEnd_6730047 : Nat := 3455748938349535393861583

theorem tailTrace_6730047 : CollatzResearch.WordTrace tailWord_6730047 prefixEnd_6730047 3455748938349535393861583 := by
  unfold tailWord_6730047
  simp only [CollatzResearch.WordTrace]
  refine ⟨245464979849196594364260395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163643319899464396242840263 245464979849196594364260395)
  ·
    refine ⟨368197469773794891546390593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245464979849196594364260395 368197469773794891546390593)
    ·
      refine ⟨276148102330346168659792945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368197469773794891546390593 276148102330346168659792945)
      ·
        refine ⟨207111076747759626494844709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276148102330346168659792945 207111076747759626494844709)
        ·
          refine ⟨38833326890204929967783383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207111076747759626494844709 38833326890204929967783383)
          ·
            refine ⟨58249990335307394951675075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38833326890204929967783383 58249990335307394951675075)
            ·
              refine ⟨87374985502961092427512613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58249990335307394951675075 87374985502961092427512613)
              ·
                refine ⟨16382809781805204830158615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87374985502961092427512613 16382809781805204830158615)
                ·
                  refine ⟨24574214672707807245237923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16382809781805204830158615 24574214672707807245237923)
                  ·
                    refine ⟨36861322009061710867856885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24574214672707807245237923 36861322009061710867856885)
                    ·
                      refine ⟨3455748938349535393861583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36861322009061710867856885 3455748938349535393861583)
                      ·
                        rfl

theorem cell23_6730047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_6730047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730047 prefixEnd_6730047 := by exact prefixLift 6730047
  have htrace : WordTrace (prefixWord ++ tailWord_6730047) baseStart_6730047 baseEnd_6730047 := by
    simpa [prefixWord, tailWord_6730047, baseEnd_6730047] using wordTrace_append hprefix tailTrace_6730047
  have hstable : (prefixWord ++ tailWord_6730047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730047).length < 2 ^ (prefixWord ++ tailWord_6730047).sum := by decide
  have hdescent : baseEnd_6730047 < baseStart_6730047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730057 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_6730057 : Nat := 118140960795 + 6730057 * 2 ^ 59
def prefixEnd_6730057 : Nat := 4983230072969 + 3 ^ 40 * 6730057 * 2
def baseEnd_6730057 : Nat := 3455754073156080354736537

theorem tailTrace_6730057 : CollatzResearch.WordTrace tailWord_6730057 prefixEnd_6730057 3455754073156080354736537 := by
  unfold tailWord_6730057
  simp only [CollatzResearch.WordTrace]
  refine ⟨245465344579160366072124425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163643563052773577381416283 245465344579160366072124425)
  ·
    refine ⟨184099008434370274554093319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245465344579160366072124425 184099008434370274554093319)
    ·
      refine ⟨276148512651555411831139979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184099008434370274554093319 276148512651555411831139979)
      ·
        refine ⟨414222768977333117746709969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276148512651555411831139979 414222768977333117746709969)
        ·
          refine ⟨310667076732999838310032477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414222768977333117746709969 310667076732999838310032477)
          ·
            refine ⟨116500153774874939366262179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310667076732999838310032477 116500153774874939366262179)
            ·
              refine ⟨174750230662312409049393269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116500153774874939366262179 174750230662312409049393269)
              ·
                refine ⟨16382834124591788348380619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174750230662312409049393269 16382834124591788348380619)
                ·
                  refine ⟨24574251186887682522570929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16382834124591788348380619 24574251186887682522570929)
                  ·
                    refine ⟨18430688390165761891928197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24574251186887682522570929 18430688390165761891928197)
                    ·
                      refine ⟨3455754073156080354736537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18430688390165761891928197 3455754073156080354736537)
                      ·
                        rfl

theorem cell23_6730057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_6730057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730057 prefixEnd_6730057 := by exact prefixLift 6730057
  have htrace : WordTrace (prefixWord ++ tailWord_6730057) baseStart_6730057 baseEnd_6730057 := by
    simpa [prefixWord, tailWord_6730057, baseEnd_6730057] using wordTrace_append hprefix tailTrace_6730057
  have hstable : (prefixWord ++ tailWord_6730057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730057).length < 2 ^ (prefixWord ++ tailWord_6730057).sum := by decide
  have hdescent : baseEnd_6730057 < baseStart_6730057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730064 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3]
def baseStart_6730064 : Nat := 118140960795 + 6730064 * 2 ^ 59
def prefixEnd_6730064 : Nat := 4983230072969 + 3 ^ 40 * 6730064 * 2
def baseEnd_6730064 : Nat := 3455757667520661827349005

theorem tailTrace_6730064 : CollatzResearch.WordTrace tailWord_6730064 prefixEnd_6730064 3455757667520661827349005 := by
  unfold tailWord_6730064
  simp only [CollatzResearch.WordTrace]
  refine ⟨122732799945067503133814623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163643733260090004178419497 122732799945067503133814623)
  ·
    refine ⟨184099199917601254700721935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122732799945067503133814623 184099199917601254700721935)
    ·
      refine ⟨276148799876401882051082903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184099199917601254700721935 276148799876401882051082903)
      ·
        refine ⟨414223199814602823076624355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276148799876401882051082903 414223199814602823076624355)
        ·
          refine ⟨621334799721904234614936533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414223199814602823076624355 621334799721904234614936533)
          ·
            refine ⟨14562534368482130498787575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 621334799721904234614936533 14562534368482130498787575)
            ·
              refine ⟨21843801552723195748181363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14562534368482130498787575 21843801552723195748181363)
              ·
                refine ⟨32765702329084793622272045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21843801552723195748181363 32765702329084793622272045)
                ·
                  refine ⟨12287138373406797608352017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32765702329084793622272045 12287138373406797608352017)
                  ·
                    refine ⟨9215353780055098206264013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12287138373406797608352017 9215353780055098206264013)
                    ·
                      refine ⟨3455757667520661827349005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9215353780055098206264013 3455757667520661827349005)
                      ·
                        rfl

theorem cell23_6730064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_6730064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730064 prefixEnd_6730064 := by exact prefixLift 6730064
  have htrace : WordTrace (prefixWord ++ tailWord_6730064) baseStart_6730064 baseEnd_6730064 := by
    simpa [prefixWord, tailWord_6730064, baseEnd_6730064] using wordTrace_append hprefix tailTrace_6730064
  have hstable : (prefixWord ++ tailWord_6730064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730064).length < 2 ^ (prefixWord ++ tailWord_6730064).sum := by decide
  have hdescent : baseEnd_6730064 < baseStart_6730064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730117 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_6730117 : Nat := 118140960795 + 6730117 * 2 ^ 59
def prefixEnd_6730117 : Nat := 4983230072969 + 3 ^ 40 * 6730117 * 2
def baseEnd_6730117 : Nat := 3455784881995350119986261

theorem tailTrace_6730117 : CollatzResearch.WordTrace tailWord_6730117 prefixEnd_6730117 3455784881995350119986261 := by
  unfold tailWord_6730117
  simp only [CollatzResearch.WordTrace]
  refine ⟨245467532958942996319308605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163645021972628664212872403 245467532958942996319308605)
  ·
    refine ⟨92050324859603623619740727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245467532958942996319308605 92050324859603623619740727)
    ·
      refine ⟨138075487289405435429611091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92050324859603623619740727 138075487289405435429611091)
      ·
        refine ⟨207113230934108153144416637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138075487289405435429611091 207113230934108153144416637)
        ·
          refine ⟨77667461600290557429156239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207113230934108153144416637 77667461600290557429156239)
          ·
            refine ⟨116501192400435836143734359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77667461600290557429156239 116501192400435836143734359)
            ·
              refine ⟨174751788600653754215601539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116501192400435836143734359 174751788600653754215601539)
              ·
                refine ⟨262127682900980631323402309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174751788600653754215601539 262127682900980631323402309)
                ·
                  refine ⟨49148940543933868373137933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262127682900980631323402309 49148940543933868373137933)
                  ·
                    refine ⟨18430852703975200639926725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49148940543933868373137933 18430852703975200639926725)
                    ·
                      refine ⟨3455784881995350119986261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18430852703975200639926725 3455784881995350119986261)
                      ·
                        rfl

theorem cell23_6730117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_6730117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730117 prefixEnd_6730117 := by exact prefixLift 6730117
  have htrace : WordTrace (prefixWord ++ tailWord_6730117) baseStart_6730117 baseEnd_6730117 := by
    simpa [prefixWord, tailWord_6730117, baseEnd_6730117] using wordTrace_append hprefix tailTrace_6730117
  have hstable : (prefixWord ++ tailWord_6730117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730117).length < 2 ^ (prefixWord ++ tailWord_6730117).sum := by decide
  have hdescent : baseEnd_6730117 < baseStart_6730117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730121 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 3, 3, 2]
def baseStart_6730121 : Nat := 118140960795 + 6730121 * 2 ^ 59
def prefixEnd_6730121 : Nat := 4983230072969 + 3 ^ 40 * 6730121 * 2
def baseEnd_6730121 : Nat := 3455786935917968104336243

theorem tailTrace_6730121 : CollatzResearch.WordTrace tailWord_6730121 prefixEnd_6730121 3455786935917968104336243 := by
  unfold tailWord_6730121
  simp only [CollatzResearch.WordTrace]
  refine ⟨245467678850928505002454217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163645119233952336668302811 245467678850928505002454217)
  ·
    refine ⟨184100759138196378751840663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245467678850928505002454217 184100759138196378751840663)
    ·
      refine ⟨276151138707294568127760995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184100759138196378751840663 276151138707294568127760995)
      ·
        refine ⟨414226708060941852191641493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276151138707294568127760995 414226708060941852191641493)
        ·
          refine ⟨19416876940356649321483195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 414226708060941852191641493 19416876940356649321483195)
          ·
            refine ⟨29125315410534973982224793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19416876940356649321483195 29125315410534973982224793)
            ·
              refine ⟨21843986557901230486668595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29125315410534973982224793 21843986557901230486668595)
              ·
                refine ⟨32765979836851845730002893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21843986557901230486668595 32765979836851845730002893)
                ·
                  refine ⟨12287242438819442148751085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32765979836851845730002893 12287242438819442148751085)
                  ·
                    refine ⟨4607715914557290805781657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12287242438819442148751085 4607715914557290805781657)
                    ·
                      refine ⟨3455786935917968104336243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607715914557290805781657 3455786935917968104336243)
                      ·
                        rfl

theorem cell23_6730121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 3, 2].length) (baseStart_6730121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730121 prefixEnd_6730121 := by exact prefixLift 6730121
  have htrace : WordTrace (prefixWord ++ tailWord_6730121) baseStart_6730121 baseEnd_6730121 := by
    simpa [prefixWord, tailWord_6730121, baseEnd_6730121] using wordTrace_append hprefix tailTrace_6730121
  have hstable : (prefixWord ++ tailWord_6730121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730121).length < 2 ^ (prefixWord ++ tailWord_6730121).sum := by decide
  have hdescent : baseEnd_6730121 < baseStart_6730121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730132 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_6730132 : Nat := 118140960795 + 6730132 * 2 ^ 59
def prefixEnd_6730132 : Nat := 4983230072969 + 3 ^ 40 * 6730132 * 2
def baseEnd_6730132 : Nat := 3455792584205167561298693

theorem tailTrace_6730132 : CollatzResearch.WordTrace tailWord_6730132 prefixEnd_6730132 3455792584205167561298693 := by
  unfold tailWord_6730132
  simp only [CollatzResearch.WordTrace]
  refine ⟨122734040026944326940552325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163645386702592435920736433 122734040026944326940552325)
  ·
    refine ⟨23012632505052061301353561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122734040026944326940552325 23012632505052061301353561)
    ·
      refine ⟨17259474378789045976015171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23012632505052061301353561 17259474378789045976015171)
      ·
        refine ⟨25889211568183568964022757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17259474378789045976015171 25889211568183568964022757)
        ·
          refine ⟨4854227169034419180754267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25889211568183568964022757 4854227169034419180754267)
          ·
            refine ⟨7281340753551628771131401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854227169034419180754267 7281340753551628771131401)
            ·
              refine ⟨5461005565163721578348551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7281340753551628771131401 5461005565163721578348551)
              ·
                refine ⟨8191508347745582367522827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461005565163721578348551 8191508347745582367522827)
                ·
                  refine ⟨12287262521618373551284241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8191508347745582367522827 12287262521618373551284241)
                  ·
                    refine ⟨9215446891213780163463181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12287262521618373551284241 9215446891213780163463181)
                    ·
                      refine ⟨3455792584205167561298693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9215446891213780163463181 3455792584205167561298693)
                      ·
                        rfl

theorem cell23_6730132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_6730132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730132 prefixEnd_6730132 := by exact prefixLift 6730132
  have htrace : WordTrace (prefixWord ++ tailWord_6730132) baseStart_6730132 baseEnd_6730132 := by
    simpa [prefixWord, tailWord_6730132, baseEnd_6730132] using wordTrace_append hprefix tailTrace_6730132
  have hstable : (prefixWord ++ tailWord_6730132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730132).length < 2 ^ (prefixWord ++ tailWord_6730132).sum := by decide
  have hdescent : baseEnd_6730132 < baseStart_6730132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730137 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_6730137 : Nat := 118140960795 + 6730137 * 2 ^ 59
def prefixEnd_6730137 : Nat := 4983230072969 + 3 ^ 40 * 6730137 * 2
def baseEnd_6730137 : Nat := 3455795151608440041736169

theorem tailTrace_6730137 : CollatzResearch.WordTrace tailWord_6730137 prefixEnd_6730137 3455795151608440041736169 := by
  unfold tailWord_6730137
  simp only [CollatzResearch.WordTrace]
  refine ⟨245468262418870539735036665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163645508279247026490024443 245468262418870539735036665)
  ·
    refine ⟨184101196814152904801277499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245468262418870539735036665 184101196814152904801277499)
    ·
      refine ⟨276151795221229357201916249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184101196814152904801277499 276151795221229357201916249)
      ·
        refine ⟨207113846415922017901437187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276151795221229357201916249 207113846415922017901437187)
        ·
          refine ⟨310670769623883026852155781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207113846415922017901437187 310670769623883026852155781)
          ·
            refine ⟨58250769304478067534779209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310670769623883026852155781 58250769304478067534779209)
            ·
              refine ⟨43688076978358550651084407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58250769304478067534779209 43688076978358550651084407)
              ·
                refine ⟨65532115467537825976626611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43688076978358550651084407 65532115467537825976626611)
                ·
                  refine ⟨98298173201306738964939917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65532115467537825976626611 98298173201306738964939917)
                  ·
                    refine ⟨36861814950490027111852469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98298173201306738964939917 36861814950490027111852469)
                    ·
                      refine ⟨3455795151608440041736169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36861814950490027111852469 3455795151608440041736169)
                      ·
                        rfl

theorem cell23_6730137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_6730137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730137 prefixEnd_6730137 := by exact prefixLift 6730137
  have htrace : WordTrace (prefixWord ++ tailWord_6730137) baseStart_6730137 baseEnd_6730137 := by
    simpa [prefixWord, tailWord_6730137, baseEnd_6730137] using wordTrace_append hprefix tailTrace_6730137
  have hstable : (prefixWord ++ tailWord_6730137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730137).length < 2 ^ (prefixWord ++ tailWord_6730137).sum := by decide
  have hdescent : baseEnd_6730137 < baseStart_6730137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730138 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2]
def baseStart_6730138 : Nat := 118140960795 + 6730138 * 2 ^ 59
def prefixEnd_6730138 : Nat := 4983230072969 + 3 ^ 40 * 6730138 * 2
def baseEnd_6730138 : Nat := 3455795665089094537823665

theorem tailTrace_6730138 : CollatzResearch.WordTrace tailWord_6730138 prefixEnd_6730138 3455795665089094537823665 := by
  unfold tailWord_6730138
  simp only [CollatzResearch.WordTrace]
  refine ⟨61367074722966729226455767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163645532594577944603882045 61367074722966729226455767)
  ·
    refine ⟨92050612084450093839683651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61367074722966729226455767 92050612084450093839683651)
    ·
      refine ⟨138075918126675140759525477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92050612084450093839683651 138075918126675140759525477)
      ·
        refine ⟨25889234648751588892411027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138075918126675140759525477 25889234648751588892411027)
        ·
          refine ⟨38833851973127383338616541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25889234648751588892411027 38833851973127383338616541)
          ·
            refine ⟨14562694489922768751981203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38833851973127383338616541 14562694489922768751981203)
            ·
              refine ⟨21844041734884153127971805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14562694489922768751981203 21844041734884153127971805)
              ·
                refine ⟨8191515650581557422989427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21844041734884153127971805 8191515650581557422989427)
                ·
                  refine ⟨12287273475872336134484141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8191515650581557422989427 12287273475872336134484141)
                  ·
                    refine ⟨4607727553452126050431553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12287273475872336134484141 4607727553452126050431553)
                    ·
                      refine ⟨3455795665089094537823665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607727553452126050431553 3455795665089094537823665)
                      ·
                        rfl

theorem cell23_6730138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_6730138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730138 prefixEnd_6730138 := by exact prefixLift 6730138
  have htrace : WordTrace (prefixWord ++ tailWord_6730138) baseStart_6730138 baseEnd_6730138 := by
    simpa [prefixWord, tailWord_6730138, baseEnd_6730138] using wordTrace_append hprefix tailTrace_6730138
  have hstable : (prefixWord ++ tailWord_6730138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730138).length < 2 ^ (prefixWord ++ tailWord_6730138).sum := by decide
  have hdescent : baseEnd_6730138 < baseStart_6730138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730174 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_6730174 : Nat := 118140960795 + 6730174 * 2 ^ 59
def prefixEnd_6730174 : Nat := 4983230072969 + 3 ^ 40 * 6730174 * 2
def baseEnd_6730174 : Nat := 383979350043628488552611

theorem tailTrace_6730174 : CollatzResearch.WordTrace tailWord_6730174 prefixEnd_6730174 383979350043628488552611 := by
  unfold tailWord_6730174
  simp only [CollatzResearch.WordTrace]
  refine ⟨30683701489967061881766697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163646407946490996702755717 30683701489967061881766697)
  ·
    refine ⟨23012776117475296411325023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30683701489967061881766697 23012776117475296411325023)
    ·
      refine ⟨34519164176212944616987535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23012776117475296411325023 34519164176212944616987535)
      ·
        refine ⟨51778746264319416925481303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34519164176212944616987535 51778746264319416925481303)
        ·
          refine ⟨77668119396479125388221955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51778746264319416925481303 77668119396479125388221955)
          ·
            refine ⟨116502179094718688082332933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77668119396479125388221955 116502179094718688082332933)
            ·
              refine ⟨21844158580259754015437425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116502179094718688082332933 21844158580259754015437425)
              ·
                refine ⟨16383118935194815511578069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21844158580259754015437425 16383118935194815511578069)
                ·
                  refine ⟨383979350043628488552611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16383118935194815511578069 383979350043628488552611)
                  ·
                    rfl

theorem cell23_6730174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_6730174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730174 prefixEnd_6730174 := by exact prefixLift 6730174
  have htrace : WordTrace (prefixWord ++ tailWord_6730174) baseStart_6730174 baseEnd_6730174 := by
    simpa [prefixWord, tailWord_6730174, baseEnd_6730174] using wordTrace_append hprefix tailTrace_6730174
  have hstable : (prefixWord ++ tailWord_6730174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730174).length < 2 ^ (prefixWord ++ tailWord_6730174).sum := by decide
  have hdescent : baseEnd_6730174 < baseStart_6730174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730217 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 2, 8]
def baseStart_6730217 : Nat := 118140960795 + 6730217 * 2 ^ 59
def prefixEnd_6730217 : Nat := 4983230072969 + 3 ^ 40 * 6730217 * 2
def baseEnd_6730217 : Nat := 1151945410020266576245267

theorem tailTrace_6730217 : CollatzResearch.WordTrace tailWord_6730217 prefixEnd_6730217 1151945410020266576245267 := by
  unfold tailWord_6730217
  simp only [CollatzResearch.WordTrace]
  refine ⟨245471180258580713397948905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163647453505720475598632603 245471180258580713397948905)
  ·
    refine ⟨184103385193935535048461679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245471180258580713397948905 184103385193935535048461679)
    ·
      refine ⟨276155077790903302572692519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184103385193935535048461679 276155077790903302572692519)
      ·
        refine ⟨414232616686354953859038779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276155077790903302572692519 414232616686354953859038779)
        ·
          refine ⟨621348925029532430788558169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414232616686354953859038779 621348925029532430788558169)
          ·
            refine ⟨466011693772149323091418627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621348925029532430788558169 466011693772149323091418627)
            ·
              refine ⟨699017540658223984637127941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466011693772149323091418627 699017540658223984637127941)
              ·
                refine ⟨131065788873416997119461489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 699017540658223984637127941 131065788873416997119461489)
                ·
                  refine ⟨98299341655062747839596117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131065788873416997119461489 98299341655062747839596117)
                  ·
                    refine ⟨1151945410020266576245267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98299341655062747839596117 1151945410020266576245267)
                    ·
                      rfl

theorem cell23_6730217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_6730217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730217 prefixEnd_6730217 := by exact prefixLift 6730217
  have htrace : WordTrace (prefixWord ++ tailWord_6730217) baseStart_6730217 baseEnd_6730217 := by
    simpa [prefixWord, tailWord_6730217, baseEnd_6730217] using wordTrace_append hprefix tailTrace_6730217
  have hstable : (prefixWord ++ tailWord_6730217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730217).length < 2 ^ (prefixWord ++ tailWord_6730217).sum := by decide
  have hdescent : baseEnd_6730217 < baseStart_6730217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730224 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_6730224 : Nat := 118140960795 + 6730224 * 2 ^ 59
def prefixEnd_6730224 : Nat := 4983230072969 + 3 ^ 40 * 6730224 * 2
def baseEnd_6730224 : Nat := 3455839824425381201348269

theorem tailTrace_6730224 : CollatzResearch.WordTrace tailWord_6730224 prefixEnd_6730224 3455839824425381201348269 := by
  unfold tailWord_6730224
  simp only [CollatzResearch.WordTrace]
  refine ⟨122735717784777676796726863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163647623713036902395635817 122735717784777676796726863)
  ·
    refine ⟨184103576677166515195090295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122735717784777676796726863 184103576677166515195090295)
    ·
      refine ⟨276155365015749772792635443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184103576677166515195090295 276155365015749772792635443)
      ·
        refine ⟨414233047523624659188953165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276155365015749772792635443 414233047523624659188953165)
        ·
          refine ⟨155337392821359247195857437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414233047523624659188953165 155337392821359247195857437)
          ·
            refine ⟨58251522308009717698446539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155337392821359247195857437 58251522308009717698446539)
            ·
              refine ⟨87377283462014576547669809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58251522308009717698446539 87377283462014576547669809)
              ·
                refine ⟨65532962596510932410752357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87377283462014576547669809 65532962596510932410752357)
                ·
                  refine ⟨12287430486845799827016067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65532962596510932410752357 12287430486845799827016067)
                  ·
                    refine ⟨18431145730268699740524101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12287430486845799827016067 18431145730268699740524101)
                    ·
                      refine ⟨3455839824425381201348269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18431145730268699740524101 3455839824425381201348269)
                      ·
                        rfl

theorem cell23_6730224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_6730224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730224 prefixEnd_6730224 := by exact prefixLift 6730224
  have htrace : WordTrace (prefixWord ++ tailWord_6730224) baseStart_6730224 baseEnd_6730224 := by
    simpa [prefixWord, tailWord_6730224, baseEnd_6730224] using wordTrace_append hprefix tailTrace_6730224
  have hstable : (prefixWord ++ tailWord_6730224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730224).length < 2 ^ (prefixWord ++ tailWord_6730224).sum := by decide
  have hdescent : baseEnd_6730224 < baseStart_6730224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730241 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_6730241 : Nat := 118140960795 + 6730241 * 2 ^ 59
def prefixEnd_6730241 : Nat := 4983230072969 + 3 ^ 40 * 6730241 * 2
def baseEnd_6730241 : Nat := 3455848553596507634835691

theorem tailTrace_6730241 : CollatzResearch.WordTrace tailWord_6730241 prefixEnd_6730241 3455848553596507634835691 := by
  unfold tailWord_6730241
  simp only [CollatzResearch.WordTrace]
  refine ⟨245472055610493765496822577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163648037073662510331215051 245472055610493765496822577)
  ·
    refine ⟨184104041707870324122616933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245472055610493765496822577 184104041707870324122616933)
    ·
      refine ⟨34519507820225685772990675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184104041707870324122616933 34519507820225685772990675)
      ·
        refine ⟨51779261730338528659486013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34519507820225685772990675 51779261730338528659486013)
        ·
          refine ⟨19417223148876948247307255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51779261730338528659486013 19417223148876948247307255)
          ·
            refine ⟨29125834723315422370960883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19417223148876948247307255 29125834723315422370960883)
            ·
              refine ⟨43688752084973133556441325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29125834723315422370960883 43688752084973133556441325)
              ·
                refine ⟨16383282031864925083665497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43688752084973133556441325 16383282031864925083665497)
                ·
                  refine ⟨12287461523898693812749123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16383282031864925083665497 12287461523898693812749123)
                  ·
                    refine ⟨18431192285848040719123685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12287461523898693812749123 18431192285848040719123685)
                    ·
                      refine ⟨3455848553596507634835691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18431192285848040719123685 3455848553596507634835691)
                      ·
                        rfl

theorem cell23_6730241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_6730241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730241 prefixEnd_6730241 := by exact prefixLift 6730241
  have htrace : WordTrace (prefixWord ++ tailWord_6730241) baseStart_6730241 baseEnd_6730241 := by
    simpa [prefixWord, tailWord_6730241, baseEnd_6730241] using wordTrace_append hprefix tailTrace_6730241
  have hstable : (prefixWord ++ tailWord_6730241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730241).length < 2 ^ (prefixWord ++ tailWord_6730241).sum := by decide
  have hdescent : baseEnd_6730241 < baseStart_6730241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730261 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_6730261 : Nat := 118140960795 + 6730261 * 2 ^ 59
def prefixEnd_6730261 : Nat := 4983230072969 + 3 ^ 40 * 6730261 * 2
def baseEnd_6730261 : Nat := 3455858823209597556585599

theorem tailTrace_6730261 : CollatzResearch.WordTrace tailWord_6730261 prefixEnd_6730261 3455858823209597556585599 := by
  unfold tailWord_6730261
  simp only [CollatzResearch.WordTrace]
  refine ⟨245472785070421308912550637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163648523380280872608367091 245472785070421308912550637)
  ·
    refine ⟨92052294401407990842206489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245472785070421308912550637 92052294401407990842206489)
    ·
      refine ⟨69039220801055993131654867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92052294401407990842206489 69039220801055993131654867)
      ·
        refine ⟨103558831201583989697482301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69039220801055993131654867 103558831201583989697482301)
        ·
          refine ⟨38834561700593996136555863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103558831201583989697482301 38834561700593996136555863)
          ·
            refine ⟨58251842550890994204833795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38834561700593996136555863 58251842550890994204833795)
            ·
              refine ⟨87377763826336491307250693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58251842550890994204833795 87377763826336491307250693)
              ·
                refine ⟨16383330717438092120109505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87377763826336491307250693 16383330717438092120109505)
                ·
                  refine ⟨12287498038078569090082129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16383330717438092120109505 12287498038078569090082129)
                  ·
                    refine ⟨9215623528558926817561597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12287498038078569090082129 9215623528558926817561597)
                    ·
                      refine ⟨3455858823209597556585599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9215623528558926817561597 3455858823209597556585599)
                      ·
                        rfl

theorem cell23_6730261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_6730261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730261 prefixEnd_6730261 := by exact prefixLift 6730261
  have htrace : WordTrace (prefixWord ++ tailWord_6730261) baseStart_6730261 baseEnd_6730261 := by
    simpa [prefixWord, tailWord_6730261, baseEnd_6730261] using wordTrace_append hprefix tailTrace_6730261
  have hstable : (prefixWord ++ tailWord_6730261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730261).length < 2 ^ (prefixWord ++ tailWord_6730261).sum := by decide
  have hdescent : baseEnd_6730261 < baseStart_6730261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730292 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6730292 : Nat := 118140960795 + 6730292 * 2 ^ 59
def prefixEnd_6730292 : Nat := 4983230072969 + 3 ^ 40 * 6730292 * 2
def baseEnd_6730292 : Nat := 3455874741109886935297957

theorem tailTrace_6730292 : CollatzResearch.WordTrace tailWord_6730292 prefixEnd_6730292 3455874741109886935297957 := by
  unfold tailWord_6730292
  simp only [CollatzResearch.WordTrace]
  refine ⟨122736957866654500603464565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163649277155539334137952753 122736957866654500603464565)
  ·
    refine ⟨11506589799998859431574803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122736957866654500603464565 11506589799998859431574803)
    ·
      refine ⟨17259884699998289147362205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11506589799998859431574803 17259884699998289147362205)
      ·
        refine ⟨6472456762499358430260827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17259884699998289147362205 6472456762499358430260827)
        ·
          refine ⟨9708685143749037645391241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472456762499358430260827 9708685143749037645391241)
          ·
            refine ⟨7281513857811778234043431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9708685143749037645391241 7281513857811778234043431)
            ·
              refine ⟨10922270786717667351065147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281513857811778234043431 10922270786717667351065147)
              ·
                refine ⟨16383406180076501026597721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922270786717667351065147 16383406180076501026597721)
                ·
                  refine ⟨12287554635057375769948291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16383406180076501026597721 12287554635057375769948291)
                  ·
                    refine ⟨18431331952586063654922437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12287554635057375769948291 18431331952586063654922437)
                    ·
                      refine ⟨3455874741109886935297957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18431331952586063654922437 3455874741109886935297957)
                      ·
                        rfl

theorem cell23_6730292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6730292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730292 prefixEnd_6730292 := by exact prefixLift 6730292
  have htrace : WordTrace (prefixWord ++ tailWord_6730292) baseStart_6730292 baseEnd_6730292 := by
    simpa [prefixWord, tailWord_6730292, baseEnd_6730292] using wordTrace_append hprefix tailTrace_6730292
  have hstable : (prefixWord ++ tailWord_6730292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730292).length < 2 ^ (prefixWord ++ tailWord_6730292).sum := by decide
  have hdescent : baseEnd_6730292 < baseStart_6730292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730318 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_6730318 : Nat := 118140960795 + 6730318 * 2 ^ 59
def prefixEnd_6730318 : Nat := 4983230072969 + 3 ^ 40 * 6730318 * 2
def baseEnd_6730318 : Nat := 3455888091606903833572837

theorem tailTrace_6730318 : CollatzResearch.WordTrace tailWord_6730318 prefixEnd_6730318 3455888091606903833572837 := by
  unfold tailWord_6730318
  simp only [CollatzResearch.WordTrace]
  refine ⟨30684358003901850955921951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163649909354143205098250405 30684358003901850955921951)
  ·
    refine ⟨46026537005852776433882927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30684358003901850955921951 46026537005852776433882927)
    ·
      refine ⟨69039805508779164650824391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46026537005852776433882927 69039805508779164650824391)
      ·
        refine ⟨103559708263168746976236587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69039805508779164650824391 103559708263168746976236587)
        ·
          refine ⟨155339562394753120464354881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103559708263168746976236587 155339562394753120464354881)
          ·
            refine ⟨116504671796064840348266161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155339562394753120464354881 116504671796064840348266161)
            ·
              refine ⟨87378503847048630261199621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116504671796064840348266161 87378503847048630261199621)
              ·
                refine ⟨16383469471321618173974929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87378503847048630261199621 16383469471321618173974929)
                ·
                  refine ⟨12287602103491213630481197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16383469471321618173974929 12287602103491213630481197)
                  ·
                    refine ⟨4607850788809205111430449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12287602103491213630481197 4607850788809205111430449)
                    ·
                      refine ⟨3455888091606903833572837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607850788809205111430449 3455888091606903833572837)
                      ·
                        rfl

theorem cell23_6730318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_6730318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730318 prefixEnd_6730318 := by exact prefixLift 6730318
  have htrace : WordTrace (prefixWord ++ tailWord_6730318) baseStart_6730318 baseEnd_6730318 := by
    simpa [prefixWord, tailWord_6730318, baseEnd_6730318] using wordTrace_append hprefix tailTrace_6730318
  have hstable : (prefixWord ++ tailWord_6730318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730318).length < 2 ^ (prefixWord ++ tailWord_6730318).sum := by decide
  have hdescent : baseEnd_6730318 < baseStart_6730318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730325 : List Nat := [1, 3, 2, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_6730325 : Nat := 118140960795 + 6730325 * 2 ^ 59
def prefixEnd_6730325 : Nat := 4983230072969 + 3 ^ 40 * 6730325 * 2
def baseEnd_6730325 : Nat := 3455891685971485306185305

theorem tailTrace_6730325 : CollatzResearch.WordTrace tailWord_6730325 prefixEnd_6730325 3455891685971485306185305 := by
  unfold tailWord_6730325
  simp only [CollatzResearch.WordTrace]
  refine ⟨245475119342189447842880429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163650079561459631895253619 245475119342189447842880429)
  ·
    refine ⟨92053169753321042941080161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245475119342189447842880429 92053169753321042941080161)
    ·
      refine ⟨69039877314990782205810121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92053169753321042941080161 69039877314990782205810121)
      ·
        refine ⟨51779907986243086654357591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69039877314990782205810121 51779907986243086654357591)
        ·
          refine ⟨77669861979364629981536387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51779907986243086654357591 77669861979364629981536387)
          ·
            refine ⟨116504792969046944972304581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77669861979364629981536387 116504792969046944972304581)
            ·
              refine ⟨21844648681696302182307109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116504792969046944972304581 21844648681696302182307109)
              ·
                refine ⟨4095871627818056659182583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21844648681696302182307109 4095871627818056659182583)
                ·
                  refine ⟨6143807441727084988773875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095871627818056659182583 6143807441727084988773875)
                  ·
                    refine ⟨9215711162590627483160813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6143807441727084988773875 9215711162590627483160813)
                    ·
                      refine ⟨3455891685971485306185305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9215711162590627483160813 3455891685971485306185305)
                      ·
                        rfl

theorem cell23_6730325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_6730325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730325 prefixEnd_6730325 := by exact prefixLift 6730325
  have htrace : WordTrace (prefixWord ++ tailWord_6730325) baseStart_6730325 baseEnd_6730325 := by
    simpa [prefixWord, tailWord_6730325, baseEnd_6730325] using wordTrace_append hprefix tailTrace_6730325
  have hstable : (prefixWord ++ tailWord_6730325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730325).length < 2 ^ (prefixWord ++ tailWord_6730325).sum := by decide
  have hdescent : baseEnd_6730325 < baseStart_6730325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730351 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 3]
def baseStart_6730351 : Nat := 118140960795 + 6730351 * 2 ^ 59
def prefixEnd_6730351 : Nat := 4983230072969 + 3 ^ 40 * 6730351 * 2
def baseEnd_6730351 : Nat := 3455905036468502204460185

theorem tailTrace_6730351 : CollatzResearch.WordTrace tailWord_6730351 prefixEnd_6730351 3455905036468502204460185 := by
  unfold tailWord_6730351
  simp only [CollatzResearch.WordTrace]
  refine ⟨245476067640095254283326907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163650711760063502855551271 245476067640095254283326907)
  ·
    refine ⟨368214101460142881424990361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245476067640095254283326907 368214101460142881424990361)
    ·
      refine ⟨276160576095107161068742771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368214101460142881424990361 276160576095107161068742771)
      ·
        refine ⟨414240864142660741603114157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276160576095107161068742771 414240864142660741603114157)
        ·
          refine ⟨155340324053497778101167809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414240864142660741603114157 155340324053497778101167809)
          ·
            refine ⟨116505243040123333575875857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155340324053497778101167809 116505243040123333575875857)
            ·
              refine ⟨87378932280092500181906893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116505243040123333575875857 87378932280092500181906893)
              ·
                refine ⟨32767099605034687568215085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87378932280092500181906893 32767099605034687568215085)
                ·
                  refine ⟨12287662351888007838080657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32767099605034687568215085 12287662351888007838080657)
                  ·
                    refine ⟨9215746763916005878560493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12287662351888007838080657 9215746763916005878560493)
                    ·
                      refine ⟨3455905036468502204460185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9215746763916005878560493 3455905036468502204460185)
                      ·
                        rfl

theorem cell23_6730351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_6730351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730351 prefixEnd_6730351 := by exact prefixLift 6730351
  have htrace : WordTrace (prefixWord ++ tailWord_6730351) baseStart_6730351 baseEnd_6730351 := by
    simpa [prefixWord, tailWord_6730351, baseEnd_6730351] using wordTrace_append hprefix tailTrace_6730351
  have hstable : (prefixWord ++ tailWord_6730351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730351).length < 2 ^ (prefixWord ++ tailWord_6730351).sum := by decide
  have hdescent : baseEnd_6730351 < baseStart_6730351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730368 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3]
def baseStart_6730368 : Nat := 118140960795 + 6730368 * 2 ^ 59
def prefixEnd_6730368 : Nat := 4983230072969 + 3 ^ 40 * 6730368 * 2
def baseEnd_6730368 : Nat := 3455913765639628637947607

theorem tailTrace_6730368 : CollatzResearch.WordTrace tailWord_6730368 prefixEnd_6730368 3455913765639628637947607 := by
  unfold tailWord_6730368
  simp only [CollatzResearch.WordTrace]
  refine ⟨122738343840516833093347879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163651125120689110791130505 122738343840516833093347879)
  ·
    refine ⟨184107515760775249640021819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122738343840516833093347879 184107515760775249640021819)
    ·
      refine ⟨276161273641162874460032729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184107515760775249640021819 276161273641162874460032729)
      ·
        refine ⟨207120955230872155845024547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276161273641162874460032729 207120955230872155845024547)
        ·
          refine ⟨310681432846308233767536821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207120955230872155845024547 310681432846308233767536821)
          ·
            refine ⟨29126384329341396915706577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310681432846308233767536821 29126384329341396915706577)
            ·
              refine ⟨21844788247006047686779933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29126384329341396915706577 21844788247006047686779933)
              ·
                refine ⟨8191795592627267882542475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21844788247006047686779933 8191795592627267882542475)
                ·
                  refine ⟨12287693388940901823813713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8191795592627267882542475 12287693388940901823813713)
                  ·
                    refine ⟨9215770041705676367860285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12287693388940901823813713 9215770041705676367860285)
                    ·
                      refine ⟨3455913765639628637947607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9215770041705676367860285 3455913765639628637947607)
                      ·
                        rfl

theorem cell23_6730368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_6730368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730368 prefixEnd_6730368 := by exact prefixLift 6730368
  have htrace : WordTrace (prefixWord ++ tailWord_6730368) baseStart_6730368 baseEnd_6730368 := by
    simpa [prefixWord, tailWord_6730368, baseEnd_6730368] using wordTrace_append hprefix tailTrace_6730368
  have hstable : (prefixWord ++ tailWord_6730368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730368).length < 2 ^ (prefixWord ++ tailWord_6730368).sum := by decide
  have hdescent : baseEnd_6730368 < baseStart_6730368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730388 : List Nat := [2, 4, 2, 2, 1, 2, 2, 8]
def baseStart_6730388 : Nat := 118140960795 + 6730388 * 2 ^ 59
def prefixEnd_6730388 : Nat := 4983230072969 + 3 ^ 40 * 6730388 * 2
def baseEnd_6730388 : Nat := 127997186490841428136945

theorem tailTrace_6730388 : CollatzResearch.WordTrace tailWord_6730388 prefixEnd_6730388 127997186490841428136945 := by
  unfold tailWord_6730388
  simp only [CollatzResearch.WordTrace]
  refine ⟨122738708570480604801211909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163651611427307473068282545 122738708570480604801211909)
  ·
    refine ⟨23013507856965113400227233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122738708570480604801211909 23013507856965113400227233)
    ·
      refine ⟨17260130892723835050170425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23013507856965113400227233 17260130892723835050170425)
      ·
        refine ⟨12945098169542876287627819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17260130892723835050170425 12945098169542876287627819)
        ·
          refine ⟨19417647254314314431441729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12945098169542876287627819 19417647254314314431441729)
          ·
            refine ⟨14563235440735735823581297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19417647254314314431441729 14563235440735735823581297)
            ·
              refine ⟨10922426580551801867685973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14563235440735735823581297 10922426580551801867685973)
              ·
                refine ⟨127997186490841428136945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10922426580551801867685973 127997186490841428136945)
                ·
                  rfl

theorem cell23_6730388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 8].length) (baseStart_6730388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730388 prefixEnd_6730388 := by exact prefixLift 6730388
  have htrace : WordTrace (prefixWord ++ tailWord_6730388) baseStart_6730388 baseEnd_6730388 := by
    simpa [prefixWord, tailWord_6730388, baseEnd_6730388] using wordTrace_append hprefix tailTrace_6730388
  have hstable : (prefixWord ++ tailWord_6730388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730388).length < 2 ^ (prefixWord ++ tailWord_6730388).sum := by decide
  have hdescent : baseEnd_6730388 < baseStart_6730388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730455 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 1, 4, 2]
def baseStart_6730455 : Nat := 118140960795 + 6730455 * 2 ^ 59
def prefixEnd_6730455 : Nat := 4983230072969 + 3 ^ 40 * 6730455 * 2
def baseEnd_6730455 : Nat := 3455958438456569797559707

theorem tailTrace_6730455 : CollatzResearch.WordTrace tailWord_6730455 prefixEnd_6730455 3455958438456569797559707 := by
  unfold tailWord_6730455
  simp only [CollatzResearch.WordTrace]
  refine ⟨245479860831718480045112819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163653240554478986696741879 245479860831718480045112819)
  ·
    refine ⟨368219791247577720067669229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245479860831718480045112819 368219791247577720067669229)
    ·
      refine ⟨138082421717841645025375961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368219791247577720067669229 138082421717841645025375961)
      ·
        refine ⟨103561816288381233769031971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138082421717841645025375961 103561816288381233769031971)
        ·
          refine ⟨155342724432571850653547957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103561816288381233769031971 155342724432571850653547957)
          ·
            refine ⟨14563380415553610998770121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155342724432571850653547957 14563380415553610998770121)
            ·
              refine ⟨10922535311665208249077591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14563380415553610998770121 10922535311665208249077591)
              ·
                refine ⟨16383802967497812373616387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922535311665208249077591 16383802967497812373616387)
                ·
                  refine ⟨24575704451246718560424581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16383802967497812373616387 24575704451246718560424581)
                  ·
                    refine ⟨4607944584608759730079609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24575704451246718560424581 4607944584608759730079609)
                    ·
                      refine ⟨3455958438456569797559707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4607944584608759730079609 3455958438456569797559707)
                      ·
                        rfl

theorem cell23_6730455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_6730455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730455 prefixEnd_6730455 := by exact prefixLift 6730455
  have htrace : WordTrace (prefixWord ++ tailWord_6730455) baseStart_6730455 baseEnd_6730455 := by
    simpa [prefixWord, tailWord_6730455, baseEnd_6730455] using wordTrace_append hprefix tailTrace_6730455
  have hstable : (prefixWord ++ tailWord_6730455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730455).length < 2 ^ (prefixWord ++ tailWord_6730455).sum := by decide
  have hdescent : baseEnd_6730455 < baseStart_6730455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730501 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_6730501 : Nat := 118140960795 + 6730501 * 2 ^ 59
def prefixEnd_6730501 : Nat := 4983230072969 + 3 ^ 40 * 6730501 * 2
def baseEnd_6730501 : Nat := 3455982058566676617584495

theorem tailTrace_6730501 : CollatzResearch.WordTrace tailWord_6730501 prefixEnd_6730501 3455982058566676617584495 := by
  unfold tailWord_6730501
  simp only [CollatzResearch.WordTrace]
  refine ⟨245481538589551829901287357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163654359059701219934191571 245481538589551829901287357)
  ·
    refine ⟨92055576971081936212982759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245481538589551829901287357 92055576971081936212982759)
    ·
      refine ⟨138083365456622904319474139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92055576971081936212982759 138083365456622904319474139)
      ·
        refine ⟨207125048184934356479211209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138083365456622904319474139 207125048184934356479211209)
        ·
          refine ⟨155343786138700767359408407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207125048184934356479211209 155343786138700767359408407)
          ·
            refine ⟨233015679208051151039112611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155343786138700767359408407 233015679208051151039112611)
            ·
              refine ⟨349523518812076726558668917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233015679208051151039112611 349523518812076726558668917)
              ·
                refine ⟨32767829888632193114875211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349523518812076726558668917 32767829888632193114875211)
                ·
                  refine ⟨49151744832948289672312817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32767829888632193114875211 49151744832948289672312817)
                  ·
                    refine ⟨36863808624711217254234613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49151744832948289672312817 36863808624711217254234613)
                    ·
                      refine ⟨3455982058566676617584495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36863808624711217254234613 3455982058566676617584495)
                      ·
                        rfl

theorem cell23_6730501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_6730501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730501 prefixEnd_6730501 := by exact prefixLift 6730501
  have htrace : WordTrace (prefixWord ++ tailWord_6730501) baseStart_6730501 baseEnd_6730501 := by
    simpa [prefixWord, tailWord_6730501, baseEnd_6730501] using wordTrace_append hprefix tailTrace_6730501
  have hstable : (prefixWord ++ tailWord_6730501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730501).length < 2 ^ (prefixWord ++ tailWord_6730501).sum := by decide
  have hdescent : baseEnd_6730501 < baseStart_6730501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730511 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_6730511 : Nat := 118140960795 + 6730511 * 2 ^ 59
def prefixEnd_6730511 : Nat := 4983230072969 + 3 ^ 40 * 6730511 * 2
def baseEnd_6730511 : Nat := 3455987193373221578459449

theorem tailTrace_6730511 : CollatzResearch.WordTrace tailWord_6730511 prefixEnd_6730511 3455987193373221578459449 := by
  unfold tailWord_6730511
  simp only [CollatzResearch.WordTrace]
  refine ⟨245481903319515601609151387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163654602213010401072767591 245481903319515601609151387)
  ·
    refine ⟨368222854979273402413727081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245481903319515601609151387 368222854979273402413727081)
    ·
      refine ⟨276167141234455051810295311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368222854979273402413727081 276167141234455051810295311)
      ·
        refine ⟨414250711851682577715442967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276167141234455051810295311 414250711851682577715442967)
        ·
          refine ⟨621376067777523866573164451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414250711851682577715442967 621376067777523866573164451)
          ·
            refine ⟨932064101666285799859746677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621376067777523866573164451 932064101666285799859746677)
            ·
              refine ⟨87381009531214293736851251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 932064101666285799859746677 87381009531214293736851251)
              ·
                refine ⟨131071514296821440605276877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87381009531214293736851251 131071514296821440605276877)
                ·
                  refine ⟨49151817861308040226978829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131071514296821440605276877 49151817861308040226978829)
                  ·
                    refine ⟨18431931697990515085117061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49151817861308040226978829 18431931697990515085117061)
                    ·
                      refine ⟨3455987193373221578459449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18431931697990515085117061 3455987193373221578459449)
                      ·
                        rfl

theorem cell23_6730511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_6730511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730511 prefixEnd_6730511 := by exact prefixLift 6730511
  have htrace : WordTrace (prefixWord ++ tailWord_6730511) baseStart_6730511 baseEnd_6730511 := by
    simpa [prefixWord, tailWord_6730511, baseEnd_6730511] using wordTrace_append hprefix tailTrace_6730511
  have hstable : (prefixWord ++ tailWord_6730511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730511).length < 2 ^ (prefixWord ++ tailWord_6730511).sum := by decide
  have hdescent : baseEnd_6730511 < baseStart_6730511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730528 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6730528 : Nat := 118140960795 + 6730528 * 2 ^ 59
def prefixEnd_6730528 : Nat := 4983230072969 + 3 ^ 40 * 6730528 * 2
def baseEnd_6730528 : Nat := 3455995922544348011946871

theorem tailTrace_6730528 : CollatzResearch.WordTrace tailWord_6730528 prefixEnd_6730528 3455995922544348011946871 := by
  unfold tailWord_6730528
  simp only [CollatzResearch.WordTrace]
  refine ⟨122741261680227006756260119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163655015573636009008346825 122741261680227006756260119)
  ·
    refine ⟨184111892520340510134390179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122741261680227006756260119 184111892520340510134390179)
    ·
      refine ⟨276167838780510765201585269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184111892520340510134390179 276167838780510765201585269)
      ·
        refine ⟨25890734885672884237648619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276167838780510765201585269 25890734885672884237648619)
        ·
          refine ⟨38836102328509326356472929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25890734885672884237648619 38836102328509326356472929)
          ·
            refine ⟨29127076746381994767354697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38836102328509326356472929 29127076746381994767354697)
            ·
              refine ⟨21845307559786496075516023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29127076746381994767354697 21845307559786496075516023)
              ·
                refine ⟨32767961339679744113274035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21845307559786496075516023 32767961339679744113274035)
                ·
                  refine ⟨49151942009519616169911053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32767961339679744113274035 49151942009519616169911053)
                  ·
                    refine ⟨18431978253569856063716645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49151942009519616169911053 18431978253569856063716645)
                    ·
                      refine ⟨3455995922544348011946871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18431978253569856063716645 3455995922544348011946871)
                      ·
                        rfl

theorem cell23_6730528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6730528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730528 prefixEnd_6730528 := by exact prefixLift 6730528
  have htrace : WordTrace (prefixWord ++ tailWord_6730528) baseStart_6730528 baseEnd_6730528 := by
    simpa [prefixWord, tailWord_6730528, baseEnd_6730528] using wordTrace_append hprefix tailTrace_6730528
  have hstable : (prefixWord ++ tailWord_6730528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730528).length < 2 ^ (prefixWord ++ tailWord_6730528).sum := by decide
  have hdescent : baseEnd_6730528 < baseStart_6730528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730531 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5]
def baseStart_6730531 : Nat := 118140960795 + 6730531 * 2 ^ 59
def prefixEnd_6730531 : Nat := 4983230072969 + 3 ^ 40 * 6730531 * 2
def baseEnd_6730531 : Nat := 3455997462986311500209357

theorem tailTrace_6730531 : CollatzResearch.WordTrace tailWord_6730531 prefixEnd_6730531 3455997462986311500209357 := by
  unfold tailWord_6730531
  simp only [CollatzResearch.WordTrace]
  refine ⟨245482632779443145024879447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163655088519628763349919631 245482632779443145024879447)
  ·
    refine ⟨368223949169164717537319171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245482632779443145024879447 368223949169164717537319171)
    ·
      refine ⟨552335923753747076305978757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368223949169164717537319171 552335923753747076305978757)
      ·
        refine ⟨103562985703827576807371017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 552335923753747076305978757 103562985703827576807371017)
        ·
          refine ⟨77672239277870682605528263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103562985703827576807371017 77672239277870682605528263)
          ·
            refine ⟨116508358916806023908292395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77672239277870682605528263 116508358916806023908292395)
            ·
              refine ⟨174762538375209035862438593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116508358916806023908292395 174762538375209035862438593)
              ·
                refine ⟨131071903781406776896828945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174762538375209035862438593 131071903781406776896828945)
                ·
                  refine ⟨98303927836055082672621709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131071903781406776896828945 98303927836055082672621709)
                  ·
                    refine ⟨36863972938520656002233141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98303927836055082672621709 36863972938520656002233141)
                    ·
                      refine ⟨3455997462986311500209357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36863972938520656002233141 3455997462986311500209357)
                      ·
                        rfl

theorem cell23_6730531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_6730531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730531 prefixEnd_6730531 := by exact prefixLift 6730531
  have htrace : WordTrace (prefixWord ++ tailWord_6730531) baseStart_6730531 baseEnd_6730531 := by
    simpa [prefixWord, tailWord_6730531, baseEnd_6730531] using wordTrace_append hprefix tailTrace_6730531
  have hstable : (prefixWord ++ tailWord_6730531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730531).length < 2 ^ (prefixWord ++ tailWord_6730531).sum := by decide
  have hdescent : baseEnd_6730531 < baseStart_6730531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730551 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 8]
def baseStart_6730551 : Nat := 118140960795 + 6730551 * 2 ^ 59
def prefixEnd_6730551 : Nat := 4983230072969 + 3 ^ 40 * 6730551 * 2
def baseEnd_6730551 : Nat := 384000859177711269106585

theorem tailTrace_6730551 : CollatzResearch.WordTrace tailWord_6730551 prefixEnd_6730551 384000859177711269106585 := by
  unfold tailWord_6730551
  simp only [CollatzResearch.WordTrace]
  refine ⟨245483362239370688440607507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163655574826247125627071671 245483362239370688440607507)
  ·
    refine ⟨368225043359056032660911261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245483362239370688440607507 368225043359056032660911261)
    ·
      refine ⟨138084391259646012247841723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368225043359056032660911261 138084391259646012247841723)
      ·
        refine ⟨207126586889469018371762585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138084391259646012247841723 207126586889469018371762585)
        ·
          refine ⟨155344940167101763778821939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207126586889469018371762585 155344940167101763778821939)
          ·
            refine ⟨233017410250652645668232909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155344940167101763778821939 233017410250652645668232909)
            ·
              refine ⟨87381528843994742125587341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233017410250652645668232909 87381528843994742125587341)
              ·
                refine ⟨32768073316498028297095253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87381528843994742125587341 32768073316498028297095253)
                ·
                  refine ⟨384000859177711269106585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32768073316498028297095253 384000859177711269106585)
                  ·
                    rfl

theorem cell23_6730551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 8].length) (baseStart_6730551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730551 prefixEnd_6730551 := by exact prefixLift 6730551
  have htrace : WordTrace (prefixWord ++ tailWord_6730551) baseStart_6730551 baseEnd_6730551 := by
    simpa [prefixWord, tailWord_6730551, baseEnd_6730551] using wordTrace_append hprefix tailTrace_6730551
  have hstable : (prefixWord ++ tailWord_6730551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730551).length < 2 ^ (prefixWord ++ tailWord_6730551).sum := by decide
  have hdescent : baseEnd_6730551 < baseStart_6730551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730568 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 6]
def baseStart_6730568 : Nat := 118140960795 + 6730568 * 2 ^ 59
def prefixEnd_6730568 : Nat := 4983230072969 + 3 ^ 40 * 6730568 * 2
def baseEnd_6730568 : Nat := 384001829085614206160743

theorem tailTrace_6730568 : CollatzResearch.WordTrace tailWord_6730568 prefixEnd_6730568 384001829085614206160743 := by
  unfold tailWord_6730568
  simp only [CollatzResearch.WordTrace]
  refine ⟨122741991140154550171988179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163655988186872733562650905 122741991140154550171988179)
  ·
    refine ⟨184112986710231825257982269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122741991140154550171988179 184112986710231825257982269)
    ·
      refine ⟨69042370016336934471743351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184112986710231825257982269 69042370016336934471743351)
      ·
        refine ⟨103563555024505401707615027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69042370016336934471743351 103563555024505401707615027)
        ·
          refine ⟨155345332536758102561422541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103563555024505401707615027 155345332536758102561422541)
          ·
            refine ⟨58254499701284288460533453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155345332536758102561422541 58254499701284288460533453)
            ·
              refine ⟨21845437387981608172700045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58254499701284288460533453 21845437387981608172700045)
              ·
                refine ⟨8192039020493103064762517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21845437387981608172700045 8192039020493103064762517)
                ·
                  refine ⟨384001829085614206160743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8192039020493103064762517 384001829085614206160743)
                  ·
                    rfl

theorem cell23_6730568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 6].length) (baseStart_6730568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730568 prefixEnd_6730568 := by exact prefixLift 6730568
  have htrace : WordTrace (prefixWord ++ tailWord_6730568) baseStart_6730568 baseEnd_6730568 := by
    simpa [prefixWord, tailWord_6730568, baseEnd_6730568] using wordTrace_append hprefix tailTrace_6730568
  have hstable : (prefixWord ++ tailWord_6730568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730568).length < 2 ^ (prefixWord ++ tailWord_6730568).sum := by decide
  have hdescent : baseEnd_6730568 < baseStart_6730568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730605 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_6730605 : Nat := 118140960795 + 6730605 * 2 ^ 59
def prefixEnd_6730605 : Nat := 4983230072969 + 3 ^ 40 * 6730605 * 2
def baseEnd_6730605 : Nat := 3456035460554744210684017

theorem tailTrace_6730605 : CollatzResearch.WordTrace tailWord_6730605 prefixEnd_6730605 3456035460554744210684017 := by
  unfold tailWord_6730605
  simp only [CollatzResearch.WordTrace]
  refine ⟨245485331781175055663073269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163656887854116703775382179 245485331781175055663073269)
  ·
    refine ⟨23014249854485161468413119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245485331781175055663073269 23014249854485161468413119)
    ·
      refine ⟨34521374781727742202619679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23014249854485161468413119 34521374781727742202619679)
      ·
        refine ⟨51782062172591613303929519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34521374781727742202619679 51782062172591613303929519)
        ·
          refine ⟨77673093258887419955894279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51782062172591613303929519 77673093258887419955894279)
          ·
            refine ⟨116509639888331129933841419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77673093258887419955894279 116509639888331129933841419)
            ·
              refine ⟨174764459832496694900762129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116509639888331129933841419 174764459832496694900762129)
              ·
                refine ⟨131073344874372521175571597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174764459832496694900762129 131073344874372521175571597)
                ·
                  refine ⟨49152504327889695440839349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131073344874372521175571597 49152504327889695440839349)
                  ·
                    refine ⟨4608047280739658947578689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49152504327889695440839349 4608047280739658947578689)
                    ·
                      refine ⟨3456035460554744210684017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608047280739658947578689 3456035460554744210684017)
                      ·
                        rfl

theorem cell23_6730605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_6730605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730605 prefixEnd_6730605 := by exact prefixLift 6730605
  have htrace : WordTrace (prefixWord ++ tailWord_6730605) baseStart_6730605 baseEnd_6730605 := by
    simpa [prefixWord, tailWord_6730605, baseEnd_6730605] using wordTrace_append hprefix tailTrace_6730605
  have hstable : (prefixWord ++ tailWord_6730605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730605).length < 2 ^ (prefixWord ++ tailWord_6730605).sum := by decide
  have hdescent : baseEnd_6730605 < baseStart_6730605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730692 : List Nat := [2, 3, 3, 3, 1, 1, 1, 9]
def baseStart_6730692 : Nat := 118140960795 + 6730692 * 2 ^ 59
def prefixEnd_6730692 : Nat := 4983230072969 + 3 ^ 40 * 6730692 * 2
def baseEnd_6730692 : Nat := 128002967902655013714671

theorem tailTrace_6730692 : CollatzResearch.WordTrace tailWord_6730692 prefixEnd_6730692 128002967902655013714671 := by
  unfold tailWord_6730692
  simp only [CollatzResearch.WordTrace]
  refine ⟨122744252465929934760745165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163659003287906579680993553 122744252465929934760745165)
  ·
    refine ⟨46029094674723725535279437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122744252465929934760745165 46029094674723725535279437)
    ·
      refine ⟨17260910503021397075729789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46029094674723725535279437 17260910503021397075729789)
      ·
        refine ⟨6472841438633023903398671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17260910503021397075729789 6472841438633023903398671)
        ·
          refine ⟨9709262157949535855098007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472841438633023903398671 9709262157949535855098007)
          ·
            refine ⟨14563893236924303782647011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9709262157949535855098007 14563893236924303782647011)
            ·
              refine ⟨21845839855386455673970517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14563893236924303782647011 21845839855386455673970517)
              ·
                refine ⟨128002967902655013714671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21845839855386455673970517 128002967902655013714671)
                ·
                  rfl

theorem cell23_6730692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 9].length) (baseStart_6730692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730692 prefixEnd_6730692 := by exact prefixLift 6730692
  have htrace : WordTrace (prefixWord ++ tailWord_6730692) baseStart_6730692 baseEnd_6730692 := by
    simpa [prefixWord, tailWord_6730692, baseEnd_6730692] using wordTrace_append hprefix tailTrace_6730692
  have hstable : (prefixWord ++ tailWord_6730692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730692).length < 2 ^ (prefixWord ++ tailWord_6730692).sum := by decide
  have hdescent : baseEnd_6730692 < baseStart_6730692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730702 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_6730702 : Nat := 118140960795 + 6730702 * 2 ^ 59
def prefixEnd_6730702 : Nat := 4983230072969 + 3 ^ 40 * 6730702 * 2
def baseEnd_6730702 : Nat := 3456085268178230331171071

theorem tailTrace_6730702 : CollatzResearch.WordTrace tailWord_6730702 prefixEnd_6730702 3456085268178230331171071 := by
  unfold tailWord_6730702
  simp only [CollatzResearch.WordTrace]
  refine ⟨30686108707727955153669295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163659246441215760819569573 30686108707727955153669295)
  ·
    refine ⟨46029163061591932730503943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30686108707727955153669295 46029163061591932730503943)
    ·
      refine ⟨69043744592387899095755915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46029163061591932730503943 69043744592387899095755915)
      ·
        refine ⟨103565616888581848643633873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69043744592387899095755915 103565616888581848643633873)
        ·
          refine ⟨77674212666436386482725405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103565616888581848643633873 77674212666436386482725405)
          ·
            refine ⟨29127829749913644931022027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77674212666436386482725405 29127829749913644931022027)
            ·
              refine ⟨43691744624870467396533041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29127829749913644931022027 43691744624870467396533041)
              ·
                refine ⟨32768808468652850547399781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43691744624870467396533041 32768808468652850547399781)
                ·
                  refine ⟨6144151587872409477637459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32768808468652850547399781 6144151587872409477637459)
                  ·
                    refine ⟨9216227381808614216456189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6144151587872409477637459 9216227381808614216456189)
                    ·
                      refine ⟨3456085268178230331171071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9216227381808614216456189 3456085268178230331171071)
                      ·
                        rfl

theorem cell23_6730702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_6730702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730702 prefixEnd_6730702 := by exact prefixLift 6730702
  have htrace : WordTrace (prefixWord ++ tailWord_6730702) baseStart_6730702 baseEnd_6730702 := by
    simpa [prefixWord, tailWord_6730702, baseEnd_6730702] using wordTrace_append hprefix tailTrace_6730702
  have hstable : (prefixWord ++ tailWord_6730702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730702).length < 2 ^ (prefixWord ++ tailWord_6730702).sum := by decide
  have hdescent : baseEnd_6730702 < baseStart_6730702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730768 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_6730768 : Nat := 118140960795 + 6730768 * 2 ^ 59
def prefixEnd_6730768 : Nat := 4983230072969 + 3 ^ 40 * 6730768 * 2
def baseEnd_6730768 : Nat := 3456119157901427072945767

theorem tailTrace_6730768 : CollatzResearch.WordTrace tailWord_6730768 prefixEnd_6730768 3456119157901427072945767 := by
  unfold tailWord_6730768
  simp only [CollatzResearch.WordTrace]
  refine ⟨122745638439792267250628479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163660851253056356334171305 122745638439792267250628479)
  ·
    refine ⟨184118457659688400875942719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122745638439792267250628479 184118457659688400875942719)
    ·
      refine ⟨276177686489532601313914079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184118457659688400875942719 276177686489532601313914079)
      ·
        refine ⟨414266529734298901970871119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276177686489532601313914079 414266529734298901970871119)
        ·
          refine ⟨621399794601448352956306679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414266529734298901970871119 621399794601448352956306679)
          ·
            refine ⟨932099691902172529434460019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621399794601448352956306679 932099691902172529434460019)
            ·
              refine ⟨1398149537853258794151690029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932099691902172529434460019 1398149537853258794151690029)
              ·
                refine ⟨524306076694972047806883761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1398149537853258794151690029 524306076694972047806883761)
                ·
                  refine ⟨393229557521229035855162821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524306076694972047806883761 393229557521229035855162821)
                  ·
                    refine ⟨73730542035230444222843029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 393229557521229035855162821 73730542035230444222843029)
                    ·
                      refine ⟨3456119157901427072945767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73730542035230444222843029 3456119157901427072945767)
                      ·
                        rfl

theorem cell23_6730768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_6730768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730768 prefixEnd_6730768 := by exact prefixLift 6730768
  have htrace : WordTrace (prefixWord ++ tailWord_6730768) baseStart_6730768 baseEnd_6730768 := by
    simpa [prefixWord, tailWord_6730768, baseEnd_6730768] using wordTrace_append hprefix tailTrace_6730768
  have hstable : (prefixWord ++ tailWord_6730768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730768).length < 2 ^ (prefixWord ++ tailWord_6730768).sum := by decide
  have hdescent : baseEnd_6730768 < baseStart_6730768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730770 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6730770 : Nat := 118140960795 + 6730770 * 2 ^ 59
def prefixEnd_6730770 : Nat := 4983230072969 + 3 ^ 40 * 6730770 * 2
def baseEnd_6730770 : Nat := 3456120184862736065120759

theorem tailTrace_6730770 : CollatzResearch.WordTrace tailWord_6730770 prefixEnd_6730770 3456120184862736065120759 := by
  unfold tailWord_6730770
  simp only [CollatzResearch.WordTrace]
  refine ⟨61372837456394322210707441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163660899883718192561886509 61372837456394322210707441)
  ·
    refine ⟨46029628092295741658030581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61372837456394322210707441 46029628092295741658030581)
    ·
      refine ⟨4315277633652725780440367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46029628092295741658030581 4315277633652725780440367)
      ·
        refine ⟨6472916450479088670660551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315277633652725780440367 6472916450479088670660551)
        ·
          refine ⟨9709374675718633005990827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472916450479088670660551 9709374675718633005990827)
          ·
            refine ⟨14564062013577949508986241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9709374675718633005990827 14564062013577949508986241)
            ·
              refine ⟨10923046510183462131739681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14564062013577949508986241 10923046510183462131739681)
              ·
                refine ⟨8192284882637596598804761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10923046510183462131739681 8192284882637596598804761)
                ·
                  refine ⟨6144213661978197449103571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8192284882637596598804761 6144213661978197449103571)
                  ·
                    refine ⟨9216320492967296173655357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6144213661978197449103571 9216320492967296173655357)
                    ·
                      refine ⟨3456120184862736065120759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9216320492967296173655357 3456120184862736065120759)
                      ·
                        rfl

theorem cell23_6730770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6730770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730770 prefixEnd_6730770 := by exact prefixLift 6730770
  have htrace : WordTrace (prefixWord ++ tailWord_6730770) baseStart_6730770 baseEnd_6730770 := by
    simpa [prefixWord, tailWord_6730770, baseEnd_6730770] using wordTrace_append hprefix tailTrace_6730770
  have hstable : (prefixWord ++ tailWord_6730770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730770).length < 2 ^ (prefixWord ++ tailWord_6730770).sum := by decide
  have hdescent : baseEnd_6730770 < baseStart_6730770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730776 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 2, 2, 2]
def baseStart_6730776 : Nat := 118140960795 + 6730776 * 2 ^ 59
def prefixEnd_6730776 : Nat := 4983230072969 + 3 ^ 40 * 6730776 * 2
def baseEnd_6730776 : Nat := 3456123265746663041645731

theorem tailTrace_6730776 : CollatzResearch.WordTrace tailWord_6730776 prefixEnd_6730776 3456123265746663041645731 := by
  unfold tailWord_6730776
  simp only [CollatzResearch.WordTrace]
  refine ⟨122745784331777775933774091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163661045775703701245032121 122745784331777775933774091)
  ·
    refine ⟨184118676497666663900661137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122745784331777775933774091 184118676497666663900661137)
    ·
      refine ⟨138089007373249997925495853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184118676497666663900661137 138089007373249997925495853)
      ·
        refine ⟨51783377764968749222060945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138089007373249997925495853 51783377764968749222060945)
        ·
          refine ⟨38837533323726561916545709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51783377764968749222060945 38837533323726561916545709)
          ·
            refine ⟨14564074996397460718704641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38837533323726561916545709 14564074996397460718704641)
            ·
              refine ⟨10923056247298095539028481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14564074996397460718704641 10923056247298095539028481)
              ·
                refine ⟨8192292185473571654271361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10923056247298095539028481 8192292185473571654271361)
                ·
                  refine ⟨6144219139105178740703521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8192292185473571654271361 6144219139105178740703521)
                  ·
                    refine ⟨4608164354328884055527641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6144219139105178740703521 4608164354328884055527641)
                    ·
                      refine ⟨3456123265746663041645731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608164354328884055527641 3456123265746663041645731)
                      ·
                        rfl

theorem cell23_6730776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_6730776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730776 prefixEnd_6730776 := by exact prefixLift 6730776
  have htrace : WordTrace (prefixWord ++ tailWord_6730776) baseStart_6730776 baseEnd_6730776 := by
    simpa [prefixWord, tailWord_6730776, baseEnd_6730776] using wordTrace_append hprefix tailTrace_6730776
  have hstable : (prefixWord ++ tailWord_6730776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730776).length < 2 ^ (prefixWord ++ tailWord_6730776).sum := by decide
  have hdescent : baseEnd_6730776 < baseStart_6730776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730802 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_6730802 : Nat := 118140960795 + 6730802 * 2 ^ 59
def prefixEnd_6730802 : Nat := 4983230072969 + 3 ^ 40 * 6730802 * 2
def baseEnd_6730802 : Nat := 3456136616243679939920611

theorem tailTrace_6730802 : CollatzResearch.WordTrace tailWord_6730802 prefixEnd_6730802 3456136616243679939920611 := by
  unfold tailWord_6730802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61373129240365339576998665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163661677974307572205329773 61373129240365339576998665)
  ·
    refine ⟨46029846930274004682748999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61373129240365339576998665 46029846930274004682748999)
    ·
      refine ⟨69044770395411007024123499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46029846930274004682748999 69044770395411007024123499)
      ·
        refine ⟨103567155593116510536185249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69044770395411007024123499 103567155593116510536185249)
        ·
          refine ⟨77675366694837382902138937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103567155593116510536185249 77675366694837382902138937)
          ·
            refine ⟨58256525021128037176604203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77675366694837382902138937 58256525021128037176604203)
            ·
              refine ⟨87384787531692055764906305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58256525021128037176604203 87384787531692055764906305)
              ·
                refine ⟨65538590648769041823679729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87384787531692055764906305 65538590648769041823679729)
                ·
                  refine ⟨49153942986576781367759797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65538590648769041823679729 49153942986576781367759797)
                  ·
                    refine ⟨4608182154991573253227481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49153942986576781367759797 4608182154991573253227481)
                    ·
                      refine ⟨3456136616243679939920611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608182154991573253227481 3456136616243679939920611)
                      ·
                        rfl

theorem cell23_6730802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_6730802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730802 prefixEnd_6730802 := by exact prefixLift 6730802
  have htrace : WordTrace (prefixWord ++ tailWord_6730802) baseStart_6730802 baseEnd_6730802 := by
    simpa [prefixWord, tailWord_6730802, baseEnd_6730802] using wordTrace_append hprefix tailTrace_6730802
  have hstable : (prefixWord ++ tailWord_6730802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730802).length < 2 ^ (prefixWord ++ tailWord_6730802).sum := by decide
  have hdescent : baseEnd_6730802 < baseStart_6730802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730812 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_6730812 : Nat := 118140960795 + 6730812 * 2 ^ 59
def prefixEnd_6730812 : Nat := 4983230072969 + 3 ^ 40 * 6730812 * 2
def baseEnd_6730812 : Nat := 1152047250350074966931855

theorem tailTrace_6730812 : CollatzResearch.WordTrace tailWord_6730812 prefixEnd_6730812 1152047250350074966931855 := by
  unfold tailWord_6730812
  simp only [CollatzResearch.WordTrace]
  refine ⟨122746440845712565007929345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163661921127616753343905793 122746440845712565007929345)
  ·
    refine ⟨92059830634284423755947009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122746440845712565007929345 92059830634284423755947009)
    ·
      refine ⟨69044872975713317816960257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92059830634284423755947009 69044872975713317816960257)
      ·
        refine ⟨51783654731784988362720193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69044872975713317816960257 51783654731784988362720193)
        ·
          refine ⟨38837741048838741272040145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51783654731784988362720193 38837741048838741272040145)
          ·
            refine ⟨29128305786629055954030109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38837741048838741272040145 29128305786629055954030109)
            ·
              refine ⟨10923114669985895982761291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29128305786629055954030109 10923114669985895982761291)
              ·
                refine ⟨16384672004978843974141937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10923114669985895982761291 16384672004978843974141937)
                ·
                  refine ⟨12288504003734132980606453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16384672004978843974141937 12288504003734132980606453)
                  ·
                    refine ⟨1152047250350074966931855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12288504003734132980606453 1152047250350074966931855)
                    ·
                      rfl

theorem cell23_6730812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_6730812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730812 prefixEnd_6730812 := by exact prefixLift 6730812
  have htrace : WordTrace (prefixWord ++ tailWord_6730812) baseStart_6730812 baseEnd_6730812 := by
    simpa [prefixWord, tailWord_6730812, baseEnd_6730812] using wordTrace_append hprefix tailTrace_6730812
  have hstable : (prefixWord ++ tailWord_6730812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730812).length < 2 ^ (prefixWord ++ tailWord_6730812).sum := by decide
  have hdescent : baseEnd_6730812 < baseStart_6730812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730835 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 3]
def baseStart_6730835 : Nat := 118140960795 + 6730835 * 2 ^ 59
def prefixEnd_6730835 : Nat := 4983230072969 + 3 ^ 40 * 6730835 * 2
def baseEnd_6730835 : Nat := 3456153561105278310807959

theorem tailTrace_6730835 : CollatzResearch.WordTrace tailWord_6730835 prefixEnd_6730835 3456153561105278310807959 := by
  unfold tailWord_6730835
  simp only [CollatzResearch.WordTrace]
  refine ⟨245493720570341804943945959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163662480380227869962630639 245493720570341804943945959)
  ·
    refine ⟨368240580855512707415918939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245493720570341804943945959 368240580855512707415918939)
    ·
      refine ⟨552360871283269061123878409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368240580855512707415918939 552360871283269061123878409)
      ·
        refine ⟨414270653462451795842908807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552360871283269061123878409 414270653462451795842908807)
        ·
          refine ⟨621405980193677693764363211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414270653462451795842908807 621405980193677693764363211)
          ·
            refine ⟨932108970290516540646544817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621405980193677693764363211 932108970290516540646544817)
            ·
              refine ⟨699081727717887405484908613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932108970290516540646544817 699081727717887405484908613)
              ·
                refine ⟨131077823947103888528420365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 699081727717887405484908613 131077823947103888528420365)
                ·
                  refine ⟨49154183980163958198157637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131077823947103888528420365 49154183980163958198157637)
                  ·
                    refine ⟨9216409496280742162154557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49154183980163958198157637 9216409496280742162154557)
                    ·
                      refine ⟨3456153561105278310807959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9216409496280742162154557 3456153561105278310807959)
                      ·
                        rfl

theorem cell23_6730835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_6730835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730835 prefixEnd_6730835 := by exact prefixLift 6730835
  have htrace : WordTrace (prefixWord ++ tailWord_6730835) baseStart_6730835 baseEnd_6730835 := by
    simpa [prefixWord, tailWord_6730835, baseEnd_6730835] using wordTrace_append hprefix tailTrace_6730835
  have hstable : (prefixWord ++ tailWord_6730835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730835).length < 2 ^ (prefixWord ++ tailWord_6730835).sum := by decide
  have hdescent : baseEnd_6730835 < baseStart_6730835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730899 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 3]
def baseStart_6730899 : Nat := 118140960795 + 6730899 * 2 ^ 59
def prefixEnd_6730899 : Nat := 4983230072969 + 3 ^ 40 * 6730899 * 2
def baseEnd_6730899 : Nat := 3456186423867166060407665

theorem tailTrace_6730899 : CollatzResearch.WordTrace tailWord_6730899 prefixEnd_6730899 3456186423867166060407665 := by
  unfold tailWord_6730899
  simp only [CollatzResearch.WordTrace]
  refine ⟨245496054842109943874275751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163664036561406629249517167 245496054842109943874275751)
  ·
    refine ⟨368244082263164915811413627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245496054842109943874275751 368244082263164915811413627)
    ·
      refine ⟨552366123394747373717120441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368244082263164915811413627 552366123394747373717120441)
      ·
        refine ⟨414274592546060530287840331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552366123394747373717120441 414274592546060530287840331)
        ·
          refine ⟨621411888819090795431760497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414274592546060530287840331 621411888819090795431760497)
          ·
            refine ⟨466058916614318096573820373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621411888819090795431760497 466058916614318096573820373)
            ·
              refine ⟨10923255858148080388448915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 466058916614318096573820373 10923255858148080388448915)
              ·
                refine ⟨16384883787222120582673373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10923255858148080388448915 16384883787222120582673373)
                ·
                  refine ⟨6144331420208295218502515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16384883787222120582673373 6144331420208295218502515)
                  ·
                    refine ⟨9216497130312442827753773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6144331420208295218502515 9216497130312442827753773)
                    ·
                      refine ⟨3456186423867166060407665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9216497130312442827753773 3456186423867166060407665)
                      ·
                        rfl

theorem cell23_6730899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3, 1, 3].length) (baseStart_6730899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730899 prefixEnd_6730899 := by exact prefixLift 6730899
  have htrace : WordTrace (prefixWord ++ tailWord_6730899) baseStart_6730899 baseEnd_6730899 := by
    simpa [prefixWord, tailWord_6730899, baseEnd_6730899] using wordTrace_append hprefix tailTrace_6730899
  have hstable : (prefixWord ++ tailWord_6730899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730899).length < 2 ^ (prefixWord ++ tailWord_6730899).sum := by decide
  have hdescent : baseEnd_6730899 < baseStart_6730899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730905 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_6730905 : Nat := 118140960795 + 6730905 * 2 ^ 59
def prefixEnd_6730905 : Nat := 4983230072969 + 3 ^ 40 * 6730905 * 2
def baseEnd_6730905 : Nat := 3456189504751093036932637

theorem tailTrace_6730905 : CollatzResearch.WordTrace tailWord_6730905 prefixEnd_6730905 3456189504751093036932637 := by
  unfold tailWord_6730905
  simp only [CollatzResearch.WordTrace]
  refine ⟨245496273680088206898994169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163664182453392137932662779 245496273680088206898994169)
  ·
    refine ⟨184122205260066155174245627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245496273680088206898994169 184122205260066155174245627)
    ·
      refine ⟨276183307890099232761368441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184122205260066155174245627 276183307890099232761368441)
      ·
        refine ⟨207137480917574424571026331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276183307890099232761368441 207137480917574424571026331)
        ·
          refine ⟨310706221376361636856539497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207137480917574424571026331 310706221376361636856539497)
          ·
            refine ⟨233029666032271227642404623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310706221376361636856539497 233029666032271227642404623)
            ·
              refine ⟨349544499048406841463606935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233029666032271227642404623 349544499048406841463606935)
              ·
                refine ⟨524316748572610262195410403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349544499048406841463606935 524316748572610262195410403)
                ·
                  refine ⟨786475122858915393293115605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524316748572610262195410403 786475122858915393293115605)
                  ·
                    refine ⟨18433010692005829530307397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 786475122858915393293115605 18433010692005829530307397)
                    ·
                      refine ⟨3456189504751093036932637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18433010692005829530307397 3456189504751093036932637)
                      ·
                        rfl

theorem cell23_6730905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_6730905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730905 prefixEnd_6730905 := by exact prefixLift 6730905
  have htrace : WordTrace (prefixWord ++ tailWord_6730905) baseStart_6730905 baseEnd_6730905 := by
    simpa [prefixWord, tailWord_6730905, baseEnd_6730905] using wordTrace_append hprefix tailTrace_6730905
  have hstable : (prefixWord ++ tailWord_6730905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730905).length < 2 ^ (prefixWord ++ tailWord_6730905).sum := by decide
  have hdescent : baseEnd_6730905 < baseStart_6730905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730906 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 6]
def baseStart_6730906 : Nat := 118140960795 + 6730906 * 2 ^ 59
def prefixEnd_6730906 : Nat := 4983230072969 + 3 ^ 40 * 6730906 * 2
def baseEnd_6730906 : Nat := 384021113136860837002237

theorem tailTrace_6730906 : CollatzResearch.WordTrace tailWord_6730906 prefixEnd_6730906 384021113136860837002237 := by
  unfold tailWord_6730906
  simp only [CollatzResearch.WordTrace]
  refine ⟨61374077538271146017445143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163664206768723056046520381 61374077538271146017445143)
  ·
    refine ⟨92061116307406719026167715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61374077538271146017445143 92061116307406719026167715)
    ·
      refine ⟨138091674461110078539251573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92061116307406719026167715 138091674461110078539251573)
      ·
        refine ⟨12946094480729069863054835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138091674461110078539251573 12946094480729069863054835)
        ·
          refine ⟨19419141721093604794582253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12946094480729069863054835 19419141721093604794582253)
          ·
            refine ⟨7282178145410101797968345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19419141721093604794582253 7282178145410101797968345)
            ·
              refine ⟨5461633609057576348476259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282178145410101797968345 5461633609057576348476259)
              ·
                refine ⟨8192450413586364522714389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461633609057576348476259 8192450413586364522714389)
                ·
                  refine ⟨384021113136860837002237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8192450413586364522714389 384021113136860837002237)
                  ·
                    rfl

theorem cell23_6730906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_6730906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730906 prefixEnd_6730906 := by exact prefixLift 6730906
  have htrace : WordTrace (prefixWord ++ tailWord_6730906) baseStart_6730906 baseEnd_6730906 := by
    simpa [prefixWord, tailWord_6730906, baseEnd_6730906] using wordTrace_append hprefix tailTrace_6730906
  have hstable : (prefixWord ++ tailWord_6730906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730906).length < 2 ^ (prefixWord ++ tailWord_6730906).sum := by decide
  have hdescent : baseEnd_6730906 < baseStart_6730906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730909 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_6730909 : Nat := 118140960795 + 6730909 * 2 ^ 59
def prefixEnd_6730909 : Nat := 4983230072969 + 3 ^ 40 * 6730909 * 2
def baseEnd_6730909 : Nat := 3456191558673711021282619

theorem tailTrace_6730909 : CollatzResearch.WordTrace tailWord_6730909 prefixEnd_6730909 3456191558673711021282619 := by
  unfold tailWord_6730909
  simp only [CollatzResearch.WordTrace]
  refine ⟨245496419572073715582139781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163664279714715810388093187 245496419572073715582139781)
  ·
    refine ⟨46030578669763821671651209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245496419572073715582139781 46030578669763821671651209)
    ·
      refine ⟨34522934002322866253738407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46030578669763821671651209 34522934002322866253738407)
      ·
        refine ⟨51784401003484299380607611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34522934002322866253738407 51784401003484299380607611)
        ·
          refine ⟨77676601505226449070911417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51784401003484299380607611 77676601505226449070911417)
          ·
            refine ⟨58257451128919836803183563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77676601505226449070911417 58257451128919836803183563)
            ·
              refine ⟨87386176693379755204775345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58257451128919836803183563 87386176693379755204775345)
              ·
                refine ⟨65539632520034816403581509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87386176693379755204775345 65539632520034816403581509)
                ·
                  refine ⟨12288681097506528075671533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65539632520034816403581509 12288681097506528075671533)
                  ·
                    refine ⟨4608255411564948028376825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12288681097506528075671533 4608255411564948028376825)
                    ·
                      refine ⟨3456191558673711021282619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608255411564948028376825 3456191558673711021282619)
                      ·
                        rfl

theorem cell23_6730909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_6730909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730909 prefixEnd_6730909 := by exact prefixLift 6730909
  have htrace : WordTrace (prefixWord ++ tailWord_6730909) baseStart_6730909 baseEnd_6730909 := by
    simpa [prefixWord, tailWord_6730909, baseEnd_6730909] using wordTrace_append hprefix tailTrace_6730909
  have hstable : (prefixWord ++ tailWord_6730909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730909).length < 2 ^ (prefixWord ++ tailWord_6730909).sum := by decide
  have hdescent : baseEnd_6730909 < baseStart_6730909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730915 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 5, 6]
def baseStart_6730915 : Nat := 118140960795 + 6730915 * 2 ^ 59
def prefixEnd_6730915 : Nat := 4983230072969 + 3 ^ 40 * 6730915 * 2
def baseEnd_6730915 : Nat := 1152064879852545999269197

theorem tailTrace_6730915 : CollatzResearch.WordTrace tailWord_6730915 prefixEnd_6730915 1152064879852545999269197 := by
  unfold tailWord_6730915
  simp only [CollatzResearch.WordTrace]
  refine ⟨245496638410051978606858199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163664425606701319071238799 245496638410051978606858199)
  ·
    refine ⟨368244957615077967910287299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245496638410051978606858199 368244957615077967910287299)
    ·
      refine ⟨552367436422616951865430949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368244957615077967910287299 552367436422616951865430949)
      ·
        refine ⟨103568894329240678474768303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 552367436422616951865430949 103568894329240678474768303)
        ·
          refine ⟨155353341493861017712152455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103568894329240678474768303 155353341493861017712152455)
          ·
            refine ⟨233030012240791526568228683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155353341493861017712152455 233030012240791526568228683)
            ·
              refine ⟨349545018361187289852343025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233030012240791526568228683 349545018361187289852343025)
              ·
                refine ⟨262158763770890467389257269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349545018361187289852343025 262158763770890467389257269)
                ·
                  refine ⟨24577384103520981317742869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262158763770890467389257269 24577384103520981317742869)
                  ·
                    refine ⟨1152064879852545999269197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24577384103520981317742869 1152064879852545999269197)
                    ·
                      rfl

theorem cell23_6730915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 6].length) (baseStart_6730915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730915 prefixEnd_6730915 := by exact prefixLift 6730915
  have htrace : WordTrace (prefixWord ++ tailWord_6730915) baseStart_6730915 baseEnd_6730915 := by
    simpa [prefixWord, tailWord_6730915, baseEnd_6730915] using wordTrace_append hprefix tailTrace_6730915
  have hstable : (prefixWord ++ tailWord_6730915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730915).length < 2 ^ (prefixWord ++ tailWord_6730915).sum := by decide
  have hdescent : baseEnd_6730915 < baseStart_6730915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730919 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6730919 : Nat := 118140960795 + 6730919 * 2 ^ 59
def prefixEnd_6730919 : Nat := 4983230072969 + 3 ^ 40 * 6730919 * 2
def baseEnd_6730919 : Nat := 1152065564493418660719191

theorem tailTrace_6730919 : CollatzResearch.WordTrace tailWord_6730919 prefixEnd_6730919 1152065564493418660719191 := by
  unfold tailWord_6730919
  simp only [CollatzResearch.WordTrace]
  refine ⟨245496784302037487290003811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163664522868024991526669207 245496784302037487290003811)
  ·
    refine ⟨368245176453056230935005717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245496784302037487290003811 368245176453056230935005717)
    ·
      refine ⟨17261492646237010825078393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 368245176453056230935005717 17261492646237010825078393)
      ·
        refine ⟨12946119484677758118808795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17261492646237010825078393 12946119484677758118808795)
        ·
          refine ⟨19419179227016637178213193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12946119484677758118808795 19419179227016637178213193)
          ·
            refine ⟨14564384420262477883659895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19419179227016637178213193 14564384420262477883659895)
            ·
              refine ⟨21846576630393716825489843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14564384420262477883659895 21846576630393716825489843)
              ·
                refine ⟨32769864945590575238234765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21846576630393716825489843 32769864945590575238234765)
                ·
                  refine ⟨12288699354596465714338037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32769864945590575238234765 12288699354596465714338037)
                  ·
                    refine ⟨1152065564493418660719191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12288699354596465714338037 1152065564493418660719191)
                    ·
                      rfl

theorem cell23_6730919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6730919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730919 prefixEnd_6730919 := by exact prefixLift 6730919
  have htrace : WordTrace (prefixWord ++ tailWord_6730919) baseStart_6730919 baseEnd_6730919 := by
    simpa [prefixWord, tailWord_6730919, baseEnd_6730919] using wordTrace_append hprefix tailTrace_6730919
  have hstable : (prefixWord ++ tailWord_6730919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730919).length < 2 ^ (prefixWord ++ tailWord_6730919).sum := by decide
  have hdescent : baseEnd_6730919 < baseStart_6730919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730939 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 7, 2, 2]
def baseStart_6730939 : Nat := 118140960795 + 6730939 * 2 ^ 59
def prefixEnd_6730939 : Nat := 4983230072969 + 3 ^ 40 * 6730939 * 2
def baseEnd_6730939 : Nat := 3456206963093345903907481

theorem tailTrace_6730939 : CollatzResearch.WordTrace tailWord_6730939 prefixEnd_6730939 3456206963093345903907481 := by
  unfold tailWord_6730939
  simp only [CollatzResearch.WordTrace]
  refine ⟨245497513761965030705731871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163665009174643353803821247 245497513761965030705731871)
  ·
    refine ⟨368246270642947546058597807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245497513761965030705731871 368246270642947546058597807)
    ·
      refine ⟨552369405964421319087896711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368246270642947546058597807 552369405964421319087896711)
      ·
        refine ⟨828554108946631978631845067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552369405964421319087896711 828554108946631978631845067)
        ·
          refine ⟨1242831163419947967947767601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828554108946631978631845067 1242831163419947967947767601)
          ·
            refine ⟨932123372564960975960825701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1242831163419947967947767601 932123372564960975960825701)
            ·
              refine ⟨174773132355930182992654819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 932123372564960975960825701 174773132355930182992654819)
              ·
                refine ⟨262159698533895274488982229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174773132355930182992654819 262159698533895274488982229)
                ·
                  refine ⟨6144367934388170495835521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 262159698533895274488982229 6144367934388170495835521)
                  ·
                    refine ⟨4608275950791127871876641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6144367934388170495835521 4608275950791127871876641)
                    ·
                      refine ⟨3456206963093345903907481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608275950791127871876641 3456206963093345903907481)
                      ·
                        rfl

theorem cell23_6730939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 2, 2].length) (baseStart_6730939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730939 prefixEnd_6730939 := by exact prefixLift 6730939
  have htrace : WordTrace (prefixWord ++ tailWord_6730939) baseStart_6730939 baseEnd_6730939 := by
    simpa [prefixWord, tailWord_6730939, baseEnd_6730939] using wordTrace_append hprefix tailTrace_6730939
  have hstable : (prefixWord ++ tailWord_6730939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730939).length < 2 ^ (prefixWord ++ tailWord_6730939).sum := by decide
  have hdescent : baseEnd_6730939 < baseStart_6730939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6730955 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7]
def baseStart_6730955 : Nat := 118140960795 + 6730955 * 2 ^ 59
def prefixEnd_6730955 : Nat := 4983230072969 + 3 ^ 40 * 6730955 * 2
def baseEnd_6730955 : Nat := 3456215178783817841307407

theorem tailTrace_6730955 : CollatzResearch.WordTrace tailWord_6730955 prefixEnd_6730955 3456215178783817841307407 := by
  unfold tailWord_6730955
  simp only [CollatzResearch.WordTrace]
  refine ⟨245498097329907065438314319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163665398219938043625542879 245498097329907065438314319)
  ·
    refine ⟨368247145994860598157471479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245498097329907065438314319 368247145994860598157471479)
    ·
      refine ⟨552370718992290897236207219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368247145994860598157471479 552370718992290897236207219)
      ·
        refine ⟨828556078488436345854310829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552370718992290897236207219 828556078488436345854310829)
        ·
          refine ⟨310708529433163629695366561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828556078488436345854310829 310708529433163629695366561)
          ·
            refine ⟨233031397074872722271524921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310708529433163629695366561 233031397074872722271524921)
            ·
              refine ⟨174773547806154541703643691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233031397074872722271524921 174773547806154541703643691)
              ·
                refine ⟨262160321709231812555465537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174773547806154541703643691 262160321709231812555465537)
                ·
                  refine ⟨196620241281923859416599153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262160321709231812555465537 196620241281923859416599153)
                  ·
                    refine ⟨147465180961442894562449365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196620241281923859416599153 147465180961442894562449365)
                    ·
                      refine ⟨3456215178783817841307407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147465180961442894562449365 3456215178783817841307407)
                      ·
                        rfl

theorem cell23_6730955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_6730955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6730955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6730955 prefixEnd_6730955 := by exact prefixLift 6730955
  have htrace : WordTrace (prefixWord ++ tailWord_6730955) baseStart_6730955 baseEnd_6730955 := by
    simpa [prefixWord, tailWord_6730955, baseEnd_6730955] using wordTrace_append hprefix tailTrace_6730955
  have hstable : (prefixWord ++ tailWord_6730955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6730955).length < 2 ^ (prefixWord ++ tailWord_6730955).sum := by decide
  have hdescent : baseEnd_6730955 < baseStart_6730955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6730955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731082 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_6731082 : Nat := 118140960795 + 6731082 * 2 ^ 59
def prefixEnd_6731082 : Nat := 4983230072969 + 3 ^ 40 * 6731082 * 2
def baseEnd_6731082 : Nat := 1152093463608979614806441

theorem tailTrace_6731082 : CollatzResearch.WordTrace tailWord_6731082 prefixEnd_6731082 1152093463608979614806441 := by
  unfold tailWord_6731082
  simp only [CollatzResearch.WordTrace]
  refine ⟨61375682350111741532046875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163668486266964644085458333 61375682350111741532046875)
  ·
    refine ⟨92063523525167612298070313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61375682350111741532046875 92063523525167612298070313)
    ·
      refine ⟨69047642643875709223552735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92063523525167612298070313 69047642643875709223552735)
      ·
        refine ⟨103571463965813563835329103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69047642643875709223552735 103571463965813563835329103)
        ·
          refine ⟨155357195948720345752993655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103571463965813563835329103 155357195948720345752993655)
          ·
            refine ⟨233035793923080518629490483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155357195948720345752993655 233035793923080518629490483)
            ·
              refine ⟨349553690884620777944235725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233035793923080518629490483 349553690884620777944235725)
              ·
                refine ⟨131082634081732791729088397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349553690884620777944235725 131082634081732791729088397)
                ·
                  refine ⟨49155987780649796898408149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131082634081732791729088397 49155987780649796898408149)
                  ·
                    refine ⟨1152093463608979614806441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49155987780649796898408149 1152093463608979614806441)
                    ·
                      rfl

theorem cell23_6731082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_6731082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731082 prefixEnd_6731082 := by exact prefixLift 6731082
  have htrace : WordTrace (prefixWord ++ tailWord_6731082) baseStart_6731082 baseEnd_6731082 := by
    simpa [prefixWord, tailWord_6731082, baseEnd_6731082] using wordTrace_append hprefix tailTrace_6731082
  have hstable : (prefixWord ++ tailWord_6731082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731082).length < 2 ^ (prefixWord ++ tailWord_6731082).sum := by decide
  have hdescent : baseEnd_6731082 < baseStart_6731082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731119 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_6731119 : Nat := 118140960795 + 6731119 * 2 ^ 59
def prefixEnd_6731119 : Nat := 4983230072969 + 3 ^ 40 * 6731119 * 2
def baseEnd_6731119 : Nat := 3456299389611155199656653

theorem tailTrace_6731119 : CollatzResearch.WordTrace tailWord_6731119 prefixEnd_6731119 3456299389611155199656653 := by
  unfold tailWord_6731119
  simp only [CollatzResearch.WordTrace]
  refine ⟨245504078901312921447284411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163669385934208614298189607 245504078901312921447284411)
  ·
    refine ⟨368256118351969382170926617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245504078901312921447284411 368256118351969382170926617)
    ·
      refine ⟨276192088763977036628194963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368256118351969382170926617 276192088763977036628194963)
      ·
        refine ⟨414288133145965554942292445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276192088763977036628194963 414288133145965554942292445)
        ·
          refine ⟨155358049929737083103359667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414288133145965554942292445 155358049929737083103359667)
          ·
            refine ⟨233037074894605624655039501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155358049929737083103359667 233037074894605624655039501)
            ·
              refine ⟨87388903085477109245639813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233037074894605624655039501 87388903085477109245639813)
              ·
                refine ⟨16385419328526957983557465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87388903085477109245639813 16385419328526957983557465)
                ·
                  refine ⟨12289064496395218487668099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16385419328526957983557465 12289064496395218487668099)
                  ·
                    refine ⟨18433596744592827731502149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12289064496395218487668099 18433596744592827731502149)
                    ·
                      refine ⟨3456299389611155199656653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18433596744592827731502149 3456299389611155199656653)
                      ·
                        rfl

theorem cell23_6731119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_6731119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731119 prefixEnd_6731119 := by exact prefixLift 6731119
  have htrace : WordTrace (prefixWord ++ tailWord_6731119) baseStart_6731119 baseEnd_6731119 := by
    simpa [prefixWord, tailWord_6731119, baseEnd_6731119] using wordTrace_append hprefix tailTrace_6731119
  have hstable : (prefixWord ++ tailWord_6731119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731119).length < 2 ^ (prefixWord ++ tailWord_6731119).sum := by decide
  have hdescent : baseEnd_6731119 < baseStart_6731119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731150 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_6731150 : Nat := 118140960795 + 6731150 * 2 ^ 59
def prefixEnd_6731150 : Nat := 4983230072969 + 3 ^ 40 * 6731150 * 2
def baseEnd_6731150 : Nat := 1152105102503814859456337

theorem tailTrace_6731150 : CollatzResearch.WordTrace tailWord_6731150 prefixEnd_6731150 1152105102503814859456337 := by
  unfold tailWord_6731150
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688151195525076717707863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163670139709467075827775269 30688151195525076717707863)
  ·
    refine ⟨46032226793287615076561795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30688151195525076717707863 46032226793287615076561795)
    ·
      refine ⟨69048340189931422614842693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46032226793287615076561795 69048340189931422614842693)
      ·
        refine ⟨12946563785612141740283005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69048340189931422614842693 12946563785612141740283005)
        ·
          refine ⟨4854961419604553152606127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12946563785612141740283005 4854961419604553152606127)
          ·
            refine ⟨7282442129406829728909191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854961419604553152606127 7282442129406829728909191)
            ·
              refine ⟨10923663194110244593363787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282442129406829728909191 10923663194110244593363787)
              ·
                refine ⟨16385494791165366890045681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10923663194110244593363787 16385494791165366890045681)
                ·
                  refine ⟨12289121093374025167534261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16385494791165366890045681 12289121093374025167534261)
                  ·
                    refine ⟨1152105102503814859456337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12289121093374025167534261 1152105102503814859456337)
                    ·
                      rfl

theorem cell23_6731150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_6731150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731150 prefixEnd_6731150 := by exact prefixLift 6731150
  have htrace : WordTrace (prefixWord ++ tailWord_6731150) baseStart_6731150 baseEnd_6731150 := by
    simpa [prefixWord, tailWord_6731150, baseEnd_6731150] using wordTrace_append hprefix tailTrace_6731150
  have hstable : (prefixWord ++ tailWord_6731150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731150).length < 2 ^ (prefixWord ++ tailWord_6731150).sum := by decide
  have hdescent : baseEnd_6731150 < baseStart_6731150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731152 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_6731152 : Nat := 118140960795 + 6731152 * 2 ^ 59
def prefixEnd_6731152 : Nat := 4983230072969 + 3 ^ 40 * 6731152 * 2
def baseEnd_6731152 : Nat := 3456316334472753570544001

theorem tailTrace_6731152 : CollatzResearch.WordTrace tailWord_6731152 prefixEnd_6731152 3456316334472753570544001 := by
  unfold tailWord_6731152
  simp only [CollatzResearch.WordTrace]
  refine ⟨122752641255096684041617855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163670188340128912055490473 122752641255096684041617855)
  ·
    refine ⟨184128961882645026062426783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122752641255096684041617855 184128961882645026062426783)
    ·
      refine ⟨276193442823967539093640175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184128961882645026062426783 276193442823967539093640175)
      ·
        refine ⟨414290164235951308640460263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276193442823967539093640175 414290164235951308640460263)
        ·
          refine ⟨621435246353926962960690395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414290164235951308640460263 621435246353926962960690395)
          ·
            refine ⟨932152869530890444441035593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621435246353926962960690395 932152869530890444441035593)
            ·
              refine ⟨699114652148167833330776695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932152869530890444441035593 699114652148167833330776695)
              ·
                refine ⟨1048671978222251749996165043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699114652148167833330776695 1048671978222251749996165043)
                ·
                  refine ⟨1573007967333377624994247565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048671978222251749996165043 1573007967333377624994247565)
                  ·
                    refine ⟨589877987750016609372842837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1573007967333377624994247565 589877987750016609372842837)
                    ·
                      refine ⟨3456316334472753570544001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 589877987750016609372842837 3456316334472753570544001)
                      ·
                        rfl

theorem cell23_6731152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_6731152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731152 prefixEnd_6731152 := by exact prefixLift 6731152
  have htrace : WordTrace (prefixWord ++ tailWord_6731152) baseStart_6731152 baseEnd_6731152 := by
    simpa [prefixWord, tailWord_6731152, baseEnd_6731152] using wordTrace_append hprefix tailTrace_6731152
  have hstable : (prefixWord ++ tailWord_6731152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731152).length < 2 ^ (prefixWord ++ tailWord_6731152).sum := by decide
  have hdescent : baseEnd_6731152 < baseStart_6731152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731193 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 6]
def baseStart_6731193 : Nat := 118140960795 + 6731193 * 2 ^ 59
def prefixEnd_6731193 : Nat := 4983230072969 + 3 ^ 40 * 6731193 * 2
def baseEnd_6731193 : Nat := 384037487464398656681257

theorem tailTrace_6731193 : CollatzResearch.WordTrace tailWord_6731193 prefixEnd_6731193 384037487464398656681257 := by
  unfold tailWord_6731193
  simp only [CollatzResearch.WordTrace]
  refine ⟨245506777903044832085478233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163671185268696554723652155 245506777903044832085478233)
  ·
    refine ⟨184130083427283624064108675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245506777903044832085478233 184130083427283624064108675)
    ·
      refine ⟨276195125140925436096163013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184130083427283624064108675 276195125140925436096163013)
      ·
        refine ⟨51786585963923519268030565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276195125140925436096163013 51786585963923519268030565)
        ·
          refine ⟨9709984868235659862755731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51786585963923519268030565 9709984868235659862755731)
          ·
            refine ⟨14564977302353489794133597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9709984868235659862755731 14564977302353489794133597)
            ·
              refine ⟨5461866488382558672800099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14564977302353489794133597 5461866488382558672800099)
              ·
                refine ⟨8192799732573838009200149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461866488382558672800099 8192799732573838009200149)
                ·
                  refine ⟨384037487464398656681257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8192799732573838009200149 384037487464398656681257)
                  ·
                    rfl

theorem cell23_6731193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 6].length) (baseStart_6731193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731193 prefixEnd_6731193 := by exact prefixLift 6731193
  have htrace : WordTrace (prefixWord ++ tailWord_6731193) baseStart_6731193 baseEnd_6731193 := by
    simpa [prefixWord, tailWord_6731193, baseEnd_6731193] using wordTrace_append hprefix tailTrace_6731193
  have hstable : (prefixWord ++ tailWord_6731193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731193).length < 2 ^ (prefixWord ++ tailWord_6731193).sum := by decide
  have hdescent : baseEnd_6731193 < baseStart_6731193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731243 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 3, 2, 2]
def baseStart_6731243 : Nat := 118140960795 + 6731243 * 2 ^ 59
def prefixEnd_6731243 : Nat := 4983230072969 + 3 ^ 40 * 6731243 * 2
def baseEnd_6731243 : Nat := 3456363061212312714506083

theorem tailTrace_6731243 : CollatzResearch.WordTrace tailWord_6731243 prefixEnd_6731243 3456363061212312714506083 := by
  unfold tailWord_6731243
  simp only [CollatzResearch.WordTrace]
  refine ⟨245508601552863690624798383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163672401035242460416532255 245508601552863690624798383)
  ·
    refine ⟨368262902329295535937197575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245508601552863690624798383 368262902329295535937197575)
    ·
      refine ⟨552394353493943303905796363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368262902329295535937197575 552394353493943303905796363)
      ·
        refine ⟨828591530240914955858694545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552394353493943303905796363 828591530240914955858694545)
        ·
          refine ⟨621443647680686216894020909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828591530240914955858694545 621443647680686216894020909)
          ·
            refine ⟨233041367880257331335257841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621443647680686216894020909 233041367880257331335257841)
            ·
              refine ⟨174781025910192998501443381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233041367880257331335257841 174781025910192998501443381)
              ·
                refine ⟨16385721179080593609510317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174781025910192998501443381 16385721179080593609510317)
                ·
                  refine ⟨6144645442155222603566369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16385721179080593609510317 6144645442155222603566369)
                  ·
                    refine ⟨4608484081616416952674777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6144645442155222603566369 4608484081616416952674777)
                    ·
                      refine ⟨3456363061212312714506083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608484081616416952674777 3456363061212312714506083)
                      ·
                        rfl

theorem cell23_6731243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 2, 2].length) (baseStart_6731243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731243 prefixEnd_6731243 := by exact prefixLift 6731243
  have htrace : WordTrace (prefixWord ++ tailWord_6731243) baseStart_6731243 baseEnd_6731243 := by
    simpa [prefixWord, tailWord_6731243, baseEnd_6731243] using wordTrace_append hprefix tailTrace_6731243
  have hstable : (prefixWord ++ tailWord_6731243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731243).length < 2 ^ (prefixWord ++ tailWord_6731243).sum := by decide
  have hdescent : baseEnd_6731243 < baseStart_6731243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731246 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_6731246 : Nat := 118140960795 + 6731246 * 2 ^ 59
def prefixEnd_6731246 : Nat := 4983230072969 + 3 ^ 40 * 6731246 * 2
def baseEnd_6731246 : Nat := 3456364601654276202768569

theorem tailTrace_6731246 : CollatzResearch.WordTrace tailWord_6731246 prefixEnd_6731246 3456364601654276202768569 := by
  unfold tailWord_6731246
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688588871481602767144699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163672473981235214758105061 30688588871481602767144699)
  ·
    refine ⟨46032883307222404150717049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30688588871481602767144699 46032883307222404150717049)
    ·
      refine ⟨34524662480416803113037787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46032883307222404150717049 34524662480416803113037787)
      ·
        refine ⟨51786993720625204669556681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34524662480416803113037787 51786993720625204669556681)
        ·
          refine ⟨38840245290468903502167511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51786993720625204669556681 38840245290468903502167511)
          ·
            refine ⟨58260367935703355253251267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38840245290468903502167511 58260367935703355253251267)
            ·
              refine ⟨87390551903555032879876901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58260367935703355253251267 87390551903555032879876901)
              ·
                refine ⟨16385728481916568664976919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87390551903555032879876901 16385728481916568664976919)
                ·
                  refine ⟨24578592722874852997465379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16385728481916568664976919 24578592722874852997465379)
                  ·
                    refine ⟨36867889084312279496198069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24578592722874852997465379 36867889084312279496198069)
                    ·
                      refine ⟨3456364601654276202768569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36867889084312279496198069 3456364601654276202768569)
                      ·
                        rfl

theorem cell23_6731246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_6731246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731246 prefixEnd_6731246 := by exact prefixLift 6731246
  have htrace : WordTrace (prefixWord ++ tailWord_6731246) baseStart_6731246 baseEnd_6731246 := by
    simpa [prefixWord, tailWord_6731246, baseEnd_6731246] using wordTrace_append hprefix tailTrace_6731246
  have hstable : (prefixWord ++ tailWord_6731246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731246).length < 2 ^ (prefixWord ++ tailWord_6731246).sum := by decide
  have hdescent : baseEnd_6731246 < baseStart_6731246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731249 : List Nat := [1, 2, 2, 2, 3, 2, 1, 10]
def baseStart_6731249 : Nat := 118140960795 + 6731249 * 2 ^ 59
def prefixEnd_6731249 : Nat := 4983230072969 + 3 ^ 40 * 6731249 * 2
def baseEnd_6731249 : Nat := 128013560818379247815965

theorem tailTrace_6731249 : CollatzResearch.WordTrace tailWord_6731249 prefixEnd_6731249 128013560818379247815965 := by
  unfold tailWord_6731249
  simp only [CollatzResearch.WordTrace]
  refine ⟨245508820390841953649516801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163672546927227969099677867 245508820390841953649516801)
  ·
    refine ⟨184131615293131465237137601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245508820390841953649516801 184131615293131465237137601)
    ·
      refine ⟨138098711469848598927853201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184131615293131465237137601 138098711469848598927853201)
      ·
        refine ⟨103574033602386449195889901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138098711469848598927853201 103574033602386449195889901)
        ·
          refine ⟨38840262600894918448458713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103574033602386449195889901 38840262600894918448458713)
          ·
            refine ⟨29130196950671188836344035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38840262600894918448458713 29130196950671188836344035)
            ·
              refine ⟨43695295426006783254516053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29130196950671188836344035 43695295426006783254516053)
              ·
                refine ⟨128013560818379247815965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43695295426006783254516053 128013560818379247815965)
                ·
                  rfl

theorem cell23_6731249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 10].length) (baseStart_6731249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731249 prefixEnd_6731249 := by exact prefixLift 6731249
  have htrace : WordTrace (prefixWord ++ tailWord_6731249) baseStart_6731249 baseEnd_6731249 := by
    simpa [prefixWord, tailWord_6731249, baseEnd_6731249] using wordTrace_append hprefix tailTrace_6731249
  have hstable : (prefixWord ++ tailWord_6731249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731249).length < 2 ^ (prefixWord ++ tailWord_6731249).sum := by decide
  have hdescent : baseEnd_6731249 < baseStart_6731249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731296 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 2, 7]
def baseStart_6731296 : Nat := 118140960795 + 6731296 * 2 ^ 59
def prefixEnd_6731296 : Nat := 4983230072969 + 3 ^ 40 * 6731296 * 2
def baseEnd_6731296 : Nat := 1152130091895667002381113

theorem tailTrace_6731296 : CollatzResearch.WordTrace tailWord_6731296 prefixEnd_6731296 1152130091895667002381113 := by
  unfold tailWord_6731296
  simp only [CollatzResearch.WordTrace]
  refine ⟨122755267310835840338238871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163673689747781120450985161 122755267310835840338238871)
  ·
    refine ⟨184132900966253760507358307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122755267310835840338238871 184132900966253760507358307)
    ·
      refine ⟨276199351449380640761037461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184132900966253760507358307 276199351449380640761037461)
      ·
        refine ⟨12946844599189717535673631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 276199351449380640761037461 12946844599189717535673631)
        ·
          refine ⟨19420266898784576303510447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12946844599189717535673631 19420266898784576303510447)
          ·
            refine ⟨29130400348176864455265671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19420266898784576303510447 29130400348176864455265671)
            ·
              refine ⟨43695600522265296682898507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29130400348176864455265671 43695600522265296682898507)
              ·
                refine ⟨65543400783397945024347761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43695600522265296682898507 65543400783397945024347761)
                ·
                  refine ⟨49157550587548458768260821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65543400783397945024347761 49157550587548458768260821)
                  ·
                    refine ⟨1152130091895667002381113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49157550587548458768260821 1152130091895667002381113)
                    ·
                      rfl

theorem cell23_6731296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_6731296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731296 prefixEnd_6731296 := by exact prefixLift 6731296
  have htrace : WordTrace (prefixWord ++ tailWord_6731296) baseStart_6731296 baseEnd_6731296 := by
    simpa [prefixWord, tailWord_6731296, baseEnd_6731296] using wordTrace_append hprefix tailTrace_6731296
  have hstable : (prefixWord ++ tailWord_6731296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731296).length < 2 ^ (prefixWord ++ tailWord_6731296).sum := by decide
  have hdescent : baseEnd_6731296 < baseStart_6731296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731310 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_6731310 : Nat := 118140960795 + 6731310 * 2 ^ 59
def prefixEnd_6731310 : Nat := 4983230072969 + 3 ^ 40 * 6731310 * 2
def baseEnd_6731310 : Nat := 3456397464416163952368275

theorem tailTrace_6731310 : CollatzResearch.WordTrace tailWord_6731310 prefixEnd_6731310 3456397464416163952368275 := by
  unfold tailWord_6731310
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688880655452620133435923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163674030162413974044991589 30688880655452620133435923)
  ·
    refine ⟨46033320983178930200153885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30688880655452620133435923 46033320983178930200153885)
    ·
      refine ⟨17262495368692098825057707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46033320983178930200153885 17262495368692098825057707)
      ·
        refine ⟨25893743053038148237586561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17262495368692098825057707 25893743053038148237586561)
        ·
          refine ⟨19420307289778611178189921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25893743053038148237586561 19420307289778611178189921)
          ·
            refine ⟨14565230467333958383642441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19420307289778611178189921 14565230467333958383642441)
            ·
              refine ⟨10923922850500468787731831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14565230467333958383642441 10923922850500468787731831)
              ·
                refine ⟨16385884275750703181597747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10923922850500468787731831 16385884275750703181597747)
                ·
                  refine ⟨24578826413626054772396621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16385884275750703181597747 24578826413626054772396621)
                  ·
                    refine ⟨9217059905109770539648733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24578826413626054772396621 9217059905109770539648733)
                    ·
                      refine ⟨3456397464416163952368275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217059905109770539648733 3456397464416163952368275)
                      ·
                        rfl

theorem cell23_6731310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_6731310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731310 prefixEnd_6731310 := by exact prefixLift 6731310
  have htrace : WordTrace (prefixWord ++ tailWord_6731310) baseStart_6731310 baseEnd_6731310 := by
    simpa [prefixWord, tailWord_6731310, baseEnd_6731310] using wordTrace_append hprefix tailTrace_6731310
  have hstable : (prefixWord ++ tailWord_6731310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731310).length < 2 ^ (prefixWord ++ tailWord_6731310).sum := by decide
  have hdescent : baseEnd_6731310 < baseStart_6731310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731333 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 1, 4, 2]
def baseStart_6731333 : Nat := 118140960795 + 6731333 * 2 ^ 59
def prefixEnd_6731333 : Nat := 4983230072969 + 3 ^ 40 * 6731333 * 2
def baseEnd_6731333 : Nat := 3456409274471217362380669

theorem tailTrace_6731333 : CollatzResearch.WordTrace tailWord_6731333 prefixEnd_6731333 3456409274471217362380669 := by
  unfold tailWord_6731333
  simp only [CollatzResearch.WordTrace]
  refine ⟨245511884122537635995574653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163674589415025090663716435 245511884122537635995574653)
  ·
    refine ⟨92066956545951613498340495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245511884122537635995574653 92066956545951613498340495)
    ·
      refine ⟨138100434818927420247510743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92066956545951613498340495 138100434818927420247510743)
      ·
        refine ⟨207150652228391130371266115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138100434818927420247510743 207150652228391130371266115)
        ·
          refine ⟨310725978342586695556899173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207150652228391130371266115 310725978342586695556899173)
          ·
            refine ⟨58261120939235005416918595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310725978342586695556899173 58261120939235005416918595)
            ·
              refine ⟨87391681408852508125377893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58261120939235005416918595 87391681408852508125377893)
              ·
                refine ⟨16385940264159845273508355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87391681408852508125377893 16385940264159845273508355)
                ·
                  refine ⟨24578910396239767910262533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16385940264159845273508355 24578910396239767910262533)
                  ·
                    refine ⟨4608545699294956483174225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24578910396239767910262533 4608545699294956483174225)
                    ·
                      refine ⟨3456409274471217362380669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608545699294956483174225 3456409274471217362380669)
                      ·
                        rfl

theorem cell23_6731333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_6731333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731333 prefixEnd_6731333 := by exact prefixLift 6731333
  have htrace : WordTrace (prefixWord ++ tailWord_6731333) baseStart_6731333 baseEnd_6731333 := by
    simpa [prefixWord, tailWord_6731333, baseEnd_6731333] using wordTrace_append hprefix tailTrace_6731333
  have hstable : (prefixWord ++ tailWord_6731333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731333).length < 2 ^ (prefixWord ++ tailWord_6731333).sum := by decide
  have hdescent : baseEnd_6731333 < baseStart_6731333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731339 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 11]
def baseStart_6731339 : Nat := 118140960795 + 6731339 * 2 ^ 59
def prefixEnd_6731339 : Nat := 4983230072969 + 3 ^ 40 * 6731339 * 2
def baseEnd_6731339 : Nat := 384045817261682704322849

theorem tailTrace_6731339 : CollatzResearch.WordTrace tailWord_6731339 prefixEnd_6731339 384045817261682704322849 := by
  unfold tailWord_6731339
  simp only [CollatzResearch.WordTrace]
  refine ⟨245512102960515899020293071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163674735307010599346862047 245512102960515899020293071)
  ·
    refine ⟨368268154440773848530439607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245512102960515899020293071 368268154440773848530439607)
    ·
      refine ⟨552402231661160772795659411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368268154440773848530439607 552402231661160772795659411)
      ·
        refine ⟨828603347491741159193489117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552402231661160772795659411 828603347491741159193489117)
        ·
          refine ⟨310726255309402934697558419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828603347491741159193489117 310726255309402934697558419)
          ·
            refine ⟨466089382964104402046337629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310726255309402934697558419 466089382964104402046337629)
            ·
              refine ⟨174783518611539150767376611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466089382964104402046337629 174783518611539150767376611)
              ·
                refine ⟨262175277917308726151064917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174783518611539150767376611 262175277917308726151064917)
                ·
                  refine ⟨384045817261682704322849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 262175277917308726151064917 384045817261682704322849)
                  ·
                    rfl

theorem cell23_6731339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 11].length) (baseStart_6731339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731339 prefixEnd_6731339 := by exact prefixLift 6731339
  have htrace : WordTrace (prefixWord ++ tailWord_6731339) baseStart_6731339 baseEnd_6731339 := by
    simpa [prefixWord, tailWord_6731339, baseEnd_6731339] using wordTrace_append hprefix tailTrace_6731339
  have hstable : (prefixWord ++ tailWord_6731339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731339).length < 2 ^ (prefixWord ++ tailWord_6731339).sum := by decide
  have hdescent : baseEnd_6731339 < baseStart_6731339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731458 : List Nat := [3, 5, 1, 2, 1, 2, 2, 2, 5]
def baseStart_6731458 : Nat := 118140960795 + 6731458 * 2 ^ 59
def prefixEnd_6731458 : Nat := 4983230072969 + 3 ^ 40 * 6731458 * 2
def baseEnd_6731458 : Nat := 384052606617003263701955

theorem tailTrace_6731458 : CollatzResearch.WordTrace tailWord_6731458 prefixEnd_6731458 384052606617003263701955 := by
  unfold tailWord_6731458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61379110811771195585968757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163677628831389854895916685 61379110811771195585968757)
  ·
    refine ⟨5754291638603549586184571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61379110811771195585968757 5754291638603549586184571)
    ·
      refine ⟨8631437457905324379276857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754291638603549586184571 8631437457905324379276857)
      ·
        refine ⟨6473578093428993284457643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8631437457905324379276857 6473578093428993284457643)
        ·
          refine ⟨9710367140143489926686465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473578093428993284457643 9710367140143489926686465)
          ·
            refine ⟨7282775355107617445014849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9710367140143489926686465 7282775355107617445014849)
            ·
              refine ⟨5462081516330713083761137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282775355107617445014849 5462081516330713083761137)
              ·
                refine ⟨4096561137248034812820853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5462081516330713083761137 4096561137248034812820853)
                ·
                  refine ⟨384052606617003263701955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4096561137248034812820853 384052606617003263701955)
                  ·
                    rfl

theorem cell23_6731458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_6731458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731458 prefixEnd_6731458 := by exact prefixLift 6731458
  have htrace : WordTrace (prefixWord ++ tailWord_6731458) baseStart_6731458 baseEnd_6731458 := by
    simpa [prefixWord, tailWord_6731458, baseEnd_6731458] using wordTrace_append hprefix tailTrace_6731458
  have hstable : (prefixWord ++ tailWord_6731458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731458).length < 2 ^ (prefixWord ++ tailWord_6731458).sum := by decide
  have hdescent : baseEnd_6731458 < baseStart_6731458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731460 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_6731460 : Nat := 118140960795 + 6731460 * 2 ^ 59
def prefixEnd_6731460 : Nat := 4983230072969 + 3 ^ 40 * 6731460 * 2
def baseEnd_6731460 : Nat := 3456474486514338365492585

theorem tailTrace_6731460 : CollatzResearch.WordTrace tailWord_6731460 prefixEnd_6731460 3456474486514338365492585 := by
  unfold tailWord_6731460
  simp only [CollatzResearch.WordTrace]
  refine ⟨122758258096538768342723917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163677677462051691123631889 122758258096538768342723917)
  ·
    refine ⟨46034346786202038128521469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122758258096538768342723917 46034346786202038128521469)
    ·
      refine ⟨17262880044825764298195551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46034346786202038128521469 17262880044825764298195551)
      ·
        refine ⟨25894320067238646447293327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17262880044825764298195551 25894320067238646447293327)
        ·
          refine ⟨38841480100857969670939991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25894320067238646447293327 38841480100857969670939991)
          ·
            refine ⟨58262220151286954506409987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38841480100857969670939991 58262220151286954506409987)
            ·
              refine ⟨87393330226930431759614981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58262220151286954506409987 87393330226930431759614981)
              ·
                refine ⟨16386249417549455954927809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87393330226930431759614981 16386249417549455954927809)
                ·
                  refine ⟨12289687063162091966195857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16386249417549455954927809 12289687063162091966195857)
                  ·
                    refine ⟨9217265297371568974646893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12289687063162091966195857 9217265297371568974646893)
                    ·
                      refine ⟨3456474486514338365492585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217265297371568974646893 3456474486514338365492585)
                      ·
                        rfl

theorem cell23_6731460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_6731460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731460 prefixEnd_6731460 := by exact prefixLift 6731460
  have htrace : WordTrace (prefixWord ++ tailWord_6731460) baseStart_6731460 baseEnd_6731460 := by
    simpa [prefixWord, tailWord_6731460, baseEnd_6731460] using wordTrace_append hprefix tailTrace_6731460
  have hstable : (prefixWord ++ tailWord_6731460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731460).length < 2 ^ (prefixWord ++ tailWord_6731460).sum := by decide
  have hdescent : baseEnd_6731460 < baseStart_6731460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731463 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 6]
def baseStart_6731463 : Nat := 118140960795 + 6731463 * 2 ^ 59
def prefixEnd_6731463 : Nat := 4983230072969 + 3 ^ 40 * 6731463 * 2
def baseEnd_6731463 : Nat := 384052891884033539306119

theorem tailTrace_6731463 : CollatzResearch.WordTrace tailWord_6731463 prefixEnd_6731463 384052891884033539306119 := by
  unfold tailWord_6731463
  simp only [CollatzResearch.WordTrace]
  refine ⟨245516625612066668197807043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163677750408044445465204695 245516625612066668197807043)
  ·
    refine ⟨368274938418100002296710565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245516625612066668197807043 368274938418100002296710565)
    ·
      refine ⟨69051550953393750430633231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368274938418100002296710565 69051550953393750430633231)
      ·
        refine ⟨103577326430090625645949847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69051550953393750430633231 103577326430090625645949847)
        ·
          refine ⟨155365989645135938468924771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103577326430090625645949847 155365989645135938468924771)
          ·
            refine ⟨233048984467703907703387157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155365989645135938468924771 233048984467703907703387157)
            ·
              refine ⟨10924171146923620673596273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233048984467703907703387157 10924171146923620673596273)
              ·
                refine ⟨8193128360192715505197205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10924171146923620673596273 8193128360192715505197205)
                ·
                  refine ⟨384052891884033539306119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8193128360192715505197205 384052891884033539306119)
                  ·
                    rfl

theorem cell23_6731463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 6].length) (baseStart_6731463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731463 prefixEnd_6731463 := by exact prefixLift 6731463
  have htrace : WordTrace (prefixWord ++ tailWord_6731463) baseStart_6731463 baseEnd_6731463 := by
    simpa [prefixWord, tailWord_6731463, baseEnd_6731463] using wordTrace_append hprefix tailTrace_6731463
  have hstable : (prefixWord ++ tailWord_6731463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731463).length < 2 ^ (prefixWord ++ tailWord_6731463).sum := by decide
  have hdescent : baseEnd_6731463 < baseStart_6731463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731493 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_6731493 : Nat := 118140960795 + 6731493 * 2 ^ 59
def prefixEnd_6731493 : Nat := 4983230072969 + 3 ^ 40 * 6731493 * 2
def baseEnd_6731493 : Nat := 1152163810458645578793311

theorem tailTrace_6731493 : CollatzResearch.WordTrace tailWord_6731493 prefixEnd_6731493 1152163810458645578793311 := by
  unfold tailWord_6731493
  simp only [CollatzResearch.WordTrace]
  refine ⟨245517719801957983321399133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163678479867971988880932755 245517719801957983321399133)
  ·
    refine ⟨92069144925734243745524675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245517719801957983321399133 92069144925734243745524675)
    ·
      refine ⟨138103717388601365618287013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92069144925734243745524675 138103717388601365618287013)
      ·
        refine ⟨25894447010362756053428815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138103717388601365618287013 25894447010362756053428815)
        ·
          refine ⟨38841670515544134080143223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25894447010362756053428815 38841670515544134080143223)
          ·
            refine ⟨58262505773316201120214835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38841670515544134080143223 58262505773316201120214835)
            ·
              refine ⟨87393758659974301680322253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58262505773316201120214835 87393758659974301680322253)
              ·
                refine ⟨32772659497490363130120845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87393758659974301680322253 32772659497490363130120845)
                ·
                  refine ⟨12289747311558886173795317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32772659497490363130120845 12289747311558886173795317)
                  ·
                    refine ⟨1152163810458645578793311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12289747311558886173795317 1152163810458645578793311)
                    ·
                      rfl

theorem cell23_6731493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_6731493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731493 prefixEnd_6731493 := by exact prefixLift 6731493
  have htrace : WordTrace (prefixWord ++ tailWord_6731493) baseStart_6731493 baseEnd_6731493 := by
    simpa [prefixWord, tailWord_6731493, baseEnd_6731493] using wordTrace_append hprefix tailTrace_6731493
  have hstable : (prefixWord ++ tailWord_6731493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731493).length < 2 ^ (prefixWord ++ tailWord_6731493).sum := by decide
  have hdescent : baseEnd_6731493 < baseStart_6731493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731507 : List Nat := [1, 1, 1, 2, 2, 3, 3, 5, 1, 1, 3]
def baseStart_6731507 : Nat := 118140960795 + 6731507 * 2 ^ 59
def prefixEnd_6731507 : Nat := 4983230072969 + 3 ^ 40 * 6731507 * 2
def baseEnd_6731507 : Nat := 3456498620105099681604869

theorem tailTrace_6731507 : CollatzResearch.WordTrace tailWord_6731507 prefixEnd_6731507 3456498620105099681604869 := by
  unfold tailWord_6731507
  simp only [CollatzResearch.WordTrace]
  refine ⟨245518230423907263712408775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163678820282604842474939183 245518230423907263712408775)
  ·
    refine ⟨368277345635860895568613163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245518230423907263712408775 368277345635860895568613163)
    ·
      refine ⟨552416018453791343352919745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368277345635860895568613163 552416018453791343352919745)
      ·
        refine ⟨414312013840343507514689809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552416018453791343352919745 414312013840343507514689809)
        ·
          refine ⟨310734010380257630636017357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414312013840343507514689809 310734010380257630636017357)
          ·
            refine ⟨116525253892596611488506509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310734010380257630636017357 116525253892596611488506509)
            ·
              refine ⟨43696970209723729308189941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116525253892596611488506509 43696970209723729308189941)
              ·
                refine ⟨4096590957161599622642807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43696970209723729308189941 4096590957161599622642807)
                ·
                  refine ⟨6144886435742399433964211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096590957161599622642807 6144886435742399433964211)
                  ·
                    refine ⟨9217329653613599150946317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6144886435742399433964211 9217329653613599150946317)
                    ·
                      refine ⟨3456498620105099681604869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217329653613599150946317 3456498620105099681604869)
                      ·
                        rfl

theorem cell23_6731507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 1, 1, 3].length) (baseStart_6731507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731507 prefixEnd_6731507 := by exact prefixLift 6731507
  have htrace : WordTrace (prefixWord ++ tailWord_6731507) baseStart_6731507 baseEnd_6731507 := by
    simpa [prefixWord, tailWord_6731507, baseEnd_6731507] using wordTrace_append hprefix tailTrace_6731507
  have hstable : (prefixWord ++ tailWord_6731507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731507).length < 2 ^ (prefixWord ++ tailWord_6731507).sum := by decide
  have hdescent : baseEnd_6731507 < baseStart_6731507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731524 : List Nat := [2, 3, 2, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6731524 : Nat := 118140960795 + 6731524 * 2 ^ 59
def prefixEnd_6731524 : Nat := 4983230072969 + 3 ^ 40 * 6731524 * 2
def baseEnd_6731524 : Nat := 3456507349276226115092291

theorem tailTrace_6731524 : CollatzResearch.WordTrace tailWord_6731524 prefixEnd_6731524 3456507349276226115092291 := by
  unfold tailWord_6731524
  simp only [CollatzResearch.WordTrace]
  refine ⟨122759425232422837807888813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163679233643230450410518417 122759425232422837807888813)
  ·
    refine ⟨46034784462158564177958305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122759425232422837807888813 46034784462158564177958305)
    ·
      refine ⟨34526088346618923133468729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46034784462158564177958305 34526088346618923133468729)
      ·
        refine ⟨25894566259964192350101547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34526088346618923133468729 25894566259964192350101547)
        ·
          refine ⟨38841849389946288525152321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25894566259964192350101547 38841849389946288525152321)
          ·
            refine ⟨29131387042459716393864241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38841849389946288525152321 29131387042459716393864241)
            ·
              refine ⟨21848540281844787295398181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29131387042459716393864241 21848540281844787295398181)
              ·
                refine ⟨4096601302845897617887159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21848540281844787295398181 4096601302845897617887159)
                ·
                  refine ⟨6144901954268846426830739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096601302845897617887159 6144901954268846426830739)
                  ·
                    refine ⟨9217352931403269640246109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6144901954268846426830739 9217352931403269640246109)
                    ·
                      refine ⟨3456507349276226115092291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217352931403269640246109 3456507349276226115092291)
                      ·
                        rfl

theorem cell23_6731524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6731524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731524 prefixEnd_6731524 := by exact prefixLift 6731524
  have htrace : WordTrace (prefixWord ++ tailWord_6731524) baseStart_6731524 baseEnd_6731524 := by
    simpa [prefixWord, tailWord_6731524, baseEnd_6731524] using wordTrace_append hprefix tailTrace_6731524
  have hstable : (prefixWord ++ tailWord_6731524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731524).length < 2 ^ (prefixWord ++ tailWord_6731524).sum := by decide
  have hdescent : baseEnd_6731524 < baseStart_6731524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731553 : List Nat := [1, 2, 3, 2, 1, 4, 1, 9]
def baseStart_6731553 : Nat := 118140960795 + 6731553 * 2 ^ 59
def prefixEnd_6731553 : Nat := 4983230072969 + 3 ^ 40 * 6731553 * 2
def baseEnd_6731553 : Nat := 128019342230192833393691

theorem tailTrace_6731553 : CollatzResearch.WordTrace tailWord_6731553 prefixEnd_6731553 128019342230192833393691 := by
  unfold tailWord_6731553
  simp only [CollatzResearch.WordTrace]
  refine ⟨245519908181740613568583313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163679938787827075712388875 245519908181740613568583313)
  ·
    refine ⟨184139931136305460176437485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245519908181740613568583313 184139931136305460176437485)
    ·
      refine ⟨69052474176114547566164057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184139931136305460176437485 69052474176114547566164057)
      ·
        refine ⟨51789355632085910674623043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69052474176114547566164057 51789355632085910674623043)
        ·
          refine ⟨77684033448128866011934565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51789355632085910674623043 77684033448128866011934565)
          ·
            refine ⟨14565756271524162377237731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77684033448128866011934565 14565756271524162377237731)
            ·
              refine ⟨21848634407286243565856597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14565756271524162377237731 21848634407286243565856597)
              ·
                refine ⟨128019342230192833393691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21848634407286243565856597 128019342230192833393691)
                ·
                  rfl

theorem cell23_6731553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 9].length) (baseStart_6731553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731553 prefixEnd_6731553 := by exact prefixLift 6731553
  have htrace : WordTrace (prefixWord ++ tailWord_6731553) baseStart_6731553 baseEnd_6731553 := by
    simpa [prefixWord, tailWord_6731553, baseEnd_6731553] using wordTrace_append hprefix tailTrace_6731553
  have hstable : (prefixWord ++ tailWord_6731553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731553).length < 2 ^ (prefixWord ++ tailWord_6731553).sum := by decide
  have hdescent : baseEnd_6731553 < baseStart_6731553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731581 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6731581 : Nat := 118140960795 + 6731581 * 2 ^ 59
def prefixEnd_6731581 : Nat := 4983230072969 + 3 ^ 40 * 6731581 * 2
def baseEnd_6731581 : Nat := 3456536617673532392079529

theorem tailTrace_6731581 : CollatzResearch.WordTrace tailWord_6731581 prefixEnd_6731581 3456536617673532392079529 := by
  unfold tailWord_6731581
  simp only [CollatzResearch.WordTrace]
  refine ⟨245520929425639174350602597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163680619617092782900401731 245520929425639174350602597)
  ·
    refine ⟨46035174267307345190737987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245520929425639174350602597 46035174267307345190737987)
    ·
      refine ⟨69052761400961017786106981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46035174267307345190737987 69052761400961017786106981)
      ·
        refine ⟨12947392762680190834895059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69052761400961017786106981 12947392762680190834895059)
        ·
          refine ⟨19421089144020286252342589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12947392762680190834895059 19421089144020286252342589)
          ·
            refine ⟨7282908429007607344628471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19421089144020286252342589 7282908429007607344628471)
            ·
              refine ⟨10924362643511411016942707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282908429007607344628471 10924362643511411016942707)
              ·
                refine ⟨16386543965267116525414061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10924362643511411016942707 16386543965267116525414061)
                ·
                  refine ⟨6144953986975168697030273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16386543965267116525414061 6144953986975168697030273)
                  ·
                    refine ⟨4608715490231376522772705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6144953986975168697030273 4608715490231376522772705)
                    ·
                      refine ⟨3456536617673532392079529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608715490231376522772705 3456536617673532392079529)
                      ·
                        rfl

theorem cell23_6731581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6731581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731581 prefixEnd_6731581 := by exact prefixLift 6731581
  have htrace : WordTrace (prefixWord ++ tailWord_6731581) baseStart_6731581 baseEnd_6731581 := by
    simpa [prefixWord, tailWord_6731581, baseEnd_6731581] using wordTrace_append hprefix tailTrace_6731581
  have hstable : (prefixWord ++ tailWord_6731581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731581).length < 2 ^ (prefixWord ++ tailWord_6731581).sum := by decide
  have hdescent : baseEnd_6731581 < baseStart_6731581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731637 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_6731637 : Nat := 118140960795 + 6731637 * 2 ^ 59
def prefixEnd_6731637 : Nat := 4983230072969 + 3 ^ 40 * 6731637 * 2
def baseEnd_6731637 : Nat := 3456565372590184172979271

theorem tailTrace_6731637 : CollatzResearch.WordTrace tailWord_6731637 prefixEnd_6731637 3456565372590184172979271 := by
  unfold tailWord_6731637
  simp only [CollatzResearch.WordTrace]
  refine ⟨245522971913436295914641165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163681981275624197276427443 245522971913436295914641165)
  ·
    refine ⟨92071114467538610967990437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245522971913436295914641165 92071114467538610967990437)
    ·
      refine ⟨17263333962663489556498207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92071114467538610967990437 17263333962663489556498207)
      ·
        refine ⟨25895000943995234334747311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17263333962663489556498207 25895000943995234334747311)
        ·
          refine ⟨38842501415992851502120967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25895000943995234334747311 38842501415992851502120967)
          ·
            refine ⟨58263752123989277253181451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38842501415992851502120967 58263752123989277253181451)
            ·
              refine ⟨87395628185983915879772177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58263752123989277253181451 87395628185983915879772177)
              ·
                refine ⟨65546721139487936909829133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87395628185983915879772177 65546721139487936909829133)
                ·
                  refine ⟨24580020427307976341185925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65546721139487936909829133 24580020427307976341185925)
                  ·
                    refine ⟨4608753830120245563972361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24580020427307976341185925 4608753830120245563972361)
                    ·
                      refine ⟨3456565372590184172979271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608753830120245563972361 3456565372590184172979271)
                      ·
                        rfl

theorem cell23_6731637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_6731637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731637 prefixEnd_6731637 := by exact prefixLift 6731637
  have htrace : WordTrace (prefixWord ++ tailWord_6731637) baseStart_6731637 baseEnd_6731637 := by
    simpa [prefixWord, tailWord_6731637, baseEnd_6731637] using wordTrace_append hprefix tailTrace_6731637
  have hstable : (prefixWord ++ tailWord_6731637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731637).length < 2 ^ (prefixWord ++ tailWord_6731637).sum := by decide
  have hdescent : baseEnd_6731637 < baseStart_6731637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731643 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 7]
def baseStart_6731643 : Nat := 118140960795 + 6731643 * 2 ^ 59
def prefixEnd_6731643 : Nat := 4983230072969 + 3 ^ 40 * 6731643 * 2
def baseEnd_6731643 : Nat := 384063161497123461056027

theorem tailTrace_6731643 : CollatzResearch.WordTrace tailWord_6731643 prefixEnd_6731643 384063161497123461056027 := by
  unfold tailWord_6731643
  simp only [CollatzResearch.WordTrace]
  refine ⟨245523190751414558939359583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163682127167609705959573055 245523190751414558939359583)
  ·
    refine ⟨368284786127121838409039375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245523190751414558939359583 368284786127121838409039375)
    ·
      refine ⟨552427179190682757613559063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368284786127121838409039375 552427179190682757613559063)
      ·
        refine ⟨828640768786024136420338595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552427179190682757613559063 828640768786024136420338595)
        ·
          refine ⟨1242961153179036204630507893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828640768786024136420338595 1242961153179036204630507893)
          ·
            refine ⟨116527608110534644184110115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1242961153179036204630507893 116527608110534644184110115)
            ·
              refine ⟨174791412165801966276165173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116527608110534644184110115 174791412165801966276165173)
              ·
                refine ⟨16386694890543934338390485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174791412165801966276165173 16386694890543934338390485)
                ·
                  refine ⟨384063161497123461056027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16386694890543934338390485 384063161497123461056027)
                  ·
                    rfl

theorem cell23_6731643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 7].length) (baseStart_6731643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731643 prefixEnd_6731643 := by exact prefixLift 6731643
  have htrace : WordTrace (prefixWord ++ tailWord_6731643) baseStart_6731643 baseEnd_6731643 := by
    simpa [prefixWord, tailWord_6731643, baseEnd_6731643] using wordTrace_append hprefix tailTrace_6731643
  have hstable : (prefixWord ++ tailWord_6731643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731643).length < 2 ^ (prefixWord ++ tailWord_6731643).sum := by decide
  have hdescent : baseEnd_6731643 < baseStart_6731643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731677 : List Nat := [1, 4, 2, 1, 2, 2, 1, 5, 5]
def baseStart_6731677 : Nat := 118140960795 + 6731677 * 2 ^ 59
def prefixEnd_6731677 : Nat := 4983230072969 + 3 ^ 40 * 6731677 * 2
def baseEnd_6731677 : Nat := 384065101312929335164343

theorem tailTrace_6731677 : CollatzResearch.WordTrace tailWord_6731677 prefixEnd_6731677 384065101312929335164343 := by
  unfold tailWord_6731677
  simp only [CollatzResearch.WordTrace]
  refine ⟨245524430833291382746097285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163682953888860921830731523 245524430833291382746097285)
  ·
    refine ⟨46035830781242134264893241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245524430833291382746097285 46035830781242134264893241)
    ·
      refine ⟨34526873085931600698669931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46035830781242134264893241 34526873085931600698669931)
      ·
        refine ⟨51790309628897401048004897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34526873085931600698669931 51790309628897401048004897)
        ·
          refine ⟨38842732221673050786003673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51790309628897401048004897 38842732221673050786003673)
          ·
            refine ⟨29132049166254788089502755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38842732221673050786003673 29132049166254788089502755)
            ·
              refine ⟨43698073749382182134254133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29132049166254788089502755 43698073749382182134254133)
              ·
                refine ⟨4096694414004579575086325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43698073749382182134254133 4096694414004579575086325)
                ·
                  refine ⟨384065101312929335164343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4096694414004579575086325 384065101312929335164343)
                  ·
                    rfl

theorem cell23_6731677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_6731677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731677 prefixEnd_6731677 := by exact prefixLift 6731677
  have htrace : WordTrace (prefixWord ++ tailWord_6731677) baseStart_6731677 baseEnd_6731677 := by
    simpa [prefixWord, tailWord_6731677, baseEnd_6731677] using wordTrace_append hprefix tailTrace_6731677
  have hstable : (prefixWord ++ tailWord_6731677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731677).length < 2 ^ (prefixWord ++ tailWord_6731677).sum := by decide
  have hdescent : baseEnd_6731677 < baseStart_6731677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731687 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_6731687 : Nat := 118140960795 + 6731687 * 2 ^ 59
def prefixEnd_6731687 : Nat := 4983230072969 + 3 ^ 40 * 6731687 * 2
def baseEnd_6731687 : Nat := 3456591046622908977354041

theorem tailTrace_6731687 : CollatzResearch.WordTrace tailWord_6731687 prefixEnd_6731687 3456591046622908977354041 := by
  unfold tailWord_6731687
  simp only [CollatzResearch.WordTrace]
  refine ⟨245524795563255154453961315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163683197042170102969307543 245524795563255154453961315)
  ·
    refine ⟨368287193344882731680941973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245524795563255154453961315 368287193344882731680941973)
    ·
      refine ⟨17263462188041378047544155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 368287193344882731680941973 17263462188041378047544155)
      ·
        refine ⟨25895193282062067071316233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17263462188041378047544155 25895193282062067071316233)
        ·
          refine ⟨19421394961546550303487175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25895193282062067071316233 19421394961546550303487175)
          ·
            refine ⟨29132092442319825455230763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19421394961546550303487175 29132092442319825455230763)
            ·
              refine ⟨43698138663479738182846145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29132092442319825455230763 43698138663479738182846145)
              ·
                refine ⟨32773603997609803637134609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43698138663479738182846145 32773603997609803637134609)
                ·
                  refine ⟨24580202998207352727850957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32773603997609803637134609 24580202998207352727850957)
                  ·
                    refine ⟨9217576124327757272944109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24580202998207352727850957 9217576124327757272944109)
                    ·
                      refine ⟨3456591046622908977354041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217576124327757272944109 3456591046622908977354041)
                      ·
                        rfl

theorem cell23_6731687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_6731687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731687 prefixEnd_6731687 := by exact prefixLift 6731687
  have htrace : WordTrace (prefixWord ++ tailWord_6731687) baseStart_6731687 baseEnd_6731687 := by
    simpa [prefixWord, tailWord_6731687, baseEnd_6731687] using wordTrace_append hprefix tailTrace_6731687
  have hstable : (prefixWord ++ tailWord_6731687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731687).length < 2 ^ (prefixWord ++ tailWord_6731687).sum := by decide
  have hdescent : baseEnd_6731687 < baseStart_6731687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731688 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6731688 : Nat := 118140960795 + 6731688 * 2 ^ 59
def prefixEnd_6731688 : Nat := 4983230072969 + 3 ^ 40 * 6731688 * 2
def baseEnd_6731688 : Nat := 3456591560103563473441537

theorem tailTrace_6731688 : CollatzResearch.WordTrace tailWord_6731688 prefixEnd_6731688 3456591560103563473441537 := by
  unfold tailWord_6731688
  simp only [CollatzResearch.WordTrace]
  refine ⟨122762416018125765812373859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163683221357501021083165145 122762416018125765812373859)
  ·
    refine ⟨184143624027188648718560789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122762416018125765812373859 184143624027188648718560789)
    ·
      refine ⟨8631732376274467908682537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184143624027188648718560789 8631732376274467908682537)
      ·
        refine ⟨6473799282205850931511903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8631732376274467908682537 6473799282205850931511903)
        ·
          refine ⟨9710698923308776397267855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473799282205850931511903 9710698923308776397267855)
          ·
            refine ⟨14566048384963164595901783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710698923308776397267855 14566048384963164595901783)
            ·
              refine ⟨21849072577444746893852675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14566048384963164595901783 21849072577444746893852675)
              ·
                refine ⟨32773608866167120340779013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21849072577444746893852675 32773608866167120340779013)
                ·
                  refine ⟨6145051662406335063896065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32773608866167120340779013 6145051662406335063896065)
                  ·
                    refine ⟨4608788746804751297922049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6145051662406335063896065 4608788746804751297922049)
                    ·
                      refine ⟨3456591560103563473441537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608788746804751297922049 3456591560103563473441537)
                      ·
                        rfl

theorem cell23_6731688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6731688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731688 prefixEnd_6731688 := by exact prefixLift 6731688
  have htrace : WordTrace (prefixWord ++ tailWord_6731688) baseStart_6731688 baseEnd_6731688 := by
    simpa [prefixWord, tailWord_6731688, baseEnd_6731688] using wordTrace_append hprefix tailTrace_6731688
  have hstable : (prefixWord ++ tailWord_6731688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731688).length < 2 ^ (prefixWord ++ tailWord_6731688).sum := by decide
  have hdescent : baseEnd_6731688 < baseStart_6731688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731747 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 3]
def baseStart_6731747 : Nat := 118140960795 + 6731747 * 2 ^ 59
def prefixEnd_6731747 : Nat := 4983230072969 + 3 ^ 40 * 6731747 * 2
def baseEnd_6731747 : Nat := 3456621855462178742603765

theorem tailTrace_6731747 : CollatzResearch.WordTrace tailWord_6731747 prefixEnd_6731747 3456621855462178742603765 := by
  unfold tailWord_6731747
  simp only [CollatzResearch.WordTrace]
  refine ⟨245526983943037784701145495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163684655962025189800763663 245526983943037784701145495)
  ·
    refine ⟨368290475914556677051718243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245526983943037784701145495 368290475914556677051718243)
    ·
      refine ⟨552435713871835015577577365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368290475914556677051718243 552435713871835015577577365)
      ·
        refine ⟨25895424087742266355198939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 552435713871835015577577365 25895424087742266355198939)
        ·
          refine ⟨38843136131613399532798409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25895424087742266355198939 38843136131613399532798409)
          ·
            refine ⟨29132352098710049649598807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38843136131613399532798409 29132352098710049649598807)
            ·
              refine ⟨43698528148065074474398211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29132352098710049649598807 43698528148065074474398211)
              ·
                refine ⟨65547792222097611711597317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43698528148065074474398211 65547792222097611711597317)
                ·
                  refine ⟨12290211041643302195924497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65547792222097611711597317 12290211041643302195924497)
                  ·
                    refine ⟨9217658281232476646943373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12290211041643302195924497 9217658281232476646943373)
                    ·
                      refine ⟨3456621855462178742603765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217658281232476646943373 3456621855462178742603765)
                      ·
                        rfl

theorem cell23_6731747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_6731747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731747 prefixEnd_6731747 := by exact prefixLift 6731747
  have htrace : WordTrace (prefixWord ++ tailWord_6731747) baseStart_6731747 baseEnd_6731747 := by
    simpa [prefixWord, tailWord_6731747, baseEnd_6731747] using wordTrace_append hprefix tailTrace_6731747
  have hstable : (prefixWord ++ tailWord_6731747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731747).length < 2 ^ (prefixWord ++ tailWord_6731747).sum := by decide
  have hdescent : baseEnd_6731747 < baseStart_6731747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731811 : List Nat := [1, 1, 1, 4, 3, 1, 3, 4, 1, 1, 3]
def baseStart_6731811 : Nat := 118140960795 + 6731811 * 2 ^ 59
def prefixEnd_6731811 : Nat := 4983230072969 + 3 ^ 40 * 6731811 * 2
def baseEnd_6731811 : Nat := 3456654718224066492203471

theorem tailTrace_6731811 : CollatzResearch.WordTrace tailWord_6731811 prefixEnd_6731811 3456654718224066492203471 := by
  unfold tailWord_6731811
  simp only [CollatzResearch.WordTrace]
  refine ⟨245529318214805923631475287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163686212143203949087650191 245529318214805923631475287)
  ·
    refine ⟨368293977322208885447212931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245529318214805923631475287 368293977322208885447212931)
    ·
      refine ⟨552440965983313328170819397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368293977322208885447212931 552440965983313328170819397)
      ·
        refine ⟨103582681121871249032028637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 552440965983313328170819397 103582681121871249032028637)
        ·
          refine ⟨38843505420701718387010739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103582681121871249032028637 38843505420701718387010739)
          ·
            refine ⟨58265258131052577580516109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38843505420701718387010739 58265258131052577580516109)
            ·
              refine ⟨21849471799144716592693541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58265258131052577580516109 21849471799144716592693541)
              ·
                refine ⟨4096775962339634361130039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21849471799144716592693541 4096775962339634361130039)
                ·
                  refine ⟨6145163943509451541695059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096775962339634361130039 6145163943509451541695059)
                  ·
                    refine ⟨9217745915264177312542589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145163943509451541695059 9217745915264177312542589)
                    ·
                      refine ⟨3456654718224066492203471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217745915264177312542589 3456654718224066492203471)
                      ·
                        rfl

theorem cell23_6731811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_6731811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731811 prefixEnd_6731811 := by exact prefixLift 6731811
  have htrace : WordTrace (prefixWord ++ tailWord_6731811) baseStart_6731811 baseEnd_6731811 := by
    simpa [prefixWord, tailWord_6731811, baseEnd_6731811] using wordTrace_append hprefix tailTrace_6731811
  have hstable : (prefixWord ++ tailWord_6731811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731811).length < 2 ^ (prefixWord ++ tailWord_6731811).sum := by decide
  have hdescent : baseEnd_6731811 < baseStart_6731811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731828 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_6731828 : Nat := 118140960795 + 6731828 * 2 ^ 59
def prefixEnd_6731828 : Nat := 4983230072969 + 3 ^ 40 * 6731828 * 2
def baseEnd_6731828 : Nat := 3456663447395192925690893

theorem tailTrace_6731828 : CollatzResearch.WordTrace tailWord_6731828 prefixEnd_6731828 3456663447395192925690893 := by
  unfold tailWord_6731828
  simp only [CollatzResearch.WordTrace]
  refine ⟨122764969127872167767422069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163686625503829557023229425 122764969127872167767422069)
  ·
    refine ⟨11509215855738015728195819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122764969127872167767422069 11509215855738015728195819)
    ·
      refine ⟨17263823783607023592293729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11509215855738015728195819 17263823783607023592293729)
      ·
        refine ⟨12947867837705267694220297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17263823783607023592293729 12947867837705267694220297)
        ·
          refine ⟨9710900878278950770665223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12947867837705267694220297 9710900878278950770665223)
          ·
            refine ⟨14566351317418426155997835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710900878278950770665223 14566351317418426155997835)
            ·
              refine ⟨21849526976127639233996753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14566351317418426155997835 21849526976127639233996753)
              ·
                refine ⟨16387145232095729425497565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21849526976127639233996753 16387145232095729425497565)
                ·
                  refine ⟨6145179462035898534561587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16387145232095729425497565 6145179462035898534561587)
                  ·
                    refine ⟨9217769193053847801842381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145179462035898534561587 9217769193053847801842381)
                    ·
                      refine ⟨3456663447395192925690893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217769193053847801842381 3456663447395192925690893)
                      ·
                        rfl

theorem cell23_6731828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_6731828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731828 prefixEnd_6731828 := by exact prefixLift 6731828
  have htrace : WordTrace (prefixWord ++ tailWord_6731828) baseStart_6731828 baseEnd_6731828 := by
    simpa [prefixWord, tailWord_6731828, baseEnd_6731828] using wordTrace_append hprefix tailTrace_6731828
  have hstable : (prefixWord ++ tailWord_6731828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731828).length < 2 ^ (prefixWord ++ tailWord_6731828).sum := by decide
  have hdescent : baseEnd_6731828 < baseStart_6731828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731847 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_6731847 : Nat := 118140960795 + 6731847 * 2 ^ 59
def prefixEnd_6731847 : Nat := 4983230072969 + 3 ^ 40 * 6731847 * 2
def baseEnd_6731847 : Nat := 3456673203527628351353305

theorem tailTrace_6731847 : CollatzResearch.WordTrace tailWord_6731847 prefixEnd_6731847 3456673203527628351353305 := by
  unfold tailWord_6731847
  simp only [CollatzResearch.WordTrace]
  refine ⟨245530631242675501779785795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163687087495117001186523863 245530631242675501779785795)
  ·
    refine ⟨368295946864013252669678693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245530631242675501779785795 368295946864013252669678693)
    ·
      refine ⟨69055490037002484875564755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368295946864013252669678693 69055490037002484875564755)
      ·
        refine ⟨103583235055503727313347133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69055490037002484875564755 103583235055503727313347133)
        ·
          refine ⟨38843713145813897742505175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103583235055503727313347133 38843713145813897742505175)
          ·
            refine ⟨58265569718720846613757763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38843713145813897742505175 58265569718720846613757763)
            ·
              refine ⟨87398354578081269920636645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58265569718720846613757763 87398354578081269920636645)
              ·
                refine ⟨16387191483390238110119371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87398354578081269920636645 16387191483390238110119371)
                ·
                  refine ⟨24580787225085357165179057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16387191483390238110119371 24580787225085357165179057)
                  ·
                    refine ⟨18435590418814017873884293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24580787225085357165179057 18435590418814017873884293)
                    ·
                      refine ⟨3456673203527628351353305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18435590418814017873884293 3456673203527628351353305)
                      ·
                        rfl

theorem cell23_6731847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_6731847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731847 prefixEnd_6731847 := by exact prefixLift 6731847
  have htrace : WordTrace (prefixWord ++ tailWord_6731847) baseStart_6731847 baseEnd_6731847 := by
    simpa [prefixWord, tailWord_6731847, baseEnd_6731847] using wordTrace_append hprefix tailTrace_6731847
  have hstable : (prefixWord ++ tailWord_6731847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731847).length < 2 ^ (prefixWord ++ tailWord_6731847).sum := by decide
  have hdescent : baseEnd_6731847 < baseStart_6731847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731861 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_6731861 : Nat := 118140960795 + 6731861 * 2 ^ 59
def prefixEnd_6731861 : Nat := 4983230072969 + 3 ^ 40 * 6731861 * 2
def baseEnd_6731861 : Nat := 1152226797418930432192747

theorem tailTrace_6731861 : CollatzResearch.WordTrace tailWord_6731861 prefixEnd_6731861 1152226797418930432192747 := by
  unfold tailWord_6731861
  simp only [CollatzResearch.WordTrace]
  refine ⟨245531141864624782170795437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163687427909749854780530291 245531141864624782170795437)
  ·
    refine ⟨92074178199234293314048289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245531141864624782170795437 92074178199234293314048289)
    ·
      refine ⟨69055633649425719985536217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92074178199234293314048289 69055633649425719985536217)
      ·
        refine ⟨51791725237069289989152163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69055633649425719985536217 51791725237069289989152163)
        ·
          refine ⟨77687587855603934983728245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51791725237069289989152163 77687587855603934983728245)
          ·
            refine ⟨7283211361462868904724523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77687587855603934983728245 7283211361462868904724523)
            ·
              refine ⟨10924817042194303357086785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7283211361462868904724523 10924817042194303357086785)
              ·
                refine ⟨8193612781645727517815089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10924817042194303357086785 8193612781645727517815089)
                ·
                  refine ⟨6145209586234295638361317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8193612781645727517815089 6145209586234295638361317)
                  ·
                    refine ⟨1152226797418930432192747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6145209586234295638361317 1152226797418930432192747)
                    ·
                      rfl

theorem cell23_6731861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_6731861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731861 prefixEnd_6731861 := by exact prefixLift 6731861
  have htrace : WordTrace (prefixWord ++ tailWord_6731861) baseStart_6731861 baseEnd_6731861 := by
    simpa [prefixWord, tailWord_6731861, baseEnd_6731861] using wordTrace_append hprefix tailTrace_6731861
  have hstable : (prefixWord ++ tailWord_6731861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731861).length < 2 ^ (prefixWord ++ tailWord_6731861).sum := by decide
  have hdescent : baseEnd_6731861 < baseStart_6731861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731868 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_6731868 : Nat := 118140960795 + 6731868 * 2 ^ 59
def prefixEnd_6731868 : Nat := 4983230072969 + 3 ^ 40 * 6731868 * 2
def baseEnd_6731868 : Nat := 3456683986621372769190709

theorem tailTrace_6731868 : CollatzResearch.WordTrace tailWord_6731868 prefixEnd_6731868 3456683986621372769190709 := by
  unfold tailWord_6731868
  simp only [CollatzResearch.WordTrace]
  refine ⟨122765698587799711183150129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163687598117066281577533505 122765698587799711183150129)
  ·
    refine ⟨92074273940849783387362597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122765698587799711183150129 92074273940849783387362597)
    ·
      refine ⟨17263926363909334385130487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92074273940849783387362597 17263926363909334385130487)
      ·
        refine ⟨25895889545864001577695731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17263926363909334385130487 25895889545864001577695731)
        ·
          refine ⟨38843834318796002366543597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25895889545864001577695731 38843834318796002366543597)
          ·
            refine ⟨14566437869548500887453849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38843834318796002366543597 14566437869548500887453849)
            ·
              refine ⟨10924828402161375665590387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14566437869548500887453849 10924828402161375665590387)
              ·
                refine ⟨16387242603242063498385581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10924828402161375665590387 16387242603242063498385581)
                ·
                  refine ⟨6145215976215773811894593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16387242603242063498385581 6145215976215773811894593)
                  ·
                    refine ⟨4608911982161830358920945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6145215976215773811894593 4608911982161830358920945)
                    ·
                      refine ⟨3456683986621372769190709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608911982161830358920945 3456683986621372769190709)
                      ·
                        rfl

theorem cell23_6731868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_6731868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731868 prefixEnd_6731868 := by exact prefixLift 6731868
  have htrace : WordTrace (prefixWord ++ tailWord_6731868) baseStart_6731868 baseEnd_6731868 := by
    simpa [prefixWord, tailWord_6731868, baseEnd_6731868] using wordTrace_append hprefix tailTrace_6731868
  have hstable : (prefixWord ++ tailWord_6731868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731868).length < 2 ^ (prefixWord ++ tailWord_6731868).sum := by decide
  have hdescent : baseEnd_6731868 < baseStart_6731868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731884 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_6731884 : Nat := 118140960795 + 6731884 * 2 ^ 59
def prefixEnd_6731884 : Nat := 4983230072969 + 3 ^ 40 * 6731884 * 2
def baseEnd_6731884 : Nat := 3456692202311844706590635

theorem tailTrace_6731884 : CollatzResearch.WordTrace tailWord_6731884 prefixEnd_6731884 3456692202311844706590635 := by
  unfold tailWord_6731884
  simp only [CollatzResearch.WordTrace]
  refine ⟨122765990371770728549441353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163687987162360971399255137 122765990371770728549441353)
  ·
    refine ⟨92074492778828046412081015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122765990371770728549441353 92074492778828046412081015)
    ·
      refine ⟨138111739168242069618121523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92074492778828046412081015 138111739168242069618121523)
      ·
        refine ⟨207167608752363104427182285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138111739168242069618121523 207167608752363104427182285)
        ·
          refine ⟨77687853282136164160193357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207167608752363104427182285 77687853282136164160193357)
          ·
            refine ⟨29132944980801061560072509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77687853282136164160193357 29132944980801061560072509)
            ·
              refine ⟨10924854367800398085027191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29132944980801061560072509 10924854367800398085027191)
              ·
                refine ⟨16387281551700597127540787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10924854367800398085027191 16387281551700597127540787)
                ·
                  refine ⟨24580922327550895691311181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16387281551700597127540787 24580922327550895691311181)
                  ·
                    refine ⟨9217845872831585884241693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24580922327550895691311181 9217845872831585884241693)
                    ·
                      refine ⟨3456692202311844706590635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217845872831585884241693 3456692202311844706590635)
                      ·
                        rfl

theorem cell23_6731884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_6731884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731884 prefixEnd_6731884 := by exact prefixLift 6731884
  have htrace : WordTrace (prefixWord ++ tailWord_6731884) baseStart_6731884 baseEnd_6731884 := by
    simpa [prefixWord, tailWord_6731884, baseEnd_6731884] using wordTrace_append hprefix tailTrace_6731884
  have hstable : (prefixWord ++ tailWord_6731884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731884).length < 2 ^ (prefixWord ++ tailWord_6731884).sum := by decide
  have hdescent : baseEnd_6731884 < baseStart_6731884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731897 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_6731897 : Nat := 118140960795 + 6731897 * 2 ^ 59
def prefixEnd_6731897 : Nat := 4983230072969 + 3 ^ 40 * 6731897 * 2
def baseEnd_6731897 : Nat := 3456698877560353155728075

theorem tailTrace_6731897 : CollatzResearch.WordTrace tailWord_6731897 prefixEnd_6731897 3456698877560353155728075 := by
  unfold tailWord_6731897
  simp only [CollatzResearch.WordTrace]
  refine ⟨245532454892494360319105945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163688303261662906879403963 245532454892494360319105945)
  ·
    refine ⟨184149341169370770239329459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245532454892494360319105945 184149341169370770239329459)
    ·
      refine ⟨276224011754056155358994189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184149341169370770239329459 276224011754056155358994189)
      ·
        refine ⟨103584004407771058259622821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276224011754056155358994189 103584004407771058259622821)
        ·
          refine ⟨19422000826457073423679279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103584004407771058259622821 19422000826457073423679279)
          ·
            refine ⟨29133001239685610135518919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19422000826457073423679279 29133001239685610135518919)
            ·
              refine ⟨43699501859528415203278379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29133001239685610135518919 43699501859528415203278379)
              ·
                refine ⟨65549252789292622804917569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43699501859528415203278379 65549252789292622804917569)
                ·
                  refine ⟨49161939591969467103688177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65549252789292622804917569 49161939591969467103688177)
                  ·
                    refine ⟨36871454693977100327766133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49161939591969467103688177 36871454693977100327766133)
                    ·
                      refine ⟨3456698877560353155728075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36871454693977100327766133 3456698877560353155728075)
                      ·
                        rfl

theorem cell23_6731897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_6731897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731897 prefixEnd_6731897 := by exact prefixLift 6731897
  have htrace : WordTrace (prefixWord ++ tailWord_6731897) baseStart_6731897 baseEnd_6731897 := by
    simpa [prefixWord, tailWord_6731897, baseEnd_6731897] using wordTrace_append hprefix tailTrace_6731897
  have hstable : (prefixWord ++ tailWord_6731897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731897).length < 2 ^ (prefixWord ++ tailWord_6731897).sum := by decide
  have hdescent : baseEnd_6731897 < baseStart_6731897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731911 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_6731911 : Nat := 118140960795 + 6731911 * 2 ^ 59
def prefixEnd_6731911 : Nat := 4983230072969 + 3 ^ 40 * 6731911 * 2
def baseEnd_6731911 : Nat := 3456706066289516100953011

theorem tailTrace_6731911 : CollatzResearch.WordTrace tailWord_6731911 prefixEnd_6731911 3456706066289516100953011 := by
  unfold tailWord_6731911
  simp only [CollatzResearch.WordTrace]
  refine ⟨245532965514443640710115587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163688643676295760473410391 245532965514443640710115587)
  ·
    refine ⟨368299448271665461065173381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245532965514443640710115587 368299448271665461065173381)
    ·
      refine ⟨69056146550937273949720009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368299448271665461065173381 69056146550937273949720009)
      ·
        refine ⟨51792109913202955462290007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69056146550937273949720009 51792109913202955462290007)
        ·
          refine ⟨77688164869804433193435011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51792109913202955462290007 77688164869804433193435011)
          ·
            refine ⟨116532247304706649790152517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77688164869804433193435011 116532247304706649790152517)
            ·
              refine ⟨21849796369632496835653597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116532247304706649790152517 21849796369632496835653597)
              ·
                refine ⟨8193673638612186313370099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21849796369632496835653597 8193673638612186313370099)
                ·
                  refine ⟨12290510457918279470055149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8193673638612186313370099 12290510457918279470055149)
                  ·
                    refine ⟨4608941421719354801270681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12290510457918279470055149 4608941421719354801270681)
                    ·
                      refine ⟨3456706066289516100953011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4608941421719354801270681 3456706066289516100953011)
                      ·
                        rfl

theorem cell23_6731911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_6731911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731911 prefixEnd_6731911 := by exact prefixLift 6731911
  have htrace : WordTrace (prefixWord ++ tailWord_6731911) baseStart_6731911 baseEnd_6731911 := by
    simpa [prefixWord, tailWord_6731911, baseEnd_6731911] using wordTrace_append hprefix tailTrace_6731911
  have hstable : (prefixWord ++ tailWord_6731911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731911).length < 2 ^ (prefixWord ++ tailWord_6731911).sum := by decide
  have hdescent : baseEnd_6731911 < baseStart_6731911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731935 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6731935 : Nat := 118140960795 + 6731935 * 2 ^ 59
def prefixEnd_6731935 : Nat := 4983230072969 + 3 ^ 40 * 6731935 * 2
def baseEnd_6731935 : Nat := 3456718389825224007052901

theorem tailTrace_6731935 : CollatzResearch.WordTrace tailWord_6731935 prefixEnd_6731935 3456718389825224007052901 := by
  unfold tailWord_6731935
  simp only [CollatzResearch.WordTrace]
  refine ⟨245533840866356692808989259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163689227244237795205992839 245533840866356692808989259)
  ·
    refine ⟨368300761299535039213483889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245533840866356692808989259 368300761299535039213483889)
    ·
      refine ⟨276225570974651279410112917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368300761299535039213483889 276225570974651279410112917)
      ·
        refine ⟨12948073639436778722349043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 276225570974651279410112917 12948073639436778722349043)
        ·
          refine ⟨19422110459155168083523565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12948073639436778722349043 19422110459155168083523565)
          ·
            refine ⟨7283291422183188031321337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19422110459155168083523565 7283291422183188031321337)
            ·
              refine ⟨5462468566637391023491003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7283291422183188031321337 5462468566637391023491003)
              ·
                refine ⟨8193702849956086535236505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462468566637391023491003 8193702849956086535236505)
                ·
                  refine ⟨6145277137467064901427379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8193702849956086535236505 6145277137467064901427379)
                  ·
                    refine ⟨9217915706200597352141069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145277137467064901427379 9217915706200597352141069)
                    ·
                      refine ⟨3456718389825224007052901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9217915706200597352141069 3456718389825224007052901)
                      ·
                        rfl

theorem cell23_6731935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6731935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731935 prefixEnd_6731935 := by exact prefixLift 6731935
  have htrace : WordTrace (prefixWord ++ tailWord_6731935) baseStart_6731935 baseEnd_6731935 := by
    simpa [prefixWord, tailWord_6731935, baseEnd_6731935] using wordTrace_append hprefix tailTrace_6731935
  have hstable : (prefixWord ++ tailWord_6731935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731935).length < 2 ^ (prefixWord ++ tailWord_6731935).sum := by decide
  have hdescent : baseEnd_6731935 < baseStart_6731935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6731977 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 4, 5]
def baseStart_6731977 : Nat := 118140960795 + 6731977 * 2 ^ 59
def prefixEnd_6731977 : Nat := 4983230072969 + 3 ^ 40 * 6731977 * 2
def baseEnd_6731977 : Nat := 1152246652004237614242569

theorem tailTrace_6731977 : CollatzResearch.WordTrace tailWord_6731977 prefixEnd_6731977 1152246652004237614242569 := by
  unfold tailWord_6731977
  simp only [CollatzResearch.WordTrace]
  refine ⟨245535372732204533982018185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163690248488136355988012123 245535372732204533982018185)
  ·
    refine ⟨184151529549153400486513639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245535372732204533982018185 184151529549153400486513639)
    ·
      refine ⟨276227294323730100729770459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184151529549153400486513639 276227294323730100729770459)
      ·
        refine ⟨414340941485595151094655689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276227294323730100729770459 414340941485595151094655689)
        ·
          refine ⟨310755706114196363320991767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414340941485595151094655689 310755706114196363320991767)
          ·
            refine ⟨466133559171294544981487651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310755706114196363320991767 466133559171294544981487651)
            ·
              refine ⟨699200338756941817472231477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466133559171294544981487651 699200338756941817472231477)
              ·
                refine ⟨65550031758463295388021701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 699200338756941817472231477 65550031758463295388021701)
                ·
                  refine ⟨12290630954711867885254069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65550031758463295388021701 12290630954711867885254069)
                  ·
                    refine ⟨1152246652004237614242569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12290630954711867885254069 1152246652004237614242569)
                    ·
                      rfl

theorem cell23_6731977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_6731977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6731977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6731977 prefixEnd_6731977 := by exact prefixLift 6731977
  have htrace : WordTrace (prefixWord ++ tailWord_6731977) baseStart_6731977 baseEnd_6731977 := by
    simpa [prefixWord, tailWord_6731977, baseEnd_6731977] using wordTrace_append hprefix tailTrace_6731977
  have hstable : (prefixWord ++ tailWord_6731977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6731977).length < 2 ^ (prefixWord ++ tailWord_6731977).sum := by decide
  have hdescent : baseEnd_6731977 < baseStart_6731977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6731977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732027 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4]
def baseStart_6732027 : Nat := 118140960795 + 6732027 * 2 ^ 59
def prefixEnd_6732027 : Nat := 4983230072969 + 3 ^ 40 * 6732027 * 2
def baseEnd_6732027 : Nat := 3456765630045437647102477

theorem tailTrace_6732027 : CollatzResearch.WordTrace tailWord_6732027 prefixEnd_6732027 3456765630045437647102477 := by
  unfold tailWord_6732027
  simp only [CollatzResearch.WordTrace]
  refine ⟨245537196382023392521338335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163691464254682261680892223 245537196382023392521338335)
  ·
    refine ⟨368305794573035088782007503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245537196382023392521338335 368305794573035088782007503)
    ·
      refine ⟨552458691859552633173011255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368305794573035088782007503 552458691859552633173011255)
      ·
        refine ⟨828688037789328949759516883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552458691859552633173011255 828688037789328949759516883)
        ·
          refine ⟨1243032056683993424639275325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828688037789328949759516883 1243032056683993424639275325)
          ·
            refine ⟨466137021256497534239728247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1243032056683993424639275325 466137021256497534239728247)
            ·
              refine ⟨699205531884746301359592371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466137021256497534239728247 699205531884746301359592371)
              ·
                refine ⟨1048808297827119452039388557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699205531884746301359592371 1048808297827119452039388557)
                ·
                  refine ⟨393303111685169794514770709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1048808297827119452039388557 393303111685169794514770709)
                  ·
                    refine ⟨18436083360242334117879877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 393303111685169794514770709 18436083360242334117879877)
                    ·
                      refine ⟨3456765630045437647102477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18436083360242334117879877 3456765630045437647102477)
                      ·
                        rfl

theorem cell23_6732027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 4].length) (baseStart_6732027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732027 prefixEnd_6732027 := by exact prefixLift 6732027
  have htrace : WordTrace (prefixWord ++ tailWord_6732027) baseStart_6732027 baseEnd_6732027 := by
    simpa [prefixWord, tailWord_6732027, baseEnd_6732027] using wordTrace_append hprefix tailTrace_6732027
  have hstable : (prefixWord ++ tailWord_6732027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732027).length < 2 ^ (prefixWord ++ tailWord_6732027).sum := by decide
  have hdescent : baseEnd_6732027 < baseStart_6732027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732041 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 3, 4]
def baseStart_6732041 : Nat := 118140960795 + 6732041 * 2 ^ 59
def prefixEnd_6732041 : Nat := 4983230072969 + 3 ^ 40 * 6732041 * 2
def baseEnd_6732041 : Nat := 1152257606258200197442471

theorem tailTrace_6732041 : CollatzResearch.WordTrace tailWord_6732041 prefixEnd_6732041 1152257606258200197442471 := by
  unfold tailWord_6732041
  simp only [CollatzResearch.WordTrace]
  refine ⟨245537707003972672912347977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163691804669315115274898651 245537707003972672912347977)
  ·
    refine ⟨184153280252979504684260983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245537707003972672912347977 184153280252979504684260983)
    ·
      refine ⟨276229920379469257026391475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184153280252979504684260983 276229920379469257026391475)
      ·
        refine ⟨414344880569203885539587213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276229920379469257026391475 414344880569203885539587213)
        ·
          refine ⟨155379330213451457077345205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414344880569203885539587213 155379330213451457077345205)
          ·
            refine ⟨14566812207511074101001113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155379330213451457077345205 14566812207511074101001113)
            ·
              refine ⟨10925109155633305575750835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14566812207511074101001113 10925109155633305575750835)
              ·
                refine ⟨16387663733449958363626253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10925109155633305575750835 16387663733449958363626253)
                ·
                  refine ⟨6145373900043734386359845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16387663733449958363626253 6145373900043734386359845)
                  ·
                    refine ⟨1152257606258200197442471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6145373900043734386359845 1152257606258200197442471)
                    ·
                      rfl

theorem cell23_6732041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_6732041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732041 prefixEnd_6732041 := by exact prefixLift 6732041
  have htrace : WordTrace (prefixWord ++ tailWord_6732041) baseStart_6732041 baseEnd_6732041 := by
    simpa [prefixWord, tailWord_6732041, baseEnd_6732041] using wordTrace_append hprefix tailTrace_6732041
  have hstable : (prefixWord ++ tailWord_6732041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732041).length < 2 ^ (prefixWord ++ tailWord_6732041).sum := by decide
  have hdescent : baseEnd_6732041 < baseStart_6732041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732149 : List Nat := [1, 3, 4, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_6732149 : Nat := 118140960795 + 6732149 * 2 ^ 59
def prefixEnd_6732149 : Nat := 4983230072969 + 3 ^ 40 * 6732149 * 2
def baseEnd_6732149 : Nat := 3456828274685286169776917

theorem tailTrace_6732149 : CollatzResearch.WordTrace tailWord_6732149 prefixEnd_6732149 3456828274685286169776917 := by
  unfold tailWord_6732149
  simp only [CollatzResearch.WordTrace]
  refine ⟨245541646087581407357279501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163694430725054271571519667 245541646087581407357279501)
  ·
    refine ⟨92078117282843027758979813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245541646087581407357279501 92078117282843027758979813)
    ·
      refine ⟨17264646990533067704808715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92078117282843027758979813 17264646990533067704808715)
      ·
        refine ⟨25896970485799601557213073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17264646990533067704808715 25896970485799601557213073)
        ·
          refine ⟨19422727864349701167909805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25896970485799601557213073 19422727864349701167909805)
          ·
            refine ⟨7283522949131137937966177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19422727864349701167909805 7283522949131137937966177)
            ·
              refine ⟨5462642211848353453474633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7283522949131137937966177 5462642211848353453474633)
              ·
                refine ⟨4096981658886265090105975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5462642211848353453474633 4096981658886265090105975)
                ·
                  refine ⟨6145472488329397635158963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096981658886265090105975 6145472488329397635158963)
                  ·
                    refine ⟨9218208732494096452738445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145472488329397635158963 9218208732494096452738445)
                    ·
                      refine ⟨3456828274685286169776917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9218208732494096452738445 3456828274685286169776917)
                      ·
                        rfl

theorem cell23_6732149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_6732149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732149 prefixEnd_6732149 := by exact prefixLift 6732149
  have htrace : WordTrace (prefixWord ++ tailWord_6732149) baseStart_6732149 baseEnd_6732149 := by
    simpa [prefixWord, tailWord_6732149, baseEnd_6732149] using wordTrace_append hprefix tailTrace_6732149
  have hstable : (prefixWord ++ tailWord_6732149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732149).length < 2 ^ (prefixWord ++ tailWord_6732149).sum := by decide
  have hdescent : baseEnd_6732149 < baseStart_6732149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732161 : List Nat := [1, 2, 4, 3, 1, 1, 3, 8]
def baseStart_6732161 : Nat := 118140960795 + 6732161 * 2 ^ 59
def prefixEnd_6732161 : Nat := 4983230072969 + 3 ^ 40 * 6732161 * 2
def baseEnd_6732161 : Nat := 128030905053820004549143

theorem tailTrace_6732161 : CollatzResearch.WordTrace tailWord_6732161 prefixEnd_6732161 128030905053820004549143 := by
  unfold tailWord_6732161
  simp only [CollatzResearch.WordTrace]
  refine ⟨245542083763537933406716337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163694722509025288937810891 245542083763537933406716337)
  ·
    refine ⟨184156562822653450055037253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245542083763537933406716337 184156562822653450055037253)
    ·
      refine ⟨34529355529247521885319485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184156562822653450055037253 34529355529247521885319485)
      ·
        refine ⟨12948508323467820706994807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34529355529247521885319485 12948508323467820706994807)
        ·
          refine ⟨19422762485201731060492211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12948508323467820706994807 19422762485201731060492211)
          ·
            refine ⟨29134143727802596590738317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19422762485201731060492211 29134143727802596590738317)
            ·
              refine ⟨10925303897925973721526869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29134143727802596590738317 10925303897925973721526869)
              ·
                refine ⟨128030905053820004549143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10925303897925973721526869 128030905053820004549143)
                ·
                  rfl

theorem cell23_6732161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 8].length) (baseStart_6732161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732161 prefixEnd_6732161 := by exact prefixLift 6732161
  have htrace : WordTrace (prefixWord ++ tailWord_6732161) baseStart_6732161 baseEnd_6732161 := by
    simpa [prefixWord, tailWord_6732161, baseEnd_6732161] using wordTrace_append hprefix tailTrace_6732161
  have hstable : (prefixWord ++ tailWord_6732161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732161).length < 2 ^ (prefixWord ++ tailWord_6732161).sum := by decide
  have hdescent : baseEnd_6732161 < baseStart_6732161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732171 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 3]
def baseStart_6732171 : Nat := 118140960795 + 6732171 * 2 ^ 59
def prefixEnd_6732171 : Nat := 4983230072969 + 3 ^ 40 * 6732171 * 2
def baseEnd_6732171 : Nat := 3456839571259685083701815

theorem tailTrace_6732171 : CollatzResearch.WordTrace tailWord_6732171 prefixEnd_6732171 3456839571259685083701815 := by
  unfold tailWord_6732171
  simp only [CollatzResearch.WordTrace]
  refine ⟨245542448493501705114580367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163694965662334470076386911 245542448493501705114580367)
  ·
    refine ⟨368313672740252557671870551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245542448493501705114580367 368313672740252557671870551)
    ·
      refine ⟨552470509110378836507805827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368313672740252557671870551 552470509110378836507805827)
      ·
        refine ⟨828705763665568254761708741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552470509110378836507805827 828705763665568254761708741)
        ·
          refine ⟨155382330687294047767820389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 828705763665568254761708741 155382330687294047767820389)
          ·
            refine ⟨29134187003867633956466323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155382330687294047767820389 29134187003867633956466323)
            ·
              refine ⟨43701280505801450934699485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29134187003867633956466323 43701280505801450934699485)
              ·
                refine ⟨16387980189675544100512307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43701280505801450934699485 16387980189675544100512307)
                ·
                  refine ⟨24581970284513316150768461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16387980189675544100512307 24581970284513316150768461)
                  ·
                    refine ⟨9218238856692493556538173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24581970284513316150768461 9218238856692493556538173)
                    ·
                      refine ⟨3456839571259685083701815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9218238856692493556538173 3456839571259685083701815)
                      ·
                        rfl

theorem cell23_6732171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 3].length) (baseStart_6732171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732171 prefixEnd_6732171 := by exact prefixLift 6732171
  have htrace : WordTrace (prefixWord ++ tailWord_6732171) baseStart_6732171 baseEnd_6732171 := by
    simpa [prefixWord, tailWord_6732171, baseEnd_6732171] using wordTrace_append hprefix tailTrace_6732171
  have hstable : (prefixWord ++ tailWord_6732171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732171).length < 2 ^ (prefixWord ++ tailWord_6732171).sum := by decide
  have hdescent : baseEnd_6732171 < baseStart_6732171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732189 : List Nat := [1, 4, 2, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_6732189 : Nat := 118140960795 + 6732189 * 2 ^ 59
def prefixEnd_6732189 : Nat := 4983230072969 + 3 ^ 40 * 6732189 * 2
def baseEnd_6732189 : Nat := 3456848813911466013276733

theorem tailTrace_6732189 : CollatzResearch.WordTrace tailWord_6732189 prefixEnd_6732189 3456848813911466013276733 := by
  unfold tailWord_6732189
  simp only [CollatzResearch.WordTrace]
  refine ⟨245543105007436494188735621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163695403338290996125823747 245543105007436494188735621)
  ·
    refine ⟨46039332188894342660387929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245543105007436494188735621 46039332188894342660387929)
    ·
      refine ⟨34529499141670756995290947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46039332188894342660387929 34529499141670756995290947)
      ·
        refine ⟨51794248712506135492936421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34529499141670756995290947 51794248712506135492936421)
        ·
          refine ⟨9711421633594900404925579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51794248712506135492936421 9711421633594900404925579)
          ·
            refine ⟨14567132450392350607388369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9711421633594900404925579 14567132450392350607388369)
            ·
              refine ⟨10925349337794262955541277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14567132450392350607388369 10925349337794262955541277)
              ·
                refine ⟨4097006001672848608327979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10925349337794262955541277 4097006001672848608327979)
                ·
                  refine ⟨6145509002509272912491969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097006001672848608327979 6145509002509272912491969)
                  ·
                    refine ⟨4609131751881954684368977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6145509002509272912491969 4609131751881954684368977)
                    ·
                      refine ⟨3456848813911466013276733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4609131751881954684368977 3456848813911466013276733)
                      ·
                        rfl

theorem cell23_6732189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_6732189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732189 prefixEnd_6732189 := by exact prefixLift 6732189
  have htrace : WordTrace (prefixWord ++ tailWord_6732189) baseStart_6732189 baseEnd_6732189 := by
    simpa [prefixWord, tailWord_6732189, baseEnd_6732189] using wordTrace_append hprefix tailTrace_6732189
  have hstable : (prefixWord ++ tailWord_6732189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732189).length < 2 ^ (prefixWord ++ tailWord_6732189).sum := by decide
  have hdescent : baseEnd_6732189 < baseStart_6732189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732211 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 8, 2]
def baseStart_6732211 : Nat := 118140960795 + 6732211 * 2 ^ 59
def prefixEnd_6732211 : Nat := 4983230072969 + 3 ^ 40 * 6732211 * 2
def baseEnd_6732211 : Nat := 3456860110485864927201631

theorem tailTrace_6732211 : CollatzResearch.WordTrace tailWord_6732211 prefixEnd_6732211 3456860110485864927201631 := by
  unfold tailWord_6732211
  simp only [CollatzResearch.WordTrace]
  refine ⟨245543907413356791946036487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163695938275571194630690991 245543907413356791946036487)
  ·
    refine ⟨368315861120035187919054731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245543907413356791946036487 368315861120035187919054731)
    ·
      refine ⟨552473791680052781878582097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368315861120035187919054731 552473791680052781878582097)
      ·
        refine ⟨414355343760039586408936573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552473791680052781878582097 414355343760039586408936573)
        ·
          refine ⟨155383253910014844903351215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414355343760039586408936573 155383253910014844903351215)
          ·
            refine ⟨233074880865022267355026823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155383253910014844903351215 233074880865022267355026823)
            ·
              refine ⟨349612321297533401032540235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233074880865022267355026823 349612321297533401032540235)
              ·
                refine ⟨524418481946300101548810353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349612321297533401032540235 524418481946300101548810353)
                ·
                  refine ⟨393313861459725076161607765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524418481946300101548810353 393313861459725076161607765)
                  ·
                    refine ⟨4609146813981153236268841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 393313861459725076161607765 4609146813981153236268841)
                    ·
                      refine ⟨3456860110485864927201631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4609146813981153236268841 3456860110485864927201631)
                      ·
                        rfl

theorem cell23_6732211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8, 2].length) (baseStart_6732211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732211 prefixEnd_6732211 := by exact prefixLift 6732211
  have htrace : WordTrace (prefixWord ++ tailWord_6732211) baseStart_6732211 baseEnd_6732211 := by
    simpa [prefixWord, tailWord_6732211, baseEnd_6732211] using wordTrace_append hprefix tailTrace_6732211
  have hstable : (prefixWord ++ tailWord_6732211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732211).length < 2 ^ (prefixWord ++ tailWord_6732211).sum := by decide
  have hdescent : baseEnd_6732211 < baseStart_6732211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732221 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_6732221 : Nat := 118140960795 + 6732221 * 2 ^ 59
def prefixEnd_6732221 : Nat := 4983230072969 + 3 ^ 40 * 6732221 * 2
def baseEnd_6732221 : Nat := 1152288415097469962692195

theorem tailTrace_6732221 : CollatzResearch.WordTrace tailWord_6732221 prefixEnd_6732221 1152288415097469962692195 := by
  unfold tailWord_6732221
  simp only [CollatzResearch.WordTrace]
  refine ⟨245544272143320563653900517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163696181428880375769267011 245544272143320563653900517)
  ·
    refine ⟨46039551026872605685106347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245544272143320563653900517 46039551026872605685106347)
    ·
      refine ⟨69059326540308908527659521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46039551026872605685106347 69059326540308908527659521)
      ·
        refine ⟨51794494905231681395744641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69059326540308908527659521 51794494905231681395744641)
        ·
          refine ⟨38845871178923761046808481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51794494905231681395744641 38845871178923761046808481)
          ·
            refine ⟨29134403384192820785106361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38845871178923761046808481 29134403384192820785106361)
            ·
              refine ⟨21850802538144615588829771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29134403384192820785106361 21850802538144615588829771)
              ·
                refine ⟨32776203807216923383244657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21850802538144615588829771 32776203807216923383244657)
                ·
                  refine ⟨24582152855412692537433493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32776203807216923383244657 24582152855412692537433493)
                  ·
                    refine ⟨1152288415097469962692195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24582152855412692537433493 1152288415097469962692195)
                    ·
                      rfl

theorem cell23_6732221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_6732221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732221 prefixEnd_6732221 := by exact prefixLift 6732221
  have htrace : WordTrace (prefixWord ++ tailWord_6732221) baseStart_6732221 baseEnd_6732221 := by
    simpa [prefixWord, tailWord_6732221, baseEnd_6732221] using wordTrace_append hprefix tailTrace_6732221
  have hstable : (prefixWord ++ tailWord_6732221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732221).length < 2 ^ (prefixWord ++ tailWord_6732221).sum := by decide
  have hdescent : baseEnd_6732221 < baseStart_6732221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732245 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6732245 : Nat := 118140960795 + 6732245 * 2 ^ 59
def prefixEnd_6732245 : Nat := 4983230072969 + 3 ^ 40 * 6732245 * 2
def baseEnd_6732245 : Nat := 3456877568828117794176475

theorem tailTrace_6732245 : CollatzResearch.WordTrace tailWord_6732245 prefixEnd_6732245 3456877568828117794176475 := by
  unfold tailWord_6732245
  simp only [CollatzResearch.WordTrace]
  refine ⟨245545147495233615752774189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163696764996822410501849459 245545147495233615752774189)
  ·
    refine ⟨92079430310712605907290321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245545147495233615752774189 92079430310712605907290321)
    ·
      refine ⟨69059572733034454430467741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92079430310712605907290321 69059572733034454430467741)
      ·
        refine ⟨25897339774887920411425403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69059572733034454430467741 25897339774887920411425403)
        ·
          refine ⟨38846009662331880617138105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25897339774887920411425403 38846009662331880617138105)
          ·
            refine ⟨29134507246748910462853579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38846009662331880617138105 29134507246748910462853579)
            ·
              refine ⟨43701760870123365694280369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29134507246748910462853579 43701760870123365694280369)
              ·
                refine ⟨32776320652592524270710277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43701760870123365694280369 32776320652592524270710277)
                ·
                  refine ⟨6145560122361098300758177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32776320652592524270710277 6145560122361098300758177)
                  ·
                    refine ⟨4609170091770823725568633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6145560122361098300758177 4609170091770823725568633)
                    ·
                      refine ⟨3456877568828117794176475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4609170091770823725568633 3456877568828117794176475)
                      ·
                        rfl

theorem cell23_6732245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6732245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732245 prefixEnd_6732245 := by exact prefixLift 6732245
  have htrace : WordTrace (prefixWord ++ tailWord_6732245) baseStart_6732245 baseEnd_6732245 := by
    simpa [prefixWord, tailWord_6732245, baseEnd_6732245] using wordTrace_append hprefix tailTrace_6732245
  have hstable : (prefixWord ++ tailWord_6732245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732245).length < 2 ^ (prefixWord ++ tailWord_6732245).sum := by decide
  have hdescent : baseEnd_6732245 < baseStart_6732245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732278 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_6732278 : Nat := 118140960795 + 6732278 * 2 ^ 59
def prefixEnd_6732278 : Nat := 4983230072969 + 3 ^ 40 * 6732278 * 2
def baseEnd_6732278 : Nat := 3456894513689716165063823

theorem tailTrace_6732278 : CollatzResearch.WordTrace tailWord_6732278 prefixEnd_6732278 3456894513689716165063823 := by
  unfold tailWord_6732278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15346646944007128899295343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163697567402742708259150325 15346646944007128899295343)
  ·
    refine ⟨23019970416010693348943015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15346646944007128899295343 23019970416010693348943015)
    ·
      refine ⟨34529955624016040023414523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23019970416010693348943015 34529955624016040023414523)
      ·
        refine ⟨51794933436024060035121785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34529955624016040023414523 51794933436024060035121785)
        ·
          refine ⟨38846200077018045026341339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51794933436024060035121785 38846200077018045026341339)
          ·
            refine ⟨58269300115527067539512009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38846200077018045026341339 58269300115527067539512009)
            ·
              refine ⟨43701975086645300654634007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58269300115527067539512009 43701975086645300654634007)
              ·
                refine ⟨65552962629967950981951011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43701975086645300654634007 65552962629967950981951011)
                ·
                  refine ⟨98329443944951926472926517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65552962629967950981951011 98329443944951926472926517)
                  ·
                    refine ⟨9218385369839243106836861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98329443944951926472926517 9218385369839243106836861)
                    ·
                      refine ⟨3456894513689716165063823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9218385369839243106836861 3456894513689716165063823)
                      ·
                        rfl

theorem cell23_6732278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_6732278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732278 prefixEnd_6732278 := by exact prefixLift 6732278
  have htrace : WordTrace (prefixWord ++ tailWord_6732278) baseStart_6732278 baseEnd_6732278 := by
    simpa [prefixWord, tailWord_6732278, baseEnd_6732278] using wordTrace_append hprefix tailTrace_6732278
  have hstable : (prefixWord ++ tailWord_6732278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732278).length < 2 ^ (prefixWord ++ tailWord_6732278).sum := by decide
  have hdescent : baseEnd_6732278 < baseStart_6732278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732298 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_6732298 : Nat := 118140960795 + 6732298 * 2 ^ 59
def prefixEnd_6732298 : Nat := 4983230072969 + 3 ^ 40 * 6732298 * 2
def baseEnd_6732298 : Nat := 1152301594434268695604577

theorem tailTrace_6732298 : CollatzResearch.WordTrace tailWord_6732298 prefixEnd_6732298 1152301594434268695604577 := by
  unfold tailWord_6732298
  simp only [CollatzResearch.WordTrace]
  refine ⟨61386770141010401451113387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163698053709361070536302365 61386770141010401451113387)
  ·
    refine ⟨92080155211515602176670081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61386770141010401451113387 92080155211515602176670081)
    ·
      refine ⟨69060116408636701632502561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92080155211515602176670081 69060116408636701632502561)
      ·
        refine ⟨51795087306477526224376921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69060116408636701632502561 51795087306477526224376921)
        ·
          refine ⟨38846315479858144668282691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51795087306477526224376921 38846315479858144668282691)
          ·
            refine ⟨58269473219787217002424037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38846315479858144668282691 58269473219787217002424037)
            ·
              refine ⟨10925526228710103187954507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58269473219787217002424037 10925526228710103187954507)
              ·
                refine ⟨16388289343065154781931761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10925526228710103187954507 16388289343065154781931761)
                ·
                  refine ⟨12291217007298866086448821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16388289343065154781931761 12291217007298866086448821)
                  ·
                    refine ⟨1152301594434268695604577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12291217007298866086448821 1152301594434268695604577)
                    ·
                      rfl

theorem cell23_6732298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_6732298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732298 prefixEnd_6732298 := by exact prefixLift 6732298
  have htrace : WordTrace (prefixWord ++ tailWord_6732298) baseStart_6732298 baseEnd_6732298 := by
    simpa [prefixWord, tailWord_6732298, baseEnd_6732298] using wordTrace_append hprefix tailTrace_6732298
  have hstable : (prefixWord ++ tailWord_6732298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732298).length < 2 ^ (prefixWord ++ tailWord_6732298).sum := by decide
  have hdescent : baseEnd_6732298 < baseStart_6732298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732321 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6732321 : Nat := 118140960795 + 6732321 * 2 ^ 59
def prefixEnd_6732321 : Nat := 4983230072969 + 3 ^ 40 * 6732321 * 2
def baseEnd_6732321 : Nat := 3456916593357859496826125

theorem tailTrace_6732321 : CollatzResearch.WordTrace tailWord_6732321 prefixEnd_6732321 3456916593357859496826125 := by
  unfold tailWord_6732321
  simp only [CollatzResearch.WordTrace]
  refine ⟨245547919442958280732540817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163698612961972187155027211 245547919442958280732540817)
  ·
    refine ⟨184160939582218710549405613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245547919442958280732540817 184160939582218710549405613)
    ·
      refine ⟨69060352343332016456027105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184160939582218710549405613 69060352343332016456027105)
      ·
        refine ⟨51795264257499012342020329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69060352343332016456027105 51795264257499012342020329)
        ·
          refine ⟨38846448193124259256515247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51795264257499012342020329 38846448193124259256515247)
          ·
            refine ⟨58269672289686388884772871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38846448193124259256515247 58269672289686388884772871)
            ·
              refine ⟨87404508434529583327159307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58269672289686388884772871 87404508434529583327159307)
              ·
                refine ⟨131106762651794374990738961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87404508434529583327159307 131106762651794374990738961)
                ·
                  refine ⟨98330071988845781243054221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131106762651794374990738961 98330071988845781243054221)
                  ·
                    refine ⟨36873776995817167966145333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98330071988845781243054221 36873776995817167966145333)
                    ·
                      refine ⟨3456916593357859496826125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36873776995817167966145333 3456916593357859496826125)
                      ·
                        rfl

theorem cell23_6732321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6732321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732321 prefixEnd_6732321 := by exact prefixLift 6732321
  have htrace : WordTrace (prefixWord ++ tailWord_6732321) baseStart_6732321 baseEnd_6732321 := by
    simpa [prefixWord, tailWord_6732321, baseEnd_6732321] using wordTrace_append hprefix tailTrace_6732321
  have hstable : (prefixWord ++ tailWord_6732321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732321).length < 2 ^ (prefixWord ++ tailWord_6732321).sum := by decide
  have hdescent : baseEnd_6732321 < baseStart_6732321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732338 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_6732338 : Nat := 118140960795 + 6732338 * 2 ^ 59
def prefixEnd_6732338 : Nat := 4983230072969 + 3 ^ 40 * 6732338 * 2
def baseEnd_6732338 : Nat := 3456925322528985930313547

theorem tailTrace_6732338 : CollatzResearch.WordTrace tailWord_6732338 prefixEnd_6732338 3456925322528985930313547 := by
  unfold tailWord_6732338
  simp only [CollatzResearch.WordTrace]
  refine ⟨61387134870974173158977417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163699026322597795090606445 61387134870974173158977417)
  ·
    refine ⟨46040351153230629869233063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61387134870974173158977417 46040351153230629869233063)
    ·
      refine ⟨69060526729845944803849595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46040351153230629869233063 69060526729845944803849595)
      ·
        refine ⟨103590790094768917205774393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69060526729845944803849595 103590790094768917205774393)
        ·
          refine ⟨77693092571076687904330795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103590790094768917205774393 77693092571076687904330795)
          ·
            refine ⟨116539638856615031856496193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77693092571076687904330795 116539638856615031856496193)
            ·
              refine ⟨87404729142461273892372145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116539638856615031856496193 87404729142461273892372145)
              ·
                refine ⟨65553546856845955419279109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87404729142461273892372145 65553546856845955419279109)
                ·
                  refine ⟨12291290035658616641114833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65553546856845955419279109 12291290035658616641114833)
                  ·
                    refine ⟨9218467526743962480836125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12291290035658616641114833 9218467526743962480836125)
                    ·
                      refine ⟨3456925322528985930313547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9218467526743962480836125 3456925322528985930313547)
                      ·
                        rfl

theorem cell23_6732338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_6732338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732338 prefixEnd_6732338 := by exact prefixLift 6732338
  have htrace : WordTrace (prefixWord ++ tailWord_6732338) baseStart_6732338 baseEnd_6732338 := by
    simpa [prefixWord, tailWord_6732338, baseEnd_6732338] using wordTrace_append hprefix tailTrace_6732338
  have hstable : (prefixWord ++ tailWord_6732338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732338).length < 2 ^ (prefixWord ++ tailWord_6732338).sum := by decide
  have hdescent : baseEnd_6732338 < baseStart_6732338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732362 : List Nat := [3, 1, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_6732362 : Nat := 118140960795 + 6732362 * 2 ^ 59
def prefixEnd_6732362 : Nat := 4983230072969 + 3 ^ 40 * 6732362 * 2
def baseEnd_6732362 : Nat := 1152312548688231278804479

theorem tailTrace_6732362 : CollatzResearch.WordTrace tailWord_6732362 prefixEnd_6732362 1152312548688231278804479 := by
  unfold tailWord_6732362
  simp only [CollatzResearch.WordTrace]
  refine ⟨61387353708952436183695835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163699609890539829823188893 61387353708952436183695835)
  ·
    refine ⟨92081030563428654275543753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61387353708952436183695835 92081030563428654275543753)
    ·
      refine ⟨69060772922571490706657815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92081030563428654275543753 69060772922571490706657815)
      ·
        refine ⟨103591159383857236059986723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69060772922571490706657815 103591159383857236059986723)
        ·
          refine ⟨155386739075785854089980085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103591159383857236059986723 155386739075785854089980085)
          ·
            refine ⟨14567506788354923820935633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155386739075785854089980085 14567506788354923820935633)
            ·
              refine ⟨10925630091266192865701725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14567506788354923820935633 10925630091266192865701725)
              ·
                refine ⟨4097111284224822324638147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10925630091266192865701725 4097111284224822324638147)
                ·
                  refine ⟨6145666926337233486957221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097111284224822324638147 6145666926337233486957221)
                  ·
                    refine ⟨1152312548688231278804479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6145666926337233486957221 1152312548688231278804479)
                    ·
                      rfl

theorem cell23_6732362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_6732362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732362 prefixEnd_6732362 := by exact prefixLift 6732362
  have htrace : WordTrace (prefixWord ++ tailWord_6732362) baseStart_6732362 baseEnd_6732362 := by
    simpa [prefixWord, tailWord_6732362, baseEnd_6732362] using wordTrace_append hprefix tailTrace_6732362
  have hstable : (prefixWord ++ tailWord_6732362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732362).length < 2 ^ (prefixWord ++ tailWord_6732362).sum := by decide
  have hdescent : baseEnd_6732362 < baseStart_6732362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732385 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_6732385 : Nat := 118140960795 + 6732385 * 2 ^ 59
def prefixEnd_6732385 : Nat := 4983230072969 + 3 ^ 40 * 6732385 * 2
def baseEnd_6732385 : Nat := 3456949456119747246425831

theorem tailTrace_6732385 : CollatzResearch.WordTrace tailWord_6732385 prefixEnd_6732385 3456949456119747246425831 := by
  unfold tailWord_6732385
  simp only [CollatzResearch.WordTrace]
  refine ⟨245550253714726419662870609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163700169143150946441913739 245550253714726419662870609)
  ·
    refine ⟨184162690286044814747152957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245550253714726419662870609 184162690286044814747152957)
    ·
      refine ⟨69061008857266805530182359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184162690286044814747152957 69061008857266805530182359)
      ·
        refine ⟨103591513285900208295273539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69061008857266805530182359 103591513285900208295273539)
        ·
          refine ⟨155387269928850312442910309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103591513285900208295273539 155387269928850312442910309)
          ·
            refine ⟨29135113111659433583045683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155387269928850312442910309 29135113111659433583045683)
            ·
              refine ⟨43702669667489150374568525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29135113111659433583045683 43702669667489150374568525)
              ·
                refine ⟨16388501125308431390463197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43702669667489150374568525 16388501125308431390463197)
                ·
                  refine ⟨6145687921990661771423699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16388501125308431390463197 6145687921990661771423699)
                  ·
                    refine ⟨9218531882985992657135549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145687921990661771423699 9218531882985992657135549)
                    ·
                      refine ⟨3456949456119747246425831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9218531882985992657135549 3456949456119747246425831)
                      ·
                        rfl

theorem cell23_6732385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_6732385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732385 prefixEnd_6732385 := by exact prefixLift 6732385
  have htrace : WordTrace (prefixWord ++ tailWord_6732385) baseStart_6732385 baseEnd_6732385 := by
    simpa [prefixWord, tailWord_6732385, baseEnd_6732385] using wordTrace_append hprefix tailTrace_6732385
  have hstable : (prefixWord ++ tailWord_6732385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732385).length < 2 ^ (prefixWord ++ tailWord_6732385).sum := by decide
  have hdescent : baseEnd_6732385 < baseStart_6732385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732392 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 6]
def baseStart_6732392 : Nat := 118140960795 + 6732392 * 2 ^ 59
def prefixEnd_6732392 : Nat := 4983230072969 + 3 ^ 40 * 6732392 * 2
def baseEnd_6732392 : Nat := 384105894498258746559811

theorem tailTrace_6732392 : CollatzResearch.WordTrace tailWord_6732392 prefixEnd_6732392 384105894498258746559811 := by
  unfold tailWord_6732392
  simp only [CollatzResearch.WordTrace]
  refine ⟨122775254512850529929187715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163700339350467373238916953 122775254512850529929187715)
  ·
    refine ⟨184162881769275794893781573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122775254512850529929187715 184162881769275794893781573)
    ·
      refine ⟨34530540331739211542584045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184162881769275794893781573 34530540331739211542584045)
      ·
        refine ⟨12948952624402204328469017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34530540331739211542584045 12948952624402204328469017)
        ·
          refine ⟨9711714468301653246351763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12948952624402204328469017 9711714468301653246351763)
          ·
            refine ⟨14567571702452479869527645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9711714468301653246351763 14567571702452479869527645)
            ·
              refine ⟨5462839388419679951072867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14567571702452479869527645 5462839388419679951072867)
              ·
                refine ⟨8194259082629519926609301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462839388419679951072867 8194259082629519926609301)
                ·
                  refine ⟨384105894498258746559811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8194259082629519926609301 384105894498258746559811)
                  ·
                    rfl

theorem cell23_6732392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 6].length) (baseStart_6732392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732392 prefixEnd_6732392 := by exact prefixLift 6732392
  have htrace : WordTrace (prefixWord ++ tailWord_6732392) baseStart_6732392 baseEnd_6732392 := by
    simpa [prefixWord, tailWord_6732392, baseEnd_6732392] using wordTrace_append hprefix tailTrace_6732392
  have hstable : (prefixWord ++ tailWord_6732392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732392).length < 2 ^ (prefixWord ++ tailWord_6732392).sum := by decide
  have hdescent : baseEnd_6732392 < baseStart_6732392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732485 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 7, 3, 2]
def baseStart_6732485 : Nat := 118140960795 + 6732485 * 2 ^ 59
def prefixEnd_6732485 : Nat := 4983230072969 + 3 ^ 40 * 6732485 * 2
def baseEnd_6732485 : Nat := 3457000804185196855175371

theorem tailTrace_6732485 : CollatzResearch.WordTrace tailWord_6732485 prefixEnd_6732485 3457000804185196855175371 := by
  unfold tailWord_6732485
  simp only [CollatzResearch.WordTrace]
  refine ⟨245553901014364136741510909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163702600676242757827673939 245553901014364136741510909)
  ·
    refine ⟨92082712880386551278066591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245553901014364136741510909 92082712880386551278066591)
    ·
      refine ⟨138124069320579826917099887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92082712880386551278066591 138124069320579826917099887)
      ·
        refine ⟨207186103980869740375649831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138124069320579826917099887 207186103980869740375649831)
        ·
          refine ⟨310779155971304610563474747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207186103980869740375649831 310779155971304610563474747)
          ·
            refine ⟨466168733956956915845212121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310779155971304610563474747 466168733956956915845212121)
            ·
              refine ⟨349626550467717686883909091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466168733956956915845212121 349626550467717686883909091)
              ·
                refine ⟨524439825701576530325863637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349626550467717686883909091 524439825701576530325863637)
                ·
                  refine ⟨12291558414880699929512429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 524439825701576530325863637 12291558414880699929512429)
                  ·
                    refine ⟨4609334405580262473567161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12291558414880699929512429 4609334405580262473567161)
                    ·
                      refine ⟨3457000804185196855175371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4609334405580262473567161 3457000804185196855175371)
                      ·
                        rfl

theorem cell23_6732485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_6732485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732485 prefixEnd_6732485 := by exact prefixLift 6732485
  have htrace : WordTrace (prefixWord ++ tailWord_6732485) baseStart_6732485 baseEnd_6732485 := by
    simpa [prefixWord, tailWord_6732485, baseEnd_6732485] using wordTrace_append hprefix tailTrace_6732485
  have hstable : (prefixWord ++ tailWord_6732485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732485).length < 2 ^ (prefixWord ++ tailWord_6732485).sum := by decide
  have hdescent : baseEnd_6732485 < baseStart_6732485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732528 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_6732528 : Nat := 118140960795 + 6732528 * 2 ^ 59
def prefixEnd_6732528 : Nat := 4983230072969 + 3 ^ 40 * 6732528 * 2
def baseEnd_6732528 : Nat := 3457022883853340186937673

theorem tailTrace_6732528 : CollatzResearch.WordTrace tailWord_6732528 prefixEnd_6732528 3457022883853340186937673 := by
  unfold tailWord_6732528
  simp only [CollatzResearch.WordTrace]
  refine ⟨122777734676604177542663119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163703646235472236723550825 122777734676604177542663119)
  ·
    refine ⟨184166602014906266313994679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122777734676604177542663119 184166602014906266313994679)
    ·
      refine ⟨276249903022359399470992019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184166602014906266313994679 276249903022359399470992019)
      ·
        refine ⟨414374854533539099206488029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276249903022359399470992019 414374854533539099206488029)
        ·
          refine ⟨155390570450077162202433011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414374854533539099206488029 155390570450077162202433011)
          ·
            refine ⟨233085855675115743303649517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155390570450077162202433011 233085855675115743303649517)
            ·
              refine ⟨87407195878168403738868569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233085855675115743303649517 87407195878168403738868569)
              ·
                refine ⟨65555396908626302804151427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87407195878168403738868569 65555396908626302804151427)
                ·
                  refine ⟨98333095362939454206227141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65555396908626302804151427 98333095362939454206227141)
                  ·
                    refine ⟨18437455380551147663667589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98333095362939454206227141 18437455380551147663667589)
                    ·
                      refine ⟨3457022883853340186937673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18437455380551147663667589 3457022883853340186937673)
                      ·
                        rfl

theorem cell23_6732528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_6732528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732528 prefixEnd_6732528 := by exact prefixLift 6732528
  have htrace : WordTrace (prefixWord ++ tailWord_6732528) baseStart_6732528 baseEnd_6732528 := by
    simpa [prefixWord, tailWord_6732528, baseEnd_6732528] using wordTrace_append hprefix tailTrace_6732528
  have hstable : (prefixWord ++ tailWord_6732528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732528).length < 2 ^ (prefixWord ++ tailWord_6732528).sum := by decide
  have hdescent : baseEnd_6732528 < baseStart_6732528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732565 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_6732565 : Nat := 118140960795 + 6732565 * 2 ^ 59
def prefixEnd_6732565 : Nat := 4983230072969 + 3 ^ 40 * 6732565 * 2
def baseEnd_6732565 : Nat := 3457041882637556542175003

theorem tailTrace_6732565 : CollatzResearch.WordTrace tailWord_6732565 prefixEnd_6732565 3457041882637556542175003 := by
  unfold tailWord_6732565
  simp only [CollatzResearch.WordTrace]
  refine ⟨245556818854074310404423149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163704545902716206936282099 245556818854074310404423149)
  ·
    refine ⟨92083807070277866401658681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245556818854074310404423149 92083807070277866401658681)
    ·
      refine ⟨69062855302708399801244011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92083807070277866401658681 69062855302708399801244011)
      ·
        refine ⟨103594282954062599701866017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69062855302708399801244011 103594282954062599701866017)
        ·
          refine ⟨77695712215546949776399513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103594282954062599701866017 77695712215546949776399513)
          ·
            refine ⟨58271784161660212332299635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77695712215546949776399513 58271784161660212332299635)
            ·
              refine ⟨87407676242490318498449453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58271784161660212332299635 87407676242490318498449453)
              ·
                refine ⟨32777878590933869436918545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87407676242490318498449453 32777878590933869436918545)
                ·
                  refine ⟨24583408943200402077688909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32777878590933869436918545 24583408943200402077688909)
                  ·
                    refine ⟨9218778353700150779133341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24583408943200402077688909 9218778353700150779133341)
                    ·
                      refine ⟨3457041882637556542175003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9218778353700150779133341 3457041882637556542175003)
                      ·
                        rfl

theorem cell23_6732565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_6732565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732565 prefixEnd_6732565 := by exact prefixLift 6732565
  have htrace : WordTrace (prefixWord ++ tailWord_6732565) baseStart_6732565 baseEnd_6732565 := by
    simpa [prefixWord, tailWord_6732565, baseEnd_6732565] using wordTrace_append hprefix tailTrace_6732565
  have hstable : (prefixWord ++ tailWord_6732565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732565).length < 2 ^ (prefixWord ++ tailWord_6732565).sum := by decide
  have hdescent : baseEnd_6732565 < baseStart_6732565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732602 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_6732602 : Nat := 118140960795 + 6732602 * 2 ^ 59
def prefixEnd_6732602 : Nat := 4983230072969 + 3 ^ 40 * 6732602 * 2
def baseEnd_6732602 : Nat := 1152353627140590965804111

theorem tailTrace_6732602 : CollatzResearch.WordTrace tailWord_6732602 prefixEnd_6732602 1152353627140590965804111 := by
  unfold tailWord_6732602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61389542088735066430880015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163705445569960177149013373 61389542088735066430880015)
  ·
    refine ⟨92084313133102599646320023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61389542088735066430880015 92084313133102599646320023)
    ·
      refine ⟨138126469699653899469480035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92084313133102599646320023 138126469699653899469480035)
      ·
        refine ⟨207189704549480849204220053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138126469699653899469480035 207189704549480849204220053)
        ·
          refine ⟨9712017400756914806447815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 207189704549480849204220053 9712017400756914806447815)
          ·
            refine ⟨14568026101135372209671723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9712017400756914806447815 14568026101135372209671723)
            ·
              refine ⟨21852039151703058314507585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14568026101135372209671723 21852039151703058314507585)
              ·
                refine ⟨16389029363777293735880689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21852039151703058314507585 16389029363777293735880689)
                ·
                  refine ⟨12291772022832970301910517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16389029363777293735880689 12291772022832970301910517)
                  ·
                    refine ⟨1152353627140590965804111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12291772022832970301910517 1152353627140590965804111)
                    ·
                      rfl

theorem cell23_6732602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_6732602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732602 prefixEnd_6732602 := by exact prefixLift 6732602
  have htrace : WordTrace (prefixWord ++ tailWord_6732602) baseStart_6732602 baseEnd_6732602 := by
    simpa [prefixWord, tailWord_6732602, baseEnd_6732602] using wordTrace_append hprefix tailTrace_6732602
  have hstable : (prefixWord ++ tailWord_6732602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732602).length < 2 ^ (prefixWord ++ tailWord_6732602).sum := by decide
  have hdescent : baseEnd_6732602 < baseStart_6732602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732606 : List Nat := [4, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_6732606 : Nat := 118140960795 + 6732606 * 2 ^ 59
def prefixEnd_6732606 : Nat := 4983230072969 + 3 ^ 40 * 6732606 * 2
def baseEnd_6732606 : Nat := 384118103927154542418035

theorem tailTrace_6732606 : CollatzResearch.WordTrace tailWord_6732606 prefixEnd_6732606 384118103927154542418035 := by
  unfold tailWord_6732606
  simp only [CollatzResearch.WordTrace]
  refine ⟨30694789280865721800833209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163705542831283849604443781 30694789280865721800833209)
  ·
    refine ⟨23021091960649291350624907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30694789280865721800833209 23021091960649291350624907)
    ·
      refine ⟨34531637940973937025937361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23021091960649291350624907 34531637940973937025937361)
      ·
        refine ⟨25898728455730452769453021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34531637940973937025937361 25898728455730452769453021)
        ·
          refine ⟨9712023170898919788544883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25898728455730452769453021 9712023170898919788544883)
          ·
            refine ⟨14568034756348379682817325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9712023170898919788544883 14568034756348379682817325)
            ·
              refine ⟨5463013033630642381056497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14568034756348379682817325 5463013033630642381056497)
              ·
                refine ⟨4097259775222981785792373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463013033630642381056497 4097259775222981785792373)
                ·
                  refine ⟨384118103927154542418035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4097259775222981785792373 384118103927154542418035)
                  ·
                    rfl

theorem cell23_6732606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_6732606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732606 prefixEnd_6732606 := by exact prefixLift 6732606
  have htrace : WordTrace (prefixWord ++ tailWord_6732606) baseStart_6732606 baseEnd_6732606 := by
    simpa [prefixWord, tailWord_6732606, baseEnd_6732606] using wordTrace_append hprefix tailTrace_6732606
  have hstable : (prefixWord ++ tailWord_6732606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732606).length < 2 ^ (prefixWord ++ tailWord_6732606).sum := by decide
  have hdescent : baseEnd_6732606 < baseStart_6732606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732622 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_6732622 : Nat := 118140960795 + 6732622 * 2 ^ 59
def prefixEnd_6732622 : Nat := 4983230072969 + 3 ^ 40 * 6732622 * 2
def baseEnd_6732622 : Nat := 3457071151034862819162241

theorem tailTrace_6732622 : CollatzResearch.WordTrace tailWord_6732622 prefixEnd_6732622 3457071151034862819162241 := by
  unfold tailWord_6732622
  simp only [CollatzResearch.WordTrace]
  refine ⟨30694862226858476142406015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163705931876578539426165413 30694862226858476142406015)
  ·
    refine ⟨46042293340287714213609023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30694862226858476142406015 46042293340287714213609023)
    ·
      refine ⟨69063440010431571320413535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46042293340287714213609023 69063440010431571320413535)
      ·
        refine ⟨103595160015647356980620303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69063440010431571320413535 103595160015647356980620303)
        ·
          refine ⟨155392740023471035470930455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103595160015647356980620303 155392740023471035470930455)
          ·
            refine ⟨233089110035206553206395683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155392740023471035470930455 233089110035206553206395683)
            ·
              refine ⟨349633665052809829809593525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233089110035206553206395683 349633665052809829809593525)
              ·
                refine ⟨32778156098700921544649393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349633665052809829809593525 32778156098700921544649393)
                ·
                  refine ⟨24583617074025691158487045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32778156098700921544649393 24583617074025691158487045)
                  ·
                    refine ⟨4609428201379817092216321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24583617074025691158487045 4609428201379817092216321)
                    ·
                      refine ⟨3457071151034862819162241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4609428201379817092216321 3457071151034862819162241)
                      ·
                        rfl

theorem cell23_6732622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_6732622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732622 prefixEnd_6732622 := by exact prefixLift 6732622
  have htrace : WordTrace (prefixWord ++ tailWord_6732622) baseStart_6732622 baseEnd_6732622 := by
    simpa [prefixWord, tailWord_6732622, baseEnd_6732622] using wordTrace_append hprefix tailTrace_6732622
  have hstable : (prefixWord ++ tailWord_6732622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732622).length < 2 ^ (prefixWord ++ tailWord_6732622).sum := by decide
  have hdescent : baseEnd_6732622 < baseStart_6732622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732675 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 5, 5]
def baseStart_6732675 : Nat := 118140960795 + 6732675 * 2 ^ 59
def prefixEnd_6732675 : Nat := 4983230072969 + 3 ^ 40 * 6732675 * 2
def baseEnd_6732675 : Nat := 1152366121836517037266499

theorem tailTrace_6732675 : CollatzResearch.WordTrace tailWord_6732675 prefixEnd_6732675 1152366121836517037266499 := by
  unfold tailWord_6732675
  simp only [CollatzResearch.WordTrace]
  refine ⟨245560830883675799190927479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163707220589117199460618319 245560830883675799190927479)
  ·
    refine ⟨368341246325513698786391219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245560830883675799190927479 368341246325513698786391219)
    ·
      refine ⟨552511869488270548179586829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368341246325513698786391219 552511869488270548179586829)
      ·
        refine ⟨207191951058101455567345061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552511869488270548179586829 207191951058101455567345061)
        ·
          refine ⟨38848490823394022918877199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207191951058101455567345061 38848490823394022918877199)
          ·
            refine ⟨58272736235091034378315799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38848490823394022918877199 58272736235091034378315799)
            ·
              refine ⟨87409104352636551567473699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58272736235091034378315799 87409104352636551567473699)
              ·
                refine ⟨131113656528954827351210549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87409104352636551567473699 131113656528954827351210549)
                ·
                  refine ⟨12291905299589515064175989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131113656528954827351210549 12291905299589515064175989)
                  ·
                    refine ⟨1152366121836517037266499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12291905299589515064175989 1152366121836517037266499)
                    ·
                      rfl

theorem cell23_6732675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 5].length) (baseStart_6732675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732675 prefixEnd_6732675 := by exact prefixLift 6732675
  have htrace : WordTrace (prefixWord ++ tailWord_6732675) baseStart_6732675 baseEnd_6732675 := by
    simpa [prefixWord, tailWord_6732675, baseEnd_6732675] using wordTrace_append hprefix tailTrace_6732675
  have hstable : (prefixWord ++ tailWord_6732675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732675).length < 2 ^ (prefixWord ++ tailWord_6732675).sum := by decide
  have hdescent : baseEnd_6732675 < baseStart_6732675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732692 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_6732692 : Nat := 118140960795 + 6732692 * 2 ^ 59
def prefixEnd_6732692 : Nat := 4983230072969 + 3 ^ 40 * 6732692 * 2
def baseEnd_6732692 : Nat := 1152369031560225848428973

theorem tailTrace_6732692 : CollatzResearch.WordTrace tailWord_6732692 prefixEnd_6732692 1152369031560225848428973 := by
  unfold tailWord_6732692
  simp only [CollatzResearch.WordTrace]
  refine ⟨122780725462307105547148165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163707633949742807396197553 122780725462307105547148165)
  ·
    refine ⟨23021386024182582290090281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122780725462307105547148165 23021386024182582290090281)
    ·
      refine ⟨17266039518136936717567711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23021386024182582290090281 17266039518136936717567711)
      ·
        refine ⟨25899059277205405076351567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17266039518136936717567711 25899059277205405076351567)
        ·
          refine ⟨38848588915808107614527351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25899059277205405076351567 38848588915808107614527351)
          ·
            refine ⟨58272883373712161421791027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38848588915808107614527351 58272883373712161421791027)
            ·
              refine ⟨87409325060568242132686541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58272883373712161421791027 87409325060568242132686541)
              ·
                refine ⟨32778496897713090799757453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87409325060568242132686541 32778496897713090799757453)
                ·
                  refine ⟨12291936336642409049909045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32778496897713090799757453 12291936336642409049909045)
                  ·
                    refine ⟨1152369031560225848428973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12291936336642409049909045 1152369031560225848428973)
                    ·
                      rfl

theorem cell23_6732692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_6732692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732692 prefixEnd_6732692 := by exact prefixLift 6732692
  have htrace : WordTrace (prefixWord ++ tailWord_6732692) baseStart_6732692 baseEnd_6732692 := by
    simpa [prefixWord, tailWord_6732692, baseEnd_6732692] using wordTrace_append hprefix tailTrace_6732692
  have hstable : (prefixWord ++ tailWord_6732692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732692).length < 2 ^ (prefixWord ++ tailWord_6732692).sum := by decide
  have hdescent : baseEnd_6732692 < baseStart_6732692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732795 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 1, 8]
def baseStart_6732795 : Nat := 118140960795 + 6732795 * 2 ^ 59
def prefixEnd_6732795 : Nat := 4983230072969 + 3 ^ 40 * 6732795 * 2
def baseEnd_6732795 : Nat := 1152386661062696880766315

theorem tailTrace_6732795 : CollatzResearch.WordTrace tailWord_6732795 prefixEnd_6732795 1152386661062696880766315 := by
  unfold tailWord_6732795
  simp only [CollatzResearch.WordTrace]
  refine ⟨245565207643241059685295839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163710138428827373123530559 245565207643241059685295839)
  ·
    refine ⟨368347811464861589527943759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245565207643241059685295839 368347811464861589527943759)
    ·
      refine ⟨552521717197292384291915639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368347811464861589527943759 552521717197292384291915639)
      ·
        refine ⟨828782575795938576437873459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552521717197292384291915639 828782575795938576437873459)
        ·
          refine ⟨1243173863693907864656810189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828782575795938576437873459 1243173863693907864656810189)
          ·
            refine ⟨466190198885215449246303821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1243173863693907864656810189 466190198885215449246303821)
            ·
              refine ⟨174821324581955793467363933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466190198885215449246303821 174821324581955793467363933)
              ·
                refine ⟨65557996718233422550261475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174821324581955793467363933 65557996718233422550261475)
                ·
                  refine ⟨98336995077350133825392213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65557996718233422550261475 98336995077350133825392213)
                  ·
                    refine ⟨1152386661062696880766315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98336995077350133825392213 1152386661062696880766315)
                    ·
                      rfl

theorem cell23_6732795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 8].length) (baseStart_6732795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732795 prefixEnd_6732795 := by exact prefixLift 6732795
  have htrace : WordTrace (prefixWord ++ tailWord_6732795) baseStart_6732795 baseEnd_6732795 := by
    simpa [prefixWord, tailWord_6732795, baseEnd_6732795] using wordTrace_append hprefix tailTrace_6732795
  have hstable : (prefixWord ++ tailWord_6732795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732795).length < 2 ^ (prefixWord ++ tailWord_6732795).sum := by decide
  have hdescent : baseEnd_6732795 < baseStart_6732795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732796 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_6732796 : Nat := 118140960795 + 6732796 * 2 ^ 59
def prefixEnd_6732796 : Nat := 4983230072969 + 3 ^ 40 * 6732796 * 2
def baseEnd_6732796 : Nat := 3457160496668745138386441

theorem tailTrace_6732796 : CollatzResearch.WordTrace tailWord_6732796 prefixEnd_6732796 3457160496668745138386441 := by
  unfold tailWord_6732796
  simp only [CollatzResearch.WordTrace]
  refine ⟨122782622058118718428041121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163710162744158291237388161 122782622058118718428041121)
  ·
    refine ⟨92086966543589038821030841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122782622058118718428041121 92086966543589038821030841)
    ·
      refine ⟨69065224907691779115773131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92086966543589038821030841 69065224907691779115773131)
      ·
        refine ⟨103597837361537668673659697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69065224907691779115773131 103597837361537668673659697)
        ·
          refine ⟨77698378021153251505244773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103597837361537668673659697 77698378021153251505244773)
          ·
            refine ⟨14568445878966234657233395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77698378021153251505244773 14568445878966234657233395)
            ·
              refine ⟨21852668818449351985850093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14568445878966234657233395 21852668818449351985850093)
              ·
                refine ⟨8194750806918506994693785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21852668818449351985850093 8194750806918506994693785)
                ·
                  refine ⟨6146063105188880246020339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8194750806918506994693785 6146063105188880246020339)
                  ·
                    refine ⟨9219094657783320369030509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146063105188880246020339 9219094657783320369030509)
                    ·
                      refine ⟨3457160496668745138386441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219094657783320369030509 3457160496668745138386441)
                      ·
                        rfl

theorem cell23_6732796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_6732796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732796 prefixEnd_6732796 := by exact prefixLift 6732796
  have htrace : WordTrace (prefixWord ++ tailWord_6732796) baseStart_6732796 baseEnd_6732796 := by
    simpa [prefixWord, tailWord_6732796, baseEnd_6732796] using wordTrace_append hprefix tailTrace_6732796
  have hstable : (prefixWord ++ tailWord_6732796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732796).length < 2 ^ (prefixWord ++ tailWord_6732796).sum := by decide
  have hdescent : baseEnd_6732796 < baseStart_6732796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732872 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 1, 7]
def baseStart_6732872 : Nat := 118140960795 + 6732872 * 2 ^ 59
def prefixEnd_6732872 : Nat := 4983230072969 + 3 ^ 40 * 6732872 * 2
def baseEnd_6732872 : Nat := 1152399840399495613678697

theorem tailTrace_6732872 : CollatzResearch.WordTrace tailWord_6732872 prefixEnd_6732872 1152399840399495613678697 := by
  unfold tailWord_6732872
  simp only [CollatzResearch.WordTrace]
  refine ⟨122784008031981050917924435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163712010709308067890565913 122784008031981050917924435)
  ·
    refine ⟨184176012047971576376886653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122784008031981050917924435 184176012047971576376886653)
    ·
      refine ⟨69066004517989341141332495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184176012047971576376886653 69066004517989341141332495)
      ·
        refine ⟨103599006776984011711998743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69066004517989341141332495 103599006776984011711998743)
        ·
          refine ⟨155398510165476017567998115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103599006776984011711998743 155398510165476017567998115)
          ·
            refine ⟨233097765248214026351997173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155398510165476017567998115 233097765248214026351997173)
            ·
              refine ⟨21852915492020064970499735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233097765248214026351997173 21852915492020064970499735)
              ·
                refine ⟨32779373238030097455749603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21852915492020064970499735 32779373238030097455749603)
                ·
                  refine ⟨49169059857045146183624405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32779373238030097455749603 49169059857045146183624405)
                  ·
                    refine ⟨1152399840399495613678697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49169059857045146183624405 1152399840399495613678697)
                    ·
                      rfl

theorem cell23_6732872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_6732872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732872 prefixEnd_6732872 := by exact prefixLift 6732872
  have htrace : WordTrace (prefixWord ++ tailWord_6732872) baseStart_6732872 baseEnd_6732872 := by
    simpa [prefixWord, tailWord_6732872, baseEnd_6732872] using wordTrace_append hprefix tailTrace_6732872
  have hstable : (prefixWord ++ tailWord_6732872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732872).length < 2 ^ (prefixWord ++ tailWord_6732872).sum := by decide
  have hdescent : baseEnd_6732872 < baseStart_6732872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732909 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6732909 : Nat := 118140960795 + 6732909 * 2 ^ 59
def prefixEnd_6732909 : Nat := 4983230072969 + 3 ^ 40 * 6732909 * 2
def baseEnd_6732909 : Nat := 3457218519982703196273421

theorem tailTrace_6732909 : CollatzResearch.WordTrace tailWord_6732909 prefixEnd_6732909 3457218519982703196273421 := by
  unfold tailWord_6732909
  simp only [CollatzResearch.WordTrace]
  refine ⟨245569365564828057154945781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163712910376552038103297187 245569365564828057154945781)
  ·
    refine ⟨23022128021702630358276167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245569365564828057154945781 23022128021702630358276167)
    ·
      refine ⟨34533192032553945537414251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23022128021702630358276167 34533192032553945537414251)
      ·
        refine ⟨51799788048830918306121377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34533192032553945537414251 51799788048830918306121377)
        ·
          refine ⟨38849841036623188729591033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51799788048830918306121377 38849841036623188729591033)
          ·
            refine ⟨29137380777467391547193275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38849841036623188729591033 29137380777467391547193275)
            ·
              refine ⟨43706071166201087320789913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29137380777467391547193275 43706071166201087320789913)
              ·
                refine ⟨32779553374650815490592435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43706071166201087320789913 32779553374650815490592435)
                ·
                  refine ⟨49169330061976223235888653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32779553374650815490592435 49169330061976223235888653)
                  ·
                    refine ⟨18438498773241083713458245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49169330061976223235888653 18438498773241083713458245)
                    ·
                      refine ⟨3457218519982703196273421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18438498773241083713458245 3457218519982703196273421)
                      ·
                        rfl

theorem cell23_6732909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6732909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732909 prefixEnd_6732909 := by exact prefixLift 6732909
  have htrace : WordTrace (prefixWord ++ tailWord_6732909) baseStart_6732909 baseEnd_6732909 := by
    simpa [prefixWord, tailWord_6732909, baseEnd_6732909] using wordTrace_append hprefix tailTrace_6732909
  have hstable : (prefixWord ++ tailWord_6732909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732909).length < 2 ^ (prefixWord ++ tailWord_6732909).sum := by decide
  have hdescent : baseEnd_6732909 < baseStart_6732909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732919 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 3, 4]
def baseStart_6732919 : Nat := 118140960795 + 6732919 * 2 ^ 59
def prefixEnd_6732919 : Nat := 4983230072969 + 3 ^ 40 * 6732919 * 2
def baseEnd_6732919 : Nat := 1152407884929749385716125

theorem tailTrace_6732919 : CollatzResearch.WordTrace tailWord_6732919 prefixEnd_6732919 1152407884929749385716125 := by
  unfold tailWord_6732919
  simp only [CollatzResearch.WordTrace]
  refine ⟨245569730294791828862809811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163713153529861219241873207 245569730294791828862809811)
  ·
    refine ⟨368354595442187743294214717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245569730294791828862809811 368354595442187743294214717)
    ·
      refine ⟨138132973290820403735330519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368354595442187743294214717 138132973290820403735330519)
      ·
        refine ⟨207199459936230605602995779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138132973290820403735330519 207199459936230605602995779)
        ·
          refine ⟨310799189904345908404493669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207199459936230605602995779 310799189904345908404493669)
          ·
            refine ⟨58274848107064857825842563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310799189904345908404493669 58274848107064857825842563)
            ·
              refine ⟨87412272160597286738763845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58274848107064857825842563 87412272160597286738763845)
              ·
                refine ⟨16389801030111991263518221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87412272160597286738763845 16389801030111991263518221)
                ·
                  refine ⟨6146175386291996723819333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16389801030111991263518221 6146175386291996723819333)
                  ·
                    refine ⟨1152407884929749385716125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146175386291996723819333 1152407884929749385716125)
                    ·
                      rfl

theorem cell23_6732919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_6732919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732919 prefixEnd_6732919 := by exact prefixLift 6732919
  have htrace : WordTrace (prefixWord ++ tailWord_6732919) baseStart_6732919 baseEnd_6732919 := by
    simpa [prefixWord, tailWord_6732919, baseEnd_6732919] using wordTrace_append hprefix tailTrace_6732919
  have hstable : (prefixWord ++ tailWord_6732919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732919).length < 2 ^ (prefixWord ++ tailWord_6732919).sum := by decide
  have hdescent : baseEnd_6732919 < baseStart_6732919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732946 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_6732946 : Nat := 118140960795 + 6732946 * 2 ^ 59
def prefixEnd_6732946 : Nat := 4983230072969 + 3 ^ 40 * 6732946 * 2
def baseEnd_6732946 : Nat := 3457237518766919551510751

theorem tailTrace_6732946 : CollatzResearch.WordTrace tailWord_6732946 prefixEnd_6732946 3457237518766919551510751 := by
  unfold tailWord_6732946
  simp only [CollatzResearch.WordTrace]
  refine ⟨61392678766423503118510673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163713810043796008316028461 61392678766423503118510673)
  ·
    refine ⟨46044509074817627338883005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61392678766423503118510673 46044509074817627338883005)
    ·
      refine ⟨17266690903056610252081127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46044509074817627338883005 17266690903056610252081127)
      ·
        refine ⟨25900036354584915378121691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17266690903056610252081127 25900036354584915378121691)
        ·
          refine ⟨38850054531877373067182537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25900036354584915378121691 38850054531877373067182537)
          ·
            refine ⟨29137540898908029800386903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38850054531877373067182537 29137540898908029800386903)
            ·
              refine ⟨43706311348362044700580355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29137540898908029800386903 43706311348362044700580355)
              ·
                refine ⟨65559467022543067050870533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43706311348362044700580355 65559467022543067050870533)
                ·
                  refine ⟨12292400066726825072038225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65559467022543067050870533 12292400066726825072038225)
                  ·
                    refine ⟨9219300050045118804028669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12292400066726825072038225 9219300050045118804028669)
                    ·
                      refine ⟨3457237518766919551510751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219300050045118804028669 3457237518766919551510751)
                      ·
                        rfl

theorem cell23_6732946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_6732946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732946 prefixEnd_6732946 := by exact prefixLift 6732946
  have htrace : WordTrace (prefixWord ++ tailWord_6732946) baseStart_6732946 baseEnd_6732946 := by
    simpa [prefixWord, tailWord_6732946, baseEnd_6732946] using wordTrace_append hprefix tailTrace_6732946
  have hstable : (prefixWord ++ tailWord_6732946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732946).length < 2 ^ (prefixWord ++ tailWord_6732946).sum := by decide
  have hdescent : baseEnd_6732946 < baseStart_6732946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6732972 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_6732972 : Nat := 118140960795 + 6732972 * 2 ^ 59
def prefixEnd_6732972 : Nat := 4983230072969 + 3 ^ 40 * 6732972 * 2
def baseEnd_6732972 : Nat := 3457250869263936449785631

theorem tailTrace_6732972 : CollatzResearch.WordTrace tailWord_6732972 prefixEnd_6732972 3457250869263936449785631 := by
  unfold tailWord_6732972
  simp only [CollatzResearch.WordTrace]
  refine ⟨122785831681799909457244585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163714442242399879276326113 122785831681799909457244585)
  ·
    refine ⟨92089373761349932092933439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122785831681799909457244585 92089373761349932092933439)
    ·
      refine ⟨138134060642024898139400159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92089373761349932092933439 138134060642024898139400159)
      ·
        refine ⟨207201090963037347209100239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138134060642024898139400159 207201090963037347209100239)
        ·
          refine ⟨310801636444556020813650359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207201090963037347209100239 310801636444556020813650359)
          ·
            refine ⟨466202454666834031220475539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310801636444556020813650359 466202454666834031220475539)
            ·
              refine ⟨699303682000251046830713309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466202454666834031220475539 699303682000251046830713309)
              ·
                refine ⟨262238880750094142561517491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 699303682000251046830713309 262238880750094142561517491)
                ·
                  refine ⟨393358321125141213842276237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262238880750094142561517491 393358321125141213842276237)
                  ·
                    refine ⟨147509370421927955190853589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 393358321125141213842276237 147509370421927955190853589)
                    ·
                      refine ⟨3457250869263936449785631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147509370421927955190853589 3457250869263936449785631)
                      ·
                        rfl

theorem cell23_6732972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_6732972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6732972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6732972 prefixEnd_6732972 := by exact prefixLift 6732972
  have htrace : WordTrace (prefixWord ++ tailWord_6732972) baseStart_6732972 baseEnd_6732972 := by
    simpa [prefixWord, tailWord_6732972, baseEnd_6732972] using wordTrace_append hprefix tailTrace_6732972
  have hstable : (prefixWord ++ tailWord_6732972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6732972).length < 2 ^ (prefixWord ++ tailWord_6732972).sum := by decide
  have hdescent : baseEnd_6732972 < baseStart_6732972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6732972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733010 : List Nat := [3, 2, 2, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_6733010 : Nat := 118140960795 + 6733010 * 2 ^ 59
def prefixEnd_6733010 : Nat := 4983230072969 + 3 ^ 40 * 6733010 * 2
def baseEnd_6733010 : Nat := 3457270381528807301110457

theorem tailTrace_6733010 : CollatzResearch.WordTrace tailWord_6733010 prefixEnd_6733010 3457270381528807301110457 := by
  unfold tailWord_6733010
  simp only [CollatzResearch.WordTrace]
  refine ⟨61393262334365537851093121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163715366224974767602914989 61393262334365537851093121)
  ·
    refine ⟨46044946750774153388319841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61393262334365537851093121 46044946750774153388319841)
    ·
      refine ⟨34533710063080615041239881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46044946750774153388319841 34533710063080615041239881)
      ·
        refine ⟨25900282547310461280929911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34533710063080615041239881 25900282547310461280929911)
        ·
          refine ⟨38850423820965691921394867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25900282547310461280929911 38850423820965691921394867)
          ·
            refine ⟨58275635731448537882092301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38850423820965691921394867 58275635731448537882092301)
            ·
              refine ⟨21853363399293201705784613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58275635731448537882092301 21853363399293201705784613)
              ·
                refine ⟨4097505637367475319834615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21853363399293201705784613 4097505637367475319834615)
                ·
                  refine ⟨6146258456051212979751923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097505637367475319834615 6146258456051212979751923)
                  ·
                    refine ⟨9219387684076819469627885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146258456051212979751923 9219387684076819469627885)
                    ·
                      refine ⟨3457270381528807301110457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219387684076819469627885 3457270381528807301110457)
                      ·
                        rfl

theorem cell23_6733010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_6733010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733010 prefixEnd_6733010 := by exact prefixLift 6733010
  have htrace : WordTrace (prefixWord ++ tailWord_6733010) baseStart_6733010 baseEnd_6733010 := by
    simpa [prefixWord, tailWord_6733010, baseEnd_6733010] using wordTrace_append hprefix tailTrace_6733010
  have hstable : (prefixWord ++ tailWord_6733010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733010).length < 2 ^ (prefixWord ++ tailWord_6733010).sum := by decide
  have hdescent : baseEnd_6733010 < baseStart_6733010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733036 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_6733036 : Nat := 118140960795 + 6733036 * 2 ^ 59
def prefixEnd_6733036 : Nat := 4983230072969 + 3 ^ 40 * 6733036 * 2
def baseEnd_6733036 : Nat := 3457283732025824199385337

theorem tailTrace_6733036 : CollatzResearch.WordTrace tailWord_6733036 prefixEnd_6733036 3457283732025824199385337 := by
  unfold tailWord_6733036
  simp only [CollatzResearch.WordTrace]
  refine ⟨122786998817683978922409481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163715998423578638563212641 122786998817683978922409481)
  ·
    refine ⟨92090249113262984191807111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122786998817683978922409481 92090249113262984191807111)
    ·
      refine ⟨138135373669894476287710667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92090249113262984191807111 138135373669894476287710667)
      ·
        refine ⟨207203060504841714431566001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138135373669894476287710667 207203060504841714431566001)
        ·
          refine ⟨155402295378631285823674501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207203060504841714431566001 155402295378631285823674501)
          ·
            refine ⟨29137930383493366091938969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155402295378631285823674501 29137930383493366091938969)
            ·
              refine ⟨21853447787620024568954227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29137930383493366091938969 21853447787620024568954227)
              ·
                refine ⟨32780171681430036853431341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21853447787620024568954227 32780171681430036853431341)
                ·
                  refine ⟨12292564380536263820036753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32780171681430036853431341 12292564380536263820036753)
                  ·
                    refine ⟨9219423285402197865027565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12292564380536263820036753 9219423285402197865027565)
                    ·
                      refine ⟨3457283732025824199385337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219423285402197865027565 3457283732025824199385337)
                      ·
                        rfl

theorem cell23_6733036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_6733036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733036 prefixEnd_6733036 := by exact prefixLift 6733036
  have htrace : WordTrace (prefixWord ++ tailWord_6733036) baseStart_6733036 baseEnd_6733036 := by
    simpa [prefixWord, tailWord_6733036, baseEnd_6733036] using wordTrace_append hprefix tailTrace_6733036
  have hstable : (prefixWord ++ tailWord_6733036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733036).length < 2 ^ (prefixWord ++ tailWord_6733036).sum := by decide
  have hdescent : baseEnd_6733036 < baseStart_6733036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733060 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_6733060 : Nat := 118140960795 + 6733060 * 2 ^ 59
def prefixEnd_6733060 : Nat := 4983230072969 + 3 ^ 40 * 6733060 * 2
def baseEnd_6733060 : Nat := 1152432018520510701828409

theorem tailTrace_6733060 : CollatzResearch.WordTrace tailWord_6733060 prefixEnd_6733060 1152432018520510701828409 := by
  unfold tailWord_6733060
  simp only [CollatzResearch.WordTrace]
  refine ⟨122787436493640504971846317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163716581991520673295795089 122787436493640504971846317)
  ·
    refine ⟨46045288685115189364442369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122787436493640504971846317 46045288685115189364442369)
    ·
      refine ⟨34533966513836392023331777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46045288685115189364442369 34533966513836392023331777)
      ·
        refine ⟨25900474885377294017498833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34533966513836392023331777 25900474885377294017498833)
        ·
          refine ⟨19425356164032970513124125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25900474885377294017498833 19425356164032970513124125)
          ·
            refine ⟨7284508561512363942421547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19425356164032970513124125 7284508561512363942421547)
            ·
              refine ⟨10926762842268545913632321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284508561512363942421547 10926762842268545913632321)
              ·
                refine ⟨8195072131701409435224241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10926762842268545913632321 8195072131701409435224241)
                ·
                  refine ⟨6146304098776057076418181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8195072131701409435224241 6146304098776057076418181)
                  ·
                    refine ⟨1152432018520510701828409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146304098776057076418181 1152432018520510701828409)
                    ·
                      rfl

theorem cell23_6733060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_6733060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733060 prefixEnd_6733060 := by exact prefixLift 6733060
  have htrace : WordTrace (prefixWord ++ tailWord_6733060) baseStart_6733060 baseEnd_6733060 := by
    simpa [prefixWord, tailWord_6733060, baseEnd_6733060] using wordTrace_append hprefix tailTrace_6733060
  have hstable : (prefixWord ++ tailWord_6733060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733060).length < 2 ^ (prefixWord ++ tailWord_6733060).sum := by decide
  have hdescent : baseEnd_6733060 < baseStart_6733060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733090 : List Nat := [3, 3, 1, 1, 5, 1, 2, 7]
def baseStart_6733090 : Nat := 118140960795 + 6733090 * 2 ^ 59
def prefixEnd_6733090 : Nat := 4983230072969 + 3 ^ 40 * 6733090 * 2
def baseEnd_6733090 : Nat := 128048572591895073633707

theorem tailTrace_6733090 : CollatzResearch.WordTrace tailWord_6733090 prefixEnd_6733090 128048572591895073633707 := by
  unfold tailWord_6733090
  simp only [CollatzResearch.WordTrace]
  refine ⟨61393991794293081266821181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163717311451448216711523149 61393991794293081266821181)
  ·
    refine ⟨23022746922859905475057943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61393991794293081266821181 23022746922859905475057943)
    ·
      refine ⟨34534120384289858212586915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23022746922859905475057943 34534120384289858212586915)
      ·
        refine ⟨51801180576434787318880373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34534120384289858212586915 51801180576434787318880373)
        ·
          refine ⟨4856360679040761311145035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51801180576434787318880373 4856360679040761311145035)
          ·
            refine ⟨7284541018561141966717553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4856360679040761311145035 7284541018561141966717553)
            ·
              refine ⟨5463405763920856475038165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7284541018561141966717553 5463405763920856475038165)
              ·
                refine ⟨128048572591895073633707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5463405763920856475038165 128048572591895073633707)
                ·
                  rfl

theorem cell23_6733090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 7].length) (baseStart_6733090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733090 prefixEnd_6733090 := by exact prefixLift 6733090
  have htrace : WordTrace (prefixWord ++ tailWord_6733090) baseStart_6733090 baseEnd_6733090 := by
    simpa [prefixWord, tailWord_6733090, baseEnd_6733090] using wordTrace_append hprefix tailTrace_6733090
  have hstable : (prefixWord ++ tailWord_6733090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733090).length < 2 ^ (prefixWord ++ tailWord_6733090).sum := by decide
  have hdescent : baseEnd_6733090 < baseStart_6733090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733096 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6733096 : Nat := 118140960795 + 6733096 * 2 ^ 59
def prefixEnd_6733096 : Nat := 4983230072969 + 3 ^ 40 * 6733096 * 2
def baseEnd_6733096 : Nat := 3457314540865093964635061

theorem tailTrace_6733096 : CollatzResearch.WordTrace tailWord_6733096 prefixEnd_6733096 3457314540865093964635061 := by
  unfold tailWord_6733096
  simp only [CollatzResearch.WordTrace]
  refine ⟨122788093007575294046001571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163717457343433725394668761 122788093007575294046001571)
  ·
    refine ⟨184182139511362941069002357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122788093007575294046001571 184182139511362941069002357)
    ·
      refine ⟨17267075579190275725218971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184182139511362941069002357 17267075579190275725218971)
      ·
        refine ⟨25900613368785413587828457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17267075579190275725218971 25900613368785413587828457)
        ·
          refine ⟨19425460026589060190871343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25900613368785413587828457 19425460026589060190871343)
          ·
            refine ⟨29138190039883590286307015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19425460026589060190871343 29138190039883590286307015)
            ·
              refine ⟨43707285059825385429460523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29138190039883590286307015 43707285059825385429460523)
              ·
                refine ⟨65560927589738078144190785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43707285059825385429460523 65560927589738078144190785)
                ·
                  refine ⟨49170695692303558608143089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65560927589738078144190785 49170695692303558608143089)
                  ·
                    refine ⟨36878021769227668956107317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49170695692303558608143089 36878021769227668956107317)
                    ·
                      refine ⟨3457314540865093964635061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36878021769227668956107317 3457314540865093964635061)
                      ·
                        rfl

theorem cell23_6733096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6733096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733096 prefixEnd_6733096 := by exact prefixLift 6733096
  have htrace : WordTrace (prefixWord ++ tailWord_6733096) baseStart_6733096 baseEnd_6733096 := by
    simpa [prefixWord, tailWord_6733096, baseEnd_6733096] using wordTrace_append hprefix tailTrace_6733096
  have hstable : (prefixWord ++ tailWord_6733096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733096).length < 2 ^ (prefixWord ++ tailWord_6733096).sum := by decide
  have hdescent : baseEnd_6733096 < baseStart_6733096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733101 : List Nat := [1, 5, 3, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_6733101 : Nat := 118140960795 + 6733101 * 2 ^ 59
def prefixEnd_6733101 : Nat := 4983230072969 + 3 ^ 40 * 6733101 * 2
def baseEnd_6733101 : Nat := 3457317108268366445072539

theorem tailTrace_6733101 : CollatzResearch.WordTrace tailWord_6733101 prefixEnd_6733101 3457317108268366445072539 := by
  unfold tailWord_6733101
  simp only [CollatzResearch.WordTrace]
  refine ⟨245576368380132473945935157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163717578920088315963956771 245576368380132473945935157)
  ·
    refine ⟨23022784535637419432431421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245576368380132473945935157 23022784535637419432431421)
    ·
      refine ⟨8633544200864032287161783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23022784535637419432431421 8633544200864032287161783)
      ·
        refine ⟨12950316301296048430742675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8633544200864032287161783 12950316301296048430742675)
        ·
          refine ⟨19425474451944072646114013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12950316301296048430742675 19425474451944072646114013)
          ·
            refine ⟨7284552919479027242292755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19425474451944072646114013 7284552919479027242292755)
            ·
              refine ⟨10926829379218540863439133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284552919479027242292755 10926829379218540863439133)
              ·
                refine ⟨4097561017206952823789675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10926829379218540863439133 4097561017206952823789675)
                ·
                  refine ⟨6146341525810429235684513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097561017206952823789675 6146341525810429235684513)
                  ·
                    refine ⟨4609756144357821926763385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6146341525810429235684513 4609756144357821926763385)
                    ·
                      refine ⟨3457317108268366445072539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4609756144357821926763385 3457317108268366445072539)
                      ·
                        rfl

theorem cell23_6733101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_6733101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733101 prefixEnd_6733101 := by exact prefixLift 6733101
  have htrace : WordTrace (prefixWord ++ tailWord_6733101) baseStart_6733101 baseEnd_6733101 := by
    simpa [prefixWord, tailWord_6733101, baseEnd_6733101] using wordTrace_append hprefix tailTrace_6733101
  have hstable : (prefixWord ++ tailWord_6733101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733101).length < 2 ^ (prefixWord ++ tailWord_6733101).sum := by decide
  have hdescent : baseEnd_6733101 < baseStart_6733101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733196 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6733196 : Nat := 118140960795 + 6733196 * 2 ^ 59
def prefixEnd_6733196 : Nat := 4983230072969 + 3 ^ 40 * 6733196 * 2
def baseEnd_6733196 : Nat := 3457365888930543573384601

theorem tailTrace_6733196 : CollatzResearch.WordTrace tailWord_6733196 prefixEnd_6733196 3457365888930543573384601 := by
  unfold tailWord_6733196
  simp only [CollatzResearch.WordTrace]
  refine ⟨122789916657394152585321721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163719888876525536780428961 122789916657394152585321721)
  ·
    refine ⟨92092437493045614438991291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122789916657394152585321721 92092437493045614438991291)
    ·
      refine ⟨138138656239568421658486937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92092437493045614438991291 138138656239568421658486937)
      ·
        refine ⟨103603992179676316243865203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138138656239568421658486937 103603992179676316243865203)
        ·
          refine ⟨155405988269514474365797805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103603992179676316243865203 155405988269514474365797805)
          ·
            refine ⟨58277245601067927887174177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155405988269514474365797805 58277245601067927887174177)
            ·
              refine ⟨43707934200800945915380633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58277245601067927887174177 43707934200800945915380633)
              ·
                refine ⟨32780950650600709436535475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43707934200800945915380633 32780950650600709436535475)
                ·
                  refine ⟨49171425975901064154803213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32780950650600709436535475 49171425975901064154803213)
                  ·
                    refine ⟨18439284740962899058051205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49171425975901064154803213 18439284740962899058051205)
                    ·
                      refine ⟨3457365888930543573384601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18439284740962899058051205 3457365888930543573384601)
                      ·
                        rfl

theorem cell23_6733196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6733196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733196 prefixEnd_6733196 := by exact prefixLift 6733196
  have htrace : WordTrace (prefixWord ++ tailWord_6733196) baseStart_6733196 baseEnd_6733196 := by
    simpa [prefixWord, tailWord_6733196, baseEnd_6733196] using wordTrace_append hprefix tailTrace_6733196
  have hstable : (prefixWord ++ tailWord_6733196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733196).length < 2 ^ (prefixWord ++ tailWord_6733196).sum := by decide
  have hdescent : baseEnd_6733196 < baseStart_6733196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733213 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_6733213 : Nat := 118140960795 + 6733213 * 2 ^ 59
def prefixEnd_6733213 : Nat := 4983230072969 + 3 ^ 40 * 6733213 * 2
def baseEnd_6733213 : Nat := 3457374618101670006872023

theorem tailTrace_6733213 : CollatzResearch.WordTrace tailWord_6733213 prefixEnd_6733213 3457374618101670006872023 := by
  unfold tailWord_6733213
  simp only [CollatzResearch.WordTrace]
  refine ⟨245580453355726717074012293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163720302237151144716008195 245580453355726717074012293)
  ·
    refine ⟨46046335004198759451377305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245580453355726717074012293 46046335004198759451377305)
    ·
      refine ⟨34534751253149069588532979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46046335004198759451377305 34534751253149069588532979)
      ·
        refine ⟨51802126879723604382799469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34534751253149069588532979 51802126879723604382799469)
        ·
          refine ⟨19425797579896351643549801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51802126879723604382799469 19425797579896351643549801)
          ·
            refine ⟨14569348184922263732662351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19425797579896351643549801 14569348184922263732662351)
            ·
              refine ⟨21854022277383395598993527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14569348184922263732662351 21854022277383395598993527)
              ·
                refine ⟨32781033416075093398490291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21854022277383395598993527 32781033416075093398490291)
                ·
                  refine ⟨49171550124112640097735437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32781033416075093398490291 49171550124112640097735437)
                  ·
                    refine ⟨18439331296542240036650789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49171550124112640097735437 18439331296542240036650789)
                    ·
                      refine ⟨3457374618101670006872023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18439331296542240036650789 3457374618101670006872023)
                      ·
                        rfl

theorem cell23_6733213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_6733213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733213 prefixEnd_6733213 := by exact prefixLift 6733213
  have htrace : WordTrace (prefixWord ++ tailWord_6733213) baseStart_6733213 baseEnd_6733213 := by
    simpa [prefixWord, tailWord_6733213, baseEnd_6733213] using wordTrace_append hprefix tailTrace_6733213
  have hstable : (prefixWord ++ tailWord_6733213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733213).length < 2 ^ (prefixWord ++ tailWord_6733213).sum := by decide
  have hdescent : baseEnd_6733213 < baseStart_6733213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733223 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6733223 : Nat := 118140960795 + 6733223 * 2 ^ 59
def prefixEnd_6733223 : Nat := 4983230072969 + 3 ^ 40 * 6733223 * 2
def baseEnd_6733223 : Nat := 1152459917636071655915659

theorem tailTrace_6733223 : CollatzResearch.WordTrace tailWord_6733223 prefixEnd_6733223 1152459917636071655915659 := by
  unfold tailWord_6733223
  simp only [CollatzResearch.WordTrace]
  refine ⟨245580818085690488781876323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163720545390460325854584215 245580818085690488781876323)
  ·
    refine ⟨368371227128535733172814485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245580818085690488781876323 368371227128535733172814485)
    ·
      refine ⟨17267401271650112492475679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 368371227128535733172814485 17267401271650112492475679)
      ·
        refine ⟨25901101907475168738713519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17267401271650112492475679 25901101907475168738713519)
        ·
          refine ⟨38851652861212753108070279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25901101907475168738713519 38851652861212753108070279)
          ·
            refine ⟨58277479291819129662105419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38851652861212753108070279 58277479291819129662105419)
            ·
              refine ⟨87416218937728694493158129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58277479291819129662105419 87416218937728694493158129)
              ·
                refine ⟨65562164203296520869868597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87416218937728694493158129 65562164203296520869868597)
                ·
                  refine ⟨6146452894059048831550181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65562164203296520869868597 6146452894059048831550181)
                  ·
                    refine ⟨1152459917636071655915659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146452894059048831550181 1152459917636071655915659)
                    ·
                      rfl

theorem cell23_6733223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6733223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733223 prefixEnd_6733223 := by exact prefixLift 6733223
  have htrace : WordTrace (prefixWord ++ tailWord_6733223) baseStart_6733223 baseEnd_6733223 := by
    simpa [prefixWord, tailWord_6733223, baseEnd_6733223] using wordTrace_append hprefix tailTrace_6733223
  have hstable : (prefixWord ++ tailWord_6733223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733223).length < 2 ^ (prefixWord ++ tailWord_6733223).sum := by decide
  have hdescent : baseEnd_6733223 < baseStart_6733223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733233 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_6733233 : Nat := 118140960795 + 6733233 * 2 ^ 59
def prefixEnd_6733233 : Nat := 4983230072969 + 3 ^ 40 * 6733233 * 2
def baseEnd_6733233 : Nat := 3457384887714759928621931

theorem tailTrace_6733233 : CollatzResearch.WordTrace tailWord_6733233 prefixEnd_6733233 3457384887714759928621931 := by
  unfold tailWord_6733233
  simp only [CollatzResearch.WordTrace]
  refine ⟨245581182815654260489740353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163720788543769506993160235 245581182815654260489740353)
  ·
    refine ⟨184185887111740695367305265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245581182815654260489740353 184185887111740695367305265)
    ·
      refine ⟨138139415333805521525478949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184185887111740695367305265 138139415333805521525478949)
      ·
        refine ⟨25901140375088535286027303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138139415333805521525478949 25901140375088535286027303)
        ·
          refine ⟨38851710562632802929040955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25901140375088535286027303 38851710562632802929040955)
          ·
            refine ⟨58277565843949204393561433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38851710562632802929040955 58277565843949204393561433)
            ·
              refine ⟨43708174382961903295171075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58277565843949204393561433 43708174382961903295171075)
              ·
                refine ⟨65562261574442854942756613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43708174382961903295171075 65562261574442854942756613)
                ·
                  refine ⟨12292924045208035301766865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65562261574442854942756613 12292924045208035301766865)
                  ·
                    refine ⟨9219693033906026476325149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12292924045208035301766865 9219693033906026476325149)
                    ·
                      refine ⟨3457384887714759928621931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219693033906026476325149 3457384887714759928621931)
                      ·
                        rfl

theorem cell23_6733233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_6733233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733233 prefixEnd_6733233 := by exact prefixLift 6733233
  have htrace : WordTrace (prefixWord ++ tailWord_6733233) baseStart_6733233 baseEnd_6733233 := by
    simpa [prefixWord, tailWord_6733233, baseEnd_6733233] using wordTrace_append hprefix tailTrace_6733233
  have hstable : (prefixWord ++ tailWord_6733233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733233).length < 2 ^ (prefixWord ++ tailWord_6733233).sum := by decide
  have hdescent : baseEnd_6733233 < baseStart_6733233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733240 : List Nat := [2, 1, 2, 1, 2, 2, 4, 4, 1, 4]
def baseStart_6733240 : Nat := 118140960795 + 6733240 * 2 ^ 59
def prefixEnd_6733240 : Nat := 4983230072969 + 3 ^ 40 * 6733240 * 2
def baseEnd_6733240 : Nat := 1152462827359780467078133

theorem tailTrace_6733240 : CollatzResearch.WordTrace tailWord_6733240 prefixEnd_6733240 1152462827359780467078133 := by
  unfold tailWord_6733240
  simp only [CollatzResearch.WordTrace]
  refine ⟨122790719063314450342622587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163720958751085933790163449 122790719063314450342622587)
  ·
    refine ⟨184186078594971675513933881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122790719063314450342622587 184186078594971675513933881)
    ·
      refine ⟨138139558946228756635450411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184186078594971675513933881 138139558946228756635450411)
      ·
        refine ⟨207209338419343134953175617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138139558946228756635450411 207209338419343134953175617)
        ·
          refine ⟨155407003814507351214881713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207209338419343134953175617 155407003814507351214881713)
          ·
            refine ⟨116555252860880513411161285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155407003814507351214881713 116555252860880513411161285)
            ·
              refine ⟨21854109911415096264592741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116555252860880513411161285 21854109911415096264592741)
              ·
                refine ⟨4097645608390330549611139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21854109911415096264592741 4097645608390330549611139)
                ·
                  refine ⟨6146468412585495824416709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097645608390330549611139 6146468412585495824416709)
                  ·
                    refine ⟨1152462827359780467078133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146468412585495824416709 1152462827359780467078133)
                    ·
                      rfl

theorem cell23_6733240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_6733240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733240 prefixEnd_6733240 := by exact prefixLift 6733240
  have htrace : WordTrace (prefixWord ++ tailWord_6733240) baseStart_6733240 baseEnd_6733240 := by
    simpa [prefixWord, tailWord_6733240, baseEnd_6733240] using wordTrace_append hprefix tailTrace_6733240
  have hstable : (prefixWord ++ tailWord_6733240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733240).length < 2 ^ (prefixWord ++ tailWord_6733240).sum := by decide
  have hdescent : baseEnd_6733240 < baseStart_6733240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733256 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_6733256 : Nat := 118140960795 + 6733256 * 2 ^ 59
def prefixEnd_6733256 : Nat := 4983230072969 + 3 ^ 40 * 6733256 * 2
def baseEnd_6733256 : Nat := 3457396697769813338634325

theorem tailTrace_6733256 : CollatzResearch.WordTrace tailWord_6733256 prefixEnd_6733256 3457396697769813338634325 := by
  unfold tailWord_6733256
  simp only [CollatzResearch.WordTrace]
  refine ⟨122791010847285467708913811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163721347796380623611885081 122791010847285467708913811)
  ·
    refine ⟨184186516270928201563370717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122791010847285467708913811 184186516270928201563370717)
    ·
      refine ⟨69069943601598075586264019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184186516270928201563370717 69069943601598075586264019)
      ·
        refine ⟨103604915402397113379396029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69069943601598075586264019 103604915402397113379396029)
        ·
          refine ⟨38851843275898917517273511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103604915402397113379396029 38851843275898917517273511)
          ·
            refine ⟨58277764913848376275910267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38851843275898917517273511 58277764913848376275910267)
            ·
              refine ⟨87416647370772564413865401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58277764913848376275910267 87416647370772564413865401)
              ·
                refine ⟨65562485528079423310399051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87416647370772564413865401 65562485528079423310399051)
                ·
                  refine ⟨98343728292119134965598577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65562485528079423310399051 98343728292119134965598577)
                  ·
                    refine ⟨73757796219089351224198933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98343728292119134965598577 73757796219089351224198933)
                    ·
                      refine ⟨3457396697769813338634325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73757796219089351224198933 3457396697769813338634325)
                      ·
                        rfl

theorem cell23_6733256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_6733256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733256 prefixEnd_6733256 := by exact prefixLift 6733256
  have htrace : WordTrace (prefixWord ++ tailWord_6733256) baseStart_6733256 baseEnd_6733256 := by
    simpa [prefixWord, tailWord_6733256, baseEnd_6733256] using wordTrace_append hprefix tailTrace_6733256
  have hstable : (prefixWord ++ tailWord_6733256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733256).length < 2 ^ (prefixWord ++ tailWord_6733256).sum := by decide
  have hdescent : baseEnd_6733256 < baseStart_6733256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733297 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_6733297 : Nat := 118140960795 + 6733297 * 2 ^ 59
def prefixEnd_6733297 : Nat := 4983230072969 + 3 ^ 40 * 6733297 * 2
def baseEnd_6733297 : Nat := 3457417750476647678221637

theorem tailTrace_6733297 : CollatzResearch.WordTrace tailWord_6733297 prefixEnd_6733297 3457417750476647678221637 := by
  unfold tailWord_6733297
  simp only [CollatzResearch.WordTrace]
  refine ⟨245583517087422399420070145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163722344724948266280046763 245583517087422399420070145)
  ·
    refine ⟨184187637815566799565052609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245583517087422399420070145 184187637815566799565052609)
    ·
      refine ⟨138140728361675099673789457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184187637815566799565052609 138140728361675099673789457)
      ·
        refine ⟨103605546271256324755342093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138140728361675099673789457 103605546271256324755342093)
        ·
          refine ⟨38852079851721121783253285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103605546271256324755342093 38852079851721121783253285)
          ·
            refine ⟨7284764972197710334359991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38852079851721121783253285 7284764972197710334359991)
            ·
              refine ⟨10927147458296565501539987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284764972197710334359991 10927147458296565501539987)
              ·
                refine ⟨16390721187444848252309981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10927147458296565501539987 16390721187444848252309981)
                ·
                  refine ⟨6146520445291818094616243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16390721187444848252309981 6146520445291818094616243)
                  ·
                    refine ⟨9219780667937727141924365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146520445291818094616243 9219780667937727141924365)
                    ·
                      refine ⟨3457417750476647678221637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219780667937727141924365 3457417750476647678221637)
                      ·
                        rfl

theorem cell23_6733297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_6733297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733297 prefixEnd_6733297 := by exact prefixLift 6733297
  have htrace : WordTrace (prefixWord ++ tailWord_6733297) baseStart_6733297 baseEnd_6733297 := by
    simpa [prefixWord, tailWord_6733297, baseEnd_6733297] using wordTrace_append hprefix tailTrace_6733297
  have hstable : (prefixWord ++ tailWord_6733297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733297).length < 2 ^ (prefixWord ++ tailWord_6733297).sum := by decide
  have hdescent : baseEnd_6733297 < baseStart_6733297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733303 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 2, 6, 2]
def baseStart_6733303 : Nat := 118140960795 + 6733303 * 2 ^ 59
def prefixEnd_6733303 : Nat := 4983230072969 + 3 ^ 40 * 6733303 * 2
def baseEnd_6733303 : Nat := 3457420831360574654746609

theorem tailTrace_6733303 : CollatzResearch.WordTrace tailWord_6733303 prefixEnd_6733303 3457420831360574654746609 := by
  unfold tailWord_6733303
  simp only [CollatzResearch.WordTrace]
  refine ⟨245583735925400662444788563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163722490616933774963192375 245583735925400662444788563)
  ·
    refine ⟨368375603888100993667182845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245583735925400662444788563 368375603888100993667182845)
    ·
      refine ⟨138140851458037872625193567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368375603888100993667182845 138140851458037872625193567)
      ·
        refine ⟨207211277187056808937790351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138140851458037872625193567 207211277187056808937790351)
        ·
          refine ⟨310816915780585213406685527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207211277187056808937790351 310816915780585213406685527)
          ·
            refine ⟨466225373670877820110028291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310816915780585213406685527 466225373670877820110028291)
            ·
              refine ⟨699338060506316730165042437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466225373670877820110028291 699338060506316730165042437)
              ·
                refine ⟨131125886344934386905945457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 699338060506316730165042437 131125886344934386905945457)
                ·
                  refine ⟨98344414758700790179459093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131125886344934386905945457 98344414758700790179459093)
                  ·
                    refine ⟨4609894441814099539662145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98344414758700790179459093 4609894441814099539662145)
                    ·
                      refine ⟨3457420831360574654746609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4609894441814099539662145 3457420831360574654746609)
                      ·
                        rfl

theorem cell23_6733303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_6733303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733303 prefixEnd_6733303 := by exact prefixLift 6733303
  have htrace : WordTrace (prefixWord ++ tailWord_6733303) baseStart_6733303 baseEnd_6733303 := by
    simpa [prefixWord, tailWord_6733303, baseEnd_6733303] using wordTrace_append hprefix tailTrace_6733303
  have hstable : (prefixWord ++ tailWord_6733303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733303).length < 2 ^ (prefixWord ++ tailWord_6733303).sum := by decide
  have hdescent : baseEnd_6733303 < baseStart_6733303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733320 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_6733320 : Nat := 118140960795 + 6733320 * 2 ^ 59
def prefixEnd_6733320 : Nat := 4983230072969 + 3 ^ 40 * 6733320 * 2
def baseEnd_6733320 : Nat := 3457429560531701088234031

theorem tailTrace_6733320 : CollatzResearch.WordTrace tailWord_6733320 prefixEnd_6733320 3457429560531701088234031 := by
  unfold tailWord_6733320
  simp only [CollatzResearch.WordTrace]
  refine ⟨122792177983169537174078707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163722903977559382898771609 122792177983169537174078707)
  ·
    refine ⟨184188266974754305761118061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122792177983169537174078707 184188266974754305761118061)
    ·
      refine ⟨69070600115532864660419273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184188266974754305761118061 69070600115532864660419273)
      ·
        refine ⟨51802950086649648495314455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69070600115532864660419273 51802950086649648495314455)
        ·
          refine ⟨77704425129974472742971683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51802950086649648495314455 77704425129974472742971683)
          ·
            refine ⟨116556637694961709114457525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77704425129974472742971683 116556637694961709114457525)
            ·
              refine ⟨10927184783902660229480393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116556637694961709114457525 10927184783902660229480393)
              ·
                refine ⟨8195388587926995172110295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10927184783902660229480393 8195388587926995172110295)
                ·
                  refine ⟨12293082881890492758165443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8195388587926995172110295 12293082881890492758165443)
                  ·
                    refine ⟨18439624322835739137248165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12293082881890492758165443 18439624322835739137248165)
                    ·
                      refine ⟨3457429560531701088234031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18439624322835739137248165 3457429560531701088234031)
                      ·
                        rfl

theorem cell23_6733320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_6733320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733320 prefixEnd_6733320 := by exact prefixLift 6733320
  have htrace : WordTrace (prefixWord ++ tailWord_6733320) baseStart_6733320 baseEnd_6733320 := by
    simpa [prefixWord, tailWord_6733320, baseEnd_6733320] using wordTrace_append hprefix tailTrace_6733320
  have hstable : (prefixWord ++ tailWord_6733320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733320).length < 2 ^ (prefixWord ++ tailWord_6733320).sum := by decide
  have hdescent : baseEnd_6733320 < baseStart_6733320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733333 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_6733333 : Nat := 118140960795 + 6733333 * 2 ^ 59
def prefixEnd_6733333 : Nat := 4983230072969 + 3 ^ 40 * 6733333 * 2
def baseEnd_6733333 : Nat := 3457436235780209537371471

theorem tailTrace_6733333 : CollatzResearch.WordTrace tailWord_6733333 prefixEnd_6733333 3457436235780209537371471 := by
  unfold tailWord_6733333
  simp only [CollatzResearch.WordTrace]
  refine ⟨245584830115291977568380653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163723220076861318378920435 245584830115291977568380653)
  ·
    refine ⟨92094311293234491588142745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245584830115291977568380653 92094311293234491588142745)
    ·
      refine ⟨69070733469925868691107059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92094311293234491588142745 69070733469925868691107059)
      ·
        refine ⟨103606100204888803036660589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69070733469925868691107059 103606100204888803036660589)
        ·
          refine ⟨38852287576833301138747721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103606100204888803036660589 38852287576833301138747721)
          ·
            refine ⟨29139215682624975854060791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38852287576833301138747721 29139215682624975854060791)
            ·
              refine ⟨43708823523937463781091187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29139215682624975854060791 43708823523937463781091187)
              ·
                refine ⟨65563235285906195671636781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43708823523937463781091187 65563235285906195671636781)
                ·
                  refine ⟨24586213232214823376863793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65563235285906195671636781 24586213232214823376863793)
                  ·
                    refine ⟨18439659924161117532647845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24586213232214823376863793 18439659924161117532647845)
                    ·
                      refine ⟨3457436235780209537371471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18439659924161117532647845 3457436235780209537371471)
                      ·
                        rfl

theorem cell23_6733333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_6733333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733333 prefixEnd_6733333 := by exact prefixLift 6733333
  have htrace : WordTrace (prefixWord ++ tailWord_6733333) baseStart_6733333 baseEnd_6733333 := by
    simpa [prefixWord, tailWord_6733333, baseEnd_6733333] using wordTrace_append hprefix tailTrace_6733333
  have hstable : (prefixWord ++ tailWord_6733333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733333).length < 2 ^ (prefixWord ++ tailWord_6733333).sum := by decide
  have hdescent : baseEnd_6733333 < baseStart_6733333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733342 : List Nat := [4, 3, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6733342 : Nat := 118140960795 + 6733342 * 2 ^ 59
def prefixEnd_6733342 : Nat := 4983230072969 + 3 ^ 40 * 6733342 * 2
def baseEnd_6733342 : Nat := 1152480285702033334052977

theorem tailTrace_6733342 : CollatzResearch.WordTrace tailWord_6733342 prefixEnd_6733342 1152480285702033334052977 := by
  unfold tailWord_6733342
  simp only [CollatzResearch.WordTrace]
  refine ⟨30698144796532421513182285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163723438914839581403638853 30698144796532421513182285)
  ·
    refine ⟨11511804298699658067443357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30698144796532421513182285 11511804298699658067443357)
    ·
      refine ⟨4316926612012371775291259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11511804298699658067443357 4316926612012371775291259)
      ·
        refine ⟨6475389918018557662936889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316926612012371775291259 6475389918018557662936889)
        ·
          refine ⟨4856542438513918247202667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6475389918018557662936889 4856542438513918247202667)
          ·
            refine ⟨7284813657770877370804001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4856542438513918247202667 7284813657770877370804001)
            ·
              refine ⟨5463610243328158028103001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7284813657770877370804001 5463610243328158028103001)
              ·
                refine ⟨4097707682496118521077251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463610243328158028103001 4097707682496118521077251)
                ·
                  refine ⟨6146561523744177781615877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097707682496118521077251 6146561523744177781615877)
                  ·
                    refine ⟨1152480285702033334052977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146561523744177781615877 1152480285702033334052977)
                    ·
                      rfl

theorem cell23_6733342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6733342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733342 prefixEnd_6733342 := by exact prefixLift 6733342
  have htrace : WordTrace (prefixWord ++ tailWord_6733342) baseStart_6733342 baseEnd_6733342 := by
    simpa [prefixWord, tailWord_6733342, baseEnd_6733342] using wordTrace_append hprefix tailTrace_6733342
  have hstable : (prefixWord ++ tailWord_6733342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733342).length < 2 ^ (prefixWord ++ tailWord_6733342).sum := by decide
  have hdescent : baseEnd_6733342 < baseStart_6733342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733347 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 2, 4]
def baseStart_6733347 : Nat := 118140960795 + 6733347 * 2 ^ 59
def prefixEnd_6733347 : Nat := 4983230072969 + 3 ^ 40 * 6733347 * 2
def baseEnd_6733347 : Nat := 1152481141503124160865469

theorem tailTrace_6733347 : CollatzResearch.WordTrace tailWord_6733347 prefixEnd_6733347 1152481141503124160865469 := by
  unfold tailWord_6733347
  simp only [CollatzResearch.WordTrace]
  refine ⟨245585340737241257959390295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163723560491494171972926863 245585340737241257959390295)
  ·
    refine ⟨368378011105861886939085443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245585340737241257959390295 368378011105861886939085443)
    ·
      refine ⟨552567016658792830408628165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368378011105861886939085443 552567016658792830408628165)
      ·
        refine ⟨103606315623523655701617781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 552567016658792830408628165 103606315623523655701617781)
        ·
          refine ⟨9713092089705342722026667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103606315623523655701617781 9713092089705342722026667)
          ·
            refine ⟨14569638134558014083040001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9713092089705342722026667 14569638134558014083040001)
            ·
              refine ⟨10927228600918510562280001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14569638134558014083040001 10927228600918510562280001)
              ·
                refine ⟨8195421450688882921710001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10927228600918510562280001 8195421450688882921710001)
                ·
                  refine ⟨6146566088016662191282501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8195421450688882921710001 6146566088016662191282501)
                  ·
                    refine ⟨1152481141503124160865469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146566088016662191282501 1152481141503124160865469)
                    ·
                      rfl

theorem cell23_6733347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 4].length) (baseStart_6733347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733347 prefixEnd_6733347 := by exact prefixLift 6733347
  have htrace : WordTrace (prefixWord ++ tailWord_6733347) baseStart_6733347 baseEnd_6733347 := by
    simpa [prefixWord, tailWord_6733347, baseEnd_6733347] using wordTrace_append hprefix tailTrace_6733347
  have hstable : (prefixWord ++ tailWord_6733347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733347).length < 2 ^ (prefixWord ++ tailWord_6733347).sum := by decide
  have hdescent : baseEnd_6733347 < baseStart_6733347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733370 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_6733370 : Nat := 118140960795 + 6733370 * 2 ^ 59
def prefixEnd_6733370 : Nat := 4983230072969 + 3 ^ 40 * 6733370 * 2
def baseEnd_6733370 : Nat := 3457455234564425892608801

theorem tailTrace_6733370 : CollatzResearch.WordTrace tailWord_6733370 prefixEnd_6733370 3457455234564425892608801 := by
  unfold tailWord_6733370
  simp only [CollatzResearch.WordTrace]
  refine ⟨61396544904039483221869391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163724119744105288591651709 61396544904039483221869391)
  ·
    refine ⟨92094817356059224832804087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61396544904039483221869391 92094817356059224832804087)
    ·
      refine ⟨138142226034088837249206131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92094817356059224832804087 138142226034088837249206131)
      ·
        refine ⟨207213339051133255873809197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138142226034088837249206131 207213339051133255873809197)
        ·
          refine ⟨77705002144174970952678449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207213339051133255873809197 77705002144174970952678449)
          ·
            refine ⟨58278751608131228214508837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77705002144174970952678449 58278751608131228214508837)
            ·
              refine ⟨10927265926524605290220407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58278751608131228214508837 10927265926524605290220407)
              ·
                refine ⟨16390898889786907935330611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10927265926524605290220407 16390898889786907935330611)
                ·
                  refine ⟨24586348334680361902995917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16390898889786907935330611 24586348334680361902995917)
                  ·
                    refine ⟨9219880625505135713623469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24586348334680361902995917 9219880625505135713623469)
                    ·
                      refine ⟨3457455234564425892608801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219880625505135713623469 3457455234564425892608801)
                      ·
                        rfl

theorem cell23_6733370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_6733370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733370 prefixEnd_6733370 := by exact prefixLift 6733370
  have htrace : WordTrace (prefixWord ++ tailWord_6733370) baseStart_6733370 baseEnd_6733370 := by
    simpa [prefixWord, tailWord_6733370, baseEnd_6733370] using wordTrace_append hprefix tailTrace_6733370
  have hstable : (prefixWord ++ tailWord_6733370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733370).length < 2 ^ (prefixWord ++ tailWord_6733370).sum := by decide
  have hdescent : baseEnd_6733370 < baseStart_6733370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733398 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_6733398 : Nat := 118140960795 + 6733398 * 2 ^ 59
def prefixEnd_6733398 : Nat := 4983230072969 + 3 ^ 40 * 6733398 * 2
def baseEnd_6733398 : Nat := 1152489870674250594352891

theorem tailTrace_6733398 : CollatzResearch.WordTrace tailWord_6733398 prefixEnd_6733398 1152489870674250594352891 := by
  unfold tailWord_6733398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349200053753530854343553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163724800573370995779664565 15349200053753530854343553)
  ·
    refine ⟨11511900040315148140757665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15349200053753530854343553 11511900040315148140757665)
    ·
      refine ⟨8633925030236361105568249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11511900040315148140757665 8633925030236361105568249)
      ·
        refine ⟨6475443772677270829176187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8633925030236361105568249 6475443772677270829176187)
        ·
          refine ⟨9713165659015906243764281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6475443772677270829176187 9713165659015906243764281)
          ·
            refine ⟨7284874244261929682823211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9713165659015906243764281 7284874244261929682823211)
            ·
              refine ⟨10927311366392894524234817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284874244261929682823211 10927311366392894524234817)
              ·
                refine ⟨8195483524794670893176113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10927311366392894524234817 8195483524794670893176113)
                ·
                  refine ⟨6146612643596003169882085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8195483524794670893176113 6146612643596003169882085)
                  ·
                    refine ⟨1152489870674250594352891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146612643596003169882085 1152489870674250594352891)
                    ·
                      rfl

theorem cell23_6733398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_6733398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733398 prefixEnd_6733398 := by exact prefixLift 6733398
  have htrace : WordTrace (prefixWord ++ tailWord_6733398) baseStart_6733398 baseEnd_6733398 := by
    simpa [prefixWord, tailWord_6733398, baseEnd_6733398] using wordTrace_append hprefix tailTrace_6733398
  have hstable : (prefixWord ++ tailWord_6733398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733398).length < 2 ^ (prefixWord ++ tailWord_6733398).sum := by decide
  have hdescent : baseEnd_6733398 < baseStart_6733398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733404 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_6733404 : Nat := 118140960795 + 6733404 * 2 ^ 59
def prefixEnd_6733404 : Nat := 4983230072969 + 3 ^ 40 * 6733404 * 2
def baseEnd_6733404 : Nat := 3457472692906678759583645

theorem tailTrace_6733404 : CollatzResearch.WordTrace tailWord_6733404 prefixEnd_6733404 3457472692906678759583645 := by
  unfold tailWord_6733404
  simp only [CollatzResearch.WordTrace]
  refine ⟨122793709849017378347107633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163724946465356504462810177 122793709849017378347107633)
  ·
    refine ⟨92095282386763033760330725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122793709849017378347107633 92095282386763033760330725)
    ·
      refine ⟨17267865447518068830062011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92095282386763033760330725 17267865447518068830062011)
      ·
        refine ⟨25901798171277103245093017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17267865447518068830062011 25901798171277103245093017)
        ·
          refine ⟨19426348628457827433819763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25901798171277103245093017 19426348628457827433819763)
          ·
            refine ⟨29139522942686741150729645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19426348628457827433819763 29139522942686741150729645)
            ·
              refine ⟨10927321103507527931523617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29139522942686741150729645 10927321103507527931523617)
              ·
                refine ⟨8195490827630645948642713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10927321103507527931523617 8195490827630645948642713)
                ·
                  refine ⟨6146618120722984461482035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8195490827630645948642713 6146618120722984461482035)
                  ·
                    refine ⟨9219927181084476692223053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146618120722984461482035 9219927181084476692223053)
                    ·
                      refine ⟨3457472692906678759583645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219927181084476692223053 3457472692906678759583645)
                      ·
                        rfl

theorem cell23_6733404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_6733404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733404 prefixEnd_6733404 := by exact prefixLift 6733404
  have htrace : WordTrace (prefixWord ++ tailWord_6733404) baseStart_6733404 baseEnd_6733404 := by
    simpa [prefixWord, tailWord_6733404, baseEnd_6733404] using wordTrace_append hprefix tailTrace_6733404
  have hstable : (prefixWord ++ tailWord_6733404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733404).length < 2 ^ (prefixWord ++ tailWord_6733404).sum := by decide
  have hdescent : baseEnd_6733404 < baseStart_6733404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733421 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_6733421 : Nat := 118140960795 + 6733421 * 2 ^ 59
def prefixEnd_6733421 : Nat := 4983230072969 + 3 ^ 40 * 6733421 * 2
def baseEnd_6733421 : Nat := 3457481422077805193071067

theorem tailTrace_6733421 : CollatzResearch.WordTrace tailWord_6733421 prefixEnd_6733421 3457481422077805193071067 := by
  unfold tailWord_6733421
  simp only [CollatzResearch.WordTrace]
  refine ⟨245588039738973168597584117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163725359825982112398389411 245588039738973168597584117)
  ·
    refine ⟨23023878725528734556023511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245588039738973168597584117 23023878725528734556023511)
    ·
      refine ⟨34535818088293101834035267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23023878725528734556023511 34535818088293101834035267)
      ·
        refine ⟨51803727132439652751052901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34535818088293101834035267 51803727132439652751052901)
        ·
          refine ⟨9713198837332434890822419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51803727132439652751052901 9713198837332434890822419)
          ·
            refine ⟨14569798255998652336233629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9713198837332434890822419 14569798255998652336233629)
            ·
              refine ⟨5463674345999494626087611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14569798255998652336233629 5463674345999494626087611)
              ·
                refine ⟨8195511518999241939131417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463674345999494626087611 8195511518999241939131417)
                ·
                  refine ⟨6146633639249431454348563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8195511518999241939131417 6146633639249431454348563)
                  ·
                    refine ⟨9219950458874147181522845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146633639249431454348563 9219950458874147181522845)
                    ·
                      refine ⟨3457481422077805193071067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9219950458874147181522845 3457481422077805193071067)
                      ·
                        rfl

theorem cell23_6733421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_6733421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733421 prefixEnd_6733421 := by exact prefixLift 6733421
  have htrace : WordTrace (prefixWord ++ tailWord_6733421) baseStart_6733421 baseEnd_6733421 := by
    simpa [prefixWord, tailWord_6733421, baseEnd_6733421] using wordTrace_append hprefix tailTrace_6733421
  have hstable : (prefixWord ++ tailWord_6733421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733421).length < 2 ^ (prefixWord ++ tailWord_6733421).sum := by decide
  have hdescent : baseEnd_6733421 < baseStart_6733421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733433 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 7]
def baseStart_6733433 : Nat := 118140960795 + 6733433 * 2 ^ 59
def prefixEnd_6733433 : Nat := 4983230072969 + 3 ^ 40 * 6733433 * 2
def baseEnd_6733433 : Nat := 384165287093962127346779

theorem tailTrace_6733433 : CollatzResearch.WordTrace tailWord_6733433 prefixEnd_6733433 384165287093962127346779 := by
  unfold tailWord_6733433
  simp only [CollatzResearch.WordTrace]
  refine ⟨245588477414929694647020953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163725651609953129764680635 245588477414929694647020953)
  ·
    refine ⟨184191358061197270985265715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245588477414929694647020953 184191358061197270985265715)
    ·
      refine ⟨276287037091795906477898573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184191358061197270985265715 276287037091795906477898573)
      ·
        refine ⟨103607638909423464929211965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276287037091795906477898573 103607638909423464929211965)
        ·
          refine ⟨38852864591033799348454487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103607638909423464929211965 38852864591033799348454487)
          ·
            refine ⟨58279296886550699022681731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38852864591033799348454487 58279296886550699022681731)
            ·
              refine ⟨87418945329826048534022597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58279296886550699022681731 87418945329826048534022597)
              ·
                refine ⟨16391052249342384100129237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87418945329826048534022597 16391052249342384100129237)
                ·
                  refine ⟨384165287093962127346779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16391052249342384100129237 384165287093962127346779)
                  ·
                    rfl

theorem cell23_6733433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_6733433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733433 prefixEnd_6733433 := by exact prefixLift 6733433
  have htrace : WordTrace (prefixWord ++ tailWord_6733433) baseStart_6733433 baseEnd_6733433 := by
    simpa [prefixWord, tailWord_6733433, baseEnd_6733433] using wordTrace_append hprefix tailTrace_6733433
  have hstable : (prefixWord ++ tailWord_6733433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733433).length < 2 ^ (prefixWord ++ tailWord_6733433).sum := by decide
  have hdescent : baseEnd_6733433 < baseStart_6733433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733520 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3]
def baseStart_6733520 : Nat := 118140960795 + 6733520 * 2 ^ 59
def prefixEnd_6733520 : Nat := 4983230072969 + 3 ^ 40 * 6733520 * 2
def baseEnd_6733520 : Nat := 3457532256662600305733111

theorem tailTrace_6733520 : CollatzResearch.WordTrace tailWord_6733520 prefixEnd_6733520 3457532256662600305733111 := by
  unfold tailWord_6733520
  simp only [CollatzResearch.WordTrace]
  refine ⟨122795825282807254252719007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163727767043743005670292009 122795825282807254252719007)
  ·
    refine ⟨184193737924210881379078511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122795825282807254252719007 184193737924210881379078511)
    ·
      refine ⟨276290606886316322068617767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184193737924210881379078511 276290606886316322068617767)
      ·
        refine ⟨414435910329474483102926651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276290606886316322068617767 414435910329474483102926651)
        ·
          refine ⟨621653865494211724654389977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414435910329474483102926651 621653865494211724654389977)
          ·
            refine ⟨466240399120658793490792483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621653865494211724654389977 466240399120658793490792483)
            ·
              refine ⟨699360598680988190236188725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466240399120658793490792483 699360598680988190236188725)
              ·
                refine ⟨65565056126342642834642693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 699360598680988190236188725 65565056126342642834642693)
                ·
                  refine ⟨12293448023689245531495505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65565056126342642834642693 12293448023689245531495505)
                  ·
                    refine ⟨9220086017766934148621629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12293448023689245531495505 9220086017766934148621629)
                    ·
                      refine ⟨3457532256662600305733111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9220086017766934148621629 3457532256662600305733111)
                      ·
                        rfl

theorem cell23_6733520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_6733520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733520 prefixEnd_6733520 := by exact prefixLift 6733520
  have htrace : WordTrace (prefixWord ++ tailWord_6733520) baseStart_6733520 baseEnd_6733520 := by
    simpa [prefixWord, tailWord_6733520, baseEnd_6733520] using wordTrace_append hprefix tailTrace_6733520
  have hstable : (prefixWord ++ tailWord_6733520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733520).length < 2 ^ (prefixWord ++ tailWord_6733520).sum := by decide
  have hdescent : baseEnd_6733520 < baseStart_6733520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733540 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 6]
def baseStart_6733540 : Nat := 118140960795 + 6733540 * 2 ^ 59
def prefixEnd_6733540 : Nat := 4983230072969 + 3 ^ 40 * 6733540 * 2
def baseEnd_6733540 : Nat := 384171391808410025275891

theorem tailTrace_6733540 : CollatzResearch.WordTrace tailWord_6733540 prefixEnd_6733540 384171391808410025275891 := by
  unfold tailWord_6733540
  simp only [CollatzResearch.WordTrace]
  refine ⟨122796190012771025960583037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163728253350361367947444049 122796190012771025960583037)
  ·
    refine ⟨46048571254789134735218639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122796190012771025960583037 46048571254789134735218639)
    ·
      refine ⟨69072856882183702102827959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46048571254789134735218639 69072856882183702102827959)
      ·
        refine ⟨103609285323275553154241939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69072856882183702102827959 103609285323275553154241939)
        ·
          refine ⟨155413927984913329731362909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103609285323275553154241939 155413927984913329731362909)
          ·
            refine ⟨58280222994342498649261091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155413927984913329731362909 58280222994342498649261091)
            ·
              refine ⟨87420334491513747973891637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58280222994342498649261091 87420334491513747973891637)
              ·
                refine ⟨8195656358579413872552341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87420334491513747973891637 8195656358579413872552341)
                ·
                  refine ⟨384171391808410025275891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8195656358579413872552341 384171391808410025275891)
                  ·
                    rfl

theorem cell23_6733540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_6733540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733540 prefixEnd_6733540 := by exact prefixLift 6733540
  have htrace : WordTrace (prefixWord ++ tailWord_6733540) baseStart_6733540 baseEnd_6733540 := by
    simpa [prefixWord, tailWord_6733540, baseEnd_6733540] using wordTrace_append hprefix tailTrace_6733540
  have hstable : (prefixWord ++ tailWord_6733540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733540).length < 2 ^ (prefixWord ++ tailWord_6733540).sum := by decide
  have hdescent : baseEnd_6733540 < baseStart_6733540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733577 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 4, 3, 2]
def baseStart_6733577 : Nat := 118140960795 + 6733577 * 2 ^ 59
def prefixEnd_6733577 : Nat := 4983230072969 + 3 ^ 40 * 6733577 * 2
def baseEnd_6733577 : Nat := 3457561525059906582720349

theorem tailTrace_6733577 : CollatzResearch.WordTrace tailWord_6733577 prefixEnd_6733577 3457561525059906582720349 := by
  unfold tailWord_6733577
  simp only [CollatzResearch.WordTrace]
  refine ⟨245593729526408007240262985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163729153017605338160175323 245593729526408007240262985)
  ·
    refine ⟨184195297144806005430197239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245593729526408007240262985 184195297144806005430197239)
    ·
      refine ⟨276292945717209008145295859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184195297144806005430197239 276292945717209008145295859)
      ·
        refine ⟨414439418575813512217943789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276292945717209008145295859 414439418575813512217943789)
        ·
          refine ⟨155414781965930067081728921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414439418575813512217943789 155414781965930067081728921)
          ·
            refine ⟨116561086474447550311296691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155414781965930067081728921 116561086474447550311296691)
            ·
              refine ⟨174841629711671325466945037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116561086474447550311296691 174841629711671325466945037)
              ·
                refine ⟨65565611141876747050104389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174841629711671325466945037 65565611141876747050104389)
                ·
                  refine ⟨12293552089101890071894573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65565611141876747050104389 12293552089101890071894573)
                  ·
                    refine ⟨4610082033413208776960465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12293552089101890071894573 4610082033413208776960465)
                    ·
                      refine ⟨3457561525059906582720349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610082033413208776960465 3457561525059906582720349)
                      ·
                        rfl

theorem cell23_6733577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 3, 2].length) (baseStart_6733577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733577 prefixEnd_6733577 := by exact prefixLift 6733577
  have htrace : WordTrace (prefixWord ++ tailWord_6733577) baseStart_6733577 baseEnd_6733577 := by
    simpa [prefixWord, tailWord_6733577, baseEnd_6733577] using wordTrace_append hprefix tailTrace_6733577
  have hstable : (prefixWord ++ tailWord_6733577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733577).length < 2 ^ (prefixWord ++ tailWord_6733577).sum := by decide
  have hdescent : baseEnd_6733577 < baseStart_6733577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733604 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_6733604 : Nat := 118140960795 + 6733604 * 2 ^ 59
def prefixEnd_6733604 : Nat := 4983230072969 + 3 ^ 40 * 6733604 * 2
def baseEnd_6733604 : Nat := 1152525129679192659027575

theorem tailTrace_6733604 : CollatzResearch.WordTrace tailWord_6733604 prefixEnd_6733604 1152525129679192659027575 := by
  unfold tailWord_6733604
  simp only [CollatzResearch.WordTrace]
  refine ⟨122797357148655095425747933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163729809531540127234330577 122797357148655095425747933)
  ·
    refine ⟨46049008930745660784655475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122797357148655095425747933 46049008930745660784655475)
    ·
      refine ⟨69073513396118491176983213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46049008930745660784655475 69073513396118491176983213)
      ·
        refine ⟨25902567523544434191368705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69073513396118491176983213 25902567523544434191368705)
        ·
          refine ⟨19426925642658325643526529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25902567523544434191368705 19426925642658325643526529)
          ·
            refine ⟨14570194231993744232644897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19426925642658325643526529 14570194231993744232644897)
            ·
              refine ⟨10927645673995308174483673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14570194231993744232644897 10927645673995308174483673)
              ·
                refine ⟨8195734255496481130862755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10927645673995308174483673 8195734255496481130862755)
                ·
                  refine ⟨12293601383244721696294133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8195734255496481130862755 12293601383244721696294133)
                  ·
                    refine ⟨1152525129679192659027575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12293601383244721696294133 1152525129679192659027575)
                    ·
                      rfl

theorem cell23_6733604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_6733604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733604 prefixEnd_6733604 := by exact prefixLift 6733604
  have htrace : WordTrace (prefixWord ++ tailWord_6733604) baseStart_6733604 baseEnd_6733604 := by
    simpa [prefixWord, tailWord_6733604, baseEnd_6733604] using wordTrace_append hprefix tailTrace_6733604
  have hstable : (prefixWord ++ tailWord_6733604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733604).length < 2 ^ (prefixWord ++ tailWord_6733604).sum := by decide
  have hdescent : baseEnd_6733604 < baseStart_6733604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733617 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 4, 4]
def baseStart_6733617 : Nat := 118140960795 + 6733617 * 2 ^ 59
def prefixEnd_6733617 : Nat := 4983230072969 + 3 ^ 40 * 6733617 * 2
def baseEnd_6733617 : Nat := 1152527354762028808740055

theorem tailTrace_6733617 : CollatzResearch.WordTrace tailWord_6733617 prefixEnd_6733617 1152527354762028808740055 := by
  unfold tailWord_6733617
  simp only [CollatzResearch.WordTrace]
  refine ⟨245595188446263094071719105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163730125630842062714479403 245595188446263094071719105)
  ·
    refine ⟨184196391334697320553789329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245595188446263094071719105 184196391334697320553789329)
    ·
      refine ⟨138147293501022990415341997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184196391334697320553789329 138147293501022990415341997)
      ·
        refine ⟨51805235062883621405753249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138147293501022990415341997 51805235062883621405753249)
        ·
          refine ⟨38853926297162716054314937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51805235062883621405753249 38853926297162716054314937)
          ·
            refine ⟨29140444722872037040736203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38853926297162716054314937 29140444722872037040736203)
            ·
              refine ⟨43710667084308055561104305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29140444722872037040736203 43710667084308055561104305)
              ·
                refine ⟨32783000313231041670828229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43710667084308055561104305 32783000313231041670828229)
                ·
                  refine ⟨6146812558730820313280293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32783000313231041670828229 6146812558730820313280293)
                  ·
                    refine ⟨1152527354762028808740055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146812558730820313280293 1152527354762028808740055)
                    ·
                      rfl

theorem cell23_6733617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_6733617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733617 prefixEnd_6733617 := by exact prefixLift 6733617
  have htrace : WordTrace (prefixWord ++ tailWord_6733617) baseStart_6733617 baseEnd_6733617 := by
    simpa [prefixWord, tailWord_6733617, baseEnd_6733617] using wordTrace_append hprefix tailTrace_6733617
  have hstable : (prefixWord ++ tailWord_6733617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733617).length < 2 ^ (prefixWord ++ tailWord_6733617).sum := by decide
  have hdescent : baseEnd_6733617 < baseStart_6733617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733618 : List Nat := [3, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_6733618 : Nat := 118140960795 + 6733618 * 2 ^ 59
def prefixEnd_6733618 : Nat := 4983230072969 + 3 ^ 40 * 6733618 * 2
def baseEnd_6733618 : Nat := 3457582577766740922307661

theorem tailTrace_6733618 : CollatzResearch.WordTrace tailWord_6733618 prefixEnd_6733618 3457582577766740922307661 := by
  unfold tailWord_6733618
  simp only [CollatzResearch.WordTrace]
  refine ⟨61398806229814867810626377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163730149946172980828337005 61398806229814867810626377)
  ·
    refine ⟨46049104672361150857969783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61398806229814867810626377 46049104672361150857969783)
    ·
      refine ⟨69073657008541726286954675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46049104672361150857969783 69073657008541726286954675)
      ·
        refine ⟨103610485512812589430432013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69073657008541726286954675 103610485512812589430432013)
        ·
          refine ⟨38853932067304721036412005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103610485512812589430432013 38853932067304721036412005)
          ·
            refine ⟨7285112262619635194327251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38853932067304721036412005 7285112262619635194327251)
            ·
              refine ⟨10927668393929452791490877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7285112262619635194327251 10927668393929452791490877)
              ·
                refine ⟨4097875647723544796809079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10927668393929452791490877 4097875647723544796809079)
                ·
                  refine ⟨6146813471585317195213619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097875647723544796809079 6146813471585317195213619)
                  ·
                    refine ⟨9220220207377975792820429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146813471585317195213619 9220220207377975792820429)
                    ·
                      refine ⟨3457582577766740922307661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9220220207377975792820429 3457582577766740922307661)
                      ·
                        rfl

theorem cell23_6733618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_6733618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733618 prefixEnd_6733618 := by exact prefixLift 6733618
  have htrace : WordTrace (prefixWord ++ tailWord_6733618) baseStart_6733618 baseEnd_6733618 := by
    simpa [prefixWord, tailWord_6733618, baseEnd_6733618] using wordTrace_append hprefix tailTrace_6733618
  have hstable : (prefixWord ++ tailWord_6733618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733618).length < 2 ^ (prefixWord ++ tailWord_6733618).sum := by decide
  have hdescent : baseEnd_6733618 < baseStart_6733618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733657 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 3]
def baseStart_6733657 : Nat := 118140960795 + 6733657 * 2 ^ 59
def prefixEnd_6733657 : Nat := 4983230072969 + 3 ^ 40 * 6733657 * 2
def baseEnd_6733657 : Nat := 3457602603512266269719981

theorem tailTrace_6733657 : CollatzResearch.WordTrace tailWord_6733657 prefixEnd_6733657 3457602603512266269719981 := by
  unfold tailWord_6733657
  simp only [CollatzResearch.WordTrace]
  refine ⟨245596647366118180903175225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163731098244078787268783483 245596647366118180903175225)
  ·
    refine ⟨184197485524588635677381419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245596647366118180903175225 184197485524588635677381419)
    ·
      refine ⟨276296228286882953516072129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184197485524588635677381419 276296228286882953516072129)
      ·
        refine ⟨207222171215162215137054097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276296228286882953516072129 207222171215162215137054097)
        ·
          refine ⟨155416628411371661352790573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207222171215162215137054097 155416628411371661352790573)
          ·
            refine ⟨58281235654264373007296465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155416628411371661352790573 58281235654264373007296465)
            ·
              refine ⟨43710926740698279755472349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58281235654264373007296465 43710926740698279755472349)
              ·
                refine ⟨16391597527761854908302131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43710926740698279755472349 16391597527761854908302131)
                ·
                  refine ⟨24587396291642782362453197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16391597527761854908302131 24587396291642782362453197)
                  ·
                    refine ⟨9220273609366043385919949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24587396291642782362453197 9220273609366043385919949)
                    ·
                      refine ⟨3457602603512266269719981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9220273609366043385919949 3457602603512266269719981)
                      ·
                        rfl

theorem cell23_6733657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_6733657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733657 prefixEnd_6733657 := by exact prefixLift 6733657
  have htrace : WordTrace (prefixWord ++ tailWord_6733657) baseStart_6733657 baseEnd_6733657 := by
    simpa [prefixWord, tailWord_6733657, baseEnd_6733657] using wordTrace_append hprefix tailTrace_6733657
  have hstable : (prefixWord ++ tailWord_6733657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733657).length < 2 ^ (prefixWord ++ tailWord_6733657).sum := by decide
  have hdescent : baseEnd_6733657 < baseStart_6733657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733678 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_6733678 : Nat := 118140960795 + 6733678 * 2 ^ 59
def prefixEnd_6733678 : Nat := 4983230072969 + 3 ^ 40 * 6733678 * 2
def baseEnd_6733678 : Nat := 3457613386606010687557385

theorem tailTrace_6733678 : CollatzResearch.WordTrace tailWord_6733678 prefixEnd_6733678 3457613386606010687557385 := by
  unfold tailWord_6733678
  simp only [CollatzResearch.WordTrace]
  refine ⟨30699676662380262686211211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163731608866028067659793125 30699676662380262686211211)
  ·
    refine ⟨46049514993570394029316817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30699676662380262686211211 46049514993570394029316817)
    ·
      refine ⟨34537136245177795521987613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46049514993570394029316817 34537136245177795521987613)
      ·
        refine ⟨12951426091941673320745355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34537136245177795521987613 12951426091941673320745355)
        ·
          refine ⟨19427139137912509981118033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12951426091941673320745355 19427139137912509981118033)
          ·
            refine ⟨14570354353434382485838525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19427139137912509981118033 14570354353434382485838525)
            ·
              refine ⟨5463882882537893432189447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14570354353434382485838525 5463882882537893432189447)
              ·
                refine ⟨8195824323806840148284171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463882882537893432189447 8195824323806840148284171)
                ·
                  refine ⟨12293736485710260222426257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8195824323806840148284171 12293736485710260222426257)
                  ·
                    refine ⟨9220302364282695166819693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12293736485710260222426257 9220302364282695166819693)
                    ·
                      refine ⟨3457613386606010687557385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9220302364282695166819693 3457613386606010687557385)
                      ·
                        rfl

theorem cell23_6733678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_6733678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733678 prefixEnd_6733678 := by exact prefixLift 6733678
  have htrace : WordTrace (prefixWord ++ tailWord_6733678) baseStart_6733678 baseEnd_6733678 := by
    simpa [prefixWord, tailWord_6733678, baseEnd_6733678] using wordTrace_append hprefix tailTrace_6733678
  have hstable : (prefixWord ++ tailWord_6733678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733678).length < 2 ^ (prefixWord ++ tailWord_6733678).sum := by decide
  have hdescent : baseEnd_6733678 < baseStart_6733678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733694 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6733694 : Nat := 118140960795 + 6733694 * 2 ^ 59
def prefixEnd_6733694 : Nat := 4983230072969 + 3 ^ 40 * 6733694 * 2
def baseEnd_6733694 : Nat := 1152540534098827541652437

theorem tailTrace_6733694 : CollatzResearch.WordTrace tailWord_6733694 prefixEnd_6733694 1152540534098827541652437 := by
  unfold tailWord_6733694
  simp only [CollatzResearch.WordTrace]
  refine ⟨30699749608373017027784017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163731997911322757481514757 30699749608373017027784017)
  ·
    refine ⟨23024812206279762770838013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30699749608373017027784017 23024812206279762770838013)
    ·
      refine ⟨8634304577354911039064255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23024812206279762770838013 8634304577354911039064255)
      ·
        refine ⟨12951456866032366558596383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8634304577354911039064255 12951456866032366558596383)
        ·
          refine ⟨19427185299048549837894575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12951456866032366558596383 19427185299048549837894575)
          ·
            refine ⟨29140777948572824756841863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19427185299048549837894575 29140777948572824756841863)
            ·
              refine ⟨43711166922859237135262795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29140777948572824756841863 43711166922859237135262795)
              ·
                refine ⟨65566750384288855702894193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43711166922859237135262795 65566750384288855702894193)
                ·
                  refine ⟨49175062788216641777170645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65566750384288855702894193 49175062788216641777170645)
                  ·
                    refine ⟨1152540534098827541652437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49175062788216641777170645 1152540534098827541652437)
                    ·
                      rfl

theorem cell23_6733694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6733694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733694 prefixEnd_6733694 := by exact prefixLift 6733694
  have htrace : WordTrace (prefixWord ++ tailWord_6733694) baseStart_6733694 baseEnd_6733694 := by
    simpa [prefixWord, tailWord_6733694, baseEnd_6733694] using wordTrace_append hprefix tailTrace_6733694
  have hstable : (prefixWord ++ tailWord_6733694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733694).length < 2 ^ (prefixWord ++ tailWord_6733694).sum := by decide
  have hdescent : baseEnd_6733694 < baseStart_6733694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733717 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_6733717 : Nat := 118140960795 + 6733717 * 2 ^ 59
def prefixEnd_6733717 : Nat := 4983230072969 + 3 ^ 40 * 6733717 * 2
def baseEnd_6733717 : Nat := 3457633412351536034969705

theorem tailTrace_6733717 : CollatzResearch.WordTrace tailWord_6733717 prefixEnd_6733717 3457633412351536034969705 := by
  unfold tailWord_6733717
  simp only [CollatzResearch.WordTrace]
  refine ⟨245598835745900811150359405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163732557163933874100239603 245598835745900811150359405)
  ·
    refine ⟨92099563404712804181384777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245598835745900811150359405 92099563404712804181384777)
    ·
      refine ⟨69074672553534603136038583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92099563404712804181384777 69074672553534603136038583)
      ·
        refine ⟨103612008830301904704057875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69074672553534603136038583 103612008830301904704057875)
        ·
          refine ⟨155418013245452857056086813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103612008830301904704057875 155418013245452857056086813)
          ·
            refine ⟨58281754967044821396032555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155418013245452857056086813 58281754967044821396032555)
            ·
              refine ⟨87422632450567232094048833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58281754967044821396032555 87422632450567232094048833)
              ·
                refine ⟨65566974337925424070536625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87422632450567232094048833 65566974337925424070536625)
                ·
                  refine ⟨49175230753444068052902469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65566974337925424070536625 49175230753444068052902469)
                  ·
                    refine ⟨9220355766270762759919213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49175230753444068052902469 9220355766270762759919213)
                    ·
                      refine ⟨3457633412351536034969705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9220355766270762759919213 3457633412351536034969705)
                      ·
                        rfl

theorem cell23_6733717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_6733717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733717 prefixEnd_6733717 := by exact prefixLift 6733717
  have htrace : WordTrace (prefixWord ++ tailWord_6733717) baseStart_6733717 baseEnd_6733717 := by
    simpa [prefixWord, tailWord_6733717, baseEnd_6733717] using wordTrace_append hprefix tailTrace_6733717
  have hstable : (prefixWord ++ tailWord_6733717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733717).length < 2 ^ (prefixWord ++ tailWord_6733717).sum := by decide
  have hdescent : baseEnd_6733717 < baseStart_6733717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733735 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_6733735 : Nat := 118140960795 + 6733735 * 2 ^ 59
def prefixEnd_6733735 : Nat := 4983230072969 + 3 ^ 40 * 6733735 * 2
def baseEnd_6733735 : Nat := 3457642655003316964544623

theorem tailTrace_6733735 : CollatzResearch.WordTrace tailWord_6733735 prefixEnd_6733735 3457642655003316964544623 := by
  unfold tailWord_6733735
  simp only [CollatzResearch.WordTrace]
  refine ⟨245599492259835600224514659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163732994839890400149676439 245599492259835600224514659)
  ·
    refine ⟨368399238389753400336771989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245599492259835600224514659 368399238389753400336771989)
    ·
      refine ⟨17268714299519690640786187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 368399238389753400336771989 17268714299519690640786187)
      ·
        refine ⟨25903071449279535961179281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17268714299519690640786187 25903071449279535961179281)
        ·
          refine ⟨19427303586959651970884461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25903071449279535961179281 19427303586959651970884461)
          ·
            refine ⟨7285238845109869489081673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19427303586959651970884461 7285238845109869489081673)
            ·
              refine ⟨5463929133832402116811255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7285238845109869489081673 5463929133832402116811255)
              ·
                refine ⟨8195893700748603175216883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463929133832402116811255 8195893700748603175216883)
                ·
                  refine ⟨12293840551122904762825325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8195893700748603175216883 12293840551122904762825325)
                  ·
                    refine ⟨4610190206671089286059497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12293840551122904762825325 4610190206671089286059497)
                    ·
                      refine ⟨3457642655003316964544623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610190206671089286059497 3457642655003316964544623)
                      ·
                        rfl

theorem cell23_6733735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_6733735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733735 prefixEnd_6733735 := by exact prefixLift 6733735
  have htrace : WordTrace (prefixWord ++ tailWord_6733735) baseStart_6733735 baseEnd_6733735 := by
    simpa [prefixWord, tailWord_6733735, baseEnd_6733735] using wordTrace_append hprefix tailTrace_6733735
  have hstable : (prefixWord ++ tailWord_6733735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733735).length < 2 ^ (prefixWord ++ tailWord_6733735).sum := by decide
  have hdescent : baseEnd_6733735 < baseStart_6733735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733747 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 3]
def baseStart_6733747 : Nat := 118140960795 + 6733747 * 2 ^ 59
def prefixEnd_6733747 : Nat := 4983230072969 + 3 ^ 40 * 6733747 * 2
def baseEnd_6733747 : Nat := 3457648816771170917594567

theorem tailTrace_6733747 : CollatzResearch.WordTrace tailWord_6733747 prefixEnd_6733747 3457648816771170917594567 := by
  unfold tailWord_6733747
  simp only [CollatzResearch.WordTrace]
  refine ⟨245599929935792126273951495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163733286623861417515967663 245599929935792126273951495)
  ·
    refine ⟨368399894903688189410927243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245599929935792126273951495 368399894903688189410927243)
    ·
      refine ⟨552599842355532284116390865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368399894903688189410927243 552599842355532284116390865)
      ·
        refine ⟨414449881766649213087293149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552599842355532284116390865 414449881766649213087293149)
        ·
          refine ⟨155418705662493454907734931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414449881766649213087293149 155418705662493454907734931)
          ·
            refine ⟨233128058493740182361602397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155418705662493454907734931 233128058493740182361602397)
            ·
              refine ⟨87423021935152568385600899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233128058493740182361602397 87423021935152568385600899)
              ·
                refine ⟨131134532902728852578401349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87423021935152568385600899 131134532902728852578401349)
                ·
                  refine ⟨24587724919261659858450253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131134532902728852578401349 24587724919261659858450253)
                  ·
                    refine ⟨9220396844723122446918845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24587724919261659858450253 9220396844723122446918845)
                    ·
                      refine ⟨3457648816771170917594567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9220396844723122446918845 3457648816771170917594567)
                      ·
                        rfl

theorem cell23_6733747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_6733747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733747 prefixEnd_6733747 := by exact prefixLift 6733747
  have htrace : WordTrace (prefixWord ++ tailWord_6733747) baseStart_6733747 baseEnd_6733747 := by
    simpa [prefixWord, tailWord_6733747, baseEnd_6733747] using wordTrace_append hprefix tailTrace_6733747
  have hstable : (prefixWord ++ tailWord_6733747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733747).length < 2 ^ (prefixWord ++ tailWord_6733747).sum := by decide
  have hdescent : baseEnd_6733747 < baseStart_6733747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733804 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 4, 4, 2]
def baseStart_6733804 : Nat := 118140960795 + 6733804 * 2 ^ 59
def prefixEnd_6733804 : Nat := 4983230072969 + 3 ^ 40 * 6733804 * 2
def baseEnd_6733804 : Nat := 3457678085168477194581805

theorem tailTrace_6733804 : CollatzResearch.WordTrace tailWord_6733804 prefixEnd_6733804 3457678085168477194581805 := by
  unfold tailWord_6733804
  simp only [CollatzResearch.WordTrace]
  refine ⟨122801004448292812504388233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163734672597723750005850977 122801004448292812504388233)
  ·
    refine ⟨92100753336219609378291175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122801004448292812504388233 92100753336219609378291175)
    ·
      refine ⟨138151130004329414067436763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92100753336219609378291175 138151130004329414067436763)
      ·
        refine ⟨207226695006494121101155145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138151130004329414067436763 207226695006494121101155145)
        ·
          refine ⟨155420021254870590825866359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207226695006494121101155145 155420021254870590825866359)
          ·
            refine ⟨233130031882305886238799539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155420021254870590825866359 233130031882305886238799539)
            ·
              refine ⟨349695047823458829358199309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233130031882305886238799539 349695047823458829358199309)
              ·
                refine ⟨131135642933797061009324741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349695047823458829358199309 131135642933797061009324741)
                ·
                  refine ⟨24587933050086948939248389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131135642933797061009324741 24587933050086948939248389)
                  ·
                    refine ⟨4610237446891302926109073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24587933050086948939248389 4610237446891302926109073)
                    ·
                      refine ⟨3457678085168477194581805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610237446891302926109073 3457678085168477194581805)
                      ·
                        rfl

theorem cell23_6733804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_6733804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733804 prefixEnd_6733804 := by exact prefixLift 6733804
  have htrace : WordTrace (prefixWord ++ tailWord_6733804) baseStart_6733804 baseEnd_6733804 := by
    simpa [prefixWord, tailWord_6733804, baseEnd_6733804] using wordTrace_append hprefix tailTrace_6733804
  have hstable : (prefixWord ++ tailWord_6733804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733804).length < 2 ^ (prefixWord ++ tailWord_6733804).sum := by decide
  have hdescent : baseEnd_6733804 < baseStart_6733804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733805 : List Nat := [1, 5, 1, 4, 1, 1, 3, 2, 5]
def baseStart_6733805 : Nat := 118140960795 + 6733805 * 2 ^ 59
def prefixEnd_6733805 : Nat := 4983230072969 + 3 ^ 40 * 6733805 * 2
def baseEnd_6733805 : Nat := 384186510961014632296589

theorem tailTrace_6733805 : CollatzResearch.WordTrace tailWord_6733805 prefixEnd_6733805 384186510961014632296589 := by
  unfold tailWord_6733805
  simp only [CollatzResearch.WordTrace]
  refine ⟨245602045369582002179562869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163734696913054668119708579 245602045369582002179562869)
  ·
    refine ⟨23025191753398312704334019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245602045369582002179562869 23025191753398312704334019)
    ·
      refine ⟨34537787630097469056501029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23025191753398312704334019 34537787630097469056501029)
      ·
        refine ⟨6475835180643275448093943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34537787630097469056501029 6475835180643275448093943)
        ·
          refine ⟨9713752770964913172140915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6475835180643275448093943 9713752770964913172140915)
          ·
            refine ⟨14570629156447369758211373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9713752770964913172140915 14570629156447369758211373)
            ·
              refine ⟨5463985933667763659329265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14570629156447369758211373 5463985933667763659329265)
              ·
                refine ⟨4097989450250822744496949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463985933667763659329265 4097989450250822744496949)
                ·
                  refine ⟨384186510961014632296589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4097989450250822744496949 384186510961014632296589)
                  ·
                    rfl

theorem cell23_6733805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_6733805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733805 prefixEnd_6733805 := by exact prefixLift 6733805
  have htrace : WordTrace (prefixWord ++ tailWord_6733805) baseStart_6733805 baseEnd_6733805 := by
    simpa [prefixWord, tailWord_6733805, baseEnd_6733805] using wordTrace_append hprefix tailTrace_6733805
  have hstable : (prefixWord ++ tailWord_6733805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733805).length < 2 ^ (prefixWord ++ tailWord_6733805).sum := by decide
  have hdescent : baseEnd_6733805 < baseStart_6733805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733874 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_6733874 : Nat := 118140960795 + 6733874 * 2 ^ 59
def prefixEnd_6733874 : Nat := 4983230072969 + 3 ^ 40 * 6733874 * 2
def baseEnd_6733874 : Nat := 1152571342938097306902161

theorem tailTrace_6733874 : CollatzResearch.WordTrace tailWord_6733874 prefixEnd_6733874 1152571342938097306902161 := by
  unfold tailWord_6733874
  simp only [CollatzResearch.WordTrace]
  refine ⟨61401140501583006740956169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163736374670888017975883117 61401140501583006740956169)
  ·
    refine ⟨46050855376187255055717127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61401140501583006740956169 46050855376187255055717127)
    ·
      refine ⟨69076283064280882583575691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46050855376187255055717127 69076283064280882583575691)
      ·
        refine ⟨103614424596421323875363537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69076283064280882583575691 103614424596421323875363537)
        ·
          refine ⟨77710818447315992906522653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103614424596421323875363537 77710818447315992906522653)
          ·
            refine ⟨29141556917743497339945995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77710818447315992906522653 29141556917743497339945995)
            ·
              refine ⟨43712335376615246009918993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29141556917743497339945995 43712335376615246009918993)
              ·
                refine ⟨32784251532461434507439245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43712335376615246009918993 32784251532461434507439245)
                ·
                  refine ⟨12294094324673037940289717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32784251532461434507439245 12294094324673037940289717)
                  ·
                    refine ⟨1152571342938097306902161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12294094324673037940289717 1152571342938097306902161)
                    ·
                      rfl

theorem cell23_6733874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_6733874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733874 prefixEnd_6733874 := by exact prefixLift 6733874
  have htrace : WordTrace (prefixWord ++ tailWord_6733874) baseStart_6733874 baseEnd_6733874 := by
    simpa [prefixWord, tailWord_6733874, baseEnd_6733874] using wordTrace_append hprefix tailTrace_6733874
  have hstable : (prefixWord ++ tailWord_6733874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733874).length < 2 ^ (prefixWord ++ tailWord_6733874).sum := by decide
  have hdescent : baseEnd_6733874 < baseStart_6733874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733914 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_6733914 : Nat := 118140960795 + 6733914 * 2 ^ 59
def prefixEnd_6733914 : Nat := 4983230072969 + 3 ^ 40 * 6733914 * 2
def baseEnd_6733914 : Nat := 3457734568040471764206299

theorem tailTrace_6733914 : CollatzResearch.WordTrace tailWord_6733914 prefixEnd_6733914 3457734568040471764206299 := by
  unfold tailWord_6733914
  simp only [CollatzResearch.WordTrace]
  refine ⟨61401505231546778448820199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163737347284124742530187197 61401505231546778448820199)
  ·
    refine ⟨92102257847320167673230299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61401505231546778448820199 92102257847320167673230299)
    ·
      refine ⟨138153386770980251509845449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92102257847320167673230299 138153386770980251509845449)
      ·
        refine ⟨103615040078235188632384087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138153386770980251509845449 103615040078235188632384087)
        ·
          refine ⟨155422560117352782948576131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103615040078235188632384087 155422560117352782948576131)
          ·
            refine ⟨233133840176029174422864197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155422560117352782948576131 233133840176029174422864197)
            ·
              refine ⟨43712595033005470204287037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233133840176029174422864197 43712595033005470204287037)
              ·
                refine ⟨16392223137377051326607639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43712595033005470204287037 16392223137377051326607639)
                ·
                  refine ⟨24588334706065576989911459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16392223137377051326607639 24588334706065576989911459)
                  ·
                    refine ⟨36882502059098365484867189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24588334706065576989911459 36882502059098365484867189)
                    ·
                      refine ⟨3457734568040471764206299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36882502059098365484867189 3457734568040471764206299)
                      ·
                        rfl

theorem cell23_6733914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_6733914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733914 prefixEnd_6733914 := by exact prefixLift 6733914
  have htrace : WordTrace (prefixWord ++ tailWord_6733914) baseStart_6733914 baseEnd_6733914 := by
    simpa [prefixWord, tailWord_6733914, baseEnd_6733914] using wordTrace_append hprefix tailTrace_6733914
  have hstable : (prefixWord ++ tailWord_6733914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733914).length < 2 ^ (prefixWord ++ tailWord_6733914).sum := by decide
  have hdescent : baseEnd_6733914 < baseStart_6733914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733924 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_6733924 : Nat := 118140960795 + 6733924 * 2 ^ 59
def prefixEnd_6733924 : Nat := 4983230072969 + 3 ^ 40 * 6733924 * 2
def baseEnd_6733924 : Nat := 3457739702847016725081253

theorem tailTrace_6733924 : CollatzResearch.WordTrace tailWord_6733924 prefixEnd_6733924 3457739702847016725081253 := by
  unfold tailWord_6733924
  simp only [CollatzResearch.WordTrace]
  refine ⟨122803192828075442751572413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163737590437433923668763217 122803192828075442751572413)
  ·
    refine ⟨46051197310528291031839655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122803192828075442751572413 46051197310528291031839655)
    ·
      refine ⟨69076795965792436547759483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46051197310528291031839655 69076795965792436547759483)
      ·
        refine ⟨103615193948688654821639225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69076795965792436547759483 103615193948688654821639225)
        ·
          refine ⟨77711395461516491116229419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103615193948688654821639225 77711395461516491116229419)
          ·
            refine ⟨116567093192274736674344129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77711395461516491116229419 116567093192274736674344129)
            ·
              refine ⟨87425319894206052505758097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116567093192274736674344129 87425319894206052505758097)
              ·
                refine ⟨65568989920654539379318573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87425319894206052505758097 65568989920654539379318573)
                ·
                  refine ⟨24588371220245452267244465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65568989920654539379318573 24588371220245452267244465)
                  ·
                    refine ⟨18441278415184089200433349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24588371220245452267244465 18441278415184089200433349)
                    ·
                      refine ⟨3457739702847016725081253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18441278415184089200433349 3457739702847016725081253)
                      ·
                        rfl

theorem cell23_6733924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_6733924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733924 prefixEnd_6733924 := by exact prefixLift 6733924
  have htrace : WordTrace (prefixWord ++ tailWord_6733924) baseStart_6733924 baseEnd_6733924 := by
    simpa [prefixWord, tailWord_6733924, baseEnd_6733924] using wordTrace_append hprefix tailTrace_6733924
  have hstable : (prefixWord ++ tailWord_6733924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733924).length < 2 ^ (prefixWord ++ tailWord_6733924).sum := by decide
  have hdescent : baseEnd_6733924 < baseStart_6733924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733934 : List Nat := [4, 1, 2, 2, 1, 1, 2, 10]
def baseStart_6733934 : Nat := 118140960795 + 6733934 * 2 ^ 59
def prefixEnd_6733934 : Nat := 4983230072969 + 3 ^ 40 * 6733934 * 2
def baseEnd_6733934 : Nat := 128064623616798580961341

theorem tailTrace_6733934 : CollatzResearch.WordTrace tailWord_6733934 prefixEnd_6733934 128064623616798580961341 := by
  unfold tailWord_6733934
  simp only [CollatzResearch.WordTrace]
  refine ⟨30700843798264332151376107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163737833590743104807339237 30700843798264332151376107)
  ·
    refine ⟨46051265697396498227064161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30700843798264332151376107 46051265697396498227064161)
    ·
      refine ⟨34538449273047373670298121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46051265697396498227064161 34538449273047373670298121)
      ·
        refine ⟨25903836954785530252723591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34538449273047373670298121 25903836954785530252723591)
        ·
          refine ⟨38855755432178295379085387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25903836954785530252723591 38855755432178295379085387)
          ·
            refine ⟨58283633148267443068628081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38855755432178295379085387 58283633148267443068628081)
            ·
              refine ⟨43712724861200582301471061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58283633148267443068628081 43712724861200582301471061)
              ·
                refine ⟨128064623616798580961341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43712724861200582301471061 128064623616798580961341)
                ·
                  rfl

theorem cell23_6733934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_6733934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733934 prefixEnd_6733934 := by exact prefixLift 6733934
  have htrace : WordTrace (prefixWord ++ tailWord_6733934) baseStart_6733934 baseEnd_6733934 := by
    simpa [prefixWord, tailWord_6733934, baseEnd_6733934] using wordTrace_append hprefix tailTrace_6733934
  have hstable : (prefixWord ++ tailWord_6733934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733934).length < 2 ^ (prefixWord ++ tailWord_6733934).sum := by decide
  have hdescent : baseEnd_6733934 < baseStart_6733934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733948 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_6733948 : Nat := 118140960795 + 6733948 * 2 ^ 59
def prefixEnd_6733948 : Nat := 4983230072969 + 3 ^ 40 * 6733948 * 2
def baseEnd_6733948 : Nat := 3457752026382724631181143

theorem tailTrace_6733948 : CollatzResearch.WordTrace tailWord_6733948 prefixEnd_6733948 3457752026382724631181143 := by
  unfold tailWord_6733948
  simp only [CollatzResearch.WordTrace]
  refine ⟨122803630504031968801009249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163738174005375958401345665 122803630504031968801009249)
  ·
    refine ⟨92102722878023976600756937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122803630504031968801009249 92102722878023976600756937)
    ·
      refine ⟨69077042158517982450567703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92102722878023976600756937 69077042158517982450567703)
      ·
        refine ⟨103615563237776973675851555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69077042158517982450567703 103615563237776973675851555)
        ·
          refine ⟨155423344856665460513777333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103615563237776973675851555 155423344856665460513777333)
          ·
            refine ⟨14570938580312386923166625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155423344856665460513777333 14570938580312386923166625)
            ·
              refine ⟨10928203935234290192374969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14570938580312386923166625 10928203935234290192374969)
              ·
                refine ⟨8196152951425717644281227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10928203935234290192374969 8196152951425717644281227)
                ·
                  refine ⟨12294229427138576466421841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8196152951425717644281227 12294229427138576466421841)
                  ·
                    refine ⟨9220672070353932349816381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12294229427138576466421841 9220672070353932349816381)
                    ·
                      refine ⟨3457752026382724631181143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9220672070353932349816381 3457752026382724631181143)
                      ·
                        rfl

theorem cell23_6733948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_6733948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733948 prefixEnd_6733948 := by exact prefixLift 6733948
  have htrace : WordTrace (prefixWord ++ tailWord_6733948) baseStart_6733948 baseEnd_6733948 := by
    simpa [prefixWord, tailWord_6733948, baseEnd_6733948] using wordTrace_append hprefix tailTrace_6733948
  have hstable : (prefixWord ++ tailWord_6733948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733948).length < 2 ^ (prefixWord ++ tailWord_6733948).sum := by decide
  have hdescent : baseEnd_6733948 < baseStart_6733948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733961 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 3]
def baseStart_6733961 : Nat := 118140960795 + 6733961 * 2 ^ 59
def prefixEnd_6733961 : Nat := 4983230072969 + 3 ^ 40 * 6733961 * 2
def baseEnd_6733961 : Nat := 3457758701631233080318583

theorem tailTrace_6733961 : CollatzResearch.WordTrace tailWord_6733961 prefixEnd_6733961 3457758701631233080318583 := by
  unfold tailWord_6733961
  simp only [CollatzResearch.WordTrace]
  refine ⟨245607735157016840822241737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163738490104677893881494491 245607735157016840822241737)
  ·
    refine ⟨184205801367762630616681303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245607735157016840822241737 184205801367762630616681303)
    ·
      refine ⟨276308702051643945925021955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184205801367762630616681303 276308702051643945925021955)
      ·
        refine ⟨414463053077465918887532933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276308702051643945925021955 414463053077465918887532933)
        ·
          refine ⟨77711822452024859791412425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 414463053077465918887532933 77711822452024859791412425)
          ·
            refine ⟨58283866839018644843559319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77711822452024859791412425 58283866839018644843559319)
            ·
              refine ⟨87425800258527967265338979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58283866839018644843559319 87425800258527967265338979)
              ·
                refine ⟨131138700387791950898008469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87425800258527967265338979 131138700387791950898008469)
                ·
                  refine ⟨6147126580677747698344147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131138700387791950898008469 6147126580677747698344147)
                  ·
                    refine ⟨9220689871016621547516221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6147126580677747698344147 9220689871016621547516221)
                    ·
                      refine ⟨3457758701631233080318583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9220689871016621547516221 3457758701631233080318583)
                      ·
                        rfl

theorem cell23_6733961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 3].length) (baseStart_6733961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733961 prefixEnd_6733961 := by exact prefixLift 6733961
  have htrace : WordTrace (prefixWord ++ tailWord_6733961) baseStart_6733961 baseEnd_6733961 := by
    simpa [prefixWord, tailWord_6733961, baseEnd_6733961] using wordTrace_append hprefix tailTrace_6733961
  have hstable : (prefixWord ++ tailWord_6733961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733961).length < 2 ^ (prefixWord ++ tailWord_6733961).sum := by decide
  have hdescent : baseEnd_6733961 < baseStart_6733961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733962 : List Nat := [3, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_6733962 : Nat := 118140960795 + 6733962 * 2 ^ 59
def prefixEnd_6733962 : Nat := 4983230072969 + 3 ^ 40 * 6733962 * 2
def baseEnd_6733962 : Nat := 3457759215111887576406079

theorem tailTrace_6733962 : CollatzResearch.WordTrace tailWord_6733962 prefixEnd_6733962 3457759215111887576406079 := by
  unfold tailWord_6733962
  simp only [CollatzResearch.WordTrace]
  refine ⟨61401942907503304498257035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163738514420008811995352093 61401942907503304498257035)
  ·
    refine ⟨92102914361254956747385553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61401942907503304498257035 92102914361254956747385553)
    ·
      refine ⟨69077185770941217560539165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92102914361254956747385553 69077185770941217560539165)
      ·
        refine ⟨25903944664102956585202187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69077185770941217560539165 25903944664102956585202187)
        ·
          refine ⟨38855916996154434877803281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25903944664102956585202187 38855916996154434877803281)
          ·
            refine ⟨29141937747115826158352461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38855916996154434877803281 29141937747115826158352461)
            ·
              refine ⟨10928226655168434809382173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29141937747115826158352461 10928226655168434809382173)
              ·
                refine ⟨4098084995688163053518315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10928226655168434809382173 4098084995688163053518315)
                ·
                  refine ⟨6147127493532244580277473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098084995688163053518315 6147127493532244580277473)
                  ·
                    refine ⟨4610345620149183435208105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6147127493532244580277473 4610345620149183435208105)
                    ·
                      refine ⟨3457759215111887576406079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610345620149183435208105 3457759215111887576406079)
                      ·
                        rfl

theorem cell23_6733962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_6733962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733962 prefixEnd_6733962 := by exact prefixLift 6733962
  have htrace : WordTrace (prefixWord ++ tailWord_6733962) baseStart_6733962 baseEnd_6733962 := by
    simpa [prefixWord, tailWord_6733962, baseEnd_6733962] using wordTrace_append hprefix tailTrace_6733962
  have hstable : (prefixWord ++ tailWord_6733962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733962).length < 2 ^ (prefixWord ++ tailWord_6733962).sum := by decide
  have hdescent : baseEnd_6733962 < baseStart_6733962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6733971 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 5, 3, 2]
def baseStart_6733971 : Nat := 118140960795 + 6733971 * 2 ^ 59
def prefixEnd_6733971 : Nat := 4983230072969 + 3 ^ 40 * 6733971 * 2
def baseEnd_6733971 : Nat := 3457763836437778041193537

theorem tailTrace_6733971 : CollatzResearch.WordTrace tailWord_6733971 prefixEnd_6733971 3457763836437778041193537 := by
  unfold tailWord_6733971
  simp only [CollatzResearch.WordTrace]
  refine ⟨245608099886980612530105767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163738733257987075020070511 245608099886980612530105767)
  ·
    refine ⟨368412149830470918795158651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245608099886980612530105767 368412149830470918795158651)
    ·
      refine ⟨552618224745706378192737977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368412149830470918795158651 552618224745706378192737977)
      ·
        refine ⟨414463668559279783644553483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552618224745706378192737977 414463668559279783644553483)
        ·
          refine ⟨621695502838919675466830225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414463668559279783644553483 621695502838919675466830225)
          ·
            refine ⟨466271627129189756600122669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621695502838919675466830225 466271627129189756600122669)
            ·
              refine ⟨174851860173446158725046001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466271627129189756600122669 174851860173446158725046001)
              ·
                refine ⟨131138895130084619043784501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174851860173446158725046001 131138895130084619043784501)
                ·
                  refine ⟨12294271418445433035354797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131138895130084619043784501 12294271418445433035354797)
                  ·
                    refine ⟨4610351781917037388258049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12294271418445433035354797 4610351781917037388258049)
                    ·
                      refine ⟨3457763836437778041193537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610351781917037388258049 3457763836437778041193537)
                      ·
                        rfl

theorem cell23_6733971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3, 2].length) (baseStart_6733971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6733971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6733971 prefixEnd_6733971 := by exact prefixLift 6733971
  have htrace : WordTrace (prefixWord ++ tailWord_6733971) baseStart_6733971 baseEnd_6733971 := by
    simpa [prefixWord, tailWord_6733971, baseEnd_6733971] using wordTrace_append hprefix tailTrace_6733971
  have hstable : (prefixWord ++ tailWord_6733971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6733971).length < 2 ^ (prefixWord ++ tailWord_6733971).sum := by decide
  have hdescent : baseEnd_6733971 < baseStart_6733971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6733971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734064 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_6734064 : Nat := 118140960795 + 6734064 * 2 ^ 59
def prefixEnd_6734064 : Nat := 4983230072969 + 3 ^ 40 * 6734064 * 2
def baseEnd_6734064 : Nat := 3457811590138646177330609

theorem tailTrace_6734064 : CollatzResearch.WordTrace tailWord_6734064 prefixEnd_6734064 3457811590138646177330609 := by
  unfold tailWord_6734064
  simp only [CollatzResearch.WordTrace]
  refine ⟨122805745937821844706620623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163740994583762459608827497 122805745937821844706620623)
  ·
    refine ⟨184208618906732767059930935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122805745937821844706620623 184208618906732767059930935)
    ·
      refine ⟨276312928360099150589896403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184208618906732767059930935 276312928360099150589896403)
      ·
        refine ⟨414469392540148725884844605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276312928360099150589896403 414469392540148725884844605)
        ·
          refine ⟨155426022202555772206816727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414469392540148725884844605 155426022202555772206816727)
          ·
            refine ⟨233139033303833658310225091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155426022202555772206816727 233139033303833658310225091)
            ·
              refine ⟨349708549955750487465337637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233139033303833658310225091 349708549955750487465337637)
              ·
                refine ⟨65570353116703216399750807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349708549955750487465337637 65570353116703216399750807)
                ·
                  refine ⟨98355529675054824599626211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65570353116703216399750807 98355529675054824599626211)
                  ·
                    refine ⟨147533294512582236899439317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98355529675054824599626211 147533294512582236899439317)
                    ·
                      refine ⟨3457811590138646177330609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147533294512582236899439317 3457811590138646177330609)
                      ·
                        rfl

theorem cell23_6734064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_6734064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734064 prefixEnd_6734064 := by exact prefixLift 6734064
  have htrace : WordTrace (prefixWord ++ tailWord_6734064) baseStart_6734064 baseEnd_6734064 := by
    simpa [prefixWord, tailWord_6734064, baseEnd_6734064] using wordTrace_append hprefix tailTrace_6734064
  have hstable : (prefixWord ++ tailWord_6734064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734064).length < 2 ^ (prefixWord ++ tailWord_6734064).sum := by decide
  have hdescent : baseEnd_6734064 < baseStart_6734064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734091 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 4]
def baseStart_6734091 : Nat := 118140960795 + 6734091 * 2 ^ 59
def prefixEnd_6734091 : Nat := 4983230072969 + 3 ^ 40 * 6734091 * 2
def baseEnd_6734091 : Nat := 3457825454116317571692985

theorem tailTrace_6734091 : CollatzResearch.WordTrace tailWord_6734091 prefixEnd_6734091 3457825454116317571692985 := by
  unfold tailWord_6734091
  simp only [CollatzResearch.WordTrace]
  refine ⟨245612476646545873024474127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163741651097697248682982751 245612476646545873024474127)
  ·
    refine ⟨368418714969818809536711191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245612476646545873024474127 368418714969818809536711191)
    ·
      refine ⟨552628072454728214305066787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368418714969818809536711191 552628072454728214305066787)
      ·
        refine ⟨828942108682092321457600181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552628072454728214305066787 828942108682092321457600181)
        ·
          refine ⟨77713322688946155136650017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 828942108682092321457600181 77713322688946155136650017)
          ·
            refine ⟨58284992016709616352487513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77713322688946155136650017 58284992016709616352487513)
            ·
              refine ⟨43713744012532212264365635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58284992016709616352487513 43713744012532212264365635)
              ·
                refine ⟨65570616018798318396548453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43713744012532212264365635 65570616018798318396548453)
                ·
                  refine ⟨12294490503524684699352835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65570616018798318396548453 12294490503524684699352835)
                  ·
                    refine ⟨18441735755287027049029253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12294490503524684699352835 18441735755287027049029253)
                    ·
                      refine ⟨3457825454116317571692985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18441735755287027049029253 3457825454116317571692985)
                      ·
                        rfl

theorem cell23_6734091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 4].length) (baseStart_6734091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734091 prefixEnd_6734091 := by exact prefixLift 6734091
  have htrace : WordTrace (prefixWord ++ tailWord_6734091) baseStart_6734091 baseEnd_6734091 := by
    simpa [prefixWord, tailWord_6734091, baseEnd_6734091] using wordTrace_append hprefix tailTrace_6734091
  have hstable : (prefixWord ++ tailWord_6734091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734091).length < 2 ^ (prefixWord ++ tailWord_6734091).sum := by decide
  have hdescent : baseEnd_6734091 < baseStart_6734091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734168 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 1, 5, 2]
def baseStart_6734168 : Nat := 118140960795 + 6734168 * 2 ^ 59
def prefixEnd_6734168 : Nat := 4983230072969 + 3 ^ 40 * 6734168 * 2
def baseEnd_6734168 : Nat := 3457864992126713770430131

theorem tailTrace_6734168 : CollatzResearch.WordTrace tailWord_6734168 prefixEnd_6734168 3457864992126713770430131 := by
  unfold tailWord_6734168
  simp only [CollatzResearch.WordTrace]
  refine ⟨122807642533633457587513579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163743523378177943450018105 122807642533633457587513579)
  ·
    refine ⟨184211463800450186381270369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122807642533633457587513579 184211463800450186381270369)
    ·
      refine ⟨138158597850337639785952777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184211463800450186381270369 138158597850337639785952777)
      ·
        refine ⟨103618948387753229839464583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138158597850337639785952777 103618948387753229839464583)
        ·
          refine ⟨155428422581629844759196875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103618948387753229839464583 155428422581629844759196875)
          ·
            refine ⟨233142633872444767138795313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155428422581629844759196875 233142633872444767138795313)
            ·
              refine ⟨174856975404333575354096485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233142633872444767138795313 174856975404333575354096485)
              ·
                refine ⟨32785682888312545378893091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174856975404333575354096485 32785682888312545378893091)
                ·
                  refine ⟨49178524332468818068339637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32785682888312545378893091 49178524332468818068339637)
                  ·
                    refine ⟨4610486656168951693906841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49178524332468818068339637 4610486656168951693906841)
                    ·
                      refine ⟨3457864992126713770430131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610486656168951693906841 3457864992126713770430131)
                      ·
                        rfl

theorem cell23_6734168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_6734168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734168 prefixEnd_6734168 := by exact prefixLift 6734168
  have htrace : WordTrace (prefixWord ++ tailWord_6734168) baseStart_6734168 baseEnd_6734168 := by
    simpa [prefixWord, tailWord_6734168, baseEnd_6734168] using wordTrace_append hprefix tailTrace_6734168
  have hstable : (prefixWord ++ tailWord_6734168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734168).length < 2 ^ (prefixWord ++ tailWord_6734168).sum := by decide
  have hdescent : baseEnd_6734168 < baseStart_6734168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734185 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 2, 3, 2]
def baseStart_6734185 : Nat := 118140960795 + 6734185 * 2 ^ 59
def prefixEnd_6734185 : Nat := 4983230072969 + 3 ^ 40 * 6734185 * 2
def baseEnd_6734185 : Nat := 3457873721297840203917553

theorem tailTrace_6734185 : CollatzResearch.WordTrace tailWord_6734185 prefixEnd_6734185 3457873721297840203917553 := by
  unfold tailWord_6734185
  simp only [CollatzResearch.WordTrace]
  refine ⟨245615905108205327078396009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163743936738803551385597339 245615905108205327078396009)
  ·
    refine ⟨184211928831153995308797007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245615905108205327078396009 184211928831153995308797007)
    ·
      refine ⟨276317893246730992963195511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184211928831153995308797007 276317893246730992963195511)
      ·
        refine ⟨414476839870096489444793267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276317893246730992963195511 414476839870096489444793267)
        ·
          refine ⟨621715259805144734167189901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414476839870096489444793267 621715259805144734167189901)
          ·
            refine ⟨233143222426929275312696213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621715259805144734167189901 233143222426929275312696213)
            ·
              refine ⟨10928588551262309780282635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233143222426929275312696213 10928588551262309780282635)
              ·
                refine ⟨16392882826893464670423953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10928588551262309780282635 16392882826893464670423953)
                ·
                  refine ⟨12294662120170098502817965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16392882826893464670423953 12294662120170098502817965)
                  ·
                    refine ⟨4610498295063786938556737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12294662120170098502817965 4610498295063786938556737)
                    ·
                      refine ⟨3457873721297840203917553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610498295063786938556737 3457873721297840203917553)
                      ·
                        rfl

theorem cell23_6734185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 3, 2].length) (baseStart_6734185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734185 prefixEnd_6734185 := by exact prefixLift 6734185
  have htrace : WordTrace (prefixWord ++ tailWord_6734185) baseStart_6734185 baseEnd_6734185 := by
    simpa [prefixWord, tailWord_6734185, baseEnd_6734185] using wordTrace_append hprefix tailTrace_6734185
  have hstable : (prefixWord ++ tailWord_6734185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734185).length < 2 ^ (prefixWord ++ tailWord_6734185).sum := by decide
  have hdescent : baseEnd_6734185 < baseStart_6734185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734209 : List Nat := [1, 2, 4, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_6734209 : Nat := 118140960795 + 6734209 * 2 ^ 59
def prefixEnd_6734209 : Nat := 4983230072969 + 3 ^ 40 * 6734209 * 2
def baseEnd_6734209 : Nat := 3457886044833548110017443

theorem tailTrace_6734209 : CollatzResearch.WordTrace tailWord_6734209 prefixEnd_6734209 3457886044833548110017443 := by
  unfold tailWord_6734209
  simp only [CollatzResearch.WordTrace]
  refine ⟨245616780460118379177269681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163744520306745586118179787 245616780460118379177269681)
  ·
    refine ⟨184212585345088784382952261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245616780460118379177269681 184212585345088784382952261)
    ·
      refine ⟨34539859752204147071803549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184212585345088784382952261 34539859752204147071803549)
      ·
        refine ⟨12952447407076555151926331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34539859752204147071803549 12952447407076555151926331)
        ·
          refine ⟨19428671110614832727889497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12952447407076555151926331 19428671110614832727889497)
          ·
            refine ⟨14571503332961124545917123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19428671110614832727889497 14571503332961124545917123)
            ·
              refine ⟨21857254999441686818875685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14571503332961124545917123 21857254999441686818875685)
              ·
                refine ⟨4098235312395316278539191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21857254999441686818875685 4098235312395316278539191)
                ·
                  refine ⟨6147352968592974417808787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098235312395316278539191 6147352968592974417808787)
                  ·
                    refine ⟨9221029452889461626713181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6147352968592974417808787 9221029452889461626713181)
                    ·
                      refine ⟨3457886044833548110017443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9221029452889461626713181 3457886044833548110017443)
                      ·
                        rfl

theorem cell23_6734209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_6734209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734209 prefixEnd_6734209 := by exact prefixLift 6734209
  have htrace : WordTrace (prefixWord ++ tailWord_6734209) baseStart_6734209 baseEnd_6734209 := by
    simpa [prefixWord, tailWord_6734209, baseEnd_6734209] using wordTrace_append hprefix tailTrace_6734209
  have hstable : (prefixWord ++ tailWord_6734209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734209).length < 2 ^ (prefixWord ++ tailWord_6734209).sum := by decide
  have hdescent : baseEnd_6734209 < baseStart_6734209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734232 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 5, 2, 2]
def baseStart_6734232 : Nat := 118140960795 + 6734232 * 2 ^ 59
def prefixEnd_6734232 : Nat := 4983230072969 + 3 ^ 40 * 6734232 * 2
def baseEnd_6734232 : Nat := 3457897854888601520029837

theorem tailTrace_6734232 : CollatzResearch.WordTrace tailWord_6734232 prefixEnd_6734232 3457897854888601520029837 := by
  unfold tailWord_6734232
  simp only [CollatzResearch.WordTrace]
  refine ⟨122808809669517527052678475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163745079559356702736904633 122808809669517527052678475)
  ·
    refine ⟨184213214504276290579017713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122808809669517527052678475 184213214504276290579017713)
    ·
      refine ⟨138159910878207217934263285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184213214504276290579017713 138159910878207217934263285)
      ·
        refine ⟨12952491644831926681337183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138159910878207217934263285 12952491644831926681337183)
        ·
          refine ⟨19428737467247890022005775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12952491644831926681337183 19428737467247890022005775)
          ·
            refine ⟨29143106200871835033008663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19428737467247890022005775 29143106200871835033008663)
            ·
              refine ⟨43714659301307752549512995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29143106200871835033008663 43714659301307752549512995)
              ·
                refine ⟨65571988951961628824269493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43714659301307752549512995 65571988951961628824269493)
                ·
                  refine ⟨6147373964246402702275265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65571988951961628824269493 6147373964246402702275265)
                  ·
                    refine ⟨4610530473184802026706449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6147373964246402702275265 4610530473184802026706449)
                    ·
                      refine ⟨3457897854888601520029837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610530473184802026706449 3457897854888601520029837)
                      ·
                        rfl

theorem cell23_6734232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_6734232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734232 prefixEnd_6734232 := by exact prefixLift 6734232
  have htrace : WordTrace (prefixWord ++ tailWord_6734232) baseStart_6734232 baseEnd_6734232 := by
    simpa [prefixWord, tailWord_6734232, baseEnd_6734232] using wordTrace_append hprefix tailTrace_6734232
  have hstable : (prefixWord ++ tailWord_6734232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734232).length < 2 ^ (prefixWord ++ tailWord_6734232).sum := by decide
  have hdescent : baseEnd_6734232 < baseStart_6734232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734305 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_6734305 : Nat := 118140960795 + 6734305 * 2 ^ 59
def prefixEnd_6734305 : Nat := 4983230072969 + 3 ^ 40 * 6734305 * 2
def baseEnd_6734305 : Nat := 3457935338976379734417001

theorem tailTrace_6734305 : CollatzResearch.WordTrace tailWord_6734305 prefixEnd_6734305 3457935338976379734417001 := by
  unfold tailWord_6734305
  simp only [CollatzResearch.WordTrace]
  refine ⟨245620281867770587572764369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163746854578513725048509579 245620281867770587572764369)
  ·
    refine ⟨184215211400827940679573277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245620281867770587572764369 184215211400827940679573277)
    ·
      refine ⟨69080704275310477754839979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184215211400827940679573277 69080704275310477754839979)
      ·
        refine ⟨103621056412965716632259969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69080704275310477754839979 103621056412965716632259969)
        ·
          refine ⟨77715792309724287474194977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103621056412965716632259969 77715792309724287474194977)
          ·
            refine ⟨58286844232293215605646233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77715792309724287474194977 58286844232293215605646233)
            ·
              refine ⟨43715133174219911704234675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58286844232293215605646233 43715133174219911704234675)
              ·
                refine ⟨65572699761329867556352013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43715133174219911704234675 65572699761329867556352013)
                ·
                  refine ⟨24589762410498700333632005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65572699761329867556352013 24589762410498700333632005)
                  ·
                    refine ⟨4610580451968506312556001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24589762410498700333632005 4610580451968506312556001)
                    ·
                      refine ⟨3457935338976379734417001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610580451968506312556001 3457935338976379734417001)
                      ·
                        rfl

theorem cell23_6734305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_6734305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734305 prefixEnd_6734305 := by exact prefixLift 6734305
  have htrace : WordTrace (prefixWord ++ tailWord_6734305) baseStart_6734305 baseEnd_6734305 := by
    simpa [prefixWord, tailWord_6734305, baseEnd_6734305] using wordTrace_append hprefix tailTrace_6734305
  have hstable : (prefixWord ++ tailWord_6734305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734305).length < 2 ^ (prefixWord ++ tailWord_6734305).sum := by decide
  have hdescent : baseEnd_6734305 < baseStart_6734305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734308 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_6734308 : Nat := 118140960795 + 6734308 * 2 ^ 59
def prefixEnd_6734308 : Nat := 4983230072969 + 3 ^ 40 * 6734308 * 2
def baseEnd_6734308 : Nat := 3457936879418343222679487

theorem tailTrace_6734308 : CollatzResearch.WordTrace tailWord_6734308 prefixEnd_6734308 3457936879418343222679487 := by
  unfold tailWord_6734308
  simp only [CollatzResearch.WordTrace]
  refine ⟨122810195643379859542561789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163746927524506479390082385 122810195643379859542561789)
  ·
    refine ⟨46053823366267447328460671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122810195643379859542561789 46053823366267447328460671)
    ·
      refine ⟨69080735049401170992691007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46053823366267447328460671 69080735049401170992691007)
      ·
        refine ⟨103621102574101756489036511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69080735049401170992691007 103621102574101756489036511)
        ·
          refine ⟨155431653861152634733554767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103621102574101756489036511 155431653861152634733554767)
          ·
            refine ⟨233147480791728952100332151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155431653861152634733554767 233147480791728952100332151)
            ·
              refine ⟨349721221187593428150498227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233147480791728952100332151 349721221187593428150498227)
              ·
                refine ⟨524581831781390142225747341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349721221187593428150498227 524581831781390142225747341)
                ·
                  refine ⟨196718186918021303334655253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524581831781390142225747341 196718186918021303334655253)
                  ·
                    refine ⟨9221165011782248593811965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 196718186918021303334655253 9221165011782248593811965)
                    ·
                      refine ⟨3457936879418343222679487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9221165011782248593811965 3457936879418343222679487)
                      ·
                        rfl

theorem cell23_6734308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_6734308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734308 prefixEnd_6734308 := by exact prefixLift 6734308
  have htrace : WordTrace (prefixWord ++ tailWord_6734308) baseStart_6734308 baseEnd_6734308 := by
    simpa [prefixWord, tailWord_6734308, baseEnd_6734308] using wordTrace_append hprefix tailTrace_6734308
  have hstable : (prefixWord ++ tailWord_6734308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734308).length < 2 ^ (prefixWord ++ tailWord_6734308).sum := by decide
  have hdescent : baseEnd_6734308 < baseStart_6734308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734405 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_6734405 : Nat := 118140960795 + 6734405 * 2 ^ 59
def prefixEnd_6734405 : Nat := 4983230072969 + 3 ^ 40 * 6734405 * 2
def baseEnd_6734405 : Nat := 1152662229013943114388847

theorem tailTrace_6734405 : CollatzResearch.WordTrace tailWord_6734405 prefixEnd_6734405 1152662229013943114388847 := by
  unfold tailWord_6734405
  simp only [CollatzResearch.WordTrace]
  refine ⟨245623929167408304651404669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163749286111605536434269779 245623929167408304651404669)
  ·
    refine ⟨92108973437778114244276751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245623929167408304651404669 92108973437778114244276751)
    ·
      refine ⟨138163460156667171366415127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92108973437778114244276751 138163460156667171366415127)
      ·
        refine ⟨207245190235000757049622691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138163460156667171366415127 207245190235000757049622691)
        ·
          refine ⟨310867785352501135574434037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207245190235000757049622691 310867785352501135574434037)
          ·
            refine ⟨29143854876796981460103191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310867785352501135574434037 29143854876796981460103191)
            ·
              refine ⟨43715782315195472190154787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29143854876796981460103191 43715782315195472190154787)
              ·
                refine ⟨65573673472793208285232181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43715782315195472190154787 65573673472793208285232181)
                ·
                  refine ⟨6147531888074363276740517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65573673472793208285232181 6147531888074363276740517)
                  ·
                    refine ⟨1152662229013943114388847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6147531888074363276740517 1152662229013943114388847)
                    ·
                      rfl

theorem cell23_6734405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_6734405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734405 prefixEnd_6734405 := by exact prefixLift 6734405
  have htrace : WordTrace (prefixWord ++ tailWord_6734405) baseStart_6734405 baseEnd_6734405 := by
    simpa [prefixWord, tailWord_6734405, baseEnd_6734405] using wordTrace_append hprefix tailTrace_6734405
  have hstable : (prefixWord ++ tailWord_6734405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734405).length < 2 ^ (prefixWord ++ tailWord_6734405).sum := by decide
  have hdescent : baseEnd_6734405 < baseStart_6734405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734408 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_6734408 : Nat := 118140960795 + 6734408 * 2 ^ 59
def prefixEnd_6734408 : Nat := 4983230072969 + 3 ^ 40 * 6734408 * 2
def baseEnd_6734408 : Nat := 3457988227483792831429027

theorem tailTrace_6734408 : CollatzResearch.WordTrace tailWord_6734408 prefixEnd_6734408 3457988227483792831429027 := by
  unfold tailWord_6734408
  simp only [CollatzResearch.WordTrace]
  refine ⟨122812019293198718081881939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163749359057598290775842585 122812019293198718081881939)
  ·
    refine ⟨184218028939798077122822909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122812019293198718081881939 184218028939798077122822909)
    ·
      refine ⟨69081760852424278921058591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184218028939798077122822909 69081760852424278921058591)
      ·
        refine ⟨103622641278636418381587887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69081760852424278921058591 103622641278636418381587887)
        ·
          refine ⟨155433961917954627572381831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103622641278636418381587887 155433961917954627572381831)
          ·
            refine ⟨233150942876931941358572747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155433961917954627572381831 233150942876931941358572747)
            ·
              refine ⟨349726414315397912037859121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233150942876931941358572747 349726414315397912037859121)
              ·
                refine ⟨262294810736548434028394341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349726414315397912037859121 262294810736548434028394341)
                ·
                  refine ⟨49180277013102831380323939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262294810736548434028394341 49180277013102831380323939)
                  ·
                    refine ⟨73770415519654247070485909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49180277013102831380323939 73770415519654247070485909)
                    ·
                      refine ⟨3457988227483792831429027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73770415519654247070485909 3457988227483792831429027)
                      ·
                        rfl

theorem cell23_6734408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_6734408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734408 prefixEnd_6734408 := by exact prefixLift 6734408
  have htrace : WordTrace (prefixWord ++ tailWord_6734408) baseStart_6734408 baseEnd_6734408 := by
    simpa [prefixWord, tailWord_6734408, baseEnd_6734408] using wordTrace_append hprefix tailTrace_6734408
  have hstable : (prefixWord ++ tailWord_6734408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734408).length < 2 ^ (prefixWord ++ tailWord_6734408).sum := by decide
  have hdescent : baseEnd_6734408 < baseStart_6734408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734485 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_6734485 : Nat := 118140960795 + 6734485 * 2 ^ 59
def prefixEnd_6734485 : Nat := 4983230072969 + 3 ^ 40 * 6734485 * 2
def baseEnd_6734485 : Nat := 3458027765494189030166173

theorem tailTrace_6734485 : CollatzResearch.WordTrace tailWord_6734485 prefixEnd_6734485 3458027765494189030166173 := by
  unfold tailWord_6734485
  simp only [CollatzResearch.WordTrace]
  refine ⟨245626847007118478314316909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163751231338078985542877939 245626847007118478314316909)
  ·
    refine ⟨92110067627669429367868841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245626847007118478314316909 92110067627669429367868841)
    ·
      refine ⟨69082550720752072025901631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92110067627669429367868841 69082550720752072025901631)
      ·
        refine ⟨103623826081128108038852447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69082550720752072025901631 103623826081128108038852447)
        ·
          refine ⟨155435739121692162058278671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103623826081128108038852447 155435739121692162058278671)
          ·
            refine ⟨233153608682538243087418007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155435739121692162058278671 233153608682538243087418007)
            ·
              refine ⟨349730413023807364631127011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233153608682538243087418007 349730413023807364631127011)
              ·
                refine ⟨524595619535711046946690517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349730413023807364631127011 524595619535711046946690517)
                ·
                  refine ⟨12295209832868227662813059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 524595619535711046946690517 12295209832868227662813059)
                  ·
                    refine ⟨18442814749302341494219589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12295209832868227662813059 18442814749302341494219589)
                    ·
                      refine ⟨3458027765494189030166173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18442814749302341494219589 3458027765494189030166173)
                      ·
                        rfl

theorem cell23_6734485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_6734485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734485 prefixEnd_6734485 := by exact prefixLift 6734485
  have htrace : WordTrace (prefixWord ++ tailWord_6734485) baseStart_6734485 baseEnd_6734485 := by
    simpa [prefixWord, tailWord_6734485, baseEnd_6734485] using wordTrace_append hprefix tailTrace_6734485
  have hstable : (prefixWord ++ tailWord_6734485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734485).length < 2 ^ (prefixWord ++ tailWord_6734485).sum := by decide
  have hdescent : baseEnd_6734485 < baseStart_6734485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734496 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 3, 1, 3]
def baseStart_6734496 : Nat := 118140960795 + 6734496 * 2 ^ 59
def prefixEnd_6734496 : Nat := 4983230072969 + 3 ^ 40 * 6734496 * 2
def baseEnd_6734496 : Nat := 3458033413781388487128623

theorem tailTrace_6734496 : CollatzResearch.WordTrace tailWord_6734496 prefixEnd_6734496 3458033413781388487128623 := by
  unfold tailWord_6734496
  simp only [CollatzResearch.WordTrace]
  refine ⟨122813624105039313596483671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163751498806719084795311561 122813624105039313596483671)
  ·
    refine ⟨184220436157558970394725507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122813624105039313596483671 184220436157558970394725507)
    ·
      refine ⟨276330654236338455592088261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184220436157558970394725507 276330654236338455592088261)
      ·
        refine ⟨51811997669313460423516549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276330654236338455592088261 51811997669313460423516549)
        ·
          refine ⟨9714749562996273829409353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51811997669313460423516549 9714749562996273829409353)
          ·
            refine ⟨7286062172247205372057015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9714749562996273829409353 7286062172247205372057015)
            ·
              refine ⟨10929093258370808058085523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286062172247205372057015 10929093258370808058085523)
              ·
                refine ⟨16393639887556212087128285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929093258370808058085523 16393639887556212087128285)
                ·
                  refine ⟨6147614957833579532673107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16393639887556212087128285 6147614957833579532673107)
                  ·
                    refine ⟨9221422436750369299009661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6147614957833579532673107 9221422436750369299009661)
                    ·
                      refine ⟨3458033413781388487128623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9221422436750369299009661 3458033413781388487128623)
                      ·
                        rfl

theorem cell23_6734496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_6734496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734496 prefixEnd_6734496 := by exact prefixLift 6734496
  have htrace : WordTrace (prefixWord ++ tailWord_6734496) baseStart_6734496 baseEnd_6734496 := by
    simpa [prefixWord, tailWord_6734496, baseEnd_6734496] using wordTrace_append hprefix tailTrace_6734496
  have hstable : (prefixWord ++ tailWord_6734496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734496).length < 2 ^ (prefixWord ++ tailWord_6734496).sum := by decide
  have hdescent : baseEnd_6734496 < baseStart_6734496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734503 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 6]
def baseStart_6734503 : Nat := 118140960795 + 6734503 * 2 ^ 59
def prefixEnd_6734503 : Nat := 4983230072969 + 3 ^ 40 * 6734503 * 2
def baseEnd_6734503 : Nat := 384226334238441106637899

theorem tailTrace_6734503 : CollatzResearch.WordTrace tailWord_6734503 prefixEnd_6734503 384226334238441106637899 := by
  unfold tailWord_6734503
  simp only [CollatzResearch.WordTrace]
  refine ⟨245627503521053267388472163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163751669014035511592314775 245627503521053267388472163)
  ·
    refine ⟨368441255281579901082708245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245627503521053267388472163 368441255281579901082708245)
    ·
      refine ⟨17270683841324057863251949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 368441255281579901082708245 17270683841324057863251949)
      ·
        refine ⟨6476506440496521698719481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17270683841324057863251949 6476506440496521698719481)
        ·
          refine ⟨4857379830372391274039611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6476506440496521698719481 4857379830372391274039611)
          ·
            refine ⟨7286069745558586911059417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4857379830372391274039611 7286069745558586911059417)
            ·
              refine ⟨5464552309168940183294563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7286069745558586911059417 5464552309168940183294563)
              ·
                refine ⟨8196828463753410274941845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5464552309168940183294563 8196828463753410274941845)
                ·
                  refine ⟨384226334238441106637899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8196828463753410274941845 384226334238441106637899)
                  ·
                    rfl

theorem cell23_6734503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 6].length) (baseStart_6734503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734503 prefixEnd_6734503 := by exact prefixLift 6734503
  have htrace : WordTrace (prefixWord ++ tailWord_6734503) baseStart_6734503 baseEnd_6734503 := by
    simpa [prefixWord, tailWord_6734503, baseEnd_6734503] using wordTrace_append hprefix tailTrace_6734503
  have hstable : (prefixWord ++ tailWord_6734503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734503).length < 2 ^ (prefixWord ++ tailWord_6734503).sum := by decide
  have hdescent : baseEnd_6734503 < baseStart_6734503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734515 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6]
def baseStart_6734515 : Nat := 118140960795 + 6734515 * 2 ^ 59
def prefixEnd_6734515 : Nat := 4983230072969 + 3 ^ 40 * 6734515 * 2
def baseEnd_6734515 : Nat := 3458043169913823912791035

theorem tailTrace_6734515 : CollatzResearch.WordTrace tailWord_6734515 prefixEnd_6734515 3458043169913823912791035 := by
  unfold tailWord_6734515
  simp only [CollatzResearch.WordTrace]
  refine ⟨245627941197009793437908999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163751960798006528958605999 245627941197009793437908999)
  ·
    refine ⟨368441911795514690156863499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245627941197009793437908999 368441911795514690156863499)
    ·
      refine ⟨552662867693272035235295249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368441911795514690156863499 552662867693272035235295249)
      ·
        refine ⟨414497150769954026426471437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552662867693272035235295249 414497150769954026426471437)
        ·
          refine ⟨155436431538732759909926789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414497150769954026426471437 155436431538732759909926789)
          ·
            refine ⟨29144330913512392483111273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155436431538732759909926789 29144330913512392483111273)
            ·
              refine ⟨21858248185134294362333455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29144330913512392483111273 21858248185134294362333455)
              ·
                refine ⟨32787372277701441543500183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21858248185134294362333455 32787372277701441543500183)
                ·
                  refine ⟨49181058416552162315250275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32787372277701441543500183 49181058416552162315250275)
                  ·
                    refine ⟨73771587624828243472875413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49181058416552162315250275 73771587624828243472875413)
                    ·
                      refine ⟨3458043169913823912791035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73771587624828243472875413 3458043169913823912791035)
                      ·
                        rfl

theorem cell23_6734515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_6734515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734515 prefixEnd_6734515 := by exact prefixLift 6734515
  have htrace : WordTrace (prefixWord ++ tailWord_6734515) baseStart_6734515 baseEnd_6734515 := by
    simpa [prefixWord, tailWord_6734515, baseEnd_6734515] using wordTrace_append hprefix tailTrace_6734515
  have hstable : (prefixWord ++ tailWord_6734515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734515).length < 2 ^ (prefixWord ++ tailWord_6734515).sum := by decide
  have hdescent : baseEnd_6734515 < baseStart_6734515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734522 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_6734522 : Nat := 118140960795 + 6734522 * 2 ^ 59
def prefixEnd_6734522 : Nat := 4983230072969 + 3 ^ 40 * 6734522 * 2
def baseEnd_6734522 : Nat := 3458046764278405385403503

theorem tailTrace_6734522 : CollatzResearch.WordTrace tailWord_6734522 prefixEnd_6734522 3458046764278405385403503 := by
  unfold tailWord_6734522
  simp only [CollatzResearch.WordTrace]
  refine ⟨61407049126996108408353455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163752131005322955755609213 61407049126996108408353455)
  ·
    refine ⟨92110573690494162612530183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61407049126996108408353455 92110573690494162612530183)
    ·
      refine ⟨138165860535741243918795275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92110573690494162612530183 138165860535741243918795275)
      ·
        refine ⟨207248790803611865878192913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138165860535741243918795275 207248790803611865878192913)
        ·
          refine ⟨155436593102708899408644685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207248790803611865878192913 155436593102708899408644685)
          ·
            refine ⟨58288722413515837278241757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155436593102708899408644685 58288722413515837278241757)
            ·
              refine ⟨21858270905068438979340659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58288722413515837278241757 21858270905068438979340659)
              ·
                refine ⟨32787406357602658469010989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21858270905068438979340659 32787406357602658469010989)
                ·
                  refine ⟨12295277384100996925879121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32787406357602658469010989 12295277384100996925879121)
                  ·
                    refine ⟨9221458038075747694409341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12295277384100996925879121 9221458038075747694409341)
                    ·
                      refine ⟨3458046764278405385403503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9221458038075747694409341 3458046764278405385403503)
                      ·
                        rfl

theorem cell23_6734522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_6734522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734522 prefixEnd_6734522 := by exact prefixLift 6734522
  have htrace : WordTrace (prefixWord ++ tailWord_6734522) baseStart_6734522 baseEnd_6734522 := by
    simpa [prefixWord, tailWord_6734522, baseEnd_6734522] using wordTrace_append hprefix tailTrace_6734522
  have hstable : (prefixWord ++ tailWord_6734522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734522).length < 2 ^ (prefixWord ++ tailWord_6734522).sum := by decide
  have hdescent : baseEnd_6734522 < baseStart_6734522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734525 : List Nat := [1, 4, 1, 2, 1, 3, 2, 9]
def baseStart_6734525 : Nat := 118140960795 + 6734525 * 2 ^ 59
def prefixEnd_6734525 : Nat := 4983230072969 + 3 ^ 40 * 6734525 * 2
def baseEnd_6734525 : Nat := 128075863137791439765407

theorem tailTrace_6734525 : CollatzResearch.WordTrace tailWord_6734525 prefixEnd_6734525 128075863137791439765407 := by
  unfold tailWord_6734525
  simp only [CollatzResearch.WordTrace]
  refine ⟨245628305926973565145773029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163752203951315710097182019 245628305926973565145773029)
  ·
    refine ⟨46055307361307543464832443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245628305926973565145773029 46055307361307543464832443)
    ·
      refine ⟨69082961041961315197248665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46055307361307543464832443 69082961041961315197248665)
      ·
        refine ⟨51812220781470986397936499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69082961041961315197248665 51812220781470986397936499)
        ·
          refine ⟨77718331172206479596904749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51812220781470986397936499 77718331172206479596904749)
          ·
            refine ⟨29144374189577429848839281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77718331172206479596904749 29144374189577429848839281)
            ·
              refine ⟨21858280642183072386629461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29144374189577429848839281 21858280642183072386629461)
              ·
                refine ⟨128075863137791439765407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21858280642183072386629461 128075863137791439765407)
                ·
                  rfl

theorem cell23_6734525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 9].length) (baseStart_6734525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734525 prefixEnd_6734525 := by exact prefixLift 6734525
  have htrace : WordTrace (prefixWord ++ tailWord_6734525) baseStart_6734525 baseEnd_6734525 := by
    simpa [prefixWord, tailWord_6734525, baseEnd_6734525] using wordTrace_append hprefix tailTrace_6734525
  have hstable : (prefixWord ++ tailWord_6734525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734525).length < 2 ^ (prefixWord ++ tailWord_6734525).sum := by decide
  have hdescent : baseEnd_6734525 < baseStart_6734525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734532 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_6734532 : Nat := 118140960795 + 6734532 * 2 ^ 59
def prefixEnd_6734532 : Nat := 4983230072969 + 3 ^ 40 * 6734532 * 2
def baseEnd_6734532 : Nat := 3458051899084950346278457

theorem tailTrace_6734532 : CollatzResearch.WordTrace tailWord_6734532 prefixEnd_6734532 3458051899084950346278457 := by
  unfold tailWord_6734532
  simp only [CollatzResearch.WordTrace]
  refine ⟨122814280618974102670638925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163752374158632136894185233 122814280618974102670638925)
  ·
    refine ⟨46055355232115288501489597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122814280618974102670638925 46055355232115288501489597)
    ·
      refine ⟨17270758212043233188058599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46055355232115288501489597 17270758212043233188058599)
      ·
        refine ⟨25906137318064849782087899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17270758212043233188058599 25906137318064849782087899)
        ·
          refine ⟨38859205977097274673131849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25906137318064849782087899 38859205977097274673131849)
          ·
            refine ⟨29144404482822956004848887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38859205977097274673131849 29144404482822956004848887)
            ·
              refine ⟨43716606724234434007273331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29144404482822956004848887 43716606724234434007273331)
              ·
                refine ⟨65574910086351651010909997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43716606724234434007273331 65574910086351651010909997)
                ·
                  refine ⟨24590591282381869129091249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65574910086351651010909997 24590591282381869129091249)
                  ·
                    refine ⟨18442943461786401846818437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24590591282381869129091249 18442943461786401846818437)
                    ·
                      refine ⟨3458051899084950346278457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18442943461786401846818437 3458051899084950346278457)
                      ·
                        rfl

theorem cell23_6734532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_6734532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734532 prefixEnd_6734532 := by exact prefixLift 6734532
  have htrace : WordTrace (prefixWord ++ tailWord_6734532) baseStart_6734532 baseEnd_6734532 := by
    simpa [prefixWord, tailWord_6734532, baseEnd_6734532] using wordTrace_append hprefix tailTrace_6734532
  have hstable : (prefixWord ++ tailWord_6734532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734532).length < 2 ^ (prefixWord ++ tailWord_6734532).sum := by decide
  have hdescent : baseEnd_6734532 < baseStart_6734532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734546 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_6734546 : Nat := 118140960795 + 6734546 * 2 ^ 59
def prefixEnd_6734546 : Nat := 4983230072969 + 3 ^ 40 * 6734546 * 2
def baseEnd_6734546 : Nat := 1152686362604704430501131

theorem tailTrace_6734546 : CollatzResearch.WordTrace tailWord_6734546 prefixEnd_6734546 1152686362604704430501131 := by
  unfold tailWord_6734546
  simp only [CollatzResearch.WordTrace]
  refine ⟨61407267964974371433071873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163752714573264990488191661 61407267964974371433071873)
  ·
    refine ⟨46055450973730778574803905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61407267964974371433071873 46055450973730778574803905)
    ·
      refine ⟨34541588230298083931102929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46055450973730778574803905 34541588230298083931102929)
      ·
        refine ⟨25906191172723562948327197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34541588230298083931102929 25906191172723562948327197)
        ·
          refine ⟨9714821689771336105622699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25906191172723562948327197 9714821689771336105622699)
          ·
            refine ⟨14572232534657004158434049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9714821689771336105622699 14572232534657004158434049)
            ·
              refine ⟨10929174400992753118825537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14572232534657004158434049 10929174400992753118825537)
              ·
                refine ⟨8196880800744564839119153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10929174400992753118825537 8196880800744564839119153)
                ·
                  refine ⟨6147660600558423629339365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8196880800744564839119153 6147660600558423629339365)
                  ·
                    refine ⟨1152686362604704430501131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6147660600558423629339365 1152686362604704430501131)
                    ·
                      rfl

theorem cell23_6734546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_6734546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734546 prefixEnd_6734546 := by exact prefixLift 6734546
  have htrace : WordTrace (prefixWord ++ tailWord_6734546) baseStart_6734546 baseEnd_6734546 := by
    simpa [prefixWord, tailWord_6734546, baseEnd_6734546] using wordTrace_append hprefix tailTrace_6734546
  have hstable : (prefixWord ++ tailWord_6734546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734546).length < 2 ^ (prefixWord ++ tailWord_6734546).sum := by decide
  have hdescent : baseEnd_6734546 < baseStart_6734546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734569 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 3]
def baseStart_6734569 : Nat := 118140960795 + 6734569 * 2 ^ 59
def prefixEnd_6734569 : Nat := 4983230072969 + 3 ^ 40 * 6734569 * 2
def baseEnd_6734569 : Nat := 3458070897869166701515787

theorem tailTrace_6734569 : CollatzResearch.WordTrace tailWord_6734569 prefixEnd_6734569 3458070897869166701515787 := by
  unfold tailWord_6734569
  simp only [CollatzResearch.WordTrace]
  refine ⟨245629910738814160660374761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163753273825876107106916507 245629910738814160660374761)
  ·
    refine ⟨184222433054110620495281071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245629910738814160660374761 184222433054110620495281071)
    ·
      refine ⟨276333649581165930742921607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184222433054110620495281071 276333649581165930742921607)
      ·
        refine ⟨414500474371748896114382411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276333649581165930742921607 414500474371748896114382411)
        ·
          refine ⟨621750711557623344171573617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414500474371748896114382411 621750711557623344171573617)
          ·
            refine ⟨466313033668217508128680213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621750711557623344171573617 466313033668217508128680213)
            ·
              refine ⟨21858423453197695693531885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 466313033668217508128680213 21858423453197695693531885)
              ·
                refine ⟨8196908794949135885074457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21858423453197695693531885 8196908794949135885074457)
                ·
                  refine ⟨6147681596211851913805843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8196908794949135885074457 6147681596211851913805843)
                  ·
                    refine ⟨9221522394317777870708765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6147681596211851913805843 9221522394317777870708765)
                    ·
                      refine ⟨3458070897869166701515787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9221522394317777870708765 3458070897869166701515787)
                      ·
                        rfl

theorem cell23_6734569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 3].length) (baseStart_6734569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734569 prefixEnd_6734569 := by exact prefixLift 6734569
  have htrace : WordTrace (prefixWord ++ tailWord_6734569) baseStart_6734569 baseEnd_6734569 := by
    simpa [prefixWord, tailWord_6734569, baseEnd_6734569] using wordTrace_append hprefix tailTrace_6734569
  have hstable : (prefixWord ++ tailWord_6734569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734569).length < 2 ^ (prefixWord ++ tailWord_6734569).sum := by decide
  have hdescent : baseEnd_6734569 < baseStart_6734569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734579 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 1, 3, 2]
def baseStart_6734579 : Nat := 118140960795 + 6734579 * 2 ^ 59
def prefixEnd_6734579 : Nat := 4983230072969 + 3 ^ 40 * 6734579 * 2
def baseEnd_6734579 : Nat := 3458076032675711662390741

theorem tailTrace_6734579 : CollatzResearch.WordTrace tailWord_6734579 prefixEnd_6734579 3458076032675711662390741 := by
  unfold tailWord_6734579
  simp only [CollatzResearch.WordTrace]
  refine ⟨245630275468777932368238791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163753516979185288245492527 245630275468777932368238791)
  ·
    refine ⟨368445413203166898552358187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245630275468777932368238791 368445413203166898552358187)
    ·
      refine ⟨552668119804750347828537281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368445413203166898552358187 552668119804750347828537281)
      ·
        refine ⟨414501089853562760871402961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552668119804750347828537281 414501089853562760871402961)
        ·
          refine ⟨310875817390172070653552221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414501089853562760871402961 310875817390172070653552221)
          ·
            refine ⟨116578431521314526495082083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310875817390172070653552221 116578431521314526495082083)
            ·
              refine ⟨174867647281971789742623125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116578431521314526495082083 174867647281971789742623125)
              ·
                refine ⟨8196920966342427644185459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174867647281971789742623125 8196920966342427644185459)
                ·
                  refine ⟨12295381449513641466278189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8196920966342427644185459 12295381449513641466278189)
                  ·
                    refine ⟨4610768043567615549854321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12295381449513641466278189 4610768043567615549854321)
                    ·
                      refine ⟨3458076032675711662390741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610768043567615549854321 3458076032675711662390741)
                      ·
                        rfl

theorem cell23_6734579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 3, 2].length) (baseStart_6734579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734579 prefixEnd_6734579 := by exact prefixLift 6734579
  have htrace : WordTrace (prefixWord ++ tailWord_6734579) baseStart_6734579 baseEnd_6734579 := by
    simpa [prefixWord, tailWord_6734579, baseEnd_6734579] using wordTrace_append hprefix tailTrace_6734579
  have hstable : (prefixWord ++ tailWord_6734579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734579).length < 2 ^ (prefixWord ++ tailWord_6734579).sum := by decide
  have hdescent : baseEnd_6734579 < baseStart_6734579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734582 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6734582 : Nat := 118140960795 + 6734582 * 2 ^ 59
def prefixEnd_6734582 : Nat := 4983230072969 + 3 ^ 40 * 6734582 * 2
def baseEnd_6734582 : Nat := 3458077573117675150653227

theorem tailTrace_6734582 : CollatzResearch.WordTrace tailWord_6734582 prefixEnd_6734582 3458077573117675150653227 := by
  unfold tailWord_6734582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15351899055485441492537375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163753589925178042587065333 15351899055485441492537375)
  ·
    refine ⟨23027848583228162238806063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15351899055485441492537375 23027848583228162238806063)
    ·
      refine ⟨34541772874842243358209095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23027848583228162238806063 34541772874842243358209095)
      ·
        refine ⟨51812659312263365037313643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34541772874842243358209095 51812659312263365037313643)
        ·
          refine ⟨77718988968395047555970465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51812659312263365037313643 77718988968395047555970465)
          ·
            refine ⟨58289241726296285666977849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77718988968395047555970465 58289241726296285666977849)
            ·
              refine ⟨43716931294722214250233387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58289241726296285666977849 43716931294722214250233387)
              ·
                refine ⟨65575396942083321375350081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43716931294722214250233387 65575396942083321375350081)
                ·
                  refine ⟨49181547706562491031512561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65575396942083321375350081 49181547706562491031512561)
                  ·
                    refine ⟨36886160779921868273634421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49181547706562491031512561 36886160779921868273634421)
                    ·
                      refine ⟨3458077573117675150653227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36886160779921868273634421 3458077573117675150653227)
                      ·
                        rfl

theorem cell23_6734582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6734582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734582 prefixEnd_6734582 := by exact prefixLift 6734582
  have htrace : WordTrace (prefixWord ++ tailWord_6734582) baseStart_6734582 baseEnd_6734582 := by
    simpa [prefixWord, tailWord_6734582, baseEnd_6734582] using wordTrace_append hprefix tailTrace_6734582
  have hstable : (prefixWord ++ tailWord_6734582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734582).length < 2 ^ (prefixWord ++ tailWord_6734582).sum := by decide
  have hdescent : baseEnd_6734582 < baseStart_6734582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734595 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5]
def baseStart_6734595 : Nat := 118140960795 + 6734595 * 2 ^ 59
def prefixEnd_6734595 : Nat := 4983230072969 + 3 ^ 40 * 6734595 * 2
def baseEnd_6734595 : Nat := 3458084248366183599790667

theorem tailTrace_6734595 : CollatzResearch.WordTrace tailWord_6734595 prefixEnd_6734595 3458084248366183599790667 := by
  unfold tailWord_6734595
  simp only [CollatzResearch.WordTrace]
  refine ⟨245630859036719967100821239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163753906024479978067214159 245630859036719967100821239)
  ·
    refine ⟨368446288555079950651231859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245630859036719967100821239 368446288555079950651231859)
    ·
      refine ⟨552669432832619925976847789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368446288555079950651231859 552669432832619925976847789)
      ·
        refine ⟨207251037312232472241317921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552669432832619925976847789 207251037312232472241317921)
        ·
          refine ⟨155438277984174354180988441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207251037312232472241317921 155438277984174354180988441)
          ·
            refine ⟨116578708488130765635741331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155438277984174354180988441 116578708488130765635741331)
            ·
              refine ⟨174868062732196148453611997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116578708488130765635741331 174868062732196148453611997)
              ·
                refine ⟨65575523524573555670104499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174868062732196148453611997 65575523524573555670104499)
                ·
                  refine ⟨98363285286860333505156749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65575523524573555670104499 98363285286860333505156749)
                  ·
                    refine ⟨36886231982572625064433781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98363285286860333505156749 36886231982572625064433781)
                    ·
                      refine ⟨3458084248366183599790667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36886231982572625064433781 3458084248366183599790667)
                      ·
                        rfl

theorem cell23_6734595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_6734595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734595 prefixEnd_6734595 := by exact prefixLift 6734595
  have htrace : WordTrace (prefixWord ++ tailWord_6734595) baseStart_6734595 baseEnd_6734595 := by
    simpa [prefixWord, tailWord_6734595, baseEnd_6734595] using wordTrace_append hprefix tailTrace_6734595
  have hstable : (prefixWord ++ tailWord_6734595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734595).length < 2 ^ (prefixWord ++ tailWord_6734595).sum := by decide
  have hdescent : baseEnd_6734595 < baseStart_6734595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734596 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6734596 : Nat := 118140960795 + 6734596 * 2 ^ 59
def prefixEnd_6734596 : Nat := 4983230072969 + 3 ^ 40 * 6734596 * 2
def baseEnd_6734596 : Nat := 3458084761846838095878163

theorem tailTrace_6734596 : CollatzResearch.WordTrace tailWord_6734596 prefixEnd_6734596 3458084761846838095878163 := by
  unfold tailWord_6734596
  simp only [CollatzResearch.WordTrace]
  refine ⟨122815447754858172135803821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163753930339810896181071761 122815447754858172135803821)
  ·
    refine ⟨46055792908071814550926433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122815447754858172135803821 46055792908071814550926433)
    ·
      refine ⟨34541844681053860913194825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46055792908071814550926433 34541844681053860913194825)
      ·
        refine ⟨25906383510790395684896119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34541844681053860913194825 25906383510790395684896119)
        ·
          refine ⟨38859575266185593527344179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25906383510790395684896119 38859575266185593527344179)
          ·
            refine ⟨58289362899278390291016269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38859575266185593527344179 58289362899278390291016269)
            ·
              refine ⟨21858511087229396359131101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58289362899278390291016269 21858511087229396359131101)
              ·
                refine ⟨8196941657711023634674163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21858511087229396359131101 8196941657711023634674163)
                ·
                  refine ⟨12295412486566535452011245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8196941657711023634674163 12295412486566535452011245)
                  ·
                    refine ⟨4610779682462450794504217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12295412486566535452011245 4610779682462450794504217)
                    ·
                      refine ⟨3458084761846838095878163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610779682462450794504217 3458084761846838095878163)
                      ·
                        rfl

theorem cell23_6734596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6734596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734596 prefixEnd_6734596 := by exact prefixLift 6734596
  have htrace : WordTrace (prefixWord ++ tailWord_6734596) baseStart_6734596 baseEnd_6734596 := by
    simpa [prefixWord, tailWord_6734596, baseEnd_6734596] using wordTrace_append hprefix tailTrace_6734596
  have hstable : (prefixWord ++ tailWord_6734596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734596).length < 2 ^ (prefixWord ++ tailWord_6734596).sum := by decide
  have hdescent : baseEnd_6734596 < baseStart_6734596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734626 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_6734626 : Nat := 118140960795 + 6734626 * 2 ^ 59
def prefixEnd_6734626 : Nat := 4983230072969 + 3 ^ 40 * 6734626 * 2
def baseEnd_6734626 : Nat := 3458100166266472978503025

theorem tailTrace_6734626 : CollatzResearch.WordTrace tailWord_6734626 prefixEnd_6734626 3458100166266472978503025 := by
  unfold tailWord_6734626
  simp only [CollatzResearch.WordTrace]
  refine ⟨61407997424901914848799933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163754659799738439596799821 61407997424901914848799933)
  ·
    refine ⟨23027999034338218068299975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61407997424901914848799933 23027999034338218068299975)
    ·
      refine ⟨34541998551507327102449963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23027999034338218068299975 34541998551507327102449963)
      ·
        refine ⟨51812997827260990653674945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34541998551507327102449963 51812997827260990653674945)
        ·
          refine ⟨38859748370445742990256209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51812997827260990653674945 38859748370445742990256209)
          ·
            refine ⟨29144811277834307242692157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38859748370445742990256209 29144811277834307242692157)
            ·
              refine ⟨10929304229187865216009559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29144811277834307242692157 10929304229187865216009559)
              ·
                refine ⟨16393956343781797824014339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929304229187865216009559 16393956343781797824014339)
                ·
                  refine ⟨24590934515672696736021509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16393956343781797824014339 24590934515672696736021509)
                  ·
                    refine ⟨4610800221688630638004033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24590934515672696736021509 4610800221688630638004033)
                    ·
                      refine ⟨3458100166266472978503025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610800221688630638004033 3458100166266472978503025)
                      ·
                        rfl

theorem cell23_6734626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_6734626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734626 prefixEnd_6734626 := by exact prefixLift 6734626
  have htrace : WordTrace (prefixWord ++ tailWord_6734626) baseStart_6734626 baseEnd_6734626 := by
    simpa [prefixWord, tailWord_6734626, baseEnd_6734626] using wordTrace_append hprefix tailTrace_6734626
  have hstable : (prefixWord ++ tailWord_6734626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734626).length < 2 ^ (prefixWord ++ tailWord_6734626).sum := by decide
  have hdescent : baseEnd_6734626 < baseStart_6734626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734632 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 7]
def baseStart_6734632 : Nat := 118140960795 + 6734632 * 2 ^ 59
def prefixEnd_6734632 : Nat := 4983230072969 + 3 ^ 40 * 6734632 * 2
def baseEnd_6734632 : Nat := 384233694127822217225333

theorem tailTrace_6734632 : CollatzResearch.WordTrace tailWord_6734632 prefixEnd_6734632 384233694127822217225333 := by
  unfold tailWord_6734632
  simp only [CollatzResearch.WordTrace]
  refine ⟨122816104268792961209959075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163754805691723948279945433 122816104268792961209959075)
  ·
    refine ⟨184224156403189441814938613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122816104268792961209959075 184224156403189441814938613)
    ·
      refine ⟨17271014662799010170150495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184224156403189441814938613 17271014662799010170150495)
      ·
        refine ⟨25906521994198515255225743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17271014662799010170150495 25906521994198515255225743)
        ·
          refine ⟨38859782991297772882838615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25906521994198515255225743 38859782991297772882838615)
          ·
            refine ⟨58289674486946659324257923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38859782991297772882838615 58289674486946659324257923)
            ·
              refine ⟨87434511730419988986386885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58289674486946659324257923 87434511730419988986386885)
              ·
                refine ⟨16393970949453747934947541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87434511730419988986386885 16393970949453747934947541)
                ·
                  refine ⟨384233694127822217225333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16393970949453747934947541 384233694127822217225333)
                  ·
                    rfl

theorem cell23_6734632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 7].length) (baseStart_6734632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734632 prefixEnd_6734632 := by exact prefixLift 6734632
  have htrace : WordTrace (prefixWord ++ tailWord_6734632) baseStart_6734632 baseEnd_6734632 := by
    simpa [prefixWord, tailWord_6734632, baseEnd_6734632] using wordTrace_append hprefix tailTrace_6734632
  have hstable : (prefixWord ++ tailWord_6734632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734632).length < 2 ^ (prefixWord ++ tailWord_6734632).sum := by decide
  have hdescent : baseEnd_6734632 < baseStart_6734632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734646 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6734646 : Nat := 118140960795 + 6734646 * 2 ^ 59
def prefixEnd_6734646 : Nat := 4983230072969 + 3 ^ 40 * 6734646 * 2
def baseEnd_6734646 : Nat := 3458110435879562900252933

theorem tailTrace_6734646 : CollatzResearch.WordTrace tailWord_6734646 prefixEnd_6734646 3458110435879562900252933 := by
  unfold tailWord_6734646
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352044947470950175682987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163755146106356801873951861 15352044947470950175682987)
  ·
    refine ⟨23028067421206425263524481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15352044947470950175682987 23028067421206425263524481)
    ·
      refine ⟨17271050565904818947643361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23028067421206425263524481 17271050565904818947643361)
      ·
        refine ⟨12953287924428614210732521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17271050565904818947643361 12953287924428614210732521)
        ·
          refine ⟨9714965943321460658049391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12953287924428614210732521 9714965943321460658049391)
          ·
            refine ⟨14572448914982190987074087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9714965943321460658049391 14572448914982190987074087)
            ·
              refine ⟨21858673372473286480611131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14572448914982190987074087 21858673372473286480611131)
              ·
                refine ⟨32788010058709929720916697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21858673372473286480611131 32788010058709929720916697)
                ·
                  refine ⟨24591007544032447290687523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32788010058709929720916697 24591007544032447290687523)
                  ·
                    refine ⟨36886511316048670936031285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24591007544032447290687523 36886511316048670936031285)
                    ·
                      refine ⟨3458110435879562900252933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36886511316048670936031285 3458110435879562900252933)
                      ·
                        rfl

theorem cell23_6734646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6734646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734646 prefixEnd_6734646 := by exact prefixLift 6734646
  have htrace : WordTrace (prefixWord ++ tailWord_6734646) baseStart_6734646 baseEnd_6734646 := by
    simpa [prefixWord, tailWord_6734646, baseEnd_6734646] using wordTrace_append hprefix tailTrace_6734646
  have hstable : (prefixWord ++ tailWord_6734646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734646).length < 2 ^ (prefixWord ++ tailWord_6734646).sum := by decide
  have hdescent : baseEnd_6734646 < baseStart_6734646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734719 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 3]
def baseStart_6734719 : Nat := 118140960795 + 6734719 * 2 ^ 59
def prefixEnd_6734719 : Nat := 4983230072969 + 3 ^ 40 * 6734719 * 2
def baseEnd_6734719 : Nat := 3458147919967341114640097

theorem tailTrace_6734719 : CollatzResearch.WordTrace tailWord_6734719 prefixEnd_6734719 3458147919967341114640097 := by
  unfold tailWord_6734719
  simp only [CollatzResearch.WordTrace]
  refine ⟨245635381688270736278335211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163756921125513824185556807 245635381688270736278335211)
  ·
    refine ⟨368453072532406104417502817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245635381688270736278335211 368453072532406104417502817)
    ·
      refine ⟨276339804399304578313127113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368453072532406104417502817 276339804399304578313127113)
      ·
        refine ⟨207254853299478433734845335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276339804399304578313127113 207254853299478433734845335)
        ·
          refine ⟨310882279949217650602268003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207254853299478433734845335 310882279949217650602268003)
          ·
            refine ⟨466323419923826475903402005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310882279949217650602268003 466323419923826475903402005)
            ·
              refine ⟨21858910308929366057971969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 466323419923826475903402005 21858910308929366057971969)
              ·
                refine ⟨16394182731697024543478977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21858910308929366057971969 16394182731697024543478977)
                ·
                  refine ⟨12295637048772768407609233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16394182731697024543478977 12295637048772768407609233)
                  ·
                    refine ⟨9221727786579576305706925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12295637048772768407609233 9221727786579576305706925)
                    ·
                      refine ⟨3458147919967341114640097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9221727786579576305706925 3458147919967341114640097)
                      ·
                        rfl

theorem cell23_6734719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_6734719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734719 prefixEnd_6734719 := by exact prefixLift 6734719
  have htrace : WordTrace (prefixWord ++ tailWord_6734719) baseStart_6734719 baseEnd_6734719 := by
    simpa [prefixWord, tailWord_6734719, baseEnd_6734719] using wordTrace_append hprefix tailTrace_6734719
  have hstable : (prefixWord ++ tailWord_6734719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734719).length < 2 ^ (prefixWord ++ tailWord_6734719).sum := by decide
  have hdescent : baseEnd_6734719 < baseStart_6734719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734753 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6734753 : Nat := 118140960795 + 6734753 * 2 ^ 59
def prefixEnd_6734753 : Nat := 4983230072969 + 3 ^ 40 * 6734753 * 2
def baseEnd_6734753 : Nat := 3458165378309593981614941

theorem tailTrace_6734753 : CollatzResearch.WordTrace tailWord_6734753 prefixEnd_6734753 3458165378309593981614941 := by
  unfold tailWord_6734753
  simp only [CollatzResearch.WordTrace]
  refine ⟨245636621770147560085072913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163757747846765040056715275 245636621770147560085072913)
  ·
    refine ⟨184227466327610670063804685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245636621770147560085072913 184227466327610670063804685)
    ·
      refine ⟨69085299872854001273926757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184227466327610670063804685 69085299872854001273926757)
      ·
        refine ⟨12953493726160125238861267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69085299872854001273926757 12953493726160125238861267)
        ·
          refine ⟨19430240589240187858291901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12953493726160125238861267 19430240589240187858291901)
          ·
            refine ⟨7286340220965070446859463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19430240589240187858291901 7286340220965070446859463)
            ·
              refine ⟨10929510331447605670289195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286340220965070446859463 10929510331447605670289195)
              ·
                refine ⟨16394265497171408505433793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929510331447605670289195 16394265497171408505433793)
                ·
                  refine ⟨12295699122878556379075345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16394265497171408505433793 12295699122878556379075345)
                  ·
                    refine ⟨9221774342158917284306509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12295699122878556379075345 9221774342158917284306509)
                    ·
                      refine ⟨3458165378309593981614941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9221774342158917284306509 3458165378309593981614941)
                      ·
                        rfl

theorem cell23_6734753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6734753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734753 prefixEnd_6734753 := by exact prefixLift 6734753
  have htrace : WordTrace (prefixWord ++ tailWord_6734753) baseStart_6734753 baseEnd_6734753 := by
    simpa [prefixWord, tailWord_6734753, baseEnd_6734753] using wordTrace_append hprefix tailTrace_6734753
  have hstable : (prefixWord ++ tailWord_6734753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734753).length < 2 ^ (prefixWord ++ tailWord_6734753).sum := by decide
  have hdescent : baseEnd_6734753 < baseStart_6734753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734799 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 1, 6]
def baseStart_6734799 : Nat := 118140960795 + 6734799 * 2 ^ 59
def prefixEnd_6734799 : Nat := 4983230072969 + 3 ^ 40 * 6734799 * 2
def baseEnd_6734799 : Nat := 1152729666139900267213243

theorem tailTrace_6734799 : CollatzResearch.WordTrace tailWord_6734799 prefixEnd_6734799 1152729666139900267213243 := by
  unfold tailWord_6734799
  simp only [CollatzResearch.WordTrace]
  refine ⟨245638299527980909941247451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163758866351987273294164967 245638299527980909941247451)
  ·
    refine ⟨368457449291971364911871177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245638299527980909941247451 368457449291971364911871177)
    ·
      refine ⟨276343086968978523683903383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368457449291971364911871177 276343086968978523683903383)
      ·
        refine ⟨414514630453467785525855075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276343086968978523683903383 414514630453467785525855075)
        ·
          refine ⟨621771945680201678288782613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414514630453467785525855075 621771945680201678288782613)
          ·
            refine ⟨29145559953759453669786685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 621771945680201678288782613 29145559953759453669786685)
            ·
              refine ⟨10929584982659795126170007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29145559953759453669786685 10929584982659795126170007)
              ·
                refine ⟨16394377473989692689255011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929584982659795126170007 16394377473989692689255011)
                ·
                  refine ⟨24591566210984539033882517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16394377473989692689255011 24591566210984539033882517)
                  ·
                    refine ⟨1152729666139900267213243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24591566210984539033882517 1152729666139900267213243)
                    ·
                      rfl

theorem cell23_6734799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_6734799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734799 prefixEnd_6734799 := by exact prefixLift 6734799
  have htrace : WordTrace (prefixWord ++ tailWord_6734799) baseStart_6734799 baseEnd_6734799 := by
    simpa [prefixWord, tailWord_6734799, baseEnd_6734799] using wordTrace_append hprefix tailTrace_6734799
  have hstable : (prefixWord ++ tailWord_6734799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734799).length < 2 ^ (prefixWord ++ tailWord_6734799).sum := by decide
  have hdescent : baseEnd_6734799 < baseStart_6734799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734819 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6734819 : Nat := 118140960795 + 6734819 * 2 ^ 59
def prefixEnd_6734819 : Nat := 4983230072969 + 3 ^ 40 * 6734819 * 2
def baseEnd_6734819 : Nat := 3458199268032790723389637

theorem tailTrace_6734819 : CollatzResearch.WordTrace tailWord_6734819 prefixEnd_6734819 3458199268032790723389637 := by
  unfold tailWord_6734819
  simp only [CollatzResearch.WordTrace]
  refine ⟨245639028987908453356975511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163759352658605635571317007 245639028987908453356975511)
  ·
    refine ⟨368458543481862680035463267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245639028987908453356975511 368458543481862680035463267)
    ·
      refine ⟨552687815222794020053194901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368458543481862680035463267 552687815222794020053194901)
      ·
        refine ⟨25907241338568469689993511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 552687815222794020053194901 25907241338568469689993511)
        ·
          refine ⟨38860862007852704534990267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25907241338568469689993511 38860862007852704534990267)
          ·
            refine ⟨58291293011779056802485401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38860862007852704534990267 58291293011779056802485401)
            ·
              refine ⟨43718469758834292601864051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58291293011779056802485401 43718469758834292601864051)
              ·
                refine ⟨65577704638251438902796077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43718469758834292601864051 65577704638251438902796077)
                ·
                  refine ⟨24591639239344289588548529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65577704638251438902796077 24591639239344289588548529)
                  ·
                    refine ⟨18443729429508217191411397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24591639239344289588548529 18443729429508217191411397)
                    ·
                      refine ⟨3458199268032790723389637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18443729429508217191411397 3458199268032790723389637)
                      ·
                        rfl

theorem cell23_6734819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6734819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734819 prefixEnd_6734819 := by exact prefixLift 6734819
  have htrace : WordTrace (prefixWord ++ tailWord_6734819) baseStart_6734819 baseEnd_6734819 := by
    simpa [prefixWord, tailWord_6734819, baseEnd_6734819] using wordTrace_append hprefix tailTrace_6734819
  have hstable : (prefixWord ++ tailWord_6734819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734819).length < 2 ^ (prefixWord ++ tailWord_6734819).sum := by decide
  have hdescent : baseEnd_6734819 < baseStart_6734819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734826 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_6734826 : Nat := 118140960795 + 6734826 * 2 ^ 59
def prefixEnd_6734826 : Nat := 4983230072969 + 3 ^ 40 * 6734826 * 2
def baseEnd_6734826 : Nat := 3458202862397372196002105

theorem tailTrace_6734826 : CollatzResearch.WordTrace tailWord_6734826 prefixEnd_6734826 3458202862397372196002105 := by
  unfold tailWord_6734826
  simp only [CollatzResearch.WordTrace]
  refine ⟨61409821074720773388120083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163759522865922062368320221 61409821074720773388120083)
  ·
    refine ⟨92114731612081160082180125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61409821074720773388120083 92114731612081160082180125)
    ·
      refine ⟨34543024354530435030817547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92114731612081160082180125 34543024354530435030817547)
      ·
        refine ⟨51814536531795652546226321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34543024354530435030817547 51814536531795652546226321)
        ·
          refine ⟨38860902398846739409669741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51814536531795652546226321 38860902398846739409669741)
          ·
            refine ⟨14572838399567527278626153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38860902398846739409669741 14572838399567527278626153)
            ·
              refine ⟨10929628799675645458969615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14572838399567527278626153 10929628799675645458969615)
              ·
                refine ⟨16394443199513468188454423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929628799675645458969615 16394443199513468188454423)
                ·
                  refine ⟨24591664799270202282681635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16394443199513468188454423 24591664799270202282681635)
                  ·
                    refine ⟨36887497198905303424022453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24591664799270202282681635 36887497198905303424022453)
                    ·
                      refine ⟨3458202862397372196002105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36887497198905303424022453 3458202862397372196002105)
                      ·
                        rfl

theorem cell23_6734826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_6734826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734826 prefixEnd_6734826 := by exact prefixLift 6734826
  have htrace : WordTrace (prefixWord ++ tailWord_6734826) baseStart_6734826 baseEnd_6734826 := by
    simpa [prefixWord, tailWord_6734826, baseEnd_6734826] using wordTrace_append hprefix tailTrace_6734826
  have hstable : (prefixWord ++ tailWord_6734826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734826).length < 2 ^ (prefixWord ++ tailWord_6734826).sum := by decide
  have hdescent : baseEnd_6734826 < baseStart_6734826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734834 : List Nat := [3, 2, 1, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6734834 : Nat := 118140960795 + 6734834 * 2 ^ 59
def prefixEnd_6734834 : Nat := 4983230072969 + 3 ^ 40 * 6734834 * 2
def baseEnd_6734834 : Nat := 3458206970242608164702069

theorem tailTrace_6734834 : CollatzResearch.WordTrace tailWord_6734834 prefixEnd_6734834 3458206970242608164702069 := by
  unfold tailWord_6734834
  simp only [CollatzResearch.WordTrace]
  refine ⟨61409894020713527729692889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163759717388569407279181037 61409894020713527729692889)
  ·
    refine ⟨46057420515535145797269667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61409894020713527729692889 46057420515535145797269667)
    ·
      refine ⟨69086130773302718695904501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46057420515535145797269667 69086130773302718695904501)
      ·
        refine ⟨6476824759997129877741047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69086130773302718695904501 6476824759997129877741047)
        ·
          refine ⟨9715237139995694816611571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476824759997129877741047 9715237139995694816611571)
          ·
            refine ⟨14572855709993542224917357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715237139995694816611571 14572855709993542224917357)
            ·
              refine ⟨5464820891247578334344009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14572855709993542224917357 5464820891247578334344009)
              ·
                refine ⟨4098615668435683750758007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5464820891247578334344009 4098615668435683750758007)
                ·
                  refine ⟨6147923502653525626137011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098615668435683750758007 6147923502653525626137011)
                  ·
                    refine ⟨9221885253980288439205517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6147923502653525626137011 9221885253980288439205517)
                    ·
                      refine ⟨3458206970242608164702069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9221885253980288439205517 3458206970242608164702069)
                      ·
                        rfl

theorem cell23_6734834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6734834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734834 prefixEnd_6734834 := by exact prefixLift 6734834
  have htrace : WordTrace (prefixWord ++ tailWord_6734834) baseStart_6734834 baseEnd_6734834 := by
    simpa [prefixWord, tailWord_6734834, baseEnd_6734834] using wordTrace_append hprefix tailTrace_6734834
  have hstable : (prefixWord ++ tailWord_6734834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734834).length < 2 ^ (prefixWord ++ tailWord_6734834).sum := by decide
  have hdescent : baseEnd_6734834 < baseStart_6734834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734896 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 3, 4, 2]
def baseStart_6734896 : Nat := 118140960795 + 6734896 * 2 ^ 59
def prefixEnd_6734896 : Nat := 4983230072969 + 3 ^ 40 * 6734896 * 2
def baseEnd_6734896 : Nat := 3458238806043186922126783

theorem tailTrace_6734896 : CollatzResearch.WordTrace tailWord_6734896 prefixEnd_6734896 3458238806043186922126783 := by
  unfold tailWord_6734896
  simp only [CollatzResearch.WordTrace]
  refine ⟨122820918704314747753764271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163761224939086330338352361 122820918704314747753764271)
  ·
    refine ⟨184231378056472121630646407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122820918704314747753764271 184231378056472121630646407)
    ·
      refine ⟨276347067084708182445969611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184231378056472121630646407 276347067084708182445969611)
      ·
        refine ⟨414520600627062273668954417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276347067084708182445969611 414520600627062273668954417)
        ·
          refine ⟨310890450470296705251715813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414520600627062273668954417 310890450470296705251715813)
          ·
            refine ⟨58291959463180632234696715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310890450470296705251715813 58291959463180632234696715)
            ·
              refine ⟨87437939194770948352045073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58291959463180632234696715 87437939194770948352045073)
              ·
                refine ⟨65578454396078211264033805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87437939194770948352045073 65578454396078211264033805)
                ·
                  refine ⟨24591920398529329224012677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65578454396078211264033805 24591920398529329224012677)
                  ·
                    refine ⟨4610985074724249229502377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24591920398529329224012677 4610985074724249229502377)
                    ·
                      refine ⟨3458238806043186922126783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610985074724249229502377 3458238806043186922126783)
                      ·
                        rfl

theorem cell23_6734896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 4, 2].length) (baseStart_6734896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734896 prefixEnd_6734896 := by exact prefixLift 6734896
  have htrace : WordTrace (prefixWord ++ tailWord_6734896) baseStart_6734896 baseEnd_6734896 := by
    simpa [prefixWord, tailWord_6734896, baseEnd_6734896] using wordTrace_append hprefix tailTrace_6734896
  have hstable : (prefixWord ++ tailWord_6734896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734896).length < 2 ^ (prefixWord ++ tailWord_6734896).sum := by decide
  have hdescent : baseEnd_6734896 < baseStart_6734896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734900 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_6734900 : Nat := 118140960795 + 6734900 * 2 ^ 59
def prefixEnd_6734900 : Nat := 4983230072969 + 3 ^ 40 * 6734900 * 2
def baseEnd_6734900 : Nat := 3458240859965804906476765

theorem tailTrace_6734900 : CollatzResearch.WordTrace tailWord_6734900 prefixEnd_6734900 3458240859965804906476765 := by
  unfold tailWord_6734900
  simp only [CollatzResearch.WordTrace]
  refine ⟨122820991650307502095337077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163761322200410002793782769 122820991650307502095337077)
  ·
    refine ⟨11514467967216328321437851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122820991650307502095337077 11514467967216328321437851)
    ·
      refine ⟨17271701950824492482156777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11514467967216328321437851 17271701950824492482156777)
      ·
        refine ⟨12953776463118369361617583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17271701950824492482156777 12953776463118369361617583)
        ·
          refine ⟨19430664694677554042426375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12953776463118369361617583 19430664694677554042426375)
          ·
            refine ⟨29145997042016331063639563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19430664694677554042426375 29145997042016331063639563)
            ·
              refine ⟨43718995563024496595459345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29145997042016331063639563 43718995563024496595459345)
              ·
                refine ⟨32789246672268372446594509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43718995563024496595459345 32789246672268372446594509)
                ·
                  refine ⟨12295967502100639667472941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32789246672268372446594509 12295967502100639667472941)
                  ·
                    refine ⟨4610987813287739875302353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12295967502100639667472941 4610987813287739875302353)
                    ·
                      refine ⟨3458240859965804906476765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4610987813287739875302353 3458240859965804906476765)
                      ·
                        rfl

theorem cell23_6734900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_6734900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734900 prefixEnd_6734900 := by exact prefixLift 6734900
  have htrace : WordTrace (prefixWord ++ tailWord_6734900) baseStart_6734900 baseEnd_6734900 := by
    simpa [prefixWord, tailWord_6734900, baseEnd_6734900] using wordTrace_append hprefix tailTrace_6734900
  have hstable : (prefixWord ++ tailWord_6734900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734900).length < 2 ^ (prefixWord ++ tailWord_6734900).sum := by decide
  have hdescent : baseEnd_6734900 < baseStart_6734900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734919 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 9]
def baseStart_6734919 : Nat := 118140960795 + 6734919 * 2 ^ 59
def prefixEnd_6734919 : Nat := 4983230072969 + 3 ^ 40 * 6734919 * 2
def baseEnd_6734919 : Nat := 384250068455360036904353

theorem tailTrace_6734919 : CollatzResearch.WordTrace tailWord_6734919 prefixEnd_6734919 384250068455360036904353 := by
  unfold tailWord_6734919
  simp only [CollatzResearch.WordTrace]
  refine ⟨245642676287546170435615811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163761784191697446957077207 245642676287546170435615811)
  ·
    refine ⟨368464014431319255653423717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245642676287546170435615811 368464014431319255653423717)
    ·
      refine ⟨69087002705872360435016947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368464014431319255653423717 69087002705872360435016947)
      ·
        refine ⟨103630504058808540652525421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69087002705872360435016947 103630504058808540652525421)
        ·
          refine ⟨38861439022053202744697033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103630504058808540652525421 38861439022053202744697033)
          ·
            refine ⟨29146079266539902058522775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38861439022053202744697033 29146079266539902058522775)
            ·
              refine ⟨43719118899809853087784163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29146079266539902058522775 43719118899809853087784163)
              ·
                refine ⟨65578678349714779631676245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43719118899809853087784163 65578678349714779631676245)
                ·
                  refine ⟨384250068455360036904353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65578678349714779631676245 384250068455360036904353)
                  ·
                    rfl

theorem cell23_6734919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 9].length) (baseStart_6734919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734919 prefixEnd_6734919 := by exact prefixLift 6734919
  have htrace : WordTrace (prefixWord ++ tailWord_6734919) baseStart_6734919 baseEnd_6734919 := by
    simpa [prefixWord, tailWord_6734919, baseEnd_6734919] using wordTrace_append hprefix tailTrace_6734919
  have hstable : (prefixWord ++ tailWord_6734919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734919).length < 2 ^ (prefixWord ++ tailWord_6734919).sum := by decide
  have hdescent : baseEnd_6734919 < baseStart_6734919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734934 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_6734934 : Nat := 118140960795 + 6734934 * 2 ^ 59
def prefixEnd_6734934 : Nat := 4983230072969 + 3 ^ 40 * 6734934 * 2
def baseEnd_6734934 : Nat := 3458258318308057773451609

theorem tailTrace_6734934 : CollatzResearch.WordTrace tailWord_6734934 prefixEnd_6734934 3458258318308057773451609 := by
  unfold tailWord_6734934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352701461405739249838241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163762148921661218664941237 15352701461405739249838241)
  ·
    refine ⟨11514526096054304437378681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15352701461405739249838241 11514526096054304437378681)
    ·
      refine ⟨8635894572040728328034011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11514526096054304437378681 8635894572040728328034011)
      ·
        refine ⟨12953841858061092492051017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8635894572040728328034011 12953841858061092492051017)
        ·
          refine ⟨9715381393545819369038263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12953841858061092492051017 9715381393545819369038263)
          ·
            refine ⟨14573072090318729053557395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715381393545819369038263 14573072090318729053557395)
            ·
              refine ⟨21859608135478093580336093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14573072090318729053557395 21859608135478093580336093)
              ·
                refine ⟨8197353050804285092626035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21859608135478093580336093 8197353050804285092626035)
                ·
                  refine ⟨12296029576206427638939053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8197353050804285092626035 12296029576206427638939053)
                  ·
                    refine ⟨4611011091077410364602145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12296029576206427638939053 4611011091077410364602145)
                    ·
                      refine ⟨3458258318308057773451609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611011091077410364602145 3458258318308057773451609)
                      ·
                        rfl

theorem cell23_6734934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_6734934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734934 prefixEnd_6734934 := by exact prefixLift 6734934
  have htrace : WordTrace (prefixWord ++ tailWord_6734934) baseStart_6734934 baseEnd_6734934 := by
    simpa [prefixWord, tailWord_6734934, baseEnd_6734934] using wordTrace_append hprefix tailTrace_6734934
  have hstable : (prefixWord ++ tailWord_6734934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734934).length < 2 ^ (prefixWord ++ tailWord_6734934).sum := by decide
  have hdescent : baseEnd_6734934 < baseStart_6734934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734959 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_6734959 : Nat := 118140960795 + 6734959 * 2 ^ 59
def prefixEnd_6734959 : Nat := 4983230072969 + 3 ^ 40 * 6734959 * 2
def baseEnd_6734959 : Nat := 3458271155324420175638993

theorem tailTrace_6734959 : CollatzResearch.WordTrace tailWord_6734959 prefixEnd_6734959 3458271155324420175638993 := by
  unfold tailWord_6734959
  simp only [CollatzResearch.WordTrace]
  refine ⟨245644135207401257267071931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163762756804934171511381287 245644135207401257267071931)
  ·
    refine ⟨368466202811101885900607897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245644135207401257267071931 368466202811101885900607897)
    ·
      refine ⟨276349652108326414425455923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368466202811101885900607897 276349652108326414425455923)
      ·
        refine ⟨414524478162489621638183885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276349652108326414425455923 414524478162489621638183885)
        ·
          refine ⟨155446679310933608114318957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414524478162489621638183885 155446679310933608114318957)
          ·
            refine ⟨58292504741600103042869609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155446679310933608114318957 58292504741600103042869609)
            ·
              refine ⟨43719378556200077282152207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58292504741600103042869609 43719378556200077282152207)
              ·
                refine ⟨65579067834300115923228311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43719378556200077282152207 65579067834300115923228311)
                ·
                  refine ⟨98368601751450173884842467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65579067834300115923228311 98368601751450173884842467)
                  ·
                    refine ⟨147552902627175260827263701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98368601751450173884842467 147552902627175260827263701)
                    ·
                      refine ⟨3458271155324420175638993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147552902627175260827263701 3458271155324420175638993)
                      ·
                        rfl

theorem cell23_6734959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_6734959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734959 prefixEnd_6734959 := by exact prefixLift 6734959
  have htrace : WordTrace (prefixWord ++ tailWord_6734959) baseStart_6734959 baseEnd_6734959 := by
    simpa [prefixWord, tailWord_6734959, baseEnd_6734959] using wordTrace_append hprefix tailTrace_6734959
  have hstable : (prefixWord ++ tailWord_6734959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734959).length < 2 ^ (prefixWord ++ tailWord_6734959).sum := by decide
  have hdescent : baseEnd_6734959 < baseStart_6734959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734966 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_6734966 : Nat := 118140960795 + 6734966 * 2 ^ 59
def prefixEnd_6734966 : Nat := 4983230072969 + 3 ^ 40 * 6734966 * 2
def baseEnd_6734966 : Nat := 1152758249896333882750487

theorem tailTrace_6734966 : CollatzResearch.WordTrace tailWord_6734966 prefixEnd_6734966 1152758249896333882750487 := by
  unfold tailWord_6734966
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352774407398493591411047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163762927012250598308384501 15352774407398493591411047)
  ·
    refine ⟨23029161611097740387116571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15352774407398493591411047 23029161611097740387116571)
    ·
      refine ⟨34543742416646610580674857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23029161611097740387116571 34543742416646610580674857)
      ·
        refine ⟨25907806812484957935506143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34543742416646610580674857 25907806812484957935506143)
        ·
          refine ⟨38861710218727436903259215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25907806812484957935506143 38861710218727436903259215)
          ·
            refine ⟨58292565328091155354888823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38861710218727436903259215 58292565328091155354888823)
            ·
              refine ⟨87438847992136733032333235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58292565328091155354888823 87438847992136733032333235)
              ·
                refine ⟨131158271988205099548499853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87438847992136733032333235 131158271988205099548499853)
                ·
                  refine ⟨49184351995576912330687445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131158271988205099548499853 49184351995576912330687445)
                  ·
                    refine ⟨1152758249896333882750487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49184351995576912330687445 1152758249896333882750487)
                    ·
                      rfl

theorem cell23_6734966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_6734966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734966 prefixEnd_6734966 := by exact prefixLift 6734966
  have htrace : WordTrace (prefixWord ++ tailWord_6734966) baseStart_6734966 baseEnd_6734966 := by
    simpa [prefixWord, tailWord_6734966, baseEnd_6734966] using wordTrace_append hprefix tailTrace_6734966
  have hstable : (prefixWord ++ tailWord_6734966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734966).length < 2 ^ (prefixWord ++ tailWord_6734966).sum := by decide
  have hdescent : baseEnd_6734966 < baseStart_6734966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734979 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 2, 8]
def baseStart_6734979 : Nat := 118140960795 + 6734979 * 2 ^ 59
def prefixEnd_6734979 : Nat := 4983230072969 + 3 ^ 40 * 6734979 * 2
def baseEnd_6734979 : Nat := 1152760474979170032462967

theorem tailTrace_6734979 : CollatzResearch.WordTrace tailWord_6734979 prefixEnd_6734979 1152760474979170032462967 := by
  unfold tailWord_6734979
  simp only [CollatzResearch.WordTrace]
  refine ⟨245644864667328800682799991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163763243111552533788533327 245644864667328800682799991)
  ·
    refine ⟨368467297000993201024199987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245644864667328800682799991 368467297000993201024199987)
    ·
      refine ⟨552700945501489801536299981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368467297000993201024199987 552700945501489801536299981)
      ·
        refine ⟨207262854563058675576112493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552700945501489801536299981 207262854563058675576112493)
        ·
          refine ⟨77723570461147003341042185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207262854563058675576112493 77723570461147003341042185)
          ·
            refine ⟨58292677845860252505781639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77723570461147003341042185 58292677845860252505781639)
            ·
              refine ⟨87439016768790378758672459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58292677845860252505781639 87439016768790378758672459)
              ·
                refine ⟨131158525153185568138008689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87439016768790378758672459 131158525153185568138008689)
                ·
                  refine ⟨98368893864889176103506517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131158525153185568138008689 98368893864889176103506517)
                  ·
                    refine ⟨1152760474979170032462967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98368893864889176103506517 1152760474979170032462967)
                    ·
                      rfl

theorem cell23_6734979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 8].length) (baseStart_6734979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734979 prefixEnd_6734979 := by exact prefixLift 6734979
  have htrace : WordTrace (prefixWord ++ tailWord_6734979) baseStart_6734979 baseEnd_6734979 := by
    simpa [prefixWord, tailWord_6734979, baseEnd_6734979] using wordTrace_append hprefix tailTrace_6734979
  have hstable : (prefixWord ++ tailWord_6734979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734979).length < 2 ^ (prefixWord ++ tailWord_6734979).sum := by decide
  have hdescent : baseEnd_6734979 < baseStart_6734979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734986 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_6734986 : Nat := 118140960795 + 6734986 * 2 ^ 59
def prefixEnd_6734986 : Nat := 4983230072969 + 3 ^ 40 * 6734986 * 2
def baseEnd_6734986 : Nat := 3458285019302091570001369

theorem tailTrace_6734986 : CollatzResearch.WordTrace tailWord_6734986 prefixEnd_6734986 3458285019302091570001369 := by
  unfold tailWord_6734986
  simp only [CollatzResearch.WordTrace]
  refine ⟨61411279994575860219576203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163763413318868960585536541 61411279994575860219576203)
  ·
    refine ⟨92116919991863790329364305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61411279994575860219576203 92116919991863790329364305)
    ·
      refine ⟨69087689993897842747023229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92116919991863790329364305 69087689993897842747023229)
      ·
        refine ⟨25907883747711691030133711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69087689993897842747023229 25907883747711691030133711)
        ·
          refine ⟨38861825621567536545200567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25907883747711691030133711 38861825621567536545200567)
          ·
            refine ⟨58292738432351304817800851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38861825621567536545200567 58292738432351304817800851)
            ·
              refine ⟨87439107648526957226701277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58292738432351304817800851 87439107648526957226701277)
              ·
                refine ⟨32789665368197608960012979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87439107648526957226701277 32789665368197608960012979)
                ·
                  refine ⟨49184498052296413440019469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32789665368197608960012979 49184498052296413440019469)
                  ·
                    refine ⟨18444186769611155040007301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49184498052296413440019469 18444186769611155040007301)
                    ·
                      refine ⟨3458285019302091570001369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18444186769611155040007301 3458285019302091570001369)
                      ·
                        rfl

theorem cell23_6734986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_6734986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6734986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6734986 prefixEnd_6734986 := by exact prefixLift 6734986
  have htrace : WordTrace (prefixWord ++ tailWord_6734986) baseStart_6734986 baseEnd_6734986 := by
    simpa [prefixWord, tailWord_6734986, baseEnd_6734986] using wordTrace_append hprefix tailTrace_6734986
  have hstable : (prefixWord ++ tailWord_6734986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734986).length < 2 ^ (prefixWord ++ tailWord_6734986).sum := by decide
  have hdescent : baseEnd_6734986 < baseStart_6734986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735013 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_6735013 : Nat := 118140960795 + 6735013 * 2 ^ 59
def prefixEnd_6735013 : Nat := 4983230072969 + 3 ^ 40 * 6735013 * 2
def baseEnd_6735013 : Nat := 1152766294426587654787915

theorem tailTrace_6735013 : CollatzResearch.WordTrace tailWord_6735013 prefixEnd_6735013 1152766294426587654787915 := by
  unfold tailWord_6735013
  simp only [CollatzResearch.WordTrace]
  refine ⟨245646104749205624489537693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163764069832803749659691795 245646104749205624489537693)
  ·
    refine ⟨92117289280952109183576635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245646104749205624489537693 92117289280952109183576635)
    ·
      refine ⟨138175933921428163775364953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92117289280952109183576635 138175933921428163775364953)
      ·
        refine ⟨103631950441071122831523715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138175933921428163775364953 103631950441071122831523715)
        ·
          refine ⟨155447925661606684247285573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103631950441071122831523715 155447925661606684247285573)
          ·
            refine ⟨29146486061551253296366045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155447925661606684247285573 29146486061551253296366045)
            ·
              refine ⟨10929932273081719986137267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29146486061551253296366045 10929932273081719986137267)
              ·
                refine ⟨16394898409622579979205901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929932273081719986137267 16394898409622579979205901)
                ·
                  refine ⟨6148086903608467492202213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16394898409622579979205901 6148086903608467492202213)
                  ·
                    refine ⟨1152766294426587654787915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6148086903608467492202213 1152766294426587654787915)
                    ·
                      rfl

theorem cell23_6735013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_6735013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735013 prefixEnd_6735013 := by exact prefixLift 6735013
  have htrace : WordTrace (prefixWord ++ tailWord_6735013) baseStart_6735013 baseEnd_6735013 := by
    simpa [prefixWord, tailWord_6735013, baseEnd_6735013] using wordTrace_append hprefix tailTrace_6735013
  have hstable : (prefixWord ++ tailWord_6735013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735013).length < 2 ^ (prefixWord ++ tailWord_6735013).sum := by decide
  have hdescent : baseEnd_6735013 < baseStart_6735013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
