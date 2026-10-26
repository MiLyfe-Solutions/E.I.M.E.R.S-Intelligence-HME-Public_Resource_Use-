import V185TrunkScan20Chunk005

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_36128 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 3]
def baseStart_36128 : Nat := 118140960795 + 36128 * 2 ^ 59
def prefixEnd_36128 : Nat := 4983230072969 + 3 ^ 40 * 36128 * 2
def baseEnd_36128 : Nat := 16489803631768784652317

theorem tailTrace_36128 : CollatzResearch.WordTrace tailWord_36128 prefixEnd_36128 16489803631768784652317 := by
  unfold tailWord_36128
  simp only [CollatzResearch.WordTrace]
  refine ⟨658848206560950508138519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 878464275414600677518025 658848206560950508138519)
  ·
    refine ⟨988272309841425762207779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 658848206560950508138519 988272309841425762207779)
    ·
      refine ⟨1482408464762138643311669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988272309841425762207779 1482408464762138643311669)
      ·
        refine ⟨138975793571450497810469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1482408464762138643311669 138975793571450497810469)
        ·
          refine ⟨26057961294646968339463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138975793571450497810469 26057961294646968339463)
          ·
            refine ⟨39086941941970452509195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26057961294646968339463 39086941941970452509195)
            ·
              refine ⟨58630412912955678763793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39086941941970452509195 58630412912955678763793)
              ·
                refine ⟨43972809684716759072845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58630412912955678763793 43972809684716759072845)
                ·
                  refine ⟨16489803631768784652317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43972809684716759072845 16489803631768784652317)
                  ·
                    rfl

theorem cell20_36128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_36128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36128 prefixEnd_36128 := by exact prefixLift 36128
  have htrace : WordTrace (prefixWord ++ tailWord_36128) baseStart_36128 baseEnd_36128 := by
    simpa [prefixWord, tailWord_36128, baseEnd_36128] using wordTrace_append hprefix tailTrace_36128
  have hstable : (prefixWord ++ tailWord_36128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36128).length < 2 ^ (prefixWord ++ tailWord_36128).sum := by decide
  have hdescent : baseEnd_36128 < baseStart_36128 := by decide
  rcases family_descends (prefixWord ++ tailWord_36128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36149 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 3]
def baseStart_36149 : Nat := 118140960795 + 36149 * 2 ^ 59
def prefixEnd_36149 : Nat := 4983230072969 + 3 ^ 40 * 36149 * 2
def baseEnd_36149 : Nat := 16499388603986044952231

theorem tailTrace_36149 : CollatzResearch.WordTrace tailWord_36149 prefixEnd_36149 16499388603986044952231 := by
  unfold tailWord_36149
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318462346045821602791501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 878974897363881068527667 1318462346045821602791501)
  ·
    refine ⟨494423379767183101046813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1318462346045821602791501 494423379767183101046813)
    ·
      refine ⟨185408767412693662892555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 494423379767183101046813 185408767412693662892555)
      ·
        refine ⟨278113151119040494338833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185408767412693662892555 278113151119040494338833)
        ·
          refine ⟨208584863339280370754125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278113151119040494338833 208584863339280370754125)
          ·
            refine ⟨78219323752230139032797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208584863339280370754125 78219323752230139032797)
            ·
              refine ⟨29332246407086302137299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78219323752230139032797 29332246407086302137299)
              ·
                refine ⟨43998369610629453205949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29332246407086302137299 43998369610629453205949)
                ·
                  refine ⟨16499388603986044952231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43998369610629453205949 16499388603986044952231)
                  ·
                    rfl

theorem cell20_36149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_36149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36149 prefixEnd_36149 := by exact prefixLift 36149
  have htrace : WordTrace (prefixWord ++ tailWord_36149) baseStart_36149 baseEnd_36149 := by
    simpa [prefixWord, tailWord_36149, baseEnd_36149] using wordTrace_append hprefix tailTrace_36149
  have hstable : (prefixWord ++ tailWord_36149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36149).length < 2 ^ (prefixWord ++ tailWord_36149).sum := by decide
  have hdescent : baseEnd_36149 < baseStart_36149 := by decide
  rcases family_descends (prefixWord ++ tailWord_36149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36160 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_36160 : Nat := 118140960795 + 36160 * 2 ^ 59
def prefixEnd_36160 : Nat := 4983230072969 + 3 ^ 40 * 36160 * 2
def baseEnd_36160 : Nat := 16504409303718895585519

theorem tailTrace_36160 : CollatzResearch.WordTrace tailWord_36160 prefixEnd_36160 16504409303718895585519 := by
  unfold tailWord_36160
  simp only [CollatzResearch.WordTrace]
  refine ⟨659431774502985240720967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 879242366003980320961289 659431774502985240720967)
  ·
    refine ⟨989147661754477861081451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659431774502985240720967 989147661754477861081451)
    ·
      refine ⟨1483721492631716791622177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989147661754477861081451 1483721492631716791622177)
      ·
        refine ⟨1112791119473787593716633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1483721492631716791622177 1112791119473787593716633)
        ·
          refine ⟨834593339605340695287475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1112791119473787593716633 834593339605340695287475)
          ·
            refine ⟨1251890009408011042931213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834593339605340695287475 1251890009408011042931213)
            ·
              refine ⟨469458753528004141099205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251890009408011042931213 469458753528004141099205)
              ·
                refine ⟨88023516286500776456101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469458753528004141099205 88023516286500776456101)
                ·
                  refine ⟨16504409303718895585519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88023516286500776456101 16504409303718895585519)
                  ·
                    rfl

theorem cell20_36160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_36160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36160 prefixEnd_36160 := by exact prefixLift 36160
  have htrace : WordTrace (prefixWord ++ tailWord_36160) baseStart_36160 baseEnd_36160 := by
    simpa [prefixWord, tailWord_36160, baseEnd_36160] using wordTrace_append hprefix tailTrace_36160
  have hstable : (prefixWord ++ tailWord_36160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36160).length < 2 ^ (prefixWord ++ tailWord_36160).sum := by decide
  have hdescent : baseEnd_36160 < baseStart_36160 := by decide
  rcases family_descends (prefixWord ++ tailWord_36160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36191 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 3]
def baseStart_36191 : Nat := 118140960795 + 36191 * 2 ^ 59
def prefixEnd_36191 : Nat := 4983230072969 + 3 ^ 40 * 36191 * 2
def baseEnd_36191 : Nat := 16518558548420565552059

theorem tailTrace_36191 : CollatzResearch.WordTrace tailWord_36191 prefixEnd_36191 16518558548420565552059 := by
  unfold tailWord_36191
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319994211893662775820427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 879996141262441850546951 1319994211893662775820427)
  ·
    refine ⟨1979991317840494163730641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1319994211893662775820427 1979991317840494163730641)
    ·
      refine ⟨1484993488380370622797981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1979991317840494163730641 1484993488380370622797981)
      ·
        refine ⟨556872558142638983549243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1484993488380370622797981 556872558142638983549243)
        ·
          refine ⟨835308837213958475323865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556872558142638983549243 835308837213958475323865)
          ·
            refine ⟨626481627910468856492899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835308837213958475323865 626481627910468856492899)
            ·
              refine ⟨939722441865703284739349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626481627910468856492899 939722441865703284739349)
              ·
                refine ⟨44049489462454841472157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 939722441865703284739349 44049489462454841472157)
                ·
                  refine ⟨16518558548420565552059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44049489462454841472157 16518558548420565552059)
                  ·
                    rfl

theorem cell20_36191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_36191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36191 prefixEnd_36191 := by exact prefixLift 36191
  have htrace : WordTrace (prefixWord ++ tailWord_36191) baseStart_36191 baseEnd_36191 := by
    simpa [prefixWord, tailWord_36191, baseEnd_36191] using wordTrace_append hprefix tailTrace_36191
  have hstable : (prefixWord ++ tailWord_36191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36191).length < 2 ^ (prefixWord ++ tailWord_36191).sum := by decide
  have hdescent : baseEnd_36191 < baseStart_36191 := by decide
  rcases family_descends (prefixWord ++ tailWord_36191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36242 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_36242 : Nat := 118140960795 + 36242 * 2 ^ 59
def prefixEnd_36242 : Nat := 4983230072969 + 3 ^ 40 * 36242 * 2
def baseEnd_36242 : Nat := 16541836338091054851851

theorem tailTrace_36242 : CollatzResearch.WordTrace tailWord_36242 prefixEnd_36242 16541836338091054851851 := by
  unfold tailWord_36242
  simp only [CollatzResearch.WordTrace]
  refine ⟨330463583677224621481745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 881236223139265657284653 330463583677224621481745)
  ·
    refine ⟨247847687757918466111309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 330463583677224621481745 247847687757918466111309)
    ·
      refine ⟨92942882909219424791741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247847687757918466111309 92942882909219424791741)
      ·
        refine ⟨34853581090957284296903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92942882909219424791741 34853581090957284296903)
        ·
          refine ⟨52280371636435926445355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34853581090957284296903 52280371636435926445355)
          ·
            refine ⟨78420557454653889668033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52280371636435926445355 78420557454653889668033)
            ·
              refine ⟨58815418090990417251025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78420557454653889668033 58815418090990417251025)
              ·
                refine ⟨44111563568242812938269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58815418090990417251025 44111563568242812938269)
                ·
                  refine ⟨16541836338091054851851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44111563568242812938269 16541836338091054851851)
                  ·
                    rfl

theorem cell20_36242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_36242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36242 prefixEnd_36242 := by exact prefixLift 36242
  have htrace : WordTrace (prefixWord ++ tailWord_36242) baseStart_36242 baseEnd_36242 := by
    simpa [prefixWord, tailWord_36242, baseEnd_36242] using wordTrace_append hprefix tailTrace_36242
  have hstable : (prefixWord ++ tailWord_36242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36242).length < 2 ^ (prefixWord ++ tailWord_36242).sum := by decide
  have hdescent : baseEnd_36242 < baseStart_36242 := by decide
  rcases family_descends (prefixWord ++ tailWord_36242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36249 : List Nat := [1, 2, 1, 2, 1, 7, 2, 2, 2]
def baseStart_36249 : Nat := 118140960795 + 36249 * 2 ^ 59
def prefixEnd_36249 : Nat := 4983230072969 + 3 ^ 40 * 36249 * 2
def baseEnd_36249 : Nat := 16545031328830141618489

theorem tailTrace_36249 : CollatzResearch.WordTrace tailWord_36249 prefixEnd_36249 16545031328830141618489 := by
  unfold tailWord_36249
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322109645683538681431801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 881406430455692454287867 1322109645683538681431801)
  ·
    refine ⟨991582234262654011073851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1322109645683538681431801 991582234262654011073851)
    ·
      refine ⟨1487373351393981016610777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 991582234262654011073851 1487373351393981016610777)
      ·
        refine ⟨1115530013545485762458083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1487373351393981016610777 1115530013545485762458083)
        ·
          refine ⟨1673295020318228643687125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115530013545485762458083 1673295020318228643687125)
          ·
            refine ⟨39217852038708483836417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1673295020318228643687125 39217852038708483836417)
            ·
              refine ⟨29413389029031362877313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39217852038708483836417 29413389029031362877313)
              ·
                refine ⟨22060041771773522157985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29413389029031362877313 22060041771773522157985)
                ·
                  refine ⟨16545031328830141618489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22060041771773522157985 16545031328830141618489)
                  ·
                    rfl

theorem cell20_36249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 2].length) (baseStart_36249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36249 prefixEnd_36249 := by exact prefixLift 36249
  have htrace : WordTrace (prefixWord ++ tailWord_36249) baseStart_36249 baseEnd_36249 := by
    simpa [prefixWord, tailWord_36249, baseEnd_36249] using wordTrace_append hprefix tailTrace_36249
  have hstable : (prefixWord ++ tailWord_36249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36249).length < 2 ^ (prefixWord ++ tailWord_36249).sum := by decide
  have hdescent : baseEnd_36249 < baseStart_36249 := by decide
  rcases family_descends (prefixWord ++ tailWord_36249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36277 : List Nat := [1, 3, 3, 2, 2, 2, 3, 4]
def baseStart_36277 : Nat := 118140960795 + 36277 * 2 ^ 59
def prefixEnd_36277 : Nat := 4983230072969 + 3 ^ 40 * 36277 * 2
def baseEnd_36277 : Nat := 5519270430595496228347

theorem tailTrace_36277 : CollatzResearch.WordTrace tailWord_36277 prefixEnd_36277 5519270430595496228347 := by
  unfold tailWord_36277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323130889582099463451085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 882087259721399642300723 1323130889582099463451085)
  ·
    refine ⟨496174083593287298794157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1323130889582099463451085 496174083593287298794157)
    ·
      refine ⟨186065281347482737047809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 496174083593287298794157 186065281347482737047809)
      ·
        refine ⟨139548961010612052785857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186065281347482737047809 139548961010612052785857)
        ·
          refine ⟨104661720757959039589393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139548961010612052785857 104661720757959039589393)
          ·
            refine ⟨78496290568469279692045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104661720757959039589393 78496290568469279692045)
            ·
              refine ⟨29436108963175979884517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78496290568469279692045 29436108963175979884517)
              ·
                refine ⟨5519270430595496228347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29436108963175979884517 5519270430595496228347)
                ·
                  rfl

theorem cell20_36277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_36277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36277 prefixEnd_36277 := by exact prefixLift 36277
  have htrace : WordTrace (prefixWord ++ tailWord_36277) baseStart_36277 baseEnd_36277 := by
    simpa [prefixWord, tailWord_36277, baseEnd_36277] using wordTrace_append hprefix tailTrace_36277
  have hstable : (prefixWord ++ tailWord_36277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36277).length < 2 ^ (prefixWord ++ tailWord_36277).sum := by decide
  have hdescent : baseEnd_36277 < baseStart_36277 := by decide
  rcases family_descends (prefixWord ++ tailWord_36277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36291 : List Nat := [1, 1, 1, 3, 1, 1, 5, 5, 2]
def baseStart_36291 : Nat := 118140960795 + 36291 * 2 ^ 59
def prefixEnd_36291 : Nat := 4983230072969 + 3 ^ 40 * 36291 * 2
def baseEnd_36291 : Nat := 16564201273264662218317

theorem tailTrace_36291 : CollatzResearch.WordTrace tailWord_36291 prefixEnd_36291 16564201273264662218317 := by
  unfold tailWord_36291
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323641511531379854460727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 882427674354253236307151 1323641511531379854460727)
  ·
    refine ⟨1985462267297069781691091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323641511531379854460727 1985462267297069781691091)
    ·
      refine ⟨2978193400945604672536637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1985462267297069781691091 2978193400945604672536637)
      ·
        refine ⟨1116822525354601752201239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2978193400945604672536637 1116822525354601752201239)
        ·
          refine ⟨1675233788031902628301859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116822525354601752201239 1675233788031902628301859)
          ·
            refine ⟨2512850682047853942452789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675233788031902628301859 2512850682047853942452789)
            ·
              refine ⟨235579751441986307104949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2512850682047853942452789 235579751441986307104949)
              ·
                refine ⟨22085601697686216291089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235579751441986307104949 22085601697686216291089)
                ·
                  refine ⟨16564201273264662218317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22085601697686216291089 16564201273264662218317)
                  ·
                    rfl

theorem cell20_36291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 2].length) (baseStart_36291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36291 prefixEnd_36291 := by exact prefixLift 36291
  have htrace : WordTrace (prefixWord ++ tailWord_36291) baseStart_36291 baseEnd_36291 := by
    simpa [prefixWord, tailWord_36291, baseEnd_36291] using wordTrace_append hprefix tailTrace_36291
  have hstable : (prefixWord ++ tailWord_36291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36291).length < 2 ^ (prefixWord ++ tailWord_36291).sum := by decide
  have hdescent : baseEnd_36291 < baseStart_36291 := by decide
  rcases family_descends (prefixWord ++ tailWord_36291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36308 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_36308 : Nat := 118140960795 + 36308 * 2 ^ 59
def prefixEnd_36308 : Nat := 4983230072969 + 3 ^ 40 * 36308 * 2
def baseEnd_36308 : Nat := 16571960536488158651581

theorem tailTrace_36308 : CollatzResearch.WordTrace tailWord_36308 prefixEnd_36308 16571960536488158651581 := by
  unfold tailWord_36308
  simp only [CollatzResearch.WordTrace]
  refine ⟨662130776234895878914789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 882841034979861171886385 662130776234895878914789)
  ·
    refine ⟨124149520544042977296523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 662130776234895878914789 124149520544042977296523)
    ·
      refine ⟨186224280816064465944785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124149520544042977296523 186224280816064465944785)
      ·
        refine ⟨139668210612048349458589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186224280816064465944785 139668210612048349458589)
        ·
          refine ⟨52375578979518131046971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139668210612048349458589 52375578979518131046971)
          ·
            refine ⟨78563368469277196570457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52375578979518131046971 78563368469277196570457)
            ·
              refine ⟨58922526351957897427843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78563368469277196570457 58922526351957897427843)
              ·
                refine ⟨88383789527936846141765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58922526351957897427843 88383789527936846141765)
                ·
                  refine ⟨16571960536488158651581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88383789527936846141765 16571960536488158651581)
                  ·
                    rfl

theorem cell20_36308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_36308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36308 prefixEnd_36308 := by exact prefixLift 36308
  have htrace : WordTrace (prefixWord ++ tailWord_36308) baseStart_36308 baseEnd_36308 := by
    simpa [prefixWord, tailWord_36308, baseEnd_36308] using wordTrace_append hprefix tailTrace_36308
  have hstable : (prefixWord ++ tailWord_36308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36308).length < 2 ^ (prefixWord ++ tailWord_36308).sum := by decide
  have hdescent : baseEnd_36308 < baseStart_36308 := by decide
  rcases family_descends (prefixWord ++ tailWord_36308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36312 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_36312 : Nat := 118140960795 + 36312 * 2 ^ 59
def prefixEnd_36312 : Nat := 4983230072969 + 3 ^ 40 * 36312 * 2
def baseEnd_36312 : Nat := 16573786245481922518231

theorem tailTrace_36312 : CollatzResearch.WordTrace tailWord_36312 prefixEnd_36312 16573786245481922518231 := by
  unfold tailWord_36312
  simp only [CollatzResearch.WordTrace]
  refine ⟨662203722227650220487595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 882938296303533627316793 662203722227650220487595)
  ·
    refine ⟨993305583341475330731393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662203722227650220487595 993305583341475330731393)
    ·
      refine ⟨744979187506106498048545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 993305583341475330731393 744979187506106498048545)
      ·
        refine ⟨558734390629579873536409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 744979187506106498048545 558734390629579873536409)
        ·
          refine ⟨419050792972184905152307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558734390629579873536409 419050792972184905152307)
          ·
            refine ⟨628576189458277357728461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419050792972184905152307 628576189458277357728461)
            ·
              refine ⟨235716071046854009148173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 628576189458277357728461 235716071046854009148173)
              ·
                refine ⟨88393526642570253430565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235716071046854009148173 88393526642570253430565)
                ·
                  refine ⟨16573786245481922518231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88393526642570253430565 16573786245481922518231)
                  ·
                    rfl

theorem cell20_36312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_36312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36312 prefixEnd_36312 := by exact prefixLift 36312
  have htrace : WordTrace (prefixWord ++ tailWord_36312) baseStart_36312 baseEnd_36312 := by
    simpa [prefixWord, tailWord_36312, baseEnd_36312] using wordTrace_append hprefix tailTrace_36312
  have hstable : (prefixWord ++ tailWord_36312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36312).length < 2 ^ (prefixWord ++ tailWord_36312).sum := by decide
  have hdescent : baseEnd_36312 < baseStart_36312 := by decide
  rcases family_descends (prefixWord ++ tailWord_36312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36319 : List Nat := [1, 1, 2, 3, 3, 1, 2, 7]
def baseStart_36319 : Nat := 118140960795 + 36319 * 2 ^ 59
def prefixEnd_36319 : Nat := 4983230072969 + 3 ^ 40 * 36319 * 2
def baseEnd_36319 : Nat := 5525660412073669761623

theorem tailTrace_36319 : CollatzResearch.WordTrace tailWord_36319 prefixEnd_36319 5525660412073669761623 := by
  unfold tailWord_36319
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324662755429940636480011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 883108503619960424320007 1324662755429940636480011)
  ·
    refine ⟨1986994133144910954720017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1324662755429940636480011 1986994133144910954720017)
    ·
      refine ⟨1490245599858683216040013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1986994133144910954720017 1490245599858683216040013)
      ·
        refine ⟨558842099947006206015005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1490245599858683216040013 558842099947006206015005)
        ·
          refine ⟨209565787480127327255627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 558842099947006206015005 209565787480127327255627)
          ·
            refine ⟨314348681220190990883441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209565787480127327255627 314348681220190990883441)
            ·
              refine ⟨235761510915143243162581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314348681220190990883441 235761510915143243162581)
              ·
                refine ⟨5525660412073669761623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 235761510915143243162581 5525660412073669761623)
                ·
                  rfl

theorem cell20_36319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_36319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36319 prefixEnd_36319 := by exact prefixLift 36319
  have htrace : WordTrace (prefixWord ++ tailWord_36319) baseStart_36319 baseEnd_36319 := by
    simpa [prefixWord, tailWord_36319, baseEnd_36319] using wordTrace_append hprefix tailTrace_36319
  have hstable : (prefixWord ++ tailWord_36319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36319).length < 2 ^ (prefixWord ++ tailWord_36319).sum := by decide
  have hdescent : baseEnd_36319 < baseStart_36319 := by decide
  rcases family_descends (prefixWord ++ tailWord_36319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36336 : List Nat := [2, 1, 1, 1, 3, 4, 4, 4]
def baseStart_36336 : Nat := 118140960795 + 36336 * 2 ^ 59
def prefixEnd_36336 : Nat := 4983230072969 + 3 ^ 40 * 36336 * 2
def baseEnd_36336 : Nat := 5528246833148168572711

theorem tailTrace_36336 : CollatzResearch.WordTrace tailWord_36336 prefixEnd_36336 5528246833148168572711 := by
  unfold tailWord_36336
  simp only [CollatzResearch.WordTrace]
  refine ⟨662641398184176269924431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 883521864245568359899241 662641398184176269924431)
  ·
    refine ⟨993962097276264404886647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662641398184176269924431 993962097276264404886647)
    ·
      refine ⟨1490943145914396607329971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993962097276264404886647 1490943145914396607329971)
      ·
        refine ⟨2236414718871594910994957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490943145914396607329971 2236414718871594910994957)
        ·
          refine ⟨838655519576848091623109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2236414718871594910994957 838655519576848091623109)
          ·
            refine ⟨157247909920659017179333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 838655519576848091623109 157247909920659017179333)
            ·
              refine ⟨29483983110123565721125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157247909920659017179333 29483983110123565721125)
              ·
                refine ⟨5528246833148168572711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29483983110123565721125 5528246833148168572711)
                ·
                  rfl

theorem cell20_36336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_36336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36336 prefixEnd_36336 := by exact prefixLift 36336
  have htrace : WordTrace (prefixWord ++ tailWord_36336) baseStart_36336 baseEnd_36336 := by
    simpa [prefixWord, tailWord_36336, baseEnd_36336] using wordTrace_append hprefix tailTrace_36336
  have hstable : (prefixWord ++ tailWord_36336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36336).length < 2 ^ (prefixWord ++ tailWord_36336).sum := by decide
  have hdescent : baseEnd_36336 < baseStart_36336 := by decide
  rcases family_descends (prefixWord ++ tailWord_36336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36353 : List Nat := [1, 2, 4, 1, 5, 1, 6]
def baseStart_36353 : Nat := 118140960795 + 36353 * 2 ^ 59
def prefixEnd_36353 : Nat := 4983230072969 + 3 ^ 40 * 36353 * 2
def baseEnd_36353 : Nat := 1843611084740889127933

theorem tailTrace_36353 : CollatzResearch.WordTrace tailWord_36353 prefixEnd_36353 1843611084740889127933 := by
  unfold tailWord_36353
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325902837306764443217713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 883935224871176295478475 1325902837306764443217713)
  ·
    refine ⟨994427127980073332413285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1325902837306764443217713 994427127980073332413285)
    ·
      refine ⟨186455086496263749827491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 994427127980073332413285 186455086496263749827491)
      ·
        refine ⟨279682629744395624741237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186455086496263749827491 279682629744395624741237)
        ·
          refine ⟨26220246538537089819491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 279682629744395624741237 26220246538537089819491)
          ·
            refine ⟨39330369807805634729237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26220246538537089819491 39330369807805634729237)
            ·
              refine ⟨1843611084740889127933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39330369807805634729237 1843611084740889127933)
              ·
                rfl

theorem cell20_36353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 6].length) (baseStart_36353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36353 prefixEnd_36353 := by exact prefixLift 36353
  have htrace : WordTrace (prefixWord ++ tailWord_36353) baseStart_36353 baseEnd_36353 := by
    simpa [prefixWord, tailWord_36353, baseEnd_36353] using wordTrace_append hprefix tailTrace_36353
  have hstable : (prefixWord ++ tailWord_36353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36353).length < 2 ^ (prefixWord ++ tailWord_36353).sum := by decide
  have hdescent : baseEnd_36353 < baseStart_36353 := by decide
  rcases family_descends (prefixWord ++ tailWord_36353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36363 : List Nat := [1, 1, 1, 1, 8, 1, 3, 2, 2]
def baseStart_36363 : Nat := 118140960795 + 36363 * 2 ^ 59
def prefixEnd_36363 : Nat := 4983230072969 + 3 ^ 40 * 36363 * 2
def baseEnd_36363 : Nat := 16597064035152411818023

theorem tailTrace_36363 : CollatzResearch.WordTrace tailWord_36363 prefixEnd_36363 16597064035152411818023 := by
  unfold tailWord_36363
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326267567270536151081743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 884178378180357434054495 1326267567270536151081743)
  ·
    refine ⟨1989401350905804226622615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1326267567270536151081743 1989401350905804226622615)
    ·
      refine ⟨2984102026358706339933923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1989401350905804226622615 2984102026358706339933923)
      ·
        refine ⟨4476153039538059509900885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2984102026358706339933923 4476153039538059509900885)
        ·
          refine ⟨52454918432086634881651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 4476153039538059509900885 52454918432086634881651)
          ·
            refine ⟨78682377648129952322477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52454918432086634881651 78682377648129952322477)
            ·
              refine ⟨29505891618048732120929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78682377648129952322477 29505891618048732120929)
              ·
                refine ⟨22129418713536549090697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29505891618048732120929 22129418713536549090697)
                ·
                  refine ⟨16597064035152411818023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22129418713536549090697 16597064035152411818023)
                  ·
                    rfl

theorem cell20_36363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 2].length) (baseStart_36363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36363 prefixEnd_36363 := by exact prefixLift 36363
  have htrace : WordTrace (prefixWord ++ tailWord_36363) baseStart_36363 baseEnd_36363 := by
    simpa [prefixWord, tailWord_36363, baseEnd_36363] using wordTrace_append hprefix tailTrace_36363
  have hstable : (prefixWord ++ tailWord_36363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36363).length < 2 ^ (prefixWord ++ tailWord_36363).sum := by decide
  have hdescent : baseEnd_36363 < baseStart_36363 := by decide
  rcases family_descends (prefixWord ++ tailWord_36363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36412 : List Nat := [2, 2, 2, 2, 5, 7]
def baseStart_36412 : Nat := 118140960795 + 36412 * 2 ^ 59
def prefixEnd_36412 : Nat := 4983230072969 + 3 ^ 40 * 36412 * 2
def baseEnd_36412 : Nat := 615534406308371080907

theorem tailTrace_36412 : CollatzResearch.WordTrace tailWord_36412 prefixEnd_36412 615534406308371080907 := by
  unfold tailWord_36412
  simp only [CollatzResearch.WordTrace]
  refine ⟨664027372046508759807745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 885369829395345013076993 664027372046508759807745)
  ·
    refine ⟨498020529034881569855809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 664027372046508759807745 498020529034881569855809)
    ·
      refine ⟨373515396776161177391857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498020529034881569855809 373515396776161177391857)
      ·
        refine ⟨280136547582120883043893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373515396776161177391857 280136547582120883043893)
        ·
          refine ⟨26262801335823832785365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 280136547582120883043893 26262801335823832785365)
          ·
            refine ⟨615534406308371080907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26262801335823832785365 615534406308371080907)
            ·
              rfl

theorem cell20_36412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 7].length) (baseStart_36412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36412 prefixEnd_36412 := by exact prefixLift 36412
  have htrace : WordTrace (prefixWord ++ tailWord_36412) baseStart_36412 baseEnd_36412 := by
    simpa [prefixWord, tailWord_36412, baseEnd_36412] using wordTrace_append hprefix tailTrace_36412
  have hstable : (prefixWord ++ tailWord_36412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36412).length < 2 ^ (prefixWord ++ tailWord_36412).sum := by decide
  have hdescent : baseEnd_36412 < baseStart_36412 := by decide
  rcases family_descends (prefixWord ++ tailWord_36412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36426 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_36426 : Nat := 118140960795 + 36426 * 2 ^ 59
def prefixEnd_36426 : Nat := 4983230072969 + 3 ^ 40 * 36426 * 2
def baseEnd_36426 : Nat := 16625818951804192717765

theorem tailTrace_36426 : CollatzResearch.WordTrace tailWord_36426 prefixEnd_36426 16625818951804192717765 := by
  unfold tailWord_36426
  simp only [CollatzResearch.WordTrace]
  refine ⟨332141341510574477656283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 885710244028198607083421 332141341510574477656283)
  ·
    refine ⟨498212012265861716484425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 332141341510574477656283 498212012265861716484425)
    ·
      refine ⟨373659009199396287363319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498212012265861716484425 373659009199396287363319)
      ·
        refine ⟨560488513799094431044979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373659009199396287363319 560488513799094431044979)
        ·
          refine ⟨840732770698641646567469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560488513799094431044979 840732770698641646567469)
          ·
            refine ⟨315274789011990617462801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 840732770698641646567469 315274789011990617462801)
            ·
              refine ⟨236456091758992963097101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315274789011990617462801 236456091758992963097101)
              ·
                refine ⟨88671034409622361161413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 236456091758992963097101 88671034409622361161413)
                ·
                  refine ⟨16625818951804192717765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88671034409622361161413 16625818951804192717765)
                  ·
                    rfl

theorem cell20_36426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_36426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36426 prefixEnd_36426 := by exact prefixLift 36426
  have htrace : WordTrace (prefixWord ++ tailWord_36426) baseStart_36426 baseEnd_36426 := by
    simpa [prefixWord, tailWord_36426, baseEnd_36426] using wordTrace_append hprefix tailTrace_36426
  have hstable : (prefixWord ++ tailWord_36426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36426).length < 2 ^ (prefixWord ++ tailWord_36426).sum := by decide
  have hdescent : baseEnd_36426 < baseStart_36426 := by decide
  rcases family_descends (prefixWord ++ tailWord_36426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36440 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_36440 : Nat := 118140960795 + 36440 * 2 ^ 59
def prefixEnd_36440 : Nat := 4983230072969 + 3 ^ 40 * 36440 * 2
def baseEnd_36440 : Nat := 16632208933282366251041

theorem tailTrace_36440 : CollatzResearch.WordTrace tailWord_36440 prefixEnd_36440 16632208933282366251041 := by
  unfold tailWord_36440
  simp only [CollatzResearch.WordTrace]
  refine ⟨664537993995789150817387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 886050658661052201089849 664537993995789150817387)
  ·
    refine ⟨996806990993683726226081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664537993995789150817387 996806990993683726226081)
    ·
      refine ⟨747605243245262794669561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 996806990993683726226081 747605243245262794669561)
      ·
        refine ⟨560703932433947096002171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 747605243245262794669561 560703932433947096002171)
        ·
          refine ⟨841055898650920644003257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560703932433947096002171 841055898650920644003257)
          ·
            refine ⟨630791923988190483002443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 841055898650920644003257 630791923988190483002443)
            ·
              refine ⟨946187885982285724503665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630791923988190483002443 946187885982285724503665)
              ·
                refine ⟨709640914486714293377749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946187885982285724503665 709640914486714293377749)
                ·
                  refine ⟨16632208933282366251041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 709640914486714293377749 16632208933282366251041)
                  ·
                    rfl

theorem cell20_36440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_36440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36440 prefixEnd_36440 := by exact prefixLift 36440
  have htrace : WordTrace (prefixWord ++ tailWord_36440) baseStart_36440 baseEnd_36440 := by
    simpa [prefixWord, tailWord_36440, baseEnd_36440] using wordTrace_append hprefix tailTrace_36440
  have hstable : (prefixWord ++ tailWord_36440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36440).length < 2 ^ (prefixWord ++ tailWord_36440).sum := by decide
  have hdescent : baseEnd_36440 < baseStart_36440 := by decide
  rcases family_descends (prefixWord ++ tailWord_36440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36481 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_36481 : Nat := 118140960795 + 36481 * 2 ^ 59
def prefixEnd_36481 : Nat := 4983230072969 + 3 ^ 40 * 36481 * 2
def baseEnd_36481 : Nat := 16650922450468445884207

theorem tailTrace_36481 : CollatzResearch.WordTrace tailWord_36481 prefixEnd_36481 16650922450468445884207 := by
  unfold tailWord_36481
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330571380843042303877297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 887047587228694869251531 1330571380843042303877297)
  ·
    refine ⟨997928535632281727907973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1330571380843042303877297 997928535632281727907973)
    ·
      refine ⟨187111600431052823982745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 997928535632281727907973 187111600431052823982745)
      ·
        refine ⟨140333700323289617987059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187111600431052823982745 140333700323289617987059)
        ·
          refine ⟨210500550484934426980589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140333700323289617987059 210500550484934426980589)
          ·
            refine ⟨78937706431850410117721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210500550484934426980589 78937706431850410117721)
            ·
              refine ⟨59203279823887807588291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78937706431850410117721 59203279823887807588291)
              ·
                refine ⟨88804919735831711382437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59203279823887807588291 88804919735831711382437)
                ·
                  refine ⟨16650922450468445884207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88804919735831711382437 16650922450468445884207)
                  ·
                    rfl

theorem cell20_36481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_36481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36481 prefixEnd_36481 := by exact prefixLift 36481
  have htrace : WordTrace (prefixWord ++ tailWord_36481) baseStart_36481 baseEnd_36481 := by
    simpa [prefixWord, tailWord_36481, baseEnd_36481] using wordTrace_append hprefix tailTrace_36481
  have hstable : (prefixWord ++ tailWord_36481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36481).length < 2 ^ (prefixWord ++ tailWord_36481).sum := by decide
  have hdescent : baseEnd_36481 < baseStart_36481 := by decide
  rcases family_descends (prefixWord ++ tailWord_36481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36564 : List Nat := [2, 4, 1, 3, 1, 1, 2, 6]
def baseStart_36564 : Nat := 118140960795 + 36564 * 2 ^ 59
def prefixEnd_36564 : Nat := 4983230072969 + 3 ^ 40 * 36564 * 2
def baseEnd_36564 : Nat := 5562935304029682039067

theorem tailTrace_36564 : CollatzResearch.WordTrace tailWord_36564 prefixEnd_36564 5562935304029682039067 := by
  unfold tailWord_36564
  simp only [CollatzResearch.WordTrace]
  refine ⟨666799319771173739574373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 889065759694898319432497 666799319771173739574373)
  ·
    refine ⟨125024872457095076170195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 666799319771173739574373 125024872457095076170195)
    ·
      refine ⟨187537308685642614255293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125024872457095076170195 187537308685642614255293)
      ·
        refine ⟨70326490757115980345735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187537308685642614255293 70326490757115980345735)
        ·
          refine ⟨105489736135673970518603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70326490757115980345735 105489736135673970518603)
          ·
            refine ⟨158234604203510955777905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105489736135673970518603 158234604203510955777905)
            ·
              refine ⟨118675953152633216833429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158234604203510955777905 118675953152633216833429)
              ·
                refine ⟨5562935304029682039067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118675953152633216833429 5562935304029682039067)
                ·
                  rfl

theorem cell20_36564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_36564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36564 prefixEnd_36564 := by exact prefixLift 36564
  have htrace : WordTrace (prefixWord ++ tailWord_36564) baseStart_36564 baseEnd_36564 := by
    simpa [prefixWord, tailWord_36564, baseEnd_36564] using wordTrace_append hprefix tailTrace_36564
  have hstable : (prefixWord ++ tailWord_36564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36564).length < 2 ^ (prefixWord ++ tailWord_36564).sum := by decide
  have hdescent : baseEnd_36564 < baseStart_36564 := by decide
  rcases family_descends (prefixWord ++ tailWord_36564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36609 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 3]
def baseStart_36609 : Nat := 118140960795 + 36609 * 2 ^ 59
def prefixEnd_36609 : Nat := 4983230072969 + 3 ^ 40 * 36609 * 2
def baseEnd_36609 : Nat := 16709345138268889617017

theorem tailTrace_36609 : CollatzResearch.WordTrace tailWord_36609 prefixEnd_36609 16709345138268889617017 := by
  unfold tailWord_36609
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335239924379320164536881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 890159949586213443024587 1335239924379320164536881)
  ·
    refine ⟨1001429943284490123402661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1335239924379320164536881 1001429943284490123402661)
    ·
      refine ⟨187768114365841898137999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1001429943284490123402661 187768114365841898137999)
      ·
        refine ⟨281652171548762847206999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187768114365841898137999 281652171548762847206999)
        ·
          refine ⟨422478257323144270810499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281652171548762847206999 422478257323144270810499)
          ·
            refine ⟨633717385984716406215749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422478257323144270810499 633717385984716406215749)
            ·
              refine ⟨118822009872134326165453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 633717385984716406215749 118822009872134326165453)
              ·
                refine ⟨44558253702050372312045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118822009872134326165453 44558253702050372312045)
                ·
                  refine ⟨16709345138268889617017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44558253702050372312045 16709345138268889617017)
                  ·
                    rfl

theorem cell20_36609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_36609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36609 prefixEnd_36609 := by exact prefixLift 36609
  have htrace : WordTrace (prefixWord ++ tailWord_36609) baseStart_36609 baseEnd_36609 := by
    simpa [prefixWord, tailWord_36609, baseEnd_36609] using wordTrace_append hprefix tailTrace_36609
  have hstable : (prefixWord ++ tailWord_36609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36609).length < 2 ^ (prefixWord ++ tailWord_36609).sum := by decide
  have hdescent : baseEnd_36609 < baseStart_36609 := by decide
  rcases family_descends (prefixWord ++ tailWord_36609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36616 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_36616 : Nat := 118140960795 + 36616 * 2 ^ 59
def prefixEnd_36616 : Nat := 4983230072969 + 3 ^ 40 * 36616 * 2
def baseEnd_36616 : Nat := 16712540129007976383655

theorem tailTrace_36616 : CollatzResearch.WordTrace tailWord_36616 prefixEnd_36616 16712540129007976383655 := by
  unfold tailWord_36616
  simp only [CollatzResearch.WordTrace]
  refine ⟨667747617676980180020851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 890330156902640240027801 667747617676980180020851)
  ·
    refine ⟨1001621426515470270031277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 667747617676980180020851 1001621426515470270031277)
    ·
      refine ⟨375608034943301351261729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1001621426515470270031277 375608034943301351261729)
      ·
        refine ⟨281706026207476013446297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375608034943301351261729 281706026207476013446297)
        ·
          refine ⟨211279519655607010084723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281706026207476013446297 211279519655607010084723)
          ·
            refine ⟨316919279483410515127085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211279519655607010084723 316919279483410515127085)
            ·
              refine ⟨118844729806278943172657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316919279483410515127085 118844729806278943172657)
              ·
                refine ⟨89133547354709207379493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118844729806278943172657 89133547354709207379493)
                ·
                  refine ⟨16712540129007976383655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89133547354709207379493 16712540129007976383655)
                  ·
                    rfl

theorem cell20_36616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_36616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36616 prefixEnd_36616 := by exact prefixLift 36616
  have htrace : WordTrace (prefixWord ++ tailWord_36616) baseStart_36616 baseEnd_36616 := by
    simpa [prefixWord, tailWord_36616, baseEnd_36616] using wordTrace_append hprefix tailTrace_36616
  have hstable : (prefixWord ++ tailWord_36616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36616).length < 2 ^ (prefixWord ++ tailWord_36616).sum := by decide
  have hdescent : baseEnd_36616 < baseStart_36616 := by decide
  rcases family_descends (prefixWord ++ tailWord_36616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36664 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_36664 : Nat := 118140960795 + 36664 * 2 ^ 59
def prefixEnd_36664 : Nat := 4983230072969 + 3 ^ 40 * 36664 * 2
def baseEnd_36664 : Nat := 16734448636933142783459

theorem tailTrace_36664 : CollatzResearch.WordTrace tailWord_36664 prefixEnd_36664 16734448636933142783459 := by
  unfold tailWord_36664
  simp only [CollatzResearch.WordTrace]
  refine ⟨668622969590032278894523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 891497292786709705192697 668622969590032278894523)
  ·
    refine ⟨1002934454385048418341785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 668622969590032278894523 1002934454385048418341785)
    ·
      refine ⟨752200840788786313756339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1002934454385048418341785 752200840788786313756339)
      ·
        refine ⟨1128301261183179470634509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752200840788786313756339 1128301261183179470634509)
        ·
          refine ⟨423112972943692301487941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1128301261183179470634509 423112972943692301487941)
          ·
            refine ⟨79333682426942306528989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 423112972943692301487941 79333682426942306528989)
            ·
              refine ⟨29750130910103364948371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79333682426942306528989 29750130910103364948371)
              ·
                refine ⟨44625196365155047422557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29750130910103364948371 44625196365155047422557)
                ·
                  refine ⟨16734448636933142783459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44625196365155047422557 16734448636933142783459)
                  ·
                    rfl

theorem cell20_36664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_36664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36664 prefixEnd_36664 := by exact prefixLift 36664
  have htrace : WordTrace (prefixWord ++ tailWord_36664) baseStart_36664 baseEnd_36664 := by
    simpa [prefixWord, tailWord_36664, baseEnd_36664] using wordTrace_append hprefix tailTrace_36664
  have hstable : (prefixWord ++ tailWord_36664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36664).length < 2 ^ (prefixWord ++ tailWord_36664).sum := by decide
  have hdescent : baseEnd_36664 < baseStart_36664 := by decide
  rcases family_descends (prefixWord ++ tailWord_36664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36760 : List Nat := [2, 1, 2, 6, 1, 2, 2, 2, 2]
def baseStart_36760 : Nat := 118140960795 + 36760 * 2 ^ 59
def prefixEnd_36760 : Nat := 4983230072969 + 3 ^ 40 * 36760 * 2
def baseEnd_36760 : Nat := 16778265652783475583067

theorem tailTrace_36760 : CollatzResearch.WordTrace tailWord_36760 prefixEnd_36760 16778265652783475583067 := by
  unfold tailWord_36760
  simp only [CollatzResearch.WordTrace]
  refine ⟨670373673416136476641867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 893831564554848635522489 670373673416136476641867)
  ·
    refine ⟨1005560510124204714962801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670373673416136476641867 1005560510124204714962801)
    ·
      refine ⟨754170382593153536222101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1005560510124204714962801 754170382593153536222101)
      ·
        refine ⟨35351736684054072010411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 754170382593153536222101 35351736684054072010411)
        ·
          refine ⟨53027605026081108015617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35351736684054072010411 53027605026081108015617)
          ·
            refine ⟨39770703769560831011713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53027605026081108015617 39770703769560831011713)
            ·
              refine ⟨29828027827170623258785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39770703769560831011713 29828027827170623258785)
              ·
                refine ⟨22371020870377967444089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29828027827170623258785 22371020870377967444089)
                ·
                  refine ⟨16778265652783475583067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22371020870377967444089 16778265652783475583067)
                  ·
                    rfl

theorem cell20_36760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_36760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36760 prefixEnd_36760 := by exact prefixLift 36760
  have htrace : WordTrace (prefixWord ++ tailWord_36760) baseStart_36760 baseEnd_36760 := by
    simpa [prefixWord, tailWord_36760, baseEnd_36760] using wordTrace_append hprefix tailTrace_36760
  have hstable : (prefixWord ++ tailWord_36760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36760).length < 2 ^ (prefixWord ++ tailWord_36760).sum := by decide
  have hdescent : baseEnd_36760 < baseStart_36760 := by decide
  rcases family_descends (prefixWord ++ tailWord_36760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36764 : List Nat := [2, 2, 3, 3, 1, 2, 1, 4, 2]
def baseStart_36764 : Nat := 118140960795 + 36764 * 2 ^ 59
def prefixEnd_36764 : Nat := 4983230072969 + 3 ^ 40 * 36764 * 2
def baseEnd_36764 : Nat := 16780091361777239449717

theorem tailTrace_36764 : CollatzResearch.WordTrace tailWord_36764 prefixEnd_36764 16780091361777239449717 := by
  unfold tailWord_36764
  simp only [CollatzResearch.WordTrace]
  refine ⟨670446619408890818214673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 893928825878521090952897 670446619408890818214673)
  ·
    refine ⟨502834964556668113661005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 670446619408890818214673 502834964556668113661005)
    ·
      refine ⟨188563111708750542622877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 502834964556668113661005 188563111708750542622877)
      ·
        refine ⟨70711166890781453483579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188563111708750542622877 70711166890781453483579)
        ·
          refine ⟨106066750336172180225369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70711166890781453483579 106066750336172180225369)
          ·
            refine ⟨79550062752129135169027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106066750336172180225369 79550062752129135169027)
            ·
              refine ⟨119325094128193702753541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79550062752129135169027 119325094128193702753541)
              ·
                refine ⟨22373455149036319266289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119325094128193702753541 22373455149036319266289)
                ·
                  refine ⟨16780091361777239449717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22373455149036319266289 16780091361777239449717)
                  ·
                    rfl

theorem cell20_36764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_36764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36764 prefixEnd_36764 := by exact prefixLift 36764
  have htrace : WordTrace (prefixWord ++ tailWord_36764) baseStart_36764 baseEnd_36764 := by
    simpa [prefixWord, tailWord_36764, baseEnd_36764] using wordTrace_append hprefix tailTrace_36764
  have hstable : (prefixWord ++ tailWord_36764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36764).length < 2 ^ (prefixWord ++ tailWord_36764).sum := by decide
  have hdescent : baseEnd_36764 < baseStart_36764 := by decide
  rcases family_descends (prefixWord ++ tailWord_36764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36788 : List Nat := [2, 5, 2, 1, 2, 1, 3, 4]
def baseStart_36788 : Nat := 118140960795 + 36788 * 2 ^ 59
def prefixEnd_36788 : Nat := 4983230072969 + 3 ^ 40 * 36788 * 2
def baseEnd_36788 : Nat := 5597015205246607549873

theorem tailTrace_36788 : CollatzResearch.WordTrace tailWord_36788 prefixEnd_36788 5597015205246607549873 := by
  unfold tailWord_36788
  simp only [CollatzResearch.WordTrace]
  refine ⟨670884295365416867651509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 894512393820555823535345 670884295365416867651509)
  ·
    refine ⟨62895402690507831342329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 670884295365416867651509 62895402690507831342329)
    ·
      refine ⟨47171552017880873506747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62895402690507831342329 47171552017880873506747)
      ·
        refine ⟨70757328026821310260121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47171552017880873506747 70757328026821310260121)
        ·
          refine ⟨53067996020115982695091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70757328026821310260121 53067996020115982695091)
          ·
            refine ⟨79601994030173974042637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53067996020115982695091 79601994030173974042637)
            ·
              refine ⟨29850747761315240265989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79601994030173974042637 29850747761315240265989)
              ·
                refine ⟨5597015205246607549873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29850747761315240265989 5597015205246607549873)
                ·
                  rfl

theorem cell20_36788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_36788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36788 prefixEnd_36788 := by exact prefixLift 36788
  have htrace : WordTrace (prefixWord ++ tailWord_36788) baseStart_36788 baseEnd_36788 := by
    simpa [prefixWord, tailWord_36788, baseEnd_36788] using wordTrace_append hprefix tailTrace_36788
  have hstable : (prefixWord ++ tailWord_36788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36788).length < 2 ^ (prefixWord ++ tailWord_36788).sum := by decide
  have hdescent : baseEnd_36788 < baseStart_36788 := by decide
  rcases family_descends (prefixWord ++ tailWord_36788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36861 : List Nat := [1, 4, 1, 1, 1, 2, 5, 3, 2]
def baseStart_36861 : Nat := 118140960795 + 36861 * 2 ^ 59
def prefixEnd_36861 : Nat := 4983230072969 + 3 ^ 40 * 36861 * 2
def baseEnd_36861 : Nat := 16824364804876013215987

theorem tailTrace_36861 : CollatzResearch.WordTrace tailWord_36861 prefixEnd_36861 16824364804876013215987 := by
  unfold tailWord_36861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344431119466367202710437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 896287412977578135140291 1344431119466367202710437)
  ·
    refine ⟨252080834899943850508207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1344431119466367202710437 252080834899943850508207)
    ·
      refine ⟨378121252349915775762311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252080834899943850508207 378121252349915775762311)
      ·
        refine ⟨567181878524873663643467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378121252349915775762311 567181878524873663643467)
        ·
          refine ⟨850772817787310495465201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567181878524873663643467 850772817787310495465201)
          ·
            refine ⟨638079613340482871598901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850772817787310495465201 638079613340482871598901)
            ·
              refine ⟨59819963750670269212397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 638079613340482871598901 59819963750670269212397)
              ·
                refine ⟨22432486406501350954649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59819963750670269212397 22432486406501350954649)
                ·
                  refine ⟨16824364804876013215987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22432486406501350954649 16824364804876013215987)
                  ·
                    rfl

theorem cell20_36861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_36861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36861 prefixEnd_36861 := by exact prefixLift 36861
  have htrace : WordTrace (prefixWord ++ tailWord_36861) baseStart_36861 baseEnd_36861 := by
    simpa [prefixWord, tailWord_36861, baseEnd_36861] using wordTrace_append hprefix tailTrace_36861
  have hstable : (prefixWord ++ tailWord_36861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36861).length < 2 ^ (prefixWord ++ tailWord_36861).sum := by decide
  have hdescent : baseEnd_36861 < baseStart_36861 := by decide
  rcases family_descends (prefixWord ++ tailWord_36861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36870 : List Nat := [6, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_36870 : Nat := 118140960795 + 36870 * 2 ^ 59
def prefixEnd_36870 : Nat := 4983230072969 + 3 ^ 40 * 36870 * 2
def baseEnd_36870 : Nat := 16828472650111981915951

theorem tailTrace_36870 : CollatzResearch.WordTrace tailWord_36870 prefixEnd_36870 16828472650111981915951 := by
  unfold tailWord_36870
  simp only [CollatzResearch.WordTrace]
  refine ⟨42023730513555054368377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 896506250955841159858709 42023730513555054368377)
  ·
    refine ⟨31517797885166290776283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42023730513555054368377 31517797885166290776283)
    ·
      refine ⟨47276696827749436164425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31517797885166290776283 47276696827749436164425)
      ·
        refine ⟨35457522620812077123319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47276696827749436164425 35457522620812077123319)
        ·
          refine ⟨53186283931218115684979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35457522620812077123319 53186283931218115684979)
          ·
            refine ⟨79779425896827173527469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53186283931218115684979 79779425896827173527469)
            ·
              refine ⟨29917284711310190072801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79779425896827173527469 29917284711310190072801)
              ·
                refine ⟨22437963533482642554601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29917284711310190072801 22437963533482642554601)
                ·
                  refine ⟨16828472650111981915951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22437963533482642554601 16828472650111981915951)
                  ·
                    rfl

theorem cell20_36870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_36870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36870 prefixEnd_36870 := by exact prefixLift 36870
  have htrace : WordTrace (prefixWord ++ tailWord_36870) baseStart_36870 baseEnd_36870 := by
    simpa [prefixWord, tailWord_36870, baseEnd_36870] using wordTrace_append hprefix tailTrace_36870
  have hstable : (prefixWord ++ tailWord_36870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36870).length < 2 ^ (prefixWord ++ tailWord_36870).sum := by decide
  have hdescent : baseEnd_36870 < baseStart_36870 := by decide
  rcases family_descends (prefixWord ++ tailWord_36870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36878 : List Nat := [4, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_36878 : Nat := 118140960795 + 36878 * 2 ^ 59
def prefixEnd_36878 : Nat := 4983230072969 + 3 ^ 40 * 36878 * 2
def baseEnd_36878 : Nat := 16832124068099509649251

theorem tailTrace_36878 : CollatzResearch.WordTrace tailWord_36878 prefixEnd_36878 16832124068099509649251 := by
  unfold tailWord_36878
  simp only [CollatzResearch.WordTrace]
  refine ⟨168131395050597388259911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 896700773603186070719525 168131395050597388259911)
  ·
    refine ⟨252197092575896082389867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168131395050597388259911 252197092575896082389867)
    ·
      refine ⟨378295638863844123584801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252197092575896082389867 378295638863844123584801)
      ·
        refine ⟨283721729147883092688601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378295638863844123584801 283721729147883092688601)
        ·
          refine ⟨212791296860912319516451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283721729147883092688601 212791296860912319516451)
          ·
            refine ⟨319186945291368479274677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212791296860912319516451 319186945291368479274677)
            ·
              refine ⟨29923776121065794932001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 319186945291368479274677 29923776121065794932001)
              ·
                refine ⟨22442832090799346199001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29923776121065794932001 22442832090799346199001)
                ·
                  refine ⟨16832124068099509649251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22442832090799346199001 16832124068099509649251)
                  ·
                    rfl

theorem cell20_36878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_36878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36878 prefixEnd_36878 := by exact prefixLift 36878
  have htrace : WordTrace (prefixWord ++ tailWord_36878) baseStart_36878 baseEnd_36878 := by
    simpa [prefixWord, tailWord_36878, baseEnd_36878] using wordTrace_append hprefix tailTrace_36878
  have hstable : (prefixWord ++ tailWord_36878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36878).length < 2 ^ (prefixWord ++ tailWord_36878).sum := by decide
  have hdescent : baseEnd_36878 < baseStart_36878 := by decide
  rcases family_descends (prefixWord ++ tailWord_36878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36892 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_36892 : Nat := 118140960795 + 36892 * 2 ^ 59
def prefixEnd_36892 : Nat := 4983230072969 + 3 ^ 40 * 36892 * 2
def baseEnd_36892 : Nat := 16838514049577683182527

theorem tailTrace_36892 : CollatzResearch.WordTrace tailWord_36892 prefixEnd_36892 16838514049577683182527 := by
  unfold tailWord_36892
  simp only [CollatzResearch.WordTrace]
  refine ⟨672780891177029748544465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 897041188236039664725953 672780891177029748544465)
  ·
    refine ⟨504585668382772311408349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 672780891177029748544465 504585668382772311408349)
    ·
      refine ⟨189219625643539616778131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 504585668382772311408349 189219625643539616778131)
      ·
        refine ⟨283829438465309425167197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189219625643539616778131 283829438465309425167197)
        ·
          refine ⟨106436039424491034437699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283829438465309425167197 106436039424491034437699)
          ·
            refine ⟨159654059136736551656549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106436039424491034437699 159654059136736551656549)
            ·
              refine ⟨29935136088138103435603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159654059136736551656549 29935136088138103435603)
              ·
                refine ⟨44902704132207155153405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29935136088138103435603 44902704132207155153405)
                ·
                  refine ⟨16838514049577683182527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44902704132207155153405 16838514049577683182527)
                  ·
                    rfl

theorem cell20_36892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_36892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36892 prefixEnd_36892 := by exact prefixLift 36892
  have htrace : WordTrace (prefixWord ++ tailWord_36892) baseStart_36892 baseEnd_36892 := by
    simpa [prefixWord, tailWord_36892, baseEnd_36892] using wordTrace_append hprefix tailTrace_36892
  have hstable : (prefixWord ++ tailWord_36892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36892).length < 2 ^ (prefixWord ++ tailWord_36892).sum := by decide
  have hdescent : baseEnd_36892 < baseStart_36892 := by decide
  rcases family_descends (prefixWord ++ tailWord_36892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36975 : List Nat := [1, 1, 2, 1, 3, 5, 2, 3, 2]
def baseStart_36975 : Nat := 118140960795 + 36975 * 2 ^ 59
def prefixEnd_36975 : Nat := 4983230072969 + 3 ^ 40 * 36975 * 2
def baseEnd_36975 : Nat := 16876397511198283415521

theorem tailTrace_36975 : CollatzResearch.WordTrace tailWord_36975 prefixEnd_36975 16876397511198283415521 := by
  unfold tailWord_36975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1348589041053364672360379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 899059360702243114906919 1348589041053364672360379)
  ·
    refine ⟨2022883561580047008540569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1348589041053364672360379 2022883561580047008540569)
    ·
      refine ⟨1517162671185035256405427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2022883561580047008540569 1517162671185035256405427)
      ·
        refine ⟨2275744006777552884608141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517162671185035256405427 2275744006777552884608141)
        ·
          refine ⟨853404002541582331728053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2275744006777552884608141 853404002541582331728053)
          ·
            refine ⟨80006625238273343599505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 853404002541582331728053 80006625238273343599505)
            ·
              refine ⟨60004968928705007699629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80006625238273343599505 60004968928705007699629)
              ·
                refine ⟨22501863348264377887361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60004968928705007699629 22501863348264377887361)
                ·
                  refine ⟨16876397511198283415521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22501863348264377887361 16876397511198283415521)
                  ·
                    rfl

theorem cell20_36975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 2].length) (baseStart_36975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36975 prefixEnd_36975 := by exact prefixLift 36975
  have htrace : WordTrace (prefixWord ++ tailWord_36975) baseStart_36975 baseEnd_36975 := by
    simpa [prefixWord, tailWord_36975, baseEnd_36975] using wordTrace_append hprefix tailTrace_36975
  have hstable : (prefixWord ++ tailWord_36975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36975).length < 2 ^ (prefixWord ++ tailWord_36975).sum := by decide
  have hdescent : baseEnd_36975 < baseStart_36975 := by decide
  rcases family_descends (prefixWord ++ tailWord_36975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36989 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 3]
def baseStart_36989 : Nat := 118140960795 + 36989 * 2 ^ 59
def prefixEnd_36989 : Nat := 4983230072969 + 3 ^ 40 * 36989 * 2
def baseEnd_36989 : Nat := 16882787492676456948797

theorem tailTrace_36989 : CollatzResearch.WordTrace tailWord_36989 prefixEnd_36989 16882787492676456948797 := by
  unfold tailWord_36989
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349099663002645063370021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 899399775335096708913347 1349099663002645063370021)
  ·
    refine ⟨252956186812995949381879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1349099663002645063370021 252956186812995949381879)
    ·
      refine ⟨379434280219493924072819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252956186812995949381879 379434280219493924072819)
      ·
        refine ⟨569151420329240886109229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379434280219493924072819 569151420329240886109229)
        ·
          refine ⟨213431782623465332290961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 569151420329240886109229 213431782623465332290961)
          ·
            refine ⟨160073836967598999218221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213431782623465332290961 160073836967598999218221)
            ·
              refine ⟨60027688862849624706833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160073836967598999218221 60027688862849624706833)
              ·
                refine ⟨45020766647137218530125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60027688862849624706833 45020766647137218530125)
                ·
                  refine ⟨16882787492676456948797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45020766647137218530125 16882787492676456948797)
                  ·
                    rfl

theorem cell20_36989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_36989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36989 prefixEnd_36989 := by exact prefixLift 36989
  have htrace : WordTrace (prefixWord ++ tailWord_36989) baseStart_36989 baseEnd_36989 := by
    simpa [prefixWord, tailWord_36989, baseEnd_36989] using wordTrace_append hprefix tailTrace_36989
  have hstable : (prefixWord ++ tailWord_36989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36989).length < 2 ^ (prefixWord ++ tailWord_36989).sum := by decide
  have hdescent : baseEnd_36989 < baseStart_36989 := by decide
  rcases family_descends (prefixWord ++ tailWord_36989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36996 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_36996 : Nat := 118140960795 + 36996 * 2 ^ 59
def prefixEnd_36996 : Nat := 4983230072969 + 3 ^ 40 * 36996 * 2
def baseEnd_36996 : Nat := 16885982483415543715435

theorem tailTrace_36996 : CollatzResearch.WordTrace tailWord_36996 prefixEnd_36996 16885982483415543715435 := by
  unfold tailWord_36996
  simp only [CollatzResearch.WordTrace]
  refine ⟨674677486988642629437421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 899569982651523505916561 674677486988642629437421)
  ·
    refine ⟨253004057620740986039033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 674677486988642629437421 253004057620740986039033)
    ·
      refine ⟨189753043215555739529275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253004057620740986039033 189753043215555739529275)
      ·
        refine ⟨284629564823333609293913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189753043215555739529275 284629564823333609293913)
        ·
          refine ⟨213472173617500206970435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284629564823333609293913 213472173617500206970435)
          ·
            refine ⟨320208260426250310455653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213472173617500206970435 320208260426250310455653)
            ·
              refine ⟨60039048829921933210435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320208260426250310455653 60039048829921933210435)
              ·
                refine ⟨90058573244882899815653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60039048829921933210435 90058573244882899815653)
                ·
                  refine ⟨16885982483415543715435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90058573244882899815653 16885982483415543715435)
                  ·
                    rfl

theorem cell20_36996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_36996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_36996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_36996 prefixEnd_36996 := by exact prefixLift 36996
  have htrace : WordTrace (prefixWord ++ tailWord_36996) baseStart_36996 baseEnd_36996 := by
    simpa [prefixWord, tailWord_36996, baseEnd_36996] using wordTrace_append hprefix tailTrace_36996
  have hstable : (prefixWord ++ tailWord_36996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36996).length < 2 ^ (prefixWord ++ tailWord_36996).sum := by decide
  have hdescent : baseEnd_36996 < baseStart_36996 := by decide
  rcases family_descends (prefixWord ++ tailWord_36996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37048 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_37048 : Nat := 118140960795 + 37048 * 2 ^ 59
def prefixEnd_37048 : Nat := 4983230072969 + 3 ^ 40 * 37048 * 2
def baseEnd_37048 : Nat := 16909716700334473981889

theorem tailTrace_37048 : CollatzResearch.WordTrace tailWord_37048 prefixEnd_37048 16909716700334473981889 := by
  unfold tailWord_37048
  simp only [CollatzResearch.WordTrace]
  refine ⟨675625784894449069883899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 900834379859265426511865 675625784894449069883899)
  ·
    refine ⟨1013438677341673604825849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 675625784894449069883899 1013438677341673604825849)
    ·
      refine ⟨760079008006255203619387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1013438677341673604825849 760079008006255203619387)
      ·
        refine ⟨1140118512009382805429081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760079008006255203619387 1140118512009382805429081)
        ·
          refine ⟨855088884007037104071811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1140118512009382805429081 855088884007037104071811)
          ·
            refine ⟨1282633326010555656107717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855088884007037104071811 1282633326010555656107717)
            ·
              refine ⟨240493748626979185520197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1282633326010555656107717 240493748626979185520197)
              ·
                refine ⟨45092577867558597285037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240493748626979185520197 45092577867558597285037)
                ·
                  refine ⟨16909716700334473981889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45092577867558597285037 16909716700334473981889)
                  ·
                    rfl

theorem cell20_37048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_37048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37048 prefixEnd_37048 := by exact prefixLift 37048
  have htrace : WordTrace (prefixWord ++ tailWord_37048) baseStart_37048 baseEnd_37048 := by
    simpa [prefixWord, tailWord_37048, baseEnd_37048] using wordTrace_append hprefix tailTrace_37048
  have hstable : (prefixWord ++ tailWord_37048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37048).length < 2 ^ (prefixWord ++ tailWord_37048).sum := by decide
  have hdescent : baseEnd_37048 < baseStart_37048 := by decide
  rcases family_descends (prefixWord ++ tailWord_37048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37051 : List Nat := [1, 1, 1, 1, 1, 2, 9, 2, 2]
def baseStart_37051 : Nat := 118140960795 + 37051 * 2 ^ 59
def prefixEnd_37051 : Nat := 4983230072969 + 3 ^ 40 * 37051 * 2
def baseEnd_37051 : Nat := 16911085982079796881877

theorem tailTrace_37051 : CollatzResearch.WordTrace tailWord_37051 prefixEnd_37051 16911085982079796881877 := by
  unfold tailWord_37051
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351360988778029652127007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 900907325852019768084671 1351360988778029652127007)
  ·
    refine ⟨2027041483167044478190511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1351360988778029652127007 2027041483167044478190511)
    ·
      refine ⟨3040562224750566717285767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2027041483167044478190511 3040562224750566717285767)
      ·
        refine ⟨4560843337125850075928651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040562224750566717285767 4560843337125850075928651)
        ·
          refine ⟨6841265005688775113892977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560843337125850075928651 6841265005688775113892977)
          ·
            refine ⟨5130948754266581335419733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6841265005688775113892977 5130948754266581335419733)
            ·
              refine ⟨30064152857030750012225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5130948754266581335419733 30064152857030750012225)
              ·
                refine ⟨22548114642773062509169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30064152857030750012225 22548114642773062509169)
                ·
                  refine ⟨16911085982079796881877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22548114642773062509169 16911085982079796881877)
                  ·
                    rfl

theorem cell20_37051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 2].length) (baseStart_37051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37051 prefixEnd_37051 := by exact prefixLift 37051
  have htrace : WordTrace (prefixWord ++ tailWord_37051) baseStart_37051 baseEnd_37051 := by
    simpa [prefixWord, tailWord_37051, baseEnd_37051] using wordTrace_append hprefix tailTrace_37051
  have hstable : (prefixWord ++ tailWord_37051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37051).length < 2 ^ (prefixWord ++ tailWord_37051).sum := by decide
  have hdescent : baseEnd_37051 < baseStart_37051 := by decide
  rcases family_descends (prefixWord ++ tailWord_37051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37103 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 3]
def baseStart_37103 : Nat := 118140960795 + 37103 * 2 ^ 59
def prefixEnd_37103 : Nat := 4983230072969 + 3 ^ 40 * 37103 * 2
def baseEnd_37103 : Nat := 16934820198998727148331

theorem tailTrace_37103 : CollatzResearch.WordTrace tailWord_37103 prefixEnd_37103 16934820198998727148331 := by
  unfold tailWord_37103
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353257584589642533019963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 902171723059761688679975 1353257584589642533019963)
  ·
    refine ⟨2029886376884463799529945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1353257584589642533019963 2029886376884463799529945)
    ·
      refine ⟨1522414782663347849647459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2029886376884463799529945 1522414782663347849647459)
      ·
        refine ⟨2283622173995021774471189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522414782663347849647459 2283622173995021774471189)
        ·
          refine ⟨107044789406016645678337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2283622173995021774471189 107044789406016645678337)
          ·
            refine ⟨80283592054512484258753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107044789406016645678337 80283592054512484258753)
            ·
              refine ⟨60212694040884363194065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80283592054512484258753 60212694040884363194065)
              ·
                refine ⟨45159520530663272395549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60212694040884363194065 45159520530663272395549)
                ·
                  refine ⟨16934820198998727148331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45159520530663272395549 16934820198998727148331)
                  ·
                    rfl

theorem cell20_37103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_37103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37103 prefixEnd_37103 := by exact prefixLift 37103
  have htrace : WordTrace (prefixWord ++ tailWord_37103) baseStart_37103 baseEnd_37103 := by
    simpa [prefixWord, tailWord_37103, baseEnd_37103] using wordTrace_append hprefix tailTrace_37103
  have hstable : (prefixWord ++ tailWord_37103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37103).length < 2 ^ (prefixWord ++ tailWord_37103).sum := by decide
  have hdescent : baseEnd_37103 < baseStart_37103 := by decide
  rcases family_descends (prefixWord ++ tailWord_37103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37106 : List Nat := [3, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_37106 : Nat := 118140960795 + 37106 * 2 ^ 59
def prefixEnd_37106 : Nat := 4983230072969 + 3 ^ 40 * 37106 * 2
def baseEnd_37106 : Nat := 16936189480744050048319

theorem tailTrace_37106 : CollatzResearch.WordTrace tailWord_37106 prefixEnd_37106 16936189480744050048319 := by
  unfold tailWord_37106
  simp only [CollatzResearch.WordTrace]
  refine ⟨338341750894693511344793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 902244669052516030252781 338341750894693511344793)
  ·
    refine ⟨253756313171020133508595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 338341750894693511344793 253756313171020133508595)
    ·
      refine ⟨380634469756530200262893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253756313171020133508595 380634469756530200262893)
      ·
        refine ⟨142737926158698825098585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380634469756530200262893 142737926158698825098585)
        ·
          refine ⟨107053444619024118823939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142737926158698825098585 107053444619024118823939)
          ·
            refine ⟨160580166928536178235909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107053444619024118823939 160580166928536178235909)
            ·
              refine ⟨30108781299100533419233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160580166928536178235909 30108781299100533419233)
              ·
                refine ⟨22581585974325400064425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30108781299100533419233 22581585974325400064425)
                ·
                  refine ⟨16936189480744050048319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22581585974325400064425 16936189480744050048319)
                  ·
                    rfl

theorem cell20_37106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_37106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37106 prefixEnd_37106 := by exact prefixLift 37106
  have htrace : WordTrace (prefixWord ++ tailWord_37106) baseStart_37106 baseEnd_37106 := by
    simpa [prefixWord, tailWord_37106, baseEnd_37106] using wordTrace_append hprefix tailTrace_37106
  have hstable : (prefixWord ++ tailWord_37106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37106).length < 2 ^ (prefixWord ++ tailWord_37106).sum := by decide
  have hdescent : baseEnd_37106 < baseStart_37106 := by decide
  rcases family_descends (prefixWord ++ tailWord_37106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37127 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 4]
def baseStart_37127 : Nat := 118140960795 + 37127 * 2 ^ 59
def prefixEnd_37127 : Nat := 4983230072969 + 3 ^ 40 * 37127 * 2
def baseEnd_37127 : Nat := 16945774452961310348233

theorem tailTrace_37127 : CollatzResearch.WordTrace tailWord_37127 prefixEnd_37127 16945774452961310348233 := by
  unfold tailWord_37127
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354132936502694631893635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 902755291001796421262423 1354132936502694631893635)
  ·
    refine ⟨2031199404754041947840453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354132936502694631893635 2031199404754041947840453)
    ·
      refine ⟨380849888391382865220085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2031199404754041947840453 380849888391382865220085)
      ·
        refine ⟨35704677036692143614383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 380849888391382865220085 35704677036692143614383)
        ·
          refine ⟨53557015555038215421575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35704677036692143614383 53557015555038215421575)
          ·
            refine ⟨80335523332557323132363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53557015555038215421575 80335523332557323132363)
            ·
              refine ⟨120503284998835984698545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80335523332557323132363 120503284998835984698545)
              ·
                refine ⟨90377463749126988523909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120503284998835984698545 90377463749126988523909)
                ·
                  refine ⟨16945774452961310348233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90377463749126988523909 16945774452961310348233)
                  ·
                    rfl

theorem cell20_37127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_37127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37127 prefixEnd_37127 := by exact prefixLift 37127
  have htrace : WordTrace (prefixWord ++ tailWord_37127) baseStart_37127 baseEnd_37127 := by
    simpa [prefixWord, tailWord_37127, baseEnd_37127] using wordTrace_append hprefix tailTrace_37127
  have hstable : (prefixWord ++ tailWord_37127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37127).length < 2 ^ (prefixWord ++ tailWord_37127).sum := by decide
  have hdescent : baseEnd_37127 < baseStart_37127 := by decide
  rcases family_descends (prefixWord ++ tailWord_37127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37131 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_37131 : Nat := 118140960795 + 37131 * 2 ^ 59
def prefixEnd_37131 : Nat := 4983230072969 + 3 ^ 40 * 37131 * 2
def baseEnd_37131 : Nat := 16947600161955074214883

theorem tailTrace_37131 : CollatzResearch.WordTrace tailWord_37131 prefixEnd_37131 16947600161955074214883 := by
  unfold tailWord_37131
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354278828488203315039247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 902852552325468876692831 1354278828488203315039247)
  ·
    refine ⟨2031418242732304972558871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354278828488203315039247 2031418242732304972558871)
    ·
      refine ⟨3047127364098457458838307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031418242732304972558871 3047127364098457458838307)
      ·
        refine ⟨4570691046147686188257461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047127364098457458838307 4570691046147686188257461)
        ·
          refine ⟨428502285576345580149137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4570691046147686188257461 428502285576345580149137)
          ·
            refine ⟨321376714182259185111853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428502285576345580149137 321376714182259185111853)
            ·
              refine ⟨120516267818347194416945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321376714182259185111853 120516267818347194416945)
              ·
                refine ⟨90387200863760395812709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120516267818347194416945 90387200863760395812709)
                ·
                  refine ⟨16947600161955074214883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90387200863760395812709 16947600161955074214883)
                  ·
                    rfl

theorem cell20_37131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_37131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37131 prefixEnd_37131 := by exact prefixLift 37131
  have htrace : WordTrace (prefixWord ++ tailWord_37131) baseStart_37131 baseEnd_37131 := by
    simpa [prefixWord, tailWord_37131, baseEnd_37131] using wordTrace_append hprefix tailTrace_37131
  have hstable : (prefixWord ++ tailWord_37131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37131).length < 2 ^ (prefixWord ++ tailWord_37131).sum := by decide
  have hdescent : baseEnd_37131 < baseStart_37131 := by decide
  rcases family_descends (prefixWord ++ tailWord_37131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37224 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_37224 : Nat := 118140960795 + 37224 * 2 ^ 59
def prefixEnd_37224 : Nat := 4983230072969 + 3 ^ 40 * 37224 * 2
def baseEnd_37224 : Nat := 16990047896060084114503

theorem tailTrace_37224 : CollatzResearch.WordTrace tailWord_37224 prefixEnd_37224 16990047896060084114503 := by
  unfold tailWord_37224
  simp only [CollatzResearch.WordTrace]
  refine ⟨678835408575640099087363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 905113878100853465449817 678835408575640099087363)
  ·
    refine ⟨1018253112863460148631045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 678835408575640099087363 1018253112863460148631045)
    ·
      refine ⟨190922458661898777868321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1018253112863460148631045 190922458661898777868321)
      ·
        refine ⟨143191843996424083401241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190922458661898777868321 143191843996424083401241)
        ·
          refine ⟨107393882997318062550931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143191843996424083401241 107393882997318062550931)
          ·
            refine ⟨161090824495977093826397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107393882997318062550931 161090824495977093826397)
            ·
              refine ⟨60409059185991410184899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161090824495977093826397 60409059185991410184899)
              ·
                refine ⟨90613588778987115277349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60409059185991410184899 90613588778987115277349)
                ·
                  refine ⟨16990047896060084114503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90613588778987115277349 16990047896060084114503)
                  ·
                    rfl

theorem cell20_37224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_37224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37224 prefixEnd_37224 := by exact prefixLift 37224
  have htrace : WordTrace (prefixWord ++ tailWord_37224) baseStart_37224 baseEnd_37224 := by
    simpa [prefixWord, tailWord_37224, baseEnd_37224] using wordTrace_append hprefix tailTrace_37224
  have hstable : (prefixWord ++ tailWord_37224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37224).length < 2 ^ (prefixWord ++ tailWord_37224).sum := by decide
  have hdescent : baseEnd_37224 < baseStart_37224 := by decide
  rcases family_descends (prefixWord ++ tailWord_37224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37234 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_37234 : Nat := 118140960795 + 37234 * 2 ^ 59
def prefixEnd_37234 : Nat := 4983230072969 + 3 ^ 40 * 37234 * 2
def baseEnd_37234 : Nat := 16994612168544493781129

theorem tailTrace_37234 : CollatzResearch.WordTrace tailWord_37234 prefixEnd_37234 16994612168544493781129 := by
  unfold tailWord_37234
  simp only [CollatzResearch.WordTrace]
  refine ⟨339508886778762976509689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 905357031410034604025837 339508886778762976509689)
  ·
    refine ⟨254631665084072232382267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 339508886778762976509689 254631665084072232382267)
    ·
      refine ⟨381947497626108348573401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254631665084072232382267 381947497626108348573401)
      ·
        refine ⟨286460623219581261430051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381947497626108348573401 286460623219581261430051)
        ·
          refine ⟨429690934829371892145077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286460623219581261430051 429690934829371892145077)
          ·
            refine ⟨40283525140253614888601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 429690934829371892145077 40283525140253614888601)
            ·
              refine ⟨30212643855190211166451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40283525140253614888601 30212643855190211166451)
              ·
                refine ⟨45318965782785316749677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30212643855190211166451 45318965782785316749677)
                ·
                  refine ⟨16994612168544493781129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45318965782785316749677 16994612168544493781129)
                  ·
                    rfl

theorem cell20_37234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_37234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37234 prefixEnd_37234 := by exact prefixLift 37234
  have htrace : WordTrace (prefixWord ++ tailWord_37234) baseStart_37234 baseEnd_37234 := by
    simpa [prefixWord, tailWord_37234, baseEnd_37234] using wordTrace_append hprefix tailTrace_37234
  have hstable : (prefixWord ++ tailWord_37234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37234).length < 2 ^ (prefixWord ++ tailWord_37234).sum := by decide
  have hdescent : baseEnd_37234 < baseStart_37234 := by decide
  rcases family_descends (prefixWord ++ tailWord_37234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37252 : List Nat := [2, 3, 2, 1, 1, 2, 1, 8]
def baseStart_37252 : Nat := 118140960795 + 37252 * 2 ^ 59
def prefixEnd_37252 : Nat := 4983230072969 + 3 ^ 40 * 37252 * 2
def baseEnd_37252 : Nat := 5667609286338810393685

theorem tailTrace_37252 : CollatzResearch.WordTrace tailWord_37252 prefixEnd_37252 5667609286338810393685 := by
  unfold tailWord_37252
  simp only [CollatzResearch.WordTrace]
  refine ⟨679346030524920490097005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 905794707366560653462673 679346030524920490097005)
  ·
    refine ⟨254754761446845183786377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 679346030524920490097005 254754761446845183786377)
    ·
      refine ⟨191066071085133887839783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254754761446845183786377 191066071085133887839783)
      ·
        refine ⟨286599106627700831759675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191066071085133887839783 286599106627700831759675)
        ·
          refine ⟨429898659941551247639513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286599106627700831759675 429898659941551247639513)
          ·
            refine ⟨322423994956163435729635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429898659941551247639513 322423994956163435729635)
            ·
              refine ⟨483635992434245153594453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322423994956163435729635 483635992434245153594453)
              ·
                refine ⟨5667609286338810393685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 483635992434245153594453 5667609286338810393685)
                ·
                  rfl

theorem cell20_37252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_37252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37252 prefixEnd_37252 := by exact prefixLift 37252
  have htrace : WordTrace (prefixWord ++ tailWord_37252) baseStart_37252 baseEnd_37252 := by
    simpa [prefixWord, tailWord_37252, baseEnd_37252] using wordTrace_append hprefix tailTrace_37252
  have hstable : (prefixWord ++ tailWord_37252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37252).length < 2 ^ (prefixWord ++ tailWord_37252).sum := by decide
  have hdescent : baseEnd_37252 < baseStart_37252 := by decide
  rcases family_descends (prefixWord ++ tailWord_37252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37338 : List Nat := [3, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_37338 : Nat := 118140960795 + 37338 * 2 ^ 59
def prefixEnd_37338 : Nat := 4983230072969 + 3 ^ 40 * 37338 * 2
def baseEnd_37338 : Nat := 17042080602382354314037

theorem tailTrace_37338 : CollatzResearch.WordTrace tailWord_37338 prefixEnd_37338 17042080602382354314037 := by
  unfold tailWord_37338
  simp only [CollatzResearch.WordTrace]
  refine ⟨340457184684569416956167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 907885825825518445216445 340457184684569416956167)
  ·
    refine ⟨510685777026854125434251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 340457184684569416956167 510685777026854125434251)
    ·
      refine ⟨766028665540281188151377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510685777026854125434251 766028665540281188151377)
      ·
        refine ⟨574521499155210891113533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 766028665540281188151377 574521499155210891113533)
        ·
          refine ⟨215445562183204084167575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574521499155210891113533 215445562183204084167575)
          ·
            refine ⟨323168343274806126251363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215445562183204084167575 323168343274806126251363)
            ·
              refine ⟨484752514912209189377045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323168343274806126251363 484752514912209189377045)
              ·
                refine ⟨22722774136509805752049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 484752514912209189377045 22722774136509805752049)
                ·
                  refine ⟨17042080602382354314037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22722774136509805752049 17042080602382354314037)
                  ·
                    rfl

theorem cell20_37338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_37338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37338 prefixEnd_37338 := by exact prefixLift 37338
  have htrace : WordTrace (prefixWord ++ tailWord_37338) baseStart_37338 baseEnd_37338 := by
    simpa [prefixWord, tailWord_37338, baseEnd_37338] using wordTrace_append hprefix tailTrace_37338
  have hstable : (prefixWord ++ tailWord_37338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37338).length < 2 ^ (prefixWord ++ tailWord_37338).sum := by decide
  have hdescent : baseEnd_37338 < baseStart_37338 := by decide
  rcases family_descends (prefixWord ++ tailWord_37338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37373 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_37373 : Nat := 118140960795 + 37373 * 2 ^ 59
def prefixEnd_37373 : Nat := 4983230072969 + 3 ^ 40 * 37373 * 2
def baseEnd_37373 : Nat := 17058055556077788147227

theorem tailTrace_37373 : CollatzResearch.WordTrace tailWord_37373 prefixEnd_37373 17058055556077788147227 := by
  unfold tailWord_37373
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363105293611478645348773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 908736862407652430232515 1363105293611478645348773)
  ·
    refine ⟨255582242552152246002895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1363105293611478645348773 255582242552152246002895)
    ·
      refine ⟨383373363828228369004343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255582242552152246002895 383373363828228369004343)
      ·
        refine ⟨575060045742342553506515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383373363828228369004343 575060045742342553506515)
        ·
          refine ⟨862590068613513830259773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575060045742342553506515 862590068613513830259773)
          ·
            refine ⟨323471275730067686347415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 862590068613513830259773 323471275730067686347415)
            ·
              refine ⟨485206913595101529521123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323471275730067686347415 485206913595101529521123)
              ·
                refine ⟨727810370392652294281685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485206913595101529521123 727810370392652294281685)
                ·
                  refine ⟨17058055556077788147227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 727810370392652294281685 17058055556077788147227)
                  ·
                    rfl

theorem cell20_37373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_37373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37373 prefixEnd_37373 := by exact prefixLift 37373
  have htrace : WordTrace (prefixWord ++ tailWord_37373) baseStart_37373 baseEnd_37373 := by
    simpa [prefixWord, tailWord_37373, baseEnd_37373] using wordTrace_append hprefix tailTrace_37373
  have hstable : (prefixWord ++ tailWord_37373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37373).length < 2 ^ (prefixWord ++ tailWord_37373).sum := by decide
  have hdescent : baseEnd_37373 < baseStart_37373 := by decide
  rcases family_descends (prefixWord ++ tailWord_37373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37383 : List Nat := [1, 1, 4, 3, 3, 2, 6]
def baseStart_37383 : Nat := 118140960795 + 37383 * 2 ^ 59
def prefixEnd_37383 : Nat := 4983230072969 + 3 ^ 40 * 37383 * 2
def baseEnd_37383 : Nat := 1895846647618021979317

theorem tailTrace_37383 : CollatzResearch.WordTrace tailWord_37383 prefixEnd_37383 1895846647618021979317 := by
  unfold tailWord_37383
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363470023575250353212803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 908980015716833568808535 1363470023575250353212803)
  ·
    refine ⟨2045205035362875529819205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1363470023575250353212803 2045205035362875529819205)
    ·
      refine ⟨383475944130539161841101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2045205035362875529819205 383475944130539161841101)
      ·
        refine ⟨143803479048952185690413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383475944130539161841101 143803479048952185690413)
        ·
          refine ⟨53926304643357069633905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143803479048952185690413 53926304643357069633905)
          ·
            refine ⟨40444728482517802225429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53926304643357069633905 40444728482517802225429)
            ·
              refine ⟨1895846647618021979317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40444728482517802225429 1895846647618021979317)
              ·
                rfl

theorem cell20_37383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 6].length) (baseStart_37383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37383 prefixEnd_37383 := by exact prefixLift 37383
  have htrace : WordTrace (prefixWord ++ tailWord_37383) baseStart_37383 baseEnd_37383 := by
    simpa [prefixWord, tailWord_37383, baseEnd_37383] using wordTrace_append hprefix tailTrace_37383
  have hstable : (prefixWord ++ tailWord_37383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37383).length < 2 ^ (prefixWord ++ tailWord_37383).sum := by decide
  have hdescent : baseEnd_37383 < baseStart_37383 := by decide
  rcases family_descends (prefixWord ++ tailWord_37383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37390 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_37390 : Nat := 118140960795 + 37390 * 2 ^ 59
def prefixEnd_37390 : Nat := 4983230072969 + 3 ^ 40 * 37390 * 2
def baseEnd_37390 : Nat := 17065814819301284580491

theorem tailTrace_37390 : CollatzResearch.WordTrace tailWord_37390 prefixEnd_37390 17065814819301284580491 := by
  unfold tailWord_37390
  simp only [CollatzResearch.WordTrace]
  refine ⟨170465666818736318589703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 909150223033260365811749 170465666818736318589703)
  ·
    refine ⟨255698500228104477884555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170465666818736318589703 255698500228104477884555)
    ·
      refine ⟨383547750342156716826833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255698500228104477884555 383547750342156716826833)
      ·
        refine ⟨287660812756617537620125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383547750342156716826833 287660812756617537620125)
        ·
          refine ⟨107872804783731576607547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287660812756617537620125 107872804783731576607547)
          ·
            refine ⟨161809207175597364911321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107872804783731576607547 161809207175597364911321)
            ·
              refine ⟨121356905381698023683491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161809207175597364911321 121356905381698023683491)
              ·
                refine ⟨182035358072547035525237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121356905381698023683491 182035358072547035525237)
                ·
                  refine ⟨17065814819301284580491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182035358072547035525237 17065814819301284580491)
                  ·
                    rfl

theorem cell20_37390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_37390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37390 prefixEnd_37390 := by exact prefixLift 37390
  have htrace : WordTrace (prefixWord ++ tailWord_37390) baseStart_37390 baseEnd_37390 := by
    simpa [prefixWord, tailWord_37390, baseEnd_37390] using wordTrace_append hprefix tailTrace_37390
  have hstable : (prefixWord ++ tailWord_37390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37390).length < 2 ^ (prefixWord ++ tailWord_37390).sum := by decide
  have hdescent : baseEnd_37390 < baseStart_37390 := by decide
  rcases family_descends (prefixWord ++ tailWord_37390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37404 : List Nat := [2, 2, 3, 1, 2, 2, 1, 7]
def baseStart_37404 : Nat := 118140960795 + 37404 * 2 ^ 59
def prefixEnd_37404 : Nat := 4983230072969 + 3 ^ 40 * 37404 * 2
def baseEnd_37404 : Nat := 5690734933593152704589

theorem tailTrace_37404 : CollatzResearch.WordTrace tailWord_37404 prefixEnd_37404 5690734933593152704589 := by
  unfold tailWord_37404
  simp only [CollatzResearch.WordTrace]
  refine ⟨682117978249585469863633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 909490637666113959818177 682117978249585469863633)
  ·
    refine ⟨511588483687189102397725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 682117978249585469863633 511588483687189102397725)
    ·
      refine ⟨191845681382695913399147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 511588483687189102397725 191845681382695913399147)
      ·
        refine ⟨287768522074043870098721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191845681382695913399147 287768522074043870098721)
        ·
          refine ⟨215826391555532902574041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287768522074043870098721 215826391555532902574041)
          ·
            refine ⟨161869793666649676930531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215826391555532902574041 161869793666649676930531)
            ·
              refine ⟨242804690499974515395797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161869793666649676930531 242804690499974515395797)
              ·
                refine ⟨5690734933593152704589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 242804690499974515395797 5690734933593152704589)
                ·
                  rfl

theorem cell20_37404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_37404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37404 prefixEnd_37404 := by exact prefixLift 37404
  have htrace : WordTrace (prefixWord ++ tailWord_37404) baseStart_37404 baseEnd_37404 := by
    simpa [prefixWord, tailWord_37404, baseEnd_37404] using wordTrace_append hprefix tailTrace_37404
  have hstable : (prefixWord ++ tailWord_37404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37404).length < 2 ^ (prefixWord ++ tailWord_37404).sum := by decide
  have hdescent : baseEnd_37404 < baseStart_37404 := by decide
  rcases family_descends (prefixWord ++ tailWord_37404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37438 : List Nat := [4, 2, 1, 4, 2, 7]
def baseStart_37438 : Nat := 118140960795 + 37438 * 2 ^ 59
def prefixEnd_37438 : Nat := 4983230072969 + 3 ^ 40 * 37438 * 2
def baseEnd_37438 : Nat := 632878641749127814085

theorem tailTrace_37438 : CollatzResearch.WordTrace tailWord_37438 prefixEnd_37438 632878641749127814085 := by
  unfold tailWord_37438
  simp only [CollatzResearch.WordTrace]
  refine ⟨170684504796999343308121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 910317358917329830976645 170684504796999343308121)
  ·
    refine ⟨128013378597749507481091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170684504796999343308121 128013378597749507481091)
    ·
      refine ⟨192020067896624261221637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128013378597749507481091 192020067896624261221637)
      ·
        refine ⟨36003762730617048979057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192020067896624261221637 36003762730617048979057)
        ·
          refine ⟨27002822047962786734293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36003762730617048979057 27002822047962786734293)
          ·
            refine ⟨632878641749127814085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27002822047962786734293 632878641749127814085)
            ·
              rfl

theorem cell20_37438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 7].length) (baseStart_37438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37438 prefixEnd_37438 := by exact prefixLift 37438
  have htrace : WordTrace (prefixWord ++ tailWord_37438) baseStart_37438 baseEnd_37438 := by
    simpa [prefixWord, tailWord_37438, baseEnd_37438] using wordTrace_append hprefix tailTrace_37438
  have hstable : (prefixWord ++ tailWord_37438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37438).length < 2 ^ (prefixWord ++ tailWord_37438).sum := by decide
  have hdescent : baseEnd_37438 < baseStart_37438 := by decide
  rcases family_descends (prefixWord ++ tailWord_37438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37452 : List Nat := [2, 2, 1, 3, 1, 2, 3, 4, 2]
def baseStart_37452 : Nat := 118140960795 + 37452 * 2 ^ 59
def prefixEnd_37452 : Nat := 4983230072969 + 3 ^ 40 * 37452 * 2
def baseEnd_37452 : Nat := 17094113308704624513571

theorem tailTrace_37452 : CollatzResearch.WordTrace tailWord_37452 prefixEnd_37452 17094113308704624513571 := by
  unfold tailWord_37452
  simp only [CollatzResearch.WordTrace]
  refine ⟨682993330162637568737305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 910657773550183424983073 682993330162637568737305)
  ·
    refine ⟨512244997621978176552979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 682993330162637568737305 512244997621978176552979)
    ·
      refine ⟨768367496432967264829469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512244997621978176552979 768367496432967264829469)
      ·
        refine ⟨288137811162362724311051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 768367496432967264829469 288137811162362724311051)
        ·
          refine ⟨432206716743544086466577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288137811162362724311051 432206716743544086466577)
          ·
            refine ⟨324155037557658064849933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432206716743544086466577 324155037557658064849933)
            ·
              refine ⟨121558139084121774318725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324155037557658064849933 121558139084121774318725)
              ·
                refine ⟨22792151078272832684761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121558139084121774318725 22792151078272832684761)
                ·
                  refine ⟨17094113308704624513571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22792151078272832684761 17094113308704624513571)
                  ·
                    rfl

theorem cell20_37452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_37452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37452 prefixEnd_37452 := by exact prefixLift 37452
  have htrace : WordTrace (prefixWord ++ tailWord_37452) baseStart_37452 baseEnd_37452 := by
    simpa [prefixWord, tailWord_37452, baseEnd_37452] using wordTrace_append hprefix tailTrace_37452
  have hstable : (prefixWord ++ tailWord_37452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37452).length < 2 ^ (prefixWord ++ tailWord_37452).sum := by decide
  have hdescent : baseEnd_37452 < baseStart_37452 := by decide
  rcases family_descends (prefixWord ++ tailWord_37452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37473 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_37473 : Nat := 118140960795 + 37473 * 2 ^ 59
def prefixEnd_37473 : Nat := 4983230072969 + 3 ^ 40 * 37473 * 2
def baseEnd_37473 : Nat := 17103698280921884813485

theorem tailTrace_37473 : CollatzResearch.WordTrace tailWord_37473 prefixEnd_37473 17103698280921884813485 := by
  unfold tailWord_37473
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366752593249195723989073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 911168395499463815992715 1366752593249195723989073)
  ·
    refine ⟨1025064444936896792991805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1366752593249195723989073 1025064444936896792991805)
    ·
      refine ⟨384399166851336297371927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1025064444936896792991805 384399166851336297371927)
      ·
        refine ⟨576598750277004446057891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384399166851336297371927 576598750277004446057891)
        ·
          refine ⟨864898125415506669086837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576598750277004446057891 864898125415506669086837)
          ·
            refine ⟨81084199257703750226891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 864898125415506669086837 81084199257703750226891)
            ·
              refine ⟨121626298886555625340337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81084199257703750226891 121626298886555625340337)
              ·
                refine ⟨91219724164916719005253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121626298886555625340337 91219724164916719005253)
                ·
                  refine ⟨17103698280921884813485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91219724164916719005253 17103698280921884813485)
                  ·
                    rfl

theorem cell20_37473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_37473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37473 prefixEnd_37473 := by exact prefixLift 37473
  have htrace : WordTrace (prefixWord ++ tailWord_37473) baseStart_37473 baseEnd_37473 := by
    simpa [prefixWord, tailWord_37473, baseEnd_37473] using wordTrace_append hprefix tailTrace_37473
  have hstable : (prefixWord ++ tailWord_37473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37473).length < 2 ^ (prefixWord ++ tailWord_37473).sum := by decide
  have hdescent : baseEnd_37473 < baseStart_37473 := by decide
  rcases family_descends (prefixWord ++ tailWord_37473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37504 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_37504 : Nat := 118140960795 + 37504 * 2 ^ 59
def prefixEnd_37504 : Nat := 4983230072969 + 3 ^ 40 * 37504 * 2
def baseEnd_37504 : Nat := 17117847525623554780025

theorem tailTrace_37504 : CollatzResearch.WordTrace tailWord_37504 prefixEnd_37504 17117847525623554780025 := by
  unfold tailWord_37504
  simp only [CollatzResearch.WordTrace]
  refine ⟨683941628068444009183783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 911922170757925345578377 683941628068444009183783)
  ·
    refine ⟨1025912442102666013775675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683941628068444009183783 1025912442102666013775675)
    ·
      refine ⟨1538868663153999020663513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025912442102666013775675 1538868663153999020663513)
      ·
        refine ⟨1154151497365499265497635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1538868663153999020663513 1154151497365499265497635)
        ·
          refine ⟨1731227246048248898246453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154151497365499265497635 1731227246048248898246453)
          ·
            refine ⟨162302554317023334210605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1731227246048248898246453 162302554317023334210605)
            ·
              refine ⟨60863457868883750328977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162302554317023334210605 60863457868883750328977)
              ·
                refine ⟨45647593401662812746733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60863457868883750328977 45647593401662812746733)
                ·
                  refine ⟨17117847525623554780025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45647593401662812746733 17117847525623554780025)
                  ·
                    rfl

theorem cell20_37504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_37504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37504 prefixEnd_37504 := by exact prefixLift 37504
  have htrace : WordTrace (prefixWord ++ tailWord_37504) baseStart_37504 baseEnd_37504 := by
    simpa [prefixWord, tailWord_37504, baseEnd_37504] using wordTrace_append hprefix tailTrace_37504
  have hstable : (prefixWord ++ tailWord_37504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37504).length < 2 ^ (prefixWord ++ tailWord_37504).sum := by decide
  have hdescent : baseEnd_37504 < baseStart_37504 := by decide
  rcases family_descends (prefixWord ++ tailWord_37504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37511 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_37511 : Nat := 118140960795 + 37511 * 2 ^ 59
def prefixEnd_37511 : Nat := 4983230072969 + 3 ^ 40 * 37511 * 2
def baseEnd_37511 : Nat := 17121042516362641546663

theorem tailTrace_37511 : CollatzResearch.WordTrace tailWord_37511 prefixEnd_37511 17121042516362641546663 := by
  unfold tailWord_37511
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368138567111528213872387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 912092378074352142581591 1368138567111528213872387)
  ·
    refine ⟨2052207850667292320808581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1368138567111528213872387 2052207850667292320808581)
    ·
      refine ⟨384788972000117310151609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2052207850667292320808581 384788972000117310151609)
      ·
        refine ⟨288591729000087982613707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384788972000117310151609 288591729000087982613707)
        ·
          refine ⟨432887593500131973920561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288591729000087982613707 432887593500131973920561)
          ·
            refine ⟨324665695125098980440421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432887593500131973920561 324665695125098980440421)
            ·
              refine ⟨60874817835956058832579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 324665695125098980440421 60874817835956058832579)
              ·
                refine ⟨91312226753934088248869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60874817835956058832579 91312226753934088248869)
                ·
                  refine ⟨17121042516362641546663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91312226753934088248869 17121042516362641546663)
                  ·
                    rfl

theorem cell20_37511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_37511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37511 prefixEnd_37511 := by exact prefixLift 37511
  have htrace : WordTrace (prefixWord ++ tailWord_37511) baseStart_37511 baseEnd_37511 := by
    simpa [prefixWord, tailWord_37511, baseEnd_37511] using wordTrace_append hprefix tailTrace_37511
  have hstable : (prefixWord ++ tailWord_37511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37511).length < 2 ^ (prefixWord ++ tailWord_37511).sum := by decide
  have hdescent : baseEnd_37511 < baseStart_37511 := by decide
  rcases family_descends (prefixWord ++ tailWord_37511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37518 : List Nat := [4, 1, 1, 3, 1, 1, 2, 7]
def baseStart_37518 : Nat := 118140960795 + 37518 * 2 ^ 59
def prefixEnd_37518 : Nat := 4983230072969 + 3 ^ 40 * 37518 * 2
def baseEnd_37518 : Nat := 5708079169033909437767

theorem tailTrace_37518 : CollatzResearch.WordTrace tailWord_37518 prefixEnd_37518 5708079169033909437767 := by
  unfold tailWord_37518
  simp only [CollatzResearch.WordTrace]
  refine ⟨171049234760771051172151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 912262585390778939584805 171049234760771051172151)
  ·
    refine ⟨256573852141156576758227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171049234760771051172151 256573852141156576758227)
    ·
      refine ⟨384860778211734865137341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256573852141156576758227 384860778211734865137341)
      ·
        refine ⟨144322791829400574426503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384860778211734865137341 144322791829400574426503)
        ·
          refine ⟨216484187744100861639755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144322791829400574426503 216484187744100861639755)
          ·
            refine ⟨324726281616151292459633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216484187744100861639755 324726281616151292459633)
            ·
              refine ⟨243544711212113469344725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324726281616151292459633 243544711212113469344725)
              ·
                refine ⟨5708079169033909437767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 243544711212113469344725 5708079169033909437767)
                ·
                  rfl

theorem cell20_37518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_37518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37518 prefixEnd_37518 := by exact prefixLift 37518
  have htrace : WordTrace (prefixWord ++ tailWord_37518) baseStart_37518 baseEnd_37518 := by
    simpa [prefixWord, tailWord_37518, baseEnd_37518] using wordTrace_append hprefix tailTrace_37518
  have hstable : (prefixWord ++ tailWord_37518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37518).length < 2 ^ (prefixWord ++ tailWord_37518).sum := by decide
  have hdescent : baseEnd_37518 < baseStart_37518 := by decide
  rcases family_descends (prefixWord ++ tailWord_37518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37615 : List Nat := [1, 1, 2, 1, 5, 10]
def baseStart_37615 : Nat := 118140960795 + 37615 * 2 ^ 59
def prefixEnd_37615 : Nat := 4983230072969 + 3 ^ 40 * 37615 * 2
def baseEnd_37615 : Nat := 635870775933351928873

theorem tailTrace_37615 : CollatzResearch.WordTrace tailWord_37615 prefixEnd_37615 635870775933351928873 := by
  unfold tailWord_37615
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371931758734753975658299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 914621172489835983772199 1371931758734753975658299)
  ·
    refine ⟨2057897638102130963487449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1371931758734753975658299 2057897638102130963487449)
    ·
      refine ⟨1543423228576598222615587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2057897638102130963487449 1543423228576598222615587)
      ·
        refine ⟨2315134842864897333923381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543423228576598222615587 2315134842864897333923381)
        ·
          refine ⟨217043891518584125055317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2315134842864897333923381 217043891518584125055317)
          ·
            refine ⟨635870775933351928873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 217043891518584125055317 635870775933351928873)
            ·
              rfl

theorem cell20_37615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 10].length) (baseStart_37615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37615 prefixEnd_37615 := by exact prefixLift 37615
  have htrace : WordTrace (prefixWord ++ tailWord_37615) baseStart_37615 baseEnd_37615 := by
    simpa [prefixWord, tailWord_37615, baseEnd_37615] using wordTrace_append hprefix tailTrace_37615
  have hstable : (prefixWord ++ tailWord_37615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37615).length < 2 ^ (prefixWord ++ tailWord_37615).sum := by decide
  have hdescent : baseEnd_37615 < baseStart_37615 := by decide
  rcases family_descends (prefixWord ++ tailWord_37615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37618 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_37618 : Nat := 118140960795 + 37618 * 2 ^ 59
def prefixEnd_37618 : Nat := 4983230072969 + 3 ^ 40 * 37618 * 2
def baseEnd_37618 : Nat := 17169880231945824979559

theorem tailTrace_37618 : CollatzResearch.WordTrace tailWord_37618 prefixEnd_37618 17169880231945824979559 := by
  unfold tailWord_37618
  simp only [CollatzResearch.WordTrace]
  refine ⟨343010294430971372004377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 914694118482590325345005 343010294430971372004377)
  ·
    refine ⟨257257720823228529003283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 343010294430971372004377 257257720823228529003283)
    ·
      refine ⟨385886581234842793504925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257257720823228529003283 385886581234842793504925)
      ·
        refine ⟨144707467963066047564347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385886581234842793504925 144707467963066047564347)
        ·
          refine ⟨217061201944599071346521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144707467963066047564347 217061201944599071346521)
          ·
            refine ⟨162795901458449303509891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217061201944599071346521 162795901458449303509891)
            ·
              refine ⟨244193852187673955264837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162795901458449303509891 244193852187673955264837)
              ·
                refine ⟨45786347285188866612157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244193852187673955264837 45786347285188866612157)
                ·
                  refine ⟨17169880231945824979559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45786347285188866612157 17169880231945824979559)
                  ·
                    rfl

theorem cell20_37618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_37618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37618 prefixEnd_37618 := by exact prefixLift 37618
  have htrace : WordTrace (prefixWord ++ tailWord_37618) baseStart_37618 baseEnd_37618 := by
    simpa [prefixWord, tailWord_37618, baseEnd_37618] using wordTrace_append hprefix tailTrace_37618
  have hstable : (prefixWord ++ tailWord_37618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37618).length < 2 ^ (prefixWord ++ tailWord_37618).sum := by decide
  have hdescent : baseEnd_37618 < baseStart_37618 := by decide
  rcases family_descends (prefixWord ++ tailWord_37618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37700 : List Nat := [2, 3, 4, 2, 2, 1, 2, 4]
def baseStart_37700 : Nat := 118140960795 + 37700 * 2 ^ 59
def prefixEnd_37700 : Nat := 4983230072969 + 3 ^ 40 * 37700 * 2
def baseEnd_37700 : Nat := 5735769088772661415297

theorem tailTrace_37700 : CollatzResearch.WordTrace tailWord_37700 prefixEnd_37700 5735769088772661415297 := by
  unfold tailWord_37700
  simp only [CollatzResearch.WordTrace]
  refine ⟨687515981713406746251277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 916687975617875661668369 687515981713406746251277)
  ·
    refine ⟨257818493142527529844229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 687515981713406746251277 257818493142527529844229)
    ·
      refine ⟨48340967464223911845793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257818493142527529844229 48340967464223911845793)
      ·
        refine ⟨36255725598167933884345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48340967464223911845793 36255725598167933884345)
        ·
          refine ⟨27191794198625950413259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36255725598167933884345 27191794198625950413259)
          ·
            refine ⟨40787691297938925619889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27191794198625950413259 40787691297938925619889)
            ·
              refine ⟨30590768473454194214917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40787691297938925619889 30590768473454194214917)
              ·
                refine ⟨5735769088772661415297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30590768473454194214917 5735769088772661415297)
                ·
                  rfl

theorem cell20_37700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_37700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37700 prefixEnd_37700 := by exact prefixLift 37700
  have htrace : WordTrace (prefixWord ++ tailWord_37700) baseStart_37700 baseEnd_37700 := by
    simpa [prefixWord, tailWord_37700, baseEnd_37700] using wordTrace_append hprefix tailTrace_37700
  have hstable : (prefixWord ++ tailWord_37700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37700).length < 2 ^ (prefixWord ++ tailWord_37700).sum := by decide
  have hdescent : baseEnd_37700 < baseStart_37700 := by decide
  rcases family_descends (prefixWord ++ tailWord_37700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37708 : List Nat := [2, 2, 1, 3, 3, 2, 1, 6]
def baseStart_37708 : Nat := 118140960795 + 37708 * 2 ^ 59
def prefixEnd_37708 : Nat := 4983230072969 + 3 ^ 40 * 37708 * 2
def baseEnd_37708 : Nat := 5736986228101837326397

theorem tailTrace_37708 : CollatzResearch.WordTrace tailWord_37708 prefixEnd_37708 5736986228101837326397 := by
  unfold tailWord_37708
  simp only [CollatzResearch.WordTrace]
  refine ⟨687661873698915429396889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 916882498265220572529185 687661873698915429396889)
  ·
    refine ⟨515746405274186572047667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 687661873698915429396889 515746405274186572047667)
    ·
      refine ⟨773619607911279858071501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515746405274186572047667 773619607911279858071501)
      ·
        refine ⟨290107352966729946776813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 773619607911279858071501 290107352966729946776813)
        ·
          refine ⟨108790257362523730041305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290107352966729946776813 108790257362523730041305)
          ·
            refine ⟨81592693021892797530979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108790257362523730041305 81592693021892797530979)
            ·
              refine ⟨122389039532839196296469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81592693021892797530979 122389039532839196296469)
              ·
                refine ⟨5736986228101837326397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122389039532839196296469 5736986228101837326397)
                ·
                  rfl

theorem cell20_37708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_37708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37708 prefixEnd_37708 := by exact prefixLift 37708
  have htrace : WordTrace (prefixWord ++ tailWord_37708) baseStart_37708 baseEnd_37708 := by
    simpa [prefixWord, tailWord_37708, baseEnd_37708] using wordTrace_append hprefix tailTrace_37708
  have hstable : (prefixWord ++ tailWord_37708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37708).length < 2 ^ (prefixWord ++ tailWord_37708).sum := by decide
  have hdescent : baseEnd_37708 < baseStart_37708 := by decide
  rcases family_descends (prefixWord ++ tailWord_37708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37735 : List Nat := [1, 1, 5, 1, 2, 3, 3, 2, 2]
def baseStart_37735 : Nat := 118140960795 + 37735 * 2 ^ 59
def prefixEnd_37735 : Nat := 4983230072969 + 3 ^ 40 * 37735 * 2
def baseEnd_37735 : Nat := 17223282220013418079081

theorem tailTrace_37735 : CollatzResearch.WordTrace tailWord_37735 prefixEnd_37735 17223282220013418079081 := by
  unfold tailWord_37735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376308518300014470026659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 917539012200009646684439 1376308518300014470026659)
  ·
    refine ⟨2064462777450021705039989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1376308518300014470026659 2064462777450021705039989)
    ·
      refine ⟨193543385385939534847499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2064462777450021705039989 193543385385939534847499)
      ·
        refine ⟨290315078078909302271249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193543385385939534847499 290315078078909302271249)
        ·
          refine ⟨217736308559181976703437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290315078078909302271249 217736308559181976703437)
          ·
            refine ⟨81651115709693241263789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217736308559181976703437 81651115709693241263789)
            ·
              refine ⟨30619168391134965473921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81651115709693241263789 30619168391134965473921)
              ·
                refine ⟨22964376293351224105441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30619168391134965473921 22964376293351224105441)
                ·
                  refine ⟨17223282220013418079081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22964376293351224105441 17223282220013418079081)
                  ·
                    rfl

theorem cell20_37735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 2].length) (baseStart_37735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37735 prefixEnd_37735 := by exact prefixLift 37735
  have htrace : WordTrace (prefixWord ++ tailWord_37735) baseStart_37735 baseEnd_37735 := by
    simpa [prefixWord, tailWord_37735, baseEnd_37735] using wordTrace_append hprefix tailTrace_37735
  have hstable : (prefixWord ++ tailWord_37735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37735).length < 2 ^ (prefixWord ++ tailWord_37735).sum := by decide
  have hdescent : baseEnd_37735 < baseStart_37735 := by decide
  rcases family_descends (prefixWord ++ tailWord_37735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37739 : List Nat := [1, 1, 1, 1, 2, 2, 4, 6, 2]
def baseStart_37739 : Nat := 118140960795 + 37739 * 2 ^ 59
def prefixEnd_37739 : Nat := 4983230072969 + 3 ^ 40 * 37739 * 2
def baseEnd_37739 : Nat := 17225107929007181945731

theorem tailTrace_37739 : CollatzResearch.WordTrace tailWord_37739 prefixEnd_37739 17225107929007181945731 := by
  unfold tailWord_37739
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376454410285523153172271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 917636273523682102114847 1376454410285523153172271)
  ·
    refine ⟨2064681615428284729758407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1376454410285523153172271 2064681615428284729758407)
    ·
      refine ⟨3097022423142427094637611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064681615428284729758407 3097022423142427094637611)
      ·
        refine ⟨4645533634713640641956417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097022423142427094637611 4645533634713640641956417)
        ·
          refine ⟨3484150226035230481467313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4645533634713640641956417 3484150226035230481467313)
          ·
            refine ⟨2613112669526422861100485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484150226035230481467313 2613112669526422861100485)
            ·
              refine ⟨489958625536204286456341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2613112669526422861100485 489958625536204286456341)
              ·
                refine ⟨22966810572009575927641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 489958625536204286456341 22966810572009575927641)
                ·
                  refine ⟨17225107929007181945731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22966810572009575927641 17225107929007181945731)
                  ·
                    rfl

theorem cell20_37739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 2].length) (baseStart_37739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37739 prefixEnd_37739 := by exact prefixLift 37739
  have htrace : WordTrace (prefixWord ++ tailWord_37739) baseStart_37739 baseEnd_37739 := by
    simpa [prefixWord, tailWord_37739, baseEnd_37739] using wordTrace_append hprefix tailTrace_37739
  have hstable : (prefixWord ++ tailWord_37739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37739).length < 2 ^ (prefixWord ++ tailWord_37739).sum := by decide
  have hdescent : baseEnd_37739 < baseStart_37739 := by decide
  rcases family_descends (prefixWord ++ tailWord_37739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37749 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 3]
def baseStart_37749 : Nat := 118140960795 + 37749 * 2 ^ 59
def prefixEnd_37749 : Nat := 4983230072969 + 3 ^ 40 * 37749 * 2
def baseEnd_37749 : Nat := 17229672201491591612357

theorem tailTrace_37749 : CollatzResearch.WordTrace tailWord_37749 prefixEnd_37749 17229672201491591612357 := by
  unfold tailWord_37749
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376819140249294861036301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 917879426832863240690867 1376819140249294861036301)
  ·
    refine ⟨516307177593485572888613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1376819140249294861036301 516307177593485572888613)
    ·
      refine ⟨96807595798778544916615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 516307177593485572888613 96807595798778544916615)
      ·
        refine ⟨145211393698167817374923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96807595798778544916615 145211393698167817374923)
        ·
          refine ⟨217817090547251726062385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145211393698167817374923 217817090547251726062385)
          ·
            refine ⟨163362817910438794546789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217817090547251726062385 163362817910438794546789)
            ·
              refine ⟨30630528358207273977523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163362817910438794546789 30630528358207273977523)
              ·
                refine ⟨45945792537310910966285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30630528358207273977523 45945792537310910966285)
                ·
                  refine ⟨17229672201491591612357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45945792537310910966285 17229672201491591612357)
                  ·
                    rfl

theorem cell20_37749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_37749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37749 prefixEnd_37749 := by exact prefixLift 37749
  have htrace : WordTrace (prefixWord ++ tailWord_37749) baseStart_37749 baseEnd_37749 := by
    simpa [prefixWord, tailWord_37749, baseEnd_37749] using wordTrace_append hprefix tailTrace_37749
  have hstable : (prefixWord ++ tailWord_37749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37749).length < 2 ^ (prefixWord ++ tailWord_37749).sum := by decide
  have hdescent : baseEnd_37749 < baseStart_37749 := by decide
  rcases family_descends (prefixWord ++ tailWord_37749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37777 : List Nat := [1, 2, 2, 1, 1, 1, 3, 7, 2]
def baseStart_37777 : Nat := 118140960795 + 37777 * 2 ^ 59
def prefixEnd_37777 : Nat := 4983230072969 + 3 ^ 40 * 37777 * 2
def baseEnd_37777 : Nat := 17242452164447938678909

theorem tailTrace_37777 : CollatzResearch.WordTrace tailWord_37777 prefixEnd_37777 17242452164447938678909 := by
  unfold tailWord_37777
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377840384147855643055585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 918560256098570428703723 1377840384147855643055585)
  ·
    refine ⟨1033380288110891732291689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1377840384147855643055585 1033380288110891732291689)
    ·
      refine ⟨775035216083168799218767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1033380288110891732291689 775035216083168799218767)
      ·
        refine ⟨1162552824124753198828151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775035216083168799218767 1162552824124753198828151)
        ·
          refine ⟨1743829236187129798242227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162552824124753198828151 1743829236187129798242227)
          ·
            refine ⟨2615743854280694697363341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743829236187129798242227 2615743854280694697363341)
            ·
              refine ⟨980903945355260511511253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2615743854280694697363341 980903945355260511511253)
              ·
                refine ⟨22989936219263918238545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 980903945355260511511253 22989936219263918238545)
                ·
                  refine ⟨17242452164447938678909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22989936219263918238545 17242452164447938678909)
                  ·
                    rfl

theorem cell20_37777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_37777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37777 prefixEnd_37777 := by exact prefixLift 37777
  have htrace : WordTrace (prefixWord ++ tailWord_37777) baseStart_37777 baseEnd_37777 := by
    simpa [prefixWord, tailWord_37777, baseEnd_37777] using wordTrace_append hprefix tailTrace_37777
  have hstable : (prefixWord ++ tailWord_37777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37777).length < 2 ^ (prefixWord ++ tailWord_37777).sum := by decide
  have hdescent : baseEnd_37777 < baseStart_37777 := by decide
  rcases family_descends (prefixWord ++ tailWord_37777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37814 : List Nat := [5, 1, 4, 1, 1, 1, 3, 4]
def baseStart_37814 : Nat := 118140960795 + 37814 * 2 ^ 59
def prefixEnd_37814 : Nat := 4983230072969 + 3 ^ 40 * 37814 * 2
def baseEnd_37814 : Nat := 5753113324213418148475

theorem tailTrace_37814 : CollatzResearch.WordTrace tailWord_37814 prefixEnd_37814 5753113324213418148475 := by
  unfold tailWord_37814
  simp only [CollatzResearch.WordTrace]
  refine ⟨86199367813363185134531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 919459923342540641434997 86199367813363185134531)
  ·
    refine ⟨129299051720044777701797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86199367813363185134531 129299051720044777701797)
    ·
      refine ⟨24243572197508395819087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129299051720044777701797 24243572197508395819087)
      ·
        refine ⟨36365358296262593728631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24243572197508395819087 36365358296262593728631)
        ·
          refine ⟨54548037444393890592947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36365358296262593728631 54548037444393890592947)
          ·
            refine ⟨81822056166590835889421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54548037444393890592947 81822056166590835889421)
            ·
              refine ⟨30683271062471563458533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81822056166590835889421 30683271062471563458533)
              ·
                refine ⟨5753113324213418148475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30683271062471563458533 5753113324213418148475)
                ·
                  rfl

theorem cell20_37814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_37814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37814 prefixEnd_37814 := by exact prefixLift 37814
  have htrace : WordTrace (prefixWord ++ tailWord_37814) baseStart_37814 baseEnd_37814 := by
    simpa [prefixWord, tailWord_37814, baseEnd_37814] using wordTrace_append hprefix tailTrace_37814
  have hstable : (prefixWord ++ tailWord_37814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37814).length < 2 ^ (prefixWord ++ tailWord_37814).sum := by decide
  have hdescent : baseEnd_37814 < baseStart_37814 := by decide
  rcases family_descends (prefixWord ++ tailWord_37814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37828 : List Nat := [2, 3, 3, 3, 1, 1, 2, 3, 2]
def baseStart_37828 : Nat := 118140960795 + 37828 * 2 ^ 59
def prefixEnd_37828 : Nat := 4983230072969 + 3 ^ 40 * 37828 * 2
def baseEnd_37828 : Nat := 17265729954118427978701

theorem tailTrace_37828 : CollatzResearch.WordTrace tailWord_37828 prefixEnd_37828 17265729954118427978701 := by
  unfold tailWord_37828
  simp only [CollatzResearch.WordTrace]
  refine ⟨689850253481545676581069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 919800337975394235441425 689850253481545676581069)
  ·
    refine ⟨258693845055579628717901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 689850253481545676581069 258693845055579628717901)
    ·
      refine ⟨97010191895842360769213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258693845055579628717901 97010191895842360769213)
      ·
        refine ⟨36378821960940885288455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97010191895842360769213 36378821960940885288455)
        ·
          refine ⟨54568232941411327932683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36378821960940885288455 54568232941411327932683)
          ·
            refine ⟨81852349412116991899025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54568232941411327932683 81852349412116991899025)
            ·
              refine ⟨61389262059087743924269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81852349412116991899025 61389262059087743924269)
              ·
                refine ⟨23020973272157903971601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61389262059087743924269 23020973272157903971601)
                ·
                  refine ⟨17265729954118427978701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23020973272157903971601 17265729954118427978701)
                  ·
                    rfl

theorem cell20_37828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_37828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37828 prefixEnd_37828 := by exact prefixLift 37828
  have htrace : WordTrace (prefixWord ++ tailWord_37828) baseStart_37828 baseEnd_37828 := by
    simpa [prefixWord, tailWord_37828, baseEnd_37828] using wordTrace_append hprefix tailTrace_37828
  have hstable : (prefixWord ++ tailWord_37828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37828).length < 2 ^ (prefixWord ++ tailWord_37828).sum := by decide
  have hdescent : baseEnd_37828 < baseStart_37828 := by decide
  rcases family_descends (prefixWord ++ tailWord_37828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37836 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_37836 : Nat := 118140960795 + 37836 * 2 ^ 59
def prefixEnd_37836 : Nat := 4983230072969 + 3 ^ 40 * 37836 * 2
def baseEnd_37836 : Nat := 17269381372105955712001

theorem tailTrace_37836 : CollatzResearch.WordTrace tailWord_37836 prefixEnd_37836 17269381372105955712001 := by
  unfold tailWord_37836
  simp only [CollatzResearch.WordTrace]
  refine ⟨689996145467054359726681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 919994860622739146302241 689996145467054359726681)
  ·
    refine ⟨517497109100290769795011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 689996145467054359726681 517497109100290769795011)
    ·
      refine ⟨776245663650436154692517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517497109100290769795011 776245663650436154692517)
      ·
        refine ⟨145546061934456779004847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 776245663650436154692517 145546061934456779004847)
        ·
          refine ⟨218319092901685168507271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145546061934456779004847 218319092901685168507271)
          ·
            refine ⟨327478639352527752760907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218319092901685168507271 327478639352527752760907)
            ·
              refine ⟨491217959028791629141361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327478639352527752760907 491217959028791629141361)
              ·
                refine ⟨368413469271593721856021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491217959028791629141361 368413469271593721856021)
                ·
                  refine ⟨17269381372105955712001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 368413469271593721856021 17269381372105955712001)
                  ·
                    rfl

theorem cell20_37836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_37836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37836 prefixEnd_37836 := by exact prefixLift 37836
  have htrace : WordTrace (prefixWord ++ tailWord_37836) baseStart_37836 baseEnd_37836 := by
    simpa [prefixWord, tailWord_37836, baseEnd_37836] using wordTrace_append hprefix tailTrace_37836
  have hstable : (prefixWord ++ tailWord_37836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37836).length < 2 ^ (prefixWord ++ tailWord_37836).sum := by decide
  have hdescent : baseEnd_37836 < baseStart_37836 := by decide
  rcases family_descends (prefixWord ++ tailWord_37836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37853 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_37853 : Nat := 118140960795 + 37853 * 2 ^ 59
def prefixEnd_37853 : Nat := 4983230072969 + 3 ^ 40 * 37853 * 2
def baseEnd_37853 : Nat := 17277140635329452145265

theorem tailTrace_37853 : CollatzResearch.WordTrace tailWord_37853 prefixEnd_37853 17277140635329452145265 := by
  unfold tailWord_37853
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380612331872520622822213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 920408221248347081881475 1380612331872520622822213)
  ·
    refine ⟨258864812226097616779165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1380612331872520622822213 258864812226097616779165)
    ·
      refine ⟨97074304584786606292187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258864812226097616779165 97074304584786606292187)
      ·
        refine ⟨145611456877179909438281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97074304584786606292187 145611456877179909438281)
        ·
          refine ⟨109208592657884932078711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145611456877179909438281 109208592657884932078711)
          ·
            refine ⟨163812888986827398118067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109208592657884932078711 163812888986827398118067)
            ·
              refine ⟨245719333480241097177101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163812888986827398118067 245719333480241097177101)
              ·
                refine ⟨92144750055090411441413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245719333480241097177101 92144750055090411441413)
                ·
                  refine ⟨17277140635329452145265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92144750055090411441413 17277140635329452145265)
                  ·
                    rfl

theorem cell20_37853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_37853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37853 prefixEnd_37853 := by exact prefixLift 37853
  have htrace : WordTrace (prefixWord ++ tailWord_37853) baseStart_37853 baseEnd_37853 := by
    simpa [prefixWord, tailWord_37853, baseEnd_37853] using wordTrace_append hprefix tailTrace_37853
  have hstable : (prefixWord ++ tailWord_37853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37853).length < 2 ^ (prefixWord ++ tailWord_37853).sum := by decide
  have hdescent : baseEnd_37853 < baseStart_37853 := by decide
  rcases family_descends (prefixWord ++ tailWord_37853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37863 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 3]
def baseStart_37863 : Nat := 118140960795 + 37863 * 2 ^ 59
def prefixEnd_37863 : Nat := 4983230072969 + 3 ^ 40 * 37863 * 2
def baseEnd_37863 : Nat := 17281704907813861811891

theorem tailTrace_37863 : CollatzResearch.WordTrace tailWord_37863 prefixEnd_37863 17281704907813861811891 := by
  unfold tailWord_37863
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380977061836292330686243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 920651374557528220457495 1380977061836292330686243)
  ·
    refine ⟨2071465592754438496029365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1380977061836292330686243 2071465592754438496029365)
    ·
      refine ⟨194199899320728609002753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2071465592754438496029365 194199899320728609002753)
      ·
        refine ⟨145649924490546456752065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194199899320728609002753 145649924490546456752065)
        ·
          refine ⟨109237443367909842564049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145649924490546456752065 109237443367909842564049)
          ·
            refine ⟨81928082525932381923037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109237443367909842564049 81928082525932381923037)
            ·
              refine ⟨30723030947224643221139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81928082525932381923037 30723030947224643221139)
              ·
                refine ⟨46084546420836964831709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30723030947224643221139 46084546420836964831709)
                ·
                  refine ⟨17281704907813861811891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46084546420836964831709 17281704907813861811891)
                  ·
                    rfl

theorem cell20_37863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 3].length) (baseStart_37863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37863 prefixEnd_37863 := by exact prefixLift 37863
  have htrace : WordTrace (prefixWord ++ tailWord_37863) baseStart_37863 baseEnd_37863 := by
    simpa [prefixWord, tailWord_37863, baseEnd_37863] using wordTrace_append hprefix tailTrace_37863
  have hstable : (prefixWord ++ tailWord_37863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37863).length < 2 ^ (prefixWord ++ tailWord_37863).sum := by decide
  have hdescent : baseEnd_37863 < baseStart_37863 := by decide
  rcases family_descends (prefixWord ++ tailWord_37863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37881 : List Nat := [1, 2, 1, 3, 1, 3, 3, 6]
def baseStart_37881 : Nat := 118140960795 + 37881 * 2 ^ 59
def prefixEnd_37881 : Nat := 4983230072969 + 3 ^ 40 * 37881 * 2
def baseEnd_37881 : Nat := 5763306866095266403939

theorem tailTrace_37881 : CollatzResearch.WordTrace tailWord_37881 prefixEnd_37881 5763306866095266403939 := by
  unfold tailWord_37881
  simp only [CollatzResearch.WordTrace]
  refine ⟨1381633575771081404841497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 921089050514054269894331 1381633575771081404841497)
  ·
    refine ⟨1036225181828311053631123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1381633575771081404841497 1036225181828311053631123)
    ·
      refine ⟨1554337772742466580446685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036225181828311053631123 1554337772742466580446685)
      ·
        refine ⟨582876664778424967667507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1554337772742466580446685 582876664778424967667507)
        ·
          refine ⟨874314997167637451501261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582876664778424967667507 874314997167637451501261)
          ·
            refine ⟨327868123937864044312973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 874314997167637451501261 327868123937864044312973)
            ·
              refine ⟨122950546476699016617365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327868123937864044312973 122950546476699016617365)
              ·
                refine ⟨5763306866095266403939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122950546476699016617365 5763306866095266403939)
                ·
                  rfl

theorem cell20_37881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_37881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37881 prefixEnd_37881 := by exact prefixLift 37881
  have htrace : WordTrace (prefixWord ++ tailWord_37881) baseStart_37881 baseEnd_37881 := by
    simpa [prefixWord, tailWord_37881, baseEnd_37881] using wordTrace_append hprefix tailTrace_37881
  have hstable : (prefixWord ++ tailWord_37881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37881).length < 2 ^ (prefixWord ++ tailWord_37881).sum := by decide
  have hdescent : baseEnd_37881 < baseStart_37881 := by decide
  rcases family_descends (prefixWord ++ tailWord_37881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37898 : List Nat := [3, 1, 2, 2, 3, 3, 6]
def baseStart_37898 : Nat := 118140960795 + 37898 * 2 ^ 59
def prefixEnd_37898 : Nat := 4983230072969 + 3 ^ 40 * 37898 * 2
def baseEnd_37898 : Nat := 1921964429056588405009

theorem tailTrace_37898 : CollatzResearch.WordTrace tailWord_37898 prefixEnd_37898 1921964429056588405009 := by
  unfold tailWord_37898
  simp only [CollatzResearch.WordTrace]
  refine ⟨345563404177373327052587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 921502411139662205473565 345563404177373327052587)
  ·
    refine ⟨518345106266059990578881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 345563404177373327052587 518345106266059990578881)
    ·
      refine ⟨388758829699544992934161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 518345106266059990578881 388758829699544992934161)
      ·
        refine ⟨291569122274658744700621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388758829699544992934161 291569122274658744700621)
        ·
          refine ⟨109338420852997029262733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291569122274658744700621 109338420852997029262733)
          ·
            refine ⟨41001907819873885973525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109338420852997029262733 41001907819873885973525)
            ·
              refine ⟨1921964429056588405009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41001907819873885973525 1921964429056588405009)
              ·
                rfl

theorem cell20_37898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 6].length) (baseStart_37898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37898 prefixEnd_37898 := by exact prefixLift 37898
  have htrace : WordTrace (prefixWord ++ tailWord_37898) baseStart_37898 baseEnd_37898 := by
    simpa [prefixWord, tailWord_37898, baseEnd_37898] using wordTrace_append hprefix tailTrace_37898
  have hstable : (prefixWord ++ tailWord_37898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37898).length < 2 ^ (prefixWord ++ tailWord_37898).sum := by decide
  have hdescent : baseEnd_37898 < baseStart_37898 := by decide
  rcases family_descends (prefixWord ++ tailWord_37898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37919 : List Nat := [1, 1, 2, 4, 1, 3, 1, 7]
def baseStart_37919 : Nat := 118140960795 + 37919 * 2 ^ 59
def prefixEnd_37919 : Nat := 4983230072969 + 3 ^ 40 * 37919 * 2
def baseEnd_37919 : Nat := 5769088277908851981665

theorem tailTrace_37919 : CollatzResearch.WordTrace tailWord_37919 prefixEnd_37919 5769088277908851981665 := by
  unfold tailWord_37919
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383019549633413894724811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 922013033088942596483207 1383019549633413894724811)
  ·
    refine ⟨2074529324450120842087217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1383019549633413894724811 2074529324450120842087217)
    ·
      refine ⟨1555896993337590631565413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2074529324450120842087217 1555896993337590631565413)
      ·
        refine ⟨291730686250798243418515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1555896993337590631565413 291730686250798243418515)
        ·
          refine ⟨437596029376197365127773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291730686250798243418515 437596029376197365127773)
          ·
            refine ⟨164098511016074011922915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 437596029376197365127773 164098511016074011922915)
            ·
              refine ⟨246147766524111017884373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164098511016074011922915 246147766524111017884373)
              ·
                refine ⟨5769088277908851981665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 246147766524111017884373 5769088277908851981665)
                ·
                  rfl

theorem cell20_37919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_37919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37919 prefixEnd_37919 := by exact prefixLift 37919
  have htrace : WordTrace (prefixWord ++ tailWord_37919) baseStart_37919 baseEnd_37919 := by
    simpa [prefixWord, tailWord_37919, baseEnd_37919] using wordTrace_append hprefix tailTrace_37919
  have hstable : (prefixWord ++ tailWord_37919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37919).length < 2 ^ (prefixWord ++ tailWord_37919).sum := by decide
  have hdescent : baseEnd_37919 < baseStart_37919 := by decide
  rcases family_descends (prefixWord ++ tailWord_37919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37922 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_37922 : Nat := 118140960795 + 37922 * 2 ^ 59
def prefixEnd_37922 : Nat := 4983230072969 + 3 ^ 40 * 37922 * 2
def baseEnd_37922 : Nat := 17308634115471878844983

theorem tailTrace_37922 : CollatzResearch.WordTrace tailWord_37922 prefixEnd_37922 17308634115471878844983 := by
  unfold tailWord_37922
  simp only [CollatzResearch.WordTrace]
  refine ⟨345782242155636351771005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 922085979081696938056013 345782242155636351771005)
  ·
    refine ⟨129668340808363631914127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 345782242155636351771005 129668340808363631914127)
    ·
      refine ⟨194502511212545447871191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129668340808363631914127 194502511212545447871191)
      ·
        refine ⟨291753766818818171806787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194502511212545447871191 291753766818818171806787)
        ·
          refine ⟨437630650228227257710181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291753766818818171806787 437630650228227257710181)
          ·
            refine ⟨82055746917792610820659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 437630650228227257710181 82055746917792610820659)
            ·
              refine ⟨123083620376688916230989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82055746917792610820659 123083620376688916230989)
              ·
                refine ⟨46156357641258343586621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123083620376688916230989 46156357641258343586621)
                ·
                  refine ⟨17308634115471878844983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46156357641258343586621 17308634115471878844983)
                  ·
                    rfl

theorem cell20_37922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_37922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_37922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_37922 prefixEnd_37922 := by exact prefixLift 37922
  have htrace : WordTrace (prefixWord ++ tailWord_37922) baseStart_37922 baseEnd_37922 := by
    simpa [prefixWord, tailWord_37922, baseEnd_37922] using wordTrace_append hprefix tailTrace_37922
  have hstable : (prefixWord ++ tailWord_37922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37922).length < 2 ^ (prefixWord ++ tailWord_37922).sum := by decide
  have hdescent : baseEnd_37922 < baseStart_37922 := by decide
  rcases family_descends (prefixWord ++ tailWord_37922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38046 : List Nat := [4, 3, 1, 1, 2, 3, 2, 4]
def baseStart_38046 : Nat := 118140960795 + 38046 * 2 ^ 59
def prefixEnd_38046 : Nat := 4983230072969 + 3 ^ 40 * 38046 * 2
def baseEnd_38046 : Nat := 5788410364759519570381

theorem tailTrace_38046 : CollatzResearch.WordTrace tailWord_38046 prefixEnd_38046 5788410364759519570381 := by
  unfold tailWord_38046
  simp only [CollatzResearch.WordTrace]
  refine ⟨173456452521664323074749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 925101080115543056398661 173456452521664323074749)
  ·
    refine ⟨65046169695624121153031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173456452521664323074749 65046169695624121153031)
    ·
      refine ⟨97569254543436181729547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65046169695624121153031 97569254543436181729547)
      ·
        refine ⟨146353881815154272594321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97569254543436181729547 146353881815154272594321)
        ·
          refine ⟨109765411361365704445741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146353881815154272594321 109765411361365704445741)
          ·
            refine ⟨41162029260512139167153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109765411361365704445741 41162029260512139167153)
            ·
              refine ⟨30871521945384104375365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41162029260512139167153 30871521945384104375365)
              ·
                refine ⟨5788410364759519570381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30871521945384104375365 5788410364759519570381)
                ·
                  rfl

theorem cell20_38046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_38046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38046 prefixEnd_38046 := by exact prefixLift 38046
  have htrace : WordTrace (prefixWord ++ tailWord_38046) baseStart_38046 baseEnd_38046 := by
    simpa [prefixWord, tailWord_38046, baseEnd_38046] using wordTrace_append hprefix tailTrace_38046
  have hstable : (prefixWord ++ tailWord_38046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38046).length < 2 ^ (prefixWord ++ tailWord_38046).sum := by decide
  have hdescent : baseEnd_38046 < baseStart_38046 := by decide
  rcases family_descends (prefixWord ++ tailWord_38046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38116 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_38116 : Nat := 118140960795 + 38116 * 2 ^ 59
def prefixEnd_38116 : Nat := 4983230072969 + 3 ^ 40 * 38116 * 2
def baseEnd_38116 : Nat := 17397181001669426377523

theorem tailTrace_38116 : CollatzResearch.WordTrace tailWord_38116 prefixEnd_38116 17397181001669426377523 := by
  unfold tailWord_38116
  simp only [CollatzResearch.WordTrace]
  refine ⟨695102364959858269823101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 926803153279811026430801 695102364959858269823101)
  ·
    refine ⟨260663386859946851183663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 695102364959858269823101 260663386859946851183663)
    ·
      refine ⟨390995080289920276775495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260663386859946851183663 390995080289920276775495)
      ·
        refine ⟨586492620434880415163243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390995080289920276775495 586492620434880415163243)
        ·
          refine ⟨879738930652320622744865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586492620434880415163243 879738930652320622744865)
          ·
            refine ⟨659804197989240467058649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879738930652320622744865 659804197989240467058649)
            ·
              refine ⟨494853148491930350293987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659804197989240467058649 494853148491930350293987)
              ·
                refine ⟨742279722737895525440981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494853148491930350293987 742279722737895525440981)
                ·
                  refine ⟨17397181001669426377523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 742279722737895525440981 17397181001669426377523)
                  ·
                    rfl

theorem cell20_38116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_38116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38116 prefixEnd_38116 := by exact prefixLift 38116
  have htrace : WordTrace (prefixWord ++ tailWord_38116) baseStart_38116 baseEnd_38116 := by
    simpa [prefixWord, tailWord_38116, baseEnd_38116] using wordTrace_append hprefix tailTrace_38116
  have hstable : (prefixWord ++ tailWord_38116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38116).length < 2 ^ (prefixWord ++ tailWord_38116).sum := by decide
  have hdescent : baseEnd_38116 < baseStart_38116 := by decide
  rcases family_descends (prefixWord ++ tailWord_38116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38147 : List Nat := [1, 1, 1, 3, 2, 4, 3, 5]
def baseStart_38147 : Nat := 118140960795 + 38147 * 2 ^ 59
def prefixEnd_38147 : Nat := 4983230072969 + 3 ^ 40 * 38147 * 2
def baseEnd_38147 : Nat := 5803776748790365448021

theorem tailTrace_38147 : CollatzResearch.WordTrace tailWord_38147 prefixEnd_38147 5803776748790365448021 := by
  unfold tailWord_38147
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391335392807408834024695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 927556928538272556016463 1391335392807408834024695)
  ·
    refine ⟨2087003089211113251037043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1391335392807408834024695 2087003089211113251037043)
    ·
      refine ⟨3130504633816669876555565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2087003089211113251037043 3130504633816669876555565)
      ·
        refine ⟨1173939237681251203708337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3130504633816669876555565 1173939237681251203708337)
        ·
          refine ⟨880454428260938402781253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173939237681251203708337 880454428260938402781253)
          ·
            refine ⟨165085205298925950521485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 880454428260938402781253 165085205298925950521485)
            ·
              refine ⟨61906951987097231445557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165085205298925950521485 61906951987097231445557)
              ·
                refine ⟨5803776748790365448021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61906951987097231445557 5803776748790365448021)
                ·
                  rfl

theorem cell20_38147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_38147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38147 prefixEnd_38147 := by exact prefixLift 38147
  have htrace : WordTrace (prefixWord ++ tailWord_38147) baseStart_38147 baseEnd_38147 := by
    simpa [prefixWord, tailWord_38147, baseEnd_38147] using wordTrace_append hprefix tailTrace_38147
  have hstable : (prefixWord ++ tailWord_38147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38147).length < 2 ^ (prefixWord ++ tailWord_38147).sum := by decide
  have hdescent : baseEnd_38147 < baseStart_38147 := by decide
  rcases family_descends (prefixWord ++ tailWord_38147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38154 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_38154 : Nat := 118140960795 + 38154 * 2 ^ 59
def prefixEnd_38154 : Nat := 4983230072969 + 3 ^ 40 * 38154 * 2
def baseEnd_38154 : Nat := 17414525237110183110701

theorem tailTrace_38154 : CollatzResearch.WordTrace tailWord_38154 prefixEnd_38154 17414525237110183110701 := by
  unfold tailWord_38154
  simp only [CollatzResearch.WordTrace]
  refine ⟨347897675945512257382379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 927727135854699353019677 347897675945512257382379)
  ·
    refine ⟨521846513918268386073569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347897675945512257382379 521846513918268386073569)
    ·
      refine ⟨391384885438701289555177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 521846513918268386073569 391384885438701289555177)
      ·
        refine ⟨293538664079025967166383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391384885438701289555177 293538664079025967166383)
        ·
          refine ⟨440307996118538950749575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293538664079025967166383 440307996118538950749575)
          ·
            refine ⟨660461994177808426124363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440307996118538950749575 660461994177808426124363)
            ·
              refine ⟨990692991266712639186545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660461994177808426124363 990692991266712639186545)
              ·
                refine ⟨743019743450034479389909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990692991266712639186545 743019743450034479389909)
                ·
                  refine ⟨17414525237110183110701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 743019743450034479389909 17414525237110183110701)
                  ·
                    rfl

theorem cell20_38154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_38154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38154 prefixEnd_38154 := by exact prefixLift 38154
  have htrace : WordTrace (prefixWord ++ tailWord_38154) baseStart_38154 baseEnd_38154 := by
    simpa [prefixWord, tailWord_38154, baseEnd_38154] using wordTrace_append hprefix tailTrace_38154
  have hstable : (prefixWord ++ tailWord_38154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38154).length < 2 ^ (prefixWord ++ tailWord_38154).sum := by decide
  have hdescent : baseEnd_38154 < baseStart_38154 := by decide
  rcases family_descends (prefixWord ++ tailWord_38154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38192 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_38192 : Nat := 118140960795 + 38192 * 2 ^ 59
def prefixEnd_38192 : Nat := 4983230072969 + 3 ^ 40 * 38192 * 2
def baseEnd_38192 : Nat := 17431869472550939843879

theorem tailTrace_38192 : CollatzResearch.WordTrace tailWord_38192 prefixEnd_38192 17431869472550939843879 := by
  unfold tailWord_38192
  simp only [CollatzResearch.WordTrace]
  refine ⟨696488338822190759706415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 928651118429587679608553 696488338822190759706415)
  ·
    refine ⟨1044732508233286139559623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 696488338822190759706415 1044732508233286139559623)
    ·
      refine ⟨1567098762349929209339435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044732508233286139559623 1567098762349929209339435)
      ·
        refine ⟨2350648143524893814009153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567098762349929209339435 2350648143524893814009153)
        ·
          refine ⟨1762986107643670360506865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2350648143524893814009153 1762986107643670360506865)
          ·
            refine ⟨1322239580732752770380149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762986107643670360506865 1322239580732752770380149)
            ·
              refine ⟨123959960693695572223139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1322239580732752770380149 123959960693695572223139)
              ·
                refine ⟨185939941040543358334709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123959960693695572223139 185939941040543358334709)
                ·
                  refine ⟨17431869472550939843879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185939941040543358334709 17431869472550939843879)
                  ·
                    rfl

theorem cell20_38192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_38192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38192 prefixEnd_38192 := by exact prefixLift 38192
  have htrace : WordTrace (prefixWord ++ tailWord_38192) baseStart_38192 baseEnd_38192 := by
    simpa [prefixWord, tailWord_38192, baseEnd_38192] using wordTrace_append hprefix tailTrace_38192
  have hstable : (prefixWord ++ tailWord_38192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38192).length < 2 ^ (prefixWord ++ tailWord_38192).sum := by decide
  have hdescent : baseEnd_38192 < baseStart_38192 := by decide
  rcases family_descends (prefixWord ++ tailWord_38192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38195 : List Nat := [1, 1, 1, 2, 5, 2, 2, 4, 2]
def baseStart_38195 : Nat := 118140960795 + 38195 * 2 ^ 59
def prefixEnd_38195 : Nat := 4983230072969 + 3 ^ 40 * 38195 * 2
def baseEnd_38195 : Nat := 17433238754296262743867

theorem tailTrace_38195 : CollatzResearch.WordTrace tailWord_38195 prefixEnd_38195 17433238754296262743867 := by
  unfold tailWord_38195
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393086096633513031772039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 928724064422342021181359 1393086096633513031772039)
  ·
    refine ⟨2089629144950269547658059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393086096633513031772039 2089629144950269547658059)
    ·
      refine ⟨3134443717425404321487089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2089629144950269547658059 3134443717425404321487089)
      ·
        refine ⟨2350832788069053241115317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3134443717425404321487089 2350832788069053241115317)
        ·
          refine ⟨220390573881473741354561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2350832788069053241115317 220390573881473741354561)
          ·
            refine ⟨165292930411105306015921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220390573881473741354561 165292930411105306015921)
            ·
              refine ⟨123969697808328979511941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165292930411105306015921 123969697808328979511941)
              ·
                refine ⟨23244318339061683658489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123969697808328979511941 23244318339061683658489)
                ·
                  refine ⟨17433238754296262743867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23244318339061683658489 17433238754296262743867)
                  ·
                    rfl

theorem cell20_38195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 2].length) (baseStart_38195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38195 prefixEnd_38195 := by exact prefixLift 38195
  have htrace : WordTrace (prefixWord ++ tailWord_38195) baseStart_38195 baseEnd_38195 := by
    simpa [prefixWord, tailWord_38195, baseEnd_38195] using wordTrace_append hprefix tailTrace_38195
  have hstable : (prefixWord ++ tailWord_38195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38195).length < 2 ^ (prefixWord ++ tailWord_38195).sum := by decide
  have hdescent : baseEnd_38195 < baseStart_38195 := by decide
  rcases family_descends (prefixWord ++ tailWord_38195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38233 : List Nat := [1, 2, 1, 2, 2, 2, 5, 3, 2]
def baseStart_38233 : Nat := 118140960795 + 38233 * 2 ^ 59
def prefixEnd_38233 : Nat := 4983230072969 + 3 ^ 40 * 38233 * 2
def baseEnd_38233 : Nat := 17450582989737019477045

theorem tailTrace_38233 : CollatzResearch.WordTrace tailWord_38233 prefixEnd_38233 17450582989737019477045 := by
  unfold tailWord_38233
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394472070495845521655353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 929648046997230347770235 1394472070495845521655353)
  ·
    refine ⟨1045854052871884141241515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1394472070495845521655353 1045854052871884141241515)
    ·
      refine ⟨1568781079307826211862273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045854052871884141241515 1568781079307826211862273)
      ·
        refine ⟨1176585809480869658896705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568781079307826211862273 1176585809480869658896705)
        ·
          refine ⟨882439357110652244172529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176585809480869658896705 882439357110652244172529)
          ·
            refine ⟨661829517832989183129397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 882439357110652244172529 661829517832989183129397)
            ·
              refine ⟨62046517296842735918381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 661829517832989183129397 62046517296842735918381)
              ·
                refine ⟨23267443986316025969393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62046517296842735918381 23267443986316025969393)
                ·
                  refine ⟨17450582989737019477045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23267443986316025969393 17450582989737019477045)
                  ·
                    rfl

theorem cell20_38233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_38233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38233 prefixEnd_38233 := by exact prefixLift 38233
  have htrace : WordTrace (prefixWord ++ tailWord_38233) baseStart_38233 baseEnd_38233 := by
    simpa [prefixWord, tailWord_38233, baseEnd_38233] using wordTrace_append hprefix tailTrace_38233
  have hstable : (prefixWord ++ tailWord_38233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38233).length < 2 ^ (prefixWord ++ tailWord_38233).sum := by decide
  have hdescent : baseEnd_38233 < baseStart_38233 := by decide
  rcases family_descends (prefixWord ++ tailWord_38233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38250 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_38250 : Nat := 118140960795 + 38250 * 2 ^ 59
def prefixEnd_38250 : Nat := 4983230072969 + 3 ^ 40 * 38250 * 2
def baseEnd_38250 : Nat := 17458342252960515910309

theorem tailTrace_38250 : CollatzResearch.WordTrace tailWord_38250 prefixEnd_38250 17458342252960515910309 := by
  unfold tailWord_38250
  simp only [CollatzResearch.WordTrace]
  refine ⟨348773027858564356256051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 930061407622838283349469 348773027858564356256051)
  ·
    refine ⟨523159541787846534384077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 348773027858564356256051 523159541787846534384077)
    ·
      refine ⟨196184828170442450394029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 523159541787846534384077 196184828170442450394029)
      ·
        refine ⟨73569310563915918897761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196184828170442450394029 73569310563915918897761)
        ·
          refine ⟨55176982922936939173321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73569310563915918897761 55176982922936939173321)
          ·
            refine ⟨41382737192202704379991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55176982922936939173321 41382737192202704379991)
            ·
              refine ⟨62074105788304056569987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41382737192202704379991 62074105788304056569987)
              ·
                refine ⟨93111158682456084854981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62074105788304056569987 93111158682456084854981)
                ·
                  refine ⟨17458342252960515910309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93111158682456084854981 17458342252960515910309)
                  ·
                    rfl

theorem cell20_38250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_38250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38250 prefixEnd_38250 := by exact prefixLift 38250
  have htrace : WordTrace (prefixWord ++ tailWord_38250) baseStart_38250 baseEnd_38250 := by
    simpa [prefixWord, tailWord_38250, baseEnd_38250] using wordTrace_append hprefix tailTrace_38250
  have hstable : (prefixWord ++ tailWord_38250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38250).length < 2 ^ (prefixWord ++ tailWord_38250).sum := by decide
  have hdescent : baseEnd_38250 < baseStart_38250 := by decide
  rcases family_descends (prefixWord ++ tailWord_38250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38312 : List Nat := [2, 1, 6, 1, 3, 1, 1, 5]
def baseStart_38312 : Nat := 118140960795 + 38312 * 2 ^ 59
def prefixEnd_38312 : Nat := 4983230072969 + 3 ^ 40 * 38312 * 2
def baseEnd_38312 : Nat := 5828880247454618614463

theorem tailTrace_38312 : CollatzResearch.WordTrace tailWord_38312 prefixEnd_38312 5828880247454618614463 := by
  unfold tailWord_38312
  simp only [CollatzResearch.WordTrace]
  refine ⟨698676718604821006890595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 931568958139761342520793 698676718604821006890595)
  ·
    refine ⟨1048015077907231510335893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698676718604821006890595 1048015077907231510335893)
    ·
      refine ⟨49125706776901477046995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1048015077907231510335893 49125706776901477046995)
      ·
        refine ⟨73688560165352215570493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49125706776901477046995 73688560165352215570493)
        ·
          refine ⟨27633210062007080838935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73688560165352215570493 27633210062007080838935)
          ·
            refine ⟨41449815093010621258403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27633210062007080838935 41449815093010621258403)
            ·
              refine ⟨62174722639515931887605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41449815093010621258403 62174722639515931887605)
              ·
                refine ⟨5828880247454618614463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62174722639515931887605 5828880247454618614463)
                ·
                  rfl

theorem cell20_38312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_38312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38312 prefixEnd_38312 := by exact prefixLift 38312
  have htrace : WordTrace (prefixWord ++ tailWord_38312) baseStart_38312 baseEnd_38312 := by
    simpa [prefixWord, tailWord_38312, baseEnd_38312] using wordTrace_append hprefix tailTrace_38312
  have hstable : (prefixWord ++ tailWord_38312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38312).length < 2 ^ (prefixWord ++ tailWord_38312).sum := by decide
  have hdescent : baseEnd_38312 < baseStart_38312 := by decide
  rcases family_descends (prefixWord ++ tailWord_38312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38320 : List Nat := [2, 1, 1, 1, 2, 1, 1, 11]
def baseStart_38320 : Nat := 118140960795 + 38320 * 2 ^ 59
def prefixEnd_38320 : Nat := 4983230072969 + 3 ^ 40 * 38320 * 2
def baseEnd_38320 : Nat := 5830097386783794525563

theorem tailTrace_38320 : CollatzResearch.WordTrace tailWord_38320 prefixEnd_38320 5830097386783794525563 := by
  unfold tailWord_38320
  simp only [CollatzResearch.WordTrace]
  refine ⟨698822610590329690036207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 931763480787106253381609 698822610590329690036207)
  ·
    refine ⟨1048233915885494535054311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698822610590329690036207 1048233915885494535054311)
    ·
      refine ⟨1572350873828241802581467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1048233915885494535054311 1572350873828241802581467)
      ·
        refine ⟨2358526310742362703872201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572350873828241802581467 2358526310742362703872201)
        ·
          refine ⟨1768894733056772027904151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2358526310742362703872201 1768894733056772027904151)
          ·
            refine ⟨2653342099585158041856227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768894733056772027904151 2653342099585158041856227)
            ·
              refine ⟨3980013149377737062784341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653342099585158041856227 3980013149377737062784341)
              ·
                refine ⟨5830097386783794525563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 3980013149377737062784341 5830097386783794525563)
                ·
                  rfl

theorem cell20_38320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_38320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38320 prefixEnd_38320 := by exact prefixLift 38320
  have htrace : WordTrace (prefixWord ++ tailWord_38320) baseStart_38320 baseEnd_38320 := by
    simpa [prefixWord, tailWord_38320, baseEnd_38320] using wordTrace_append hprefix tailTrace_38320
  have hstable : (prefixWord ++ tailWord_38320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38320).length < 2 ^ (prefixWord ++ tailWord_38320).sum := by decide
  have hdescent : baseEnd_38320 < baseStart_38320 := by decide
  rcases family_descends (prefixWord ++ tailWord_38320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38344 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_38344 : Nat := 118140960795 + 38344 * 2 ^ 59
def prefixEnd_38344 : Nat := 4983230072969 + 3 ^ 40 * 38344 * 2
def baseEnd_38344 : Nat := 17501246414313966776591

theorem tailTrace_38344 : CollatzResearch.WordTrace tailWord_38344 prefixEnd_38344 17501246414313966776591 := by
  unfold tailWord_38344
  simp only [CollatzResearch.WordTrace]
  refine ⟨699260286546855739473043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 932347048729140985964057 699260286546855739473043)
  ·
    refine ⟨1048890429820283609209565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699260286546855739473043 1048890429820283609209565)
    ·
      refine ⟨393333911182606353453587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1048890429820283609209565 393333911182606353453587)
      ·
        refine ⟨590000866773909530180381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393333911182606353453587 590000866773909530180381)
        ·
          refine ⟨221250325040216073817643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590000866773909530180381 221250325040216073817643)
          ·
            refine ⟨331875487560324110726465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221250325040216073817643 331875487560324110726465)
            ·
              refine ⟨248906615670243083044849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331875487560324110726465 248906615670243083044849)
              ·
                refine ⟨186679961752682312283637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248906615670243083044849 186679961752682312283637)
                ·
                  refine ⟨17501246414313966776591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186679961752682312283637 17501246414313966776591)
                  ·
                    rfl

theorem cell20_38344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_38344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38344 prefixEnd_38344 := by exact prefixLift 38344
  have htrace : WordTrace (prefixWord ++ tailWord_38344) baseStart_38344 baseEnd_38344 := by
    simpa [prefixWord, tailWord_38344, baseEnd_38344] using wordTrace_append hprefix tailTrace_38344
  have hstable : (prefixWord ++ tailWord_38344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38344).length < 2 ^ (prefixWord ++ tailWord_38344).sum := by decide
  have hdescent : baseEnd_38344 < baseStart_38344 := by decide
  rcases family_descends (prefixWord ++ tailWord_38344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38361 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 3]
def baseStart_38361 : Nat := 118140960795 + 38361 * 2 ^ 59
def prefixEnd_38361 : Nat := 4983230072969 + 3 ^ 40 * 38361 * 2
def baseEnd_38361 : Nat := 17509005677537463209855

theorem tailTrace_38361 : CollatzResearch.WordTrace tailWord_38361 prefixEnd_38361 17509005677537463209855 := by
  unfold tailWord_38361
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399140614032123382314937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 932760409354748921543291 1399140614032123382314937)
  ·
    refine ⟨1049355460524092536736203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1399140614032123382314937 1049355460524092536736203)
    ·
      refine ⟨1574033190786138805104305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049355460524092536736203 1574033190786138805104305)
      ·
        refine ⟨1180524893089604103828229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1574033190786138805104305 1180524893089604103828229)
        ·
          refine ⟨221348417454300769467793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1180524893089604103828229 221348417454300769467793)
          ·
            refine ⟨166011313090725577100845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221348417454300769467793 166011313090725577100845)
            ·
              refine ⟨62254242409022091412817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166011313090725577100845 62254242409022091412817)
              ·
                refine ⟨46690681806766568559613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62254242409022091412817 46690681806766568559613)
                ·
                  refine ⟨17509005677537463209855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46690681806766568559613 17509005677537463209855)
                  ·
                    rfl

theorem cell20_38361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_38361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38361 prefixEnd_38361 := by exact prefixLift 38361
  have htrace : WordTrace (prefixWord ++ tailWord_38361) baseStart_38361 baseEnd_38361 := by
    simpa [prefixWord, tailWord_38361, baseEnd_38361] using wordTrace_append hprefix tailTrace_38361
  have hstable : (prefixWord ++ tailWord_38361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38361).length < 2 ^ (prefixWord ++ tailWord_38361).sum := by decide
  have hdescent : baseEnd_38361 < baseStart_38361 := by decide
  rcases family_descends (prefixWord ++ tailWord_38361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38392 : List Nat := [2, 1, 2, 1, 1, 7, 2, 4]
def baseStart_38392 : Nat := 118140960795 + 38392 * 2 ^ 59
def prefixEnd_38392 : Nat := 4983230072969 + 3 ^ 40 * 38392 * 2
def baseEnd_38392 : Nat := 5841051640746377725465

theorem tailTrace_38392 : CollatzResearch.WordTrace tailWord_38392 prefixEnd_38392 5841051640746377725465 := by
  unfold tailWord_38392
  simp only [CollatzResearch.WordTrace]
  refine ⟨700135638459907838346715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 933514184613210451128953 700135638459907838346715)
  ·
    refine ⟨1050203457689861757520073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 700135638459907838346715 1050203457689861757520073)
    ·
      refine ⟨787652593267396318140055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050203457689861757520073 787652593267396318140055)
      ·
        refine ⟨1181478889901094477210083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787652593267396318140055 1181478889901094477210083)
        ·
          refine ⟨1772218334851641715815125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181478889901094477210083 1772218334851641715815125)
          ·
            refine ⟨41536367223085352714417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1772218334851641715815125 41536367223085352714417)
            ·
              refine ⟨31152275417314014535813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41536367223085352714417 31152275417314014535813)
              ·
                refine ⟨5841051640746377725465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31152275417314014535813 5841051640746377725465)
                ·
                  rfl

theorem cell20_38392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_38392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38392 prefixEnd_38392 := by exact prefixLift 38392
  have htrace : WordTrace (prefixWord ++ tailWord_38392) baseStart_38392 baseEnd_38392 := by
    simpa [prefixWord, tailWord_38392, baseEnd_38392] using wordTrace_append hprefix tailTrace_38392
  have hstable : (prefixWord ++ tailWord_38392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38392).length < 2 ^ (prefixWord ++ tailWord_38392).sum := by decide
  have hdescent : baseEnd_38392 < baseStart_38392 := by decide
  rcases family_descends (prefixWord ++ tailWord_38392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38398 : List Nat := [4, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_38398 : Nat := 118140960795 + 38398 * 2 ^ 59
def prefixEnd_38398 : Nat := 4983230072969 + 3 ^ 40 * 38398 * 2
def baseEnd_38398 : Nat := 17525893485729778976371

theorem tailTrace_38398 : CollatzResearch.WordTrace tailWord_38398 prefixEnd_38398 17525893485729778976371 := by
  unfold tailWord_38398
  simp only [CollatzResearch.WordTrace]
  refine ⟨175061264362259837676481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 933660076598719134274565 175061264362259837676481)
  ·
    refine ⟨131295948271694878257361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175061264362259837676481 131295948271694878257361)
    ·
      refine ⟨98471961203771158693021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131295948271694878257361 98471961203771158693021)
      ·
        refine ⟨36926985451414184509883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98471961203771158693021 36926985451414184509883)
        ·
          refine ⟨55390478177121276764825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36926985451414184509883 55390478177121276764825)
          ·
            refine ⟨41542858632840957573619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55390478177121276764825 41542858632840957573619)
            ·
              refine ⟨62314287949261436360429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41542858632840957573619 62314287949261436360429)
              ·
                refine ⟨23367857980973038635161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62314287949261436360429 23367857980973038635161)
                ·
                  refine ⟨17525893485729778976371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23367857980973038635161 17525893485729778976371)
                  ·
                    rfl

theorem cell20_38398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_38398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38398 prefixEnd_38398 := by exact prefixLift 38398
  have htrace : WordTrace (prefixWord ++ tailWord_38398) baseStart_38398 baseEnd_38398 := by
    simpa [prefixWord, tailWord_38398, baseEnd_38398] using wordTrace_append hprefix tailTrace_38398
  have hstable : (prefixWord ++ tailWord_38398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38398).length < 2 ^ (prefixWord ++ tailWord_38398).sum := by decide
  have hdescent : baseEnd_38398 < baseStart_38398 := by decide
  rcases family_descends (prefixWord ++ tailWord_38398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38503 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_38503 : Nat := 118140960795 + 38503 * 2 ^ 59
def prefixEnd_38503 : Nat := 4983230072969 + 3 ^ 40 * 38503 * 2
def baseEnd_38503 : Nat := 17573818346816080475941

theorem tailTrace_38503 : CollatzResearch.WordTrace tailWord_38503 prefixEnd_38503 17573818346816080475941 := by
  unfold tailWord_38503
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404319779517681633984163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 936213186345121089322775 1404319779517681633984163)
  ·
    refine ⟨2106479669276522450976245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1404319779517681633984163 2106479669276522450976245)
    ·
      refine ⟨197482468994673979779023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2106479669276522450976245 197482468994673979779023)
      ·
        refine ⟨296223703492010969668535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197482468994673979779023 296223703492010969668535)
        ·
          refine ⟨444335555238016454502803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296223703492010969668535 444335555238016454502803)
          ·
            refine ⟨666503332857024681754205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444335555238016454502803 666503332857024681754205)
            ·
              refine ⟨249938749821384255657827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666503332857024681754205 249938749821384255657827)
              ·
                refine ⟨374908124732076383486741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249938749821384255657827 374908124732076383486741)
                ·
                  refine ⟨17573818346816080475941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 374908124732076383486741 17573818346816080475941)
                  ·
                    rfl

theorem cell20_38503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_38503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38503 prefixEnd_38503 := by exact prefixLift 38503
  have htrace : WordTrace (prefixWord ++ tailWord_38503) baseStart_38503 baseEnd_38503 := by
    simpa [prefixWord, tailWord_38503, baseEnd_38503] using wordTrace_append hprefix tailTrace_38503
  have hstable : (prefixWord ++ tailWord_38503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38503).length < 2 ^ (prefixWord ++ tailWord_38503).sum := by decide
  have hdescent : baseEnd_38503 < baseStart_38503 := by decide
  rcases family_descends (prefixWord ++ tailWord_38503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38506 : List Nat := [3, 1, 3, 2, 1, 3, 3, 4]
def baseStart_38506 : Nat := 118140960795 + 38506 * 2 ^ 59
def prefixEnd_38506 : Nat := 4983230072969 + 3 ^ 40 * 38506 * 2
def baseEnd_38506 : Nat := 5858395876187134458643

theorem tailTrace_38506 : CollatzResearch.WordTrace tailWord_38506 prefixEnd_38506 5858395876187134458643 := by
  unfold tailWord_38506
  simp only [CollatzResearch.WordTrace]
  refine ⟨351107299626703286585843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 936286132337875430895581 351107299626703286585843)
  ·
    refine ⟨526660949440054929878765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351107299626703286585843 526660949440054929878765)
    ·
      refine ⟨197497856040020598704537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 526660949440054929878765 197497856040020598704537)
      ·
        refine ⟨148123392030015449028403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197497856040020598704537 148123392030015449028403)
        ·
          refine ⟨222185088045023173542605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148123392030015449028403 222185088045023173542605)
          ·
            refine ⟨83319408016883690078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222185088045023173542605 83319408016883690078477)
            ·
              refine ⟨31244778006331383779429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83319408016883690078477 31244778006331383779429)
              ·
                refine ⟨5858395876187134458643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31244778006331383779429 5858395876187134458643)
                ·
                  rfl

theorem cell20_38506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_38506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38506 prefixEnd_38506 := by exact prefixLift 38506
  have htrace : WordTrace (prefixWord ++ tailWord_38506) baseStart_38506 baseEnd_38506 := by
    simpa [prefixWord, tailWord_38506, baseEnd_38506] using wordTrace_append hprefix tailTrace_38506
  have hstable : (prefixWord ++ tailWord_38506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38506).length < 2 ^ (prefixWord ++ tailWord_38506).sum := by decide
  have hdescent : baseEnd_38506 < baseStart_38506 := by decide
  rcases family_descends (prefixWord ++ tailWord_38506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38565 : List Nat := [1, 3, 1, 2, 1, 2, 6, 4]
def baseStart_38565 : Nat := 118140960795 + 38565 * 2 ^ 59
def prefixEnd_38565 : Nat := 4983230072969 + 3 ^ 40 * 38565 * 2
def baseEnd_38565 : Nat := 5867372278739806803007

theorem tailTrace_38565 : CollatzResearch.WordTrace tailWord_38565 prefixEnd_38565 5867372278739806803007 := by
  unfold tailWord_38565
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406581105293066222741149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 937720736862044148494099 1406581105293066222741149)
  ·
    refine ⟨527467914484899833527931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1406581105293066222741149 527467914484899833527931)
    ·
      refine ⟨791201871727349750291897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527467914484899833527931 791201871727349750291897)
      ·
        refine ⟨593401403795512312718923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 791201871727349750291897 593401403795512312718923)
        ·
          refine ⟨890102105693268469078385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593401403795512312718923 890102105693268469078385)
          ·
            refine ⟨667576579269951351808789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890102105693268469078385 667576579269951351808789)
            ·
              refine ⟨31292652153278969616037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 667576579269951351808789 31292652153278969616037)
              ·
                refine ⟨5867372278739806803007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31292652153278969616037 5867372278739806803007)
                ·
                  rfl

theorem cell20_38565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_38565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38565 prefixEnd_38565 := by exact prefixLift 38565
  have htrace : WordTrace (prefixWord ++ tailWord_38565) baseStart_38565 baseEnd_38565 := by
    simpa [prefixWord, tailWord_38565, baseEnd_38565] using wordTrace_append hprefix tailTrace_38565
  have hstable : (prefixWord ++ tailWord_38565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38565).length < 2 ^ (prefixWord ++ tailWord_38565).sum := by decide
  have hdescent : baseEnd_38565 < baseStart_38565 := by decide
  rcases family_descends (prefixWord ++ tailWord_38565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38582 : List Nat := [5, 1, 3, 1, 1, 1, 8]
def baseStart_38582 : Nat := 118140960795 + 38582 * 2 ^ 59
def prefixEnd_38582 : Nat := 4983230072969 + 3 ^ 40 * 38582 * 2
def baseEnd_38582 : Nat := 1956652899938101871365

theorem tailTrace_38582 : CollatzResearch.WordTrace tailWord_38582 prefixEnd_38582 1956652899938101871365 := by
  unfold tailWord_38582
  simp only [CollatzResearch.WordTrace]
  refine ⟨87950071639467382881875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 938134097487652084073333 87950071639467382881875)
  ·
    refine ⟨131925107459201074322813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87950071639467382881875 131925107459201074322813)
    ·
      refine ⟨49471915297200402871055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131925107459201074322813 49471915297200402871055)
      ·
        refine ⟨74207872945800604306583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49471915297200402871055 74207872945800604306583)
        ·
          refine ⟨111311809418700906459875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74207872945800604306583 111311809418700906459875)
          ·
            refine ⟨166967714128051359689813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111311809418700906459875 166967714128051359689813)
            ·
              refine ⟨1956652899938101871365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 166967714128051359689813 1956652899938101871365)
              ·
                rfl

theorem cell20_38582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 8].length) (baseStart_38582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38582 prefixEnd_38582 := by exact prefixLift 38582
  have htrace : WordTrace (prefixWord ++ tailWord_38582) baseStart_38582 baseEnd_38582 := by
    simpa [prefixWord, tailWord_38582, baseEnd_38582] using wordTrace_append hprefix tailTrace_38582
  have hstable : (prefixWord ++ tailWord_38582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38582).length < 2 ^ (prefixWord ++ tailWord_38582).sum := by decide
  have hdescent : baseEnd_38582 < baseStart_38582 := by decide
  rcases family_descends (prefixWord ++ tailWord_38582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38586 : List Nat := [3, 1, 1, 1, 2, 4, 8]
def baseStart_38586 : Nat := 118140960795 + 38586 * 2 ^ 59
def prefixEnd_38586 : Nat := 4983230072969 + 3 ^ 40 * 38586 * 2
def baseEnd_38586 : Nat := 1956855756492964523215

theorem tailTrace_38586 : CollatzResearch.WordTrace tailWord_38586 prefixEnd_38586 1956855756492964523215 := by
  unfold tailWord_38586
  simp only [CollatzResearch.WordTrace]
  refine ⟨351836759554246702313903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 938231358811324539503741 351836759554246702313903)
  ·
    refine ⟨527755139331370053470855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351836759554246702313903 527755139331370053470855)
    ·
      refine ⟨791632708997055080206283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527755139331370053470855 791632708997055080206283)
      ·
        refine ⟨1187449063495582620309425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791632708997055080206283 1187449063495582620309425)
        ·
          refine ⟨890586797621686965232069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1187449063495582620309425 890586797621686965232069)
          ·
            refine ⟨166985024554066305981013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 890586797621686965232069 166985024554066305981013)
            ·
              refine ⟨1956855756492964523215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 166985024554066305981013 1956855756492964523215)
              ·
                rfl

theorem cell20_38586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 8].length) (baseStart_38586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38586 prefixEnd_38586 := by exact prefixLift 38586
  have htrace : WordTrace (prefixWord ++ tailWord_38586) baseStart_38586 baseEnd_38586 := by
    simpa [prefixWord, tailWord_38586, baseEnd_38586] using wordTrace_append hprefix tailTrace_38586
  have hstable : (prefixWord ++ tailWord_38586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38586).length < 2 ^ (prefixWord ++ tailWord_38586).sum := by decide
  have hdescent : baseEnd_38586 < baseStart_38586 := by decide
  rcases family_descends (prefixWord ++ tailWord_38586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38624 : List Nat := [2, 1, 1, 3, 1, 2, 4, 6]
def baseStart_38624 : Nat := 118140960795 + 38624 * 2 ^ 59
def prefixEnd_38624 : Nat := 4983230072969 + 3 ^ 40 * 38624 * 2
def baseEnd_38624 : Nat := 5876348681292479147371

theorem tailTrace_38624 : CollatzResearch.WordTrace tailWord_38624 prefixEnd_38624 5876348681292479147371 := by
  unfold tailWord_38624
  simp only [CollatzResearch.WordTrace]
  refine ⟨704366506039659649569463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 939155341386212866092617 704366506039659649569463)
  ·
    refine ⟨1056549759059489474354195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 704366506039659649569463 1056549759059489474354195)
    ·
      refine ⟨1584824638589234211531293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056549759059489474354195 1584824638589234211531293)
      ·
        refine ⟨594309239470962829324235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1584824638589234211531293 594309239470962829324235)
        ·
          refine ⟨891463859206444243986353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594309239470962829324235 891463859206444243986353)
          ·
            refine ⟨668597894404833182989765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891463859206444243986353 668597894404833182989765)
            ·
              refine ⟨125362105200906221810581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 668597894404833182989765 125362105200906221810581)
              ·
                refine ⟨5876348681292479147371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125362105200906221810581 5876348681292479147371)
                ·
                  rfl

theorem cell20_38624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_38624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38624 prefixEnd_38624 := by exact prefixLift 38624
  have htrace : WordTrace (prefixWord ++ tailWord_38624) baseStart_38624 baseEnd_38624 := by
    simpa [prefixWord, tailWord_38624, baseEnd_38624] using wordTrace_append hprefix tailTrace_38624
  have hstable : (prefixWord ++ tailWord_38624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38624).length < 2 ^ (prefixWord ++ tailWord_38624).sum := by decide
  have hdescent : baseEnd_38624 < baseStart_38624 := by decide
  rcases family_descends (prefixWord ++ tailWord_38624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38689 : List Nat := [1, 2, 3, 2, 1, 4, 2, 3, 2]
def baseStart_38689 : Nat := 118140960795 + 38689 * 2 ^ 59
def prefixEnd_38689 : Nat := 4983230072969 + 3 ^ 40 * 38689 * 2
def baseEnd_38689 : Nat := 17658713815026100275181

theorem tailTrace_38689 : CollatzResearch.WordTrace tailWord_38689 prefixEnd_38689 17658713815026100275181 := by
  unfold tailWord_38689
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411103756843835400255121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 940735837895890266836747 1411103756843835400255121)
  ·
    refine ⟨1058327817632876550191341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1411103756843835400255121 1058327817632876550191341)
    ·
      refine ⟨396872931612328706321753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1058327817632876550191341 396872931612328706321753)
      ·
        refine ⟨297654698709246529741315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396872931612328706321753 297654698709246529741315)
        ·
          refine ⟨446482048063869794611973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297654698709246529741315 446482048063869794611973)
          ·
            refine ⟨83715384011975586489745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 446482048063869794611973 83715384011975586489745)
            ·
              refine ⟨62786538008981689867309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83715384011975586489745 62786538008981689867309)
              ·
                refine ⟨23544951753368133700241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62786538008981689867309 23544951753368133700241)
                ·
                  refine ⟨17658713815026100275181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23544951753368133700241 17658713815026100275181)
                  ·
                    rfl

theorem cell20_38689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_38689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38689 prefixEnd_38689 := by exact prefixLift 38689
  have htrace : WordTrace (prefixWord ++ tailWord_38689) baseStart_38689 baseEnd_38689 := by
    simpa [prefixWord, tailWord_38689, baseEnd_38689] using wordTrace_append hprefix tailTrace_38689
  have hstable : (prefixWord ++ tailWord_38689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38689).length < 2 ^ (prefixWord ++ tailWord_38689).sum := by decide
  have hdescent : baseEnd_38689 < baseStart_38689 := by decide
  rcases family_descends (prefixWord ++ tailWord_38689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38700 : List Nat := [2, 2, 1, 1, 1, 6, 7]
def baseStart_38700 : Nat := 118140960795 + 38700 * 2 ^ 59
def prefixEnd_38700 : Nat := 4983230072969 + 3 ^ 40 * 38700 * 2
def baseEnd_38700 : Nat := 1962637168306550100941

theorem tailTrace_38700 : CollatzResearch.WordTrace tailWord_38700 prefixEnd_38700 1962637168306550100941 := by
  unfold tailWord_38700
  simp only [CollatzResearch.WordTrace]
  refine ⟨705752479901992139452777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 941003306535989519270369 705752479901992139452777)
  ·
    refine ⟨529314359926494104589583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 705752479901992139452777 529314359926494104589583)
    ·
      refine ⟨793971539889741156884375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529314359926494104589583 793971539889741156884375)
      ·
        refine ⟨1190957309834611735326563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793971539889741156884375 1190957309834611735326563)
        ·
          refine ⟨1786435964751917602989845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190957309834611735326563 1786435964751917602989845)
          ·
            refine ⟨83739185847746137640149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1786435964751917602989845 83739185847746137640149)
            ·
              refine ⟨1962637168306550100941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83739185847746137640149 1962637168306550100941)
              ·
                rfl

theorem cell20_38700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 7].length) (baseStart_38700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38700 prefixEnd_38700 := by exact prefixLift 38700
  have htrace : WordTrace (prefixWord ++ tailWord_38700) baseStart_38700 baseEnd_38700 := by
    simpa [prefixWord, tailWord_38700, baseEnd_38700] using wordTrace_append hprefix tailTrace_38700
  have hstable : (prefixWord ++ tailWord_38700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38700).length < 2 ^ (prefixWord ++ tailWord_38700).sum := by decide
  have hdescent : baseEnd_38700 < baseStart_38700 := by decide
  rcases family_descends (prefixWord ++ tailWord_38700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38745 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_38745 : Nat := 118140960795 + 38745 * 2 ^ 59
def prefixEnd_38745 : Nat := 4983230072969 + 3 ^ 40 * 38745 * 2
def baseEnd_38745 : Nat := 17684273740938794408285

theorem tailTrace_38745 : CollatzResearch.WordTrace tailWord_38745 prefixEnd_38745 17684273740938794408285 := by
  unfold tailWord_38745
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413146244640956964293689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 942097496427304642862459 1413146244640956964293689)
  ·
    refine ⟨1059859683480717723220267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1413146244640956964293689 1059859683480717723220267)
    ·
      refine ⟨1589789525221076584830401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059859683480717723220267 1589789525221076584830401)
      ·
        refine ⟨1192342143915807438622801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1589789525221076584830401 1192342143915807438622801)
        ·
          refine ⟨894256607936855578967101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1192342143915807438622801 894256607936855578967101)
          ·
            refine ⟨335346227976320842112663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 894256607936855578967101 335346227976320842112663)
            ·
              refine ⟨503019341964481263168995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335346227976320842112663 503019341964481263168995)
              ·
                refine ⟨754529012946721894753493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503019341964481263168995 754529012946721894753493)
                ·
                  refine ⟨17684273740938794408285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 754529012946721894753493 17684273740938794408285)
                  ·
                    rfl

theorem cell20_38745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_38745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38745 prefixEnd_38745 := by exact prefixLift 38745
  have htrace : WordTrace (prefixWord ++ tailWord_38745) baseStart_38745 baseEnd_38745 := by
    simpa [prefixWord, tailWord_38745, baseEnd_38745] using wordTrace_append hprefix tailTrace_38745
  have hstable : (prefixWord ++ tailWord_38745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38745).length < 2 ^ (prefixWord ++ tailWord_38745).sum := by decide
  have hdescent : baseEnd_38745 < baseStart_38745 := by decide
  rcases family_descends (prefixWord ++ tailWord_38745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38755 : List Nat := [1, 1, 1, 5, 4, 2, 6]
def baseStart_38755 : Nat := 118140960795 + 38755 * 2 ^ 59
def prefixEnd_38755 : Nat := 4983230072969 + 3 ^ 40 * 38755 * 2
def baseEnd_38755 : Nat := 1965426445935911563879

theorem tailTrace_38755 : CollatzResearch.WordTrace tailWord_38755 prefixEnd_38755 1965426445935911563879 := by
  unfold tailWord_38755
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413510974604728672157719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 942340649736485781438479 1413510974604728672157719)
  ·
    refine ⟨2120266461907093008236579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1413510974604728672157719 2120266461907093008236579)
    ·
      refine ⟨3180399692860639512354869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120266461907093008236579 3180399692860639512354869)
      ·
        refine ⟨298162471205684954283269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3180399692860639512354869 298162471205684954283269)
        ·
          refine ⟨55905463351065928928113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298162471205684954283269 55905463351065928928113)
          ·
            refine ⟨41929097513299446696085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55905463351065928928113 41929097513299446696085)
            ·
              refine ⟨1965426445935911563879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41929097513299446696085 1965426445935911563879)
              ·
                rfl

theorem cell20_38755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 6].length) (baseStart_38755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38755 prefixEnd_38755 := by exact prefixLift 38755
  have htrace : WordTrace (prefixWord ++ tailWord_38755) baseStart_38755 baseEnd_38755 := by
    simpa [prefixWord, tailWord_38755, baseEnd_38755] using wordTrace_append hprefix tailTrace_38755
  have hstable : (prefixWord ++ tailWord_38755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38755).length < 2 ^ (prefixWord ++ tailWord_38755).sum := by decide
  have hdescent : baseEnd_38755 < baseStart_38755 := by decide
  rcases family_descends (prefixWord ++ tailWord_38755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38820 : List Nat := [2, 3, 1, 2, 1, 5, 2, 2, 2]
def baseStart_38820 : Nat := 118140960795 + 38820 * 2 ^ 59
def prefixEnd_38820 : Nat := 4983230072969 + 3 ^ 40 * 38820 * 2
def baseEnd_38820 : Nat := 17718505784571866907979

theorem tailTrace_38820 : CollatzResearch.WordTrace tailWord_38820 prefixEnd_38820 17718505784571866907979 := by
  unfold tailWord_38820
  simp only [CollatzResearch.WordTrace]
  refine ⟨707940859684622386636957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 943921146246163182182609 707940859684622386636957)
  ·
    refine ⟨265477822381733394988859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 707940859684622386636957 265477822381733394988859)
    ·
      refine ⟨398216733572600092483289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265477822381733394988859 398216733572600092483289)
      ·
        refine ⟨298662550179450069362467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398216733572600092483289 298662550179450069362467)
        ·
          refine ⟨447993825269175104043701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298662550179450069362467 447993825269175104043701)
          ·
            refine ⟨41999421118985166004097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 447993825269175104043701 41999421118985166004097)
            ·
              refine ⟨31499565839238874503073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41999421118985166004097 31499565839238874503073)
              ·
                refine ⟨23624674379429155877305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31499565839238874503073 23624674379429155877305)
                ·
                  refine ⟨17718505784571866907979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23624674379429155877305 17718505784571866907979)
                  ·
                    rfl

theorem cell20_38820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_38820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38820 prefixEnd_38820 := by exact prefixLift 38820
  have htrace : WordTrace (prefixWord ++ tailWord_38820) baseStart_38820 baseEnd_38820 := by
    simpa [prefixWord, tailWord_38820, baseEnd_38820] using wordTrace_append hprefix tailTrace_38820
  have hstable : (prefixWord ++ tailWord_38820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38820).length < 2 ^ (prefixWord ++ tailWord_38820).sum := by decide
  have hdescent : baseEnd_38820 < baseStart_38820 := by decide
  rcases family_descends (prefixWord ++ tailWord_38820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38821 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_38821 : Nat := 118140960795 + 38821 * 2 ^ 59
def prefixEnd_38821 : Nat := 4983230072969 + 3 ^ 40 * 38821 * 2
def baseEnd_38821 : Nat := 17718962211820307874641

theorem tailTrace_38821 : CollatzResearch.WordTrace tailWord_38821 prefixEnd_38821 17718962211820307874641 := by
  unfold tailWord_38821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415918192365621944060317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 943945461577081296040211 1415918192365621944060317)
  ·
    refine ⟨530969322137108229022619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1415918192365621944060317 530969322137108229022619)
    ·
      refine ⟨796453983205662343533929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530969322137108229022619 796453983205662343533929)
      ·
        refine ⟨597340487404246757650447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 796453983205662343533929 597340487404246757650447)
        ·
          refine ⟨896010731106370136475671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597340487404246757650447 896010731106370136475671)
          ·
            refine ⟨1344016096659555204713507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896010731106370136475671 1344016096659555204713507)
            ·
              refine ⟨2016024144989332807070261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344016096659555204713507 2016024144989332807070261)
              ·
                refine ⟨189002263592749950662837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2016024144989332807070261 189002263592749950662837)
                ·
                  refine ⟨17718962211820307874641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189002263592749950662837 17718962211820307874641)
                  ·
                    rfl

theorem cell20_38821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_38821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38821 prefixEnd_38821 := by exact prefixLift 38821
  have htrace : WordTrace (prefixWord ++ tailWord_38821) baseStart_38821 baseEnd_38821 := by
    simpa [prefixWord, tailWord_38821, baseEnd_38821] using wordTrace_append hprefix tailTrace_38821
  have hstable : (prefixWord ++ tailWord_38821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38821).length < 2 ^ (prefixWord ++ tailWord_38821).sum := by decide
  have hdescent : baseEnd_38821 < baseStart_38821 := by decide
  rcases family_descends (prefixWord ++ tailWord_38821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38845 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_38845 : Nat := 118140960795 + 38845 * 2 ^ 59
def prefixEnd_38845 : Nat := 4983230072969 + 3 ^ 40 * 38845 * 2
def baseEnd_38845 : Nat := 17729916465782891074543

theorem tailTrace_38845 : CollatzResearch.WordTrace tailWord_38845 prefixEnd_38845 17729916465782891074543 := by
  unfold tailWord_38845
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416793544278674042933989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 944529029519116028622659 1416793544278674042933989)
  ·
    refine ⟨265648789552251383050123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1416793544278674042933989 265648789552251383050123)
    ·
      refine ⟨398473184328377074575185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265648789552251383050123 398473184328377074575185)
      ·
        refine ⟨298854888246282805931389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398473184328377074575185 298854888246282805931389)
        ·
          refine ⟨112070583092356052224271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298854888246282805931389 112070583092356052224271)
          ·
            refine ⟨168105874638534078336407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112070583092356052224271 168105874638534078336407)
            ·
              refine ⟨252158811957801117504611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168105874638534078336407 252158811957801117504611)
              ·
                refine ⟨378238217936701676256917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252158811957801117504611 378238217936701676256917)
                ·
                  refine ⟨17729916465782891074543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 378238217936701676256917 17729916465782891074543)
                  ·
                    rfl

theorem cell20_38845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_38845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38845 prefixEnd_38845 := by exact prefixLift 38845
  have htrace : WordTrace (prefixWord ++ tailWord_38845) baseStart_38845 baseEnd_38845 := by
    simpa [prefixWord, tailWord_38845, baseEnd_38845] using wordTrace_append hprefix tailTrace_38845
  have hstable : (prefixWord ++ tailWord_38845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38845).length < 2 ^ (prefixWord ++ tailWord_38845).sum := by decide
  have hdescent : baseEnd_38845 < baseStart_38845 := by decide
  rcases family_descends (prefixWord ++ tailWord_38845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38859 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_38859 : Nat := 118140960795 + 38859 * 2 ^ 59
def prefixEnd_38859 : Nat := 4983230072969 + 3 ^ 40 * 38859 * 2
def baseEnd_38859 : Nat := 17736306447261064607819

theorem tailTrace_38859 : CollatzResearch.WordTrace tailWord_38859 prefixEnd_38859 17736306447261064607819 := by
  unfold tailWord_38859
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417304166227954433943631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 944869444151969622629087 1417304166227954433943631)
  ·
    refine ⟨2125956249341931650915447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417304166227954433943631 2125956249341931650915447)
    ·
      refine ⟨3188934374012897476373171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2125956249341931650915447 3188934374012897476373171)
      ·
        refine ⟨4783401561019346214559757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188934374012897476373171 4783401561019346214559757)
        ·
          refine ⟨1793775585382254830459909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4783401561019346214559757 1793775585382254830459909)
          ·
            refine ⟨336332922259172780711233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1793775585382254830459909 336332922259172780711233)
            ·
              refine ⟨252249691694379585533425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336332922259172780711233 252249691694379585533425)
              ·
                refine ⟨189187268770784689150069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252249691694379585533425 189187268770784689150069)
                ·
                  refine ⟨17736306447261064607819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189187268770784689150069 17736306447261064607819)
                  ·
                    rfl

theorem cell20_38859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_38859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38859 prefixEnd_38859 := by exact prefixLift 38859
  have htrace : WordTrace (prefixWord ++ tailWord_38859) baseStart_38859 baseEnd_38859 := by
    simpa [prefixWord, tailWord_38859, baseEnd_38859] using wordTrace_append hprefix tailTrace_38859
  have hstable : (prefixWord ++ tailWord_38859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38859).length < 2 ^ (prefixWord ++ tailWord_38859).sum := by decide
  have hdescent : baseEnd_38859 < baseStart_38859 := by decide
  rcases family_descends (prefixWord ++ tailWord_38859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38883 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_38883 : Nat := 118140960795 + 38883 * 2 ^ 59
def prefixEnd_38883 : Nat := 4983230072969 + 3 ^ 40 * 38883 * 2
def baseEnd_38883 : Nat := 17747260701223647807721

theorem tailTrace_38883 : CollatzResearch.WordTrace tailWord_38883 prefixEnd_38883 17747260701223647807721 := by
  unfold tailWord_38883
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418179518141006532817303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 945453012094004355211535 1418179518141006532817303)
  ·
    refine ⟨2127269277211509799225955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1418179518141006532817303 2127269277211509799225955)
    ·
      refine ⟨3190903915817264698838933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127269277211509799225955 3190903915817264698838933)
      ·
        refine ⟨149573621053934282758075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3190903915817264698838933 149573621053934282758075)
        ·
          refine ⟨224360431580901424137113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149573621053934282758075 224360431580901424137113)
          ·
            refine ⟨168270323685676068102835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224360431580901424137113 168270323685676068102835)
            ·
              refine ⟨252405485528514102154253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168270323685676068102835 252405485528514102154253)
              ·
                refine ⟨94652057073192788307845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252405485528514102154253 94652057073192788307845)
                ·
                  refine ⟨17747260701223647807721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94652057073192788307845 17747260701223647807721)
                  ·
                    rfl

theorem cell20_38883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_38883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38883 prefixEnd_38883 := by exact prefixLift 38883
  have htrace : WordTrace (prefixWord ++ tailWord_38883) baseStart_38883 baseEnd_38883 := by
    simpa [prefixWord, tailWord_38883, baseEnd_38883] using wordTrace_append hprefix tailTrace_38883
  have hstable : (prefixWord ++ tailWord_38883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38883).length < 2 ^ (prefixWord ++ tailWord_38883).sum := by decide
  have hdescent : baseEnd_38883 < baseStart_38883 := by decide
  rcases family_descends (prefixWord ++ tailWord_38883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38890 : List Nat := [3, 1, 3, 1, 2, 1, 2, 7]
def baseStart_38890 : Nat := 118140960795 + 38890 * 2 ^ 59
def prefixEnd_38890 : Nat := 4983230072969 + 3 ^ 40 * 38890 * 2
def baseEnd_38890 : Nat := 5916818563987578191453

theorem tailTrace_38890 : CollatzResearch.WordTrace tailWord_38890 prefixEnd_38890 5916818563987578191453 := by
  unfold tailWord_38890
  simp only [CollatzResearch.WordTrace]
  refine ⟨354608707278911682080531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 945623219410431152214749 354608707278911682080531)
  ·
    refine ⟨531913060918367523120797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 354608707278911682080531 531913060918367523120797)
    ·
      refine ⟨199467397844387821170299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 531913060918367523120797 199467397844387821170299)
      ·
        refine ⟨299201096766581731755449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199467397844387821170299 299201096766581731755449)
        ·
          refine ⟨224400822574936298816587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299201096766581731755449 224400822574936298816587)
          ·
            refine ⟨336601233862404448224881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224400822574936298816587 336601233862404448224881)
            ·
              refine ⟨252450925396803336168661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336601233862404448224881 252450925396803336168661)
              ·
                refine ⟨5916818563987578191453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 252450925396803336168661 5916818563987578191453)
                ·
                  rfl

theorem cell20_38890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_38890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38890 prefixEnd_38890 := by exact prefixLift 38890
  have htrace : WordTrace (prefixWord ++ tailWord_38890) baseStart_38890 baseEnd_38890 := by
    simpa [prefixWord, tailWord_38890, baseEnd_38890] using wordTrace_append hprefix tailTrace_38890
  have hstable : (prefixWord ++ tailWord_38890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38890).length < 2 ^ (prefixWord ++ tailWord_38890).sum := by decide
  have hdescent : baseEnd_38890 < baseStart_38890 := by decide
  rcases family_descends (prefixWord ++ tailWord_38890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38917 : List Nat := [1, 3, 1, 1, 2, 6, 1, 3, 2]
def baseStart_38917 : Nat := 118140960795 + 38917 * 2 ^ 59
def prefixEnd_38917 : Nat := 4983230072969 + 3 ^ 40 * 38917 * 2
def baseEnd_38917 : Nat := 17762779227670640674249

theorem tailTrace_38917 : CollatzResearch.WordTrace tailWord_38917 prefixEnd_38917 17762779227670640674249 := by
  unfold tailWord_38917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1419419600017830339555005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 946279733345220226370003 1419419600017830339555005)
  ·
    refine ⟨532282350006686377333127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1419419600017830339555005 532282350006686377333127)
    ·
      refine ⟨798423525010029565999691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 532282350006686377333127 798423525010029565999691)
      ·
        refine ⟨1197635287515044348999537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798423525010029565999691 1197635287515044348999537)
        ·
          refine ⟨898226465636283261749653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197635287515044348999537 898226465636283261749653)
          ·
            refine ⟨42104365576700777894515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 898226465636283261749653 42104365576700777894515)
            ·
              refine ⟨63156548365051166841773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42104365576700777894515 63156548365051166841773)
              ·
                refine ⟨23683705636894187565665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63156548365051166841773 23683705636894187565665)
                ·
                  refine ⟨17762779227670640674249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23683705636894187565665 17762779227670640674249)
                  ·
                    rfl

theorem cell20_38917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_38917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38917 prefixEnd_38917 := by exact prefixLift 38917
  have htrace : WordTrace (prefixWord ++ tailWord_38917) baseStart_38917 baseEnd_38917 := by
    simpa [prefixWord, tailWord_38917, baseEnd_38917] using wordTrace_append hprefix tailTrace_38917
  have hstable : (prefixWord ++ tailWord_38917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38917).length < 2 ^ (prefixWord ++ tailWord_38917).sum := by decide
  have hdescent : baseEnd_38917 < baseStart_38917 := by decide
  rcases family_descends (prefixWord ++ tailWord_38917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38938 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_38938 : Nat := 118140960795 + 38938 * 2 ^ 59
def prefixEnd_38938 : Nat := 4983230072969 + 3 ^ 40 * 38938 * 2
def baseEnd_38938 : Nat := 17772364199887900974163

theorem tailTrace_38938 : CollatzResearch.WordTrace tailWord_38938 prefixEnd_38938 17772364199887900974163 := by
  unfold tailWord_38938
  simp only [CollatzResearch.WordTrace]
  refine ⟨355046383235437731517367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 946790355294500617379645 355046383235437731517367)
  ·
    refine ⟨532569574853156597276051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 355046383235437731517367 532569574853156597276051)
    ·
      refine ⟨798854362279734895914077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 532569574853156597276051 798854362279734895914077)
      ·
        refine ⟨299570385854900585967779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 798854362279734895914077 299570385854900585967779)
        ·
          refine ⟨449355578782350878951669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299570385854900585967779 449355578782350878951669)
          ·
            refine ⟨42127085510845394901719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 449355578782350878951669 42127085510845394901719)
            ·
              refine ⟨63190628266268092352579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42127085510845394901719 63190628266268092352579)
              ·
                refine ⟨94785942399402138528869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63190628266268092352579 94785942399402138528869)
                ·
                  refine ⟨17772364199887900974163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94785942399402138528869 17772364199887900974163)
                  ·
                    rfl

theorem cell20_38938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_38938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38938 prefixEnd_38938 := by exact prefixLift 38938
  have htrace : WordTrace (prefixWord ++ tailWord_38938) baseStart_38938 baseEnd_38938 := by
    simpa [prefixWord, tailWord_38938, baseEnd_38938] using wordTrace_append hprefix tailTrace_38938
  have hstable : (prefixWord ++ tailWord_38938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38938).length < 2 ^ (prefixWord ++ tailWord_38938).sum := by decide
  have hdescent : baseEnd_38938 < baseStart_38938 := by decide
  rcases family_descends (prefixWord ++ tailWord_38938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38945 : List Nat := [1, 2, 3, 2, 4, 1, 2, 5]
def baseStart_38945 : Nat := 118140960795 + 38945 * 2 ^ 59
def prefixEnd_38945 : Nat := 4983230072969 + 3 ^ 40 * 38945 * 2
def baseEnd_38945 : Nat := 5925186396875662580267

theorem tailTrace_38945 : CollatzResearch.WordTrace tailWord_38945 prefixEnd_38945 5925186396875662580267 := by
  unfold tailWord_38945
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420440843916391121574289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 946960562610927414382859 1420440843916391121574289)
  ·
    refine ⟨1065330632937293341180717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1420440843916391121574289 1065330632937293341180717)
    ·
      refine ⟨399498987351485002942769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1065330632937293341180717 399498987351485002942769)
      ·
        refine ⟨299624240513613752207077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399498987351485002942769 299624240513613752207077)
        ·
          refine ⟨56179545096302578538827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299624240513613752207077 56179545096302578538827)
          ·
            refine ⟨84269317644453867808241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56179545096302578538827 84269317644453867808241)
            ·
              refine ⟨63201988233340400856181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84269317644453867808241 63201988233340400856181)
              ·
                refine ⟨5925186396875662580267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63201988233340400856181 5925186396875662580267)
                ·
                  rfl

theorem cell20_38945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_38945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38945 prefixEnd_38945 := by exact prefixLift 38945
  have htrace : WordTrace (prefixWord ++ tailWord_38945) baseStart_38945 baseEnd_38945 := by
    simpa [prefixWord, tailWord_38945, baseEnd_38945] using wordTrace_append hprefix tailTrace_38945
  have hstable : (prefixWord ++ tailWord_38945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38945).length < 2 ^ (prefixWord ++ tailWord_38945).sum := by decide
  have hdescent : baseEnd_38945 < baseStart_38945 := by decide
  rcases family_descends (prefixWord ++ tailWord_38945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38990 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_38990 : Nat := 118140960795 + 38990 * 2 ^ 59
def prefixEnd_38990 : Nat := 4983230072969 + 3 ^ 40 * 38990 * 2
def baseEnd_38990 : Nat := 17796098416806831240617

theorem tailTrace_38990 : CollatzResearch.WordTrace tailWord_38990 prefixEnd_38990 17796098416806831240617 := by
  unfold tailWord_38990
  simp only [CollatzResearch.WordTrace]
  refine ⟨177760266094170475870303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 948054752502242537974949 177760266094170475870303)
  ·
    refine ⟨266640399141255713805455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177760266094170475870303 266640399141255713805455)
    ·
      refine ⟨399960598711883570708183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266640399141255713805455 399960598711883570708183)
      ·
        refine ⟨599940898067825356062275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399960598711883570708183 599940898067825356062275)
        ·
          refine ⟨899911347101738034093413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599940898067825356062275 899911347101738034093413)
          ·
            refine ⟨168733377581575881392515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 899911347101738034093413 168733377581575881392515)
            ·
              refine ⟨253100066372363822088773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168733377581575881392515 253100066372363822088773)
              ·
                refine ⟨47456262444818216641645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253100066372363822088773 47456262444818216641645)
                ·
                  refine ⟨17796098416806831240617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47456262444818216641645 17796098416806831240617)
                  ·
                    rfl

theorem cell20_38990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_38990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_38990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_38990 prefixEnd_38990 := by exact prefixLift 38990
  have htrace : WordTrace (prefixWord ++ tailWord_38990) baseStart_38990 baseEnd_38990 := by
    simpa [prefixWord, tailWord_38990, baseEnd_38990] using wordTrace_append hprefix tailTrace_38990
  have hstable : (prefixWord ++ tailWord_38990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38990).length < 2 ^ (prefixWord ++ tailWord_38990).sum := by decide
  have hdescent : baseEnd_38990 < baseStart_38990 := by decide
  rcases family_descends (prefixWord ++ tailWord_38990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39021 : List Nat := [1, 5, 1, 1, 2, 1, 5, 4]
def baseStart_39021 : Nat := 118140960795 + 39021 * 2 ^ 59
def prefixEnd_39021 : Nat := 4983230072969 + 3 ^ 40 * 39021 * 2
def baseEnd_39021 : Nat := 5936749220502833735719

theorem tailTrace_39021 : CollatzResearch.WordTrace tailWord_39021 prefixEnd_39021 5936749220502833735719 := by
  unfold tailWord_39021
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423212791641056101340917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 948808527760704067560611 1423212791641056101340917)
  ·
    refine ⟨133426199216349009500711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1423212791641056101340917 133426199216349009500711)
    ·
      refine ⟨200139298824523514251067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133426199216349009500711 200139298824523514251067)
      ·
        refine ⟨300208948236785271376601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200139298824523514251067 300208948236785271376601)
        ·
          refine ⟨225156711177588953532451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300208948236785271376601 225156711177588953532451)
          ·
            refine ⟨337735066766383430298677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225156711177588953532451 337735066766383430298677)
            ·
              refine ⟨31662662509348446590501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 337735066766383430298677 31662662509348446590501)
              ·
                refine ⟨5936749220502833735719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31662662509348446590501 5936749220502833735719)
                ·
                  rfl

theorem cell20_39021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_39021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39021 prefixEnd_39021 := by exact prefixLift 39021
  have htrace : WordTrace (prefixWord ++ tailWord_39021) baseStart_39021 baseEnd_39021 := by
    simpa [prefixWord, tailWord_39021, baseEnd_39021] using wordTrace_append hprefix tailTrace_39021
  have hstable : (prefixWord ++ tailWord_39021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39021).length < 2 ^ (prefixWord ++ tailWord_39021).sum := by decide
  have hdescent : baseEnd_39021 < baseStart_39021 := by decide
  rcases family_descends (prefixWord ++ tailWord_39021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39045 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 3]
def baseStart_39045 : Nat := 118140960795 + 39045 * 2 ^ 59
def prefixEnd_39045 : Nat := 4983230072969 + 3 ^ 40 * 39045 * 2
def baseEnd_39045 : Nat := 17821201915471084407059

theorem tailTrace_39045 : CollatzResearch.WordTrace tailWord_39045 prefixEnd_39045 17821201915471084407059 := by
  unfold tailWord_39045
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424088143554108200214589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 949392095702738800143059 1424088143554108200214589)
  ·
    refine ⟨534033053832790575080471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1424088143554108200214589 534033053832790575080471)
    ·
      refine ⟨801049580749185862620707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534033053832790575080471 801049580749185862620707)
      ·
        refine ⟨1201574371123778793931061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801049580749185862620707 1201574371123778793931061)
        ·
          refine ⟨112647597292854261931037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1201574371123778793931061 112647597292854261931037)
          ·
            refine ⟨42242848984820348224139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112647597292854261931037 42242848984820348224139)
            ·
              refine ⟨63364273477230522336209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42242848984820348224139 63364273477230522336209)
              ·
                refine ⟨47523205107922891752157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63364273477230522336209 47523205107922891752157)
                ·
                  refine ⟨17821201915471084407059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47523205107922891752157 17821201915471084407059)
                  ·
                    rfl

theorem cell20_39045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_39045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39045 prefixEnd_39045 := by exact prefixLift 39045
  have htrace : WordTrace (prefixWord ++ tailWord_39045) baseStart_39045 baseEnd_39045 := by
    simpa [prefixWord, tailWord_39045, baseEnd_39045] using wordTrace_append hprefix tailTrace_39045
  have hstable : (prefixWord ++ tailWord_39045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39045).length < 2 ^ (prefixWord ++ tailWord_39045).sum := by decide
  have hdescent : baseEnd_39045 < baseStart_39045 := by decide
  rcases family_descends (prefixWord ++ tailWord_39045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39049 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_39049 : Nat := 118140960795 + 39049 * 2 ^ 59
def prefixEnd_39049 : Nat := 4983230072969 + 3 ^ 40 * 39049 * 2
def baseEnd_39049 : Nat := 17823027624464848273709

theorem tailTrace_39049 : CollatzResearch.WordTrace tailWord_39049 prefixEnd_39049 17823027624464848273709 := by
  unfold tailWord_39049
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424234035539616883360201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 949489357026411255573467 1424234035539616883360201)
  ·
    refine ⟨1068175526654712662520151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1424234035539616883360201 1068175526654712662520151)
    ·
      refine ⟨1602263289982068993780227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068175526654712662520151 1602263289982068993780227)
      ·
        refine ⟨2403394934973103490670341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602263289982068993780227 2403394934973103490670341)
        ·
          refine ⟨450636550307456904500689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2403394934973103490670341 450636550307456904500689)
          ·
            refine ⟨337977412730592678375517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450636550307456904500689 337977412730592678375517)
            ·
              refine ⟨126741529773972254390819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337977412730592678375517 126741529773972254390819)
              ·
                refine ⟨190112294660958381586229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126741529773972254390819 190112294660958381586229)
                ·
                  refine ⟨17823027624464848273709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190112294660958381586229 17823027624464848273709)
                  ·
                    rfl

theorem cell20_39049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_39049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39049 prefixEnd_39049 := by exact prefixLift 39049
  have htrace : WordTrace (prefixWord ++ tailWord_39049) baseStart_39049 baseEnd_39049 := by
    simpa [prefixWord, tailWord_39049, baseEnd_39049] using wordTrace_append hprefix tailTrace_39049
  have hstable : (prefixWord ++ tailWord_39049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39049).length < 2 ^ (prefixWord ++ tailWord_39049).sum := by decide
  have hdescent : baseEnd_39049 < baseStart_39049 := by decide
  rcases family_descends (prefixWord ++ tailWord_39049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39073 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_39073 : Nat := 118140960795 + 39073 * 2 ^ 59
def prefixEnd_39073 : Nat := 4983230072969 + 3 ^ 40 * 39073 * 2
def baseEnd_39073 : Nat := 17833981878427431473611

theorem tailTrace_39073 : CollatzResearch.WordTrace tailWord_39073 prefixEnd_39073 17833981878427431473611 := by
  unfold tailWord_39073
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425109387452668982233873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 950072924968445988155915 1425109387452668982233873)
  ·
    refine ⟨1068832040589501736675405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1425109387452668982233873 1068832040589501736675405)
    ·
      refine ⟨400812015221063151253277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1068832040589501736675405 400812015221063151253277)
      ·
        refine ⟨150304505707898681719979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400812015221063151253277 150304505707898681719979)
        ·
          refine ⟨225456758561848022579969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150304505707898681719979 225456758561848022579969)
          ·
            refine ⟨169092568921386016934977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225456758561848022579969 169092568921386016934977)
            ·
              refine ⟨126819426691039512701233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169092568921386016934977 126819426691039512701233)
              ·
                refine ⟨95114570018279634525925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126819426691039512701233 95114570018279634525925)
                ·
                  refine ⟨17833981878427431473611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95114570018279634525925 17833981878427431473611)
                  ·
                    rfl

theorem cell20_39073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_39073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39073 prefixEnd_39073 := by exact prefixLift 39073
  have htrace : WordTrace (prefixWord ++ tailWord_39073) baseStart_39073 baseEnd_39073 := by
    simpa [prefixWord, tailWord_39073, baseEnd_39073] using wordTrace_append hprefix tailTrace_39073
  have hstable : (prefixWord ++ tailWord_39073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39073).length < 2 ^ (prefixWord ++ tailWord_39073).sum := by decide
  have hdescent : baseEnd_39073 < baseStart_39073 := by decide
  rcases family_descends (prefixWord ++ tailWord_39073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39076 : List Nat := [2, 3, 1, 2, 4, 2, 2, 4]
def baseStart_39076 : Nat := 118140960795 + 39076 * 2 ^ 59
def prefixEnd_39076 : Nat := 4983230072969 + 3 ^ 40 * 39076 * 2
def baseEnd_39076 : Nat := 5945117053390918124533

theorem tailTrace_39076 : CollatzResearch.WordTrace tailWord_39076 prefixEnd_39076 5945117053390918124533 := by
  unfold tailWord_39076
  simp only [CollatzResearch.WordTrace]
  refine ⟨712609403220900247296541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 950145870961200329728721 712609403220900247296541)
  ·
    refine ⟨267228526207837592736203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 712609403220900247296541 267228526207837592736203)
    ·
      refine ⟨400842789311756389104305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267228526207837592736203 400842789311756389104305)
      ·
        refine ⟨300632091983817291828229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400842789311756389104305 300632091983817291828229)
        ·
          refine ⟨56368517246965742217793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300632091983817291828229 56368517246965742217793)
          ·
            refine ⟨42276387935224306663345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56368517246965742217793 42276387935224306663345)
            ·
              refine ⟨31707290951418229997509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42276387935224306663345 31707290951418229997509)
              ·
                refine ⟨5945117053390918124533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31707290951418229997509 5945117053390918124533)
                ·
                  rfl

theorem cell20_39076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_39076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39076 prefixEnd_39076 := by exact prefixLift 39076
  have htrace : WordTrace (prefixWord ++ tailWord_39076) baseStart_39076 baseEnd_39076 := by
    simpa [prefixWord, tailWord_39076, baseEnd_39076] using wordTrace_append hprefix tailTrace_39076
  have hstable : (prefixWord ++ tailWord_39076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39076).length < 2 ^ (prefixWord ++ tailWord_39076).sum := by decide
  have hdescent : baseEnd_39076 < baseStart_39076 := by decide
  rcases family_descends (prefixWord ++ tailWord_39076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39118 : List Nat := [4, 1, 1, 1, 4, 1, 1, 7]
def baseStart_39118 : Nat := 118140960795 + 39118 * 2 ^ 59
def prefixEnd_39118 : Nat := 4983230072969 + 3 ^ 40 * 39118 * 2
def baseEnd_39118 : Nat := 5951507034869091657809

theorem tailTrace_39118 : CollatzResearch.WordTrace tailWord_39118 prefixEnd_39118 5951507034869091657809 := by
  unfold tailWord_39118
  simp only [CollatzResearch.WordTrace]
  refine ⟨178343834036205208452751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 951167114859761111748005 178343834036205208452751)
  ·
    refine ⟨267515751054307812679127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178343834036205208452751 267515751054307812679127)
    ·
      refine ⟨401273626581461719018691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267515751054307812679127 401273626581461719018691)
      ·
        refine ⟨601910439872192578528037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401273626581461719018691 601910439872192578528037)
        ·
          refine ⟨112858207476036108474007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 601910439872192578528037 112858207476036108474007)
          ·
            refine ⟨169287311214054162711011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112858207476036108474007 169287311214054162711011)
            ·
              refine ⟨253930966821081244066517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169287311214054162711011 253930966821081244066517)
              ·
                refine ⟨5951507034869091657809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 253930966821081244066517 5951507034869091657809)
                ·
                  rfl

theorem cell20_39118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_39118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39118 prefixEnd_39118 := by exact prefixLift 39118
  have htrace : WordTrace (prefixWord ++ tailWord_39118) baseStart_39118 baseEnd_39118 := by
    simpa [prefixWord, tailWord_39118, baseEnd_39118] using wordTrace_append hprefix tailTrace_39118
  have hstable : (prefixWord ++ tailWord_39118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39118).length < 2 ^ (prefixWord ++ tailWord_39118).sum := by decide
  have hdescent : baseEnd_39118 < baseStart_39118 := by decide
  rcases family_descends (prefixWord ++ tailWord_39118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39204 : List Nat := [2, 3, 1, 3, 1, 2, 1, 5, 2]
def baseStart_39204 : Nat := 118140960795 + 39204 * 2 ^ 59
def prefixEnd_39204 : Nat := 4983230072969 + 3 ^ 40 * 39204 * 2
def baseEnd_39204 : Nat := 17893773847973198106409

theorem tailTrace_39204 : CollatzResearch.WordTrace tailWord_39204 prefixEnd_39204 17893773847973198106409 := by
  unfold tailWord_39204
  simp only [CollatzResearch.WordTrace]
  refine ⟨714943674989039177626333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 953258233318718903501777 714943674989039177626333)
  ·
    refine ⟨268103878120889691609875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 714943674989039177626333 268103878120889691609875)
    ·
      refine ⟨402155817181334537414813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268103878120889691609875 402155817181334537414813)
      ·
        refine ⟨150808431443000451530555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402155817181334537414813 150808431443000451530555)
        ·
          refine ⟨226212647164500677295833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150808431443000451530555 226212647164500677295833)
          ·
            refine ⟨169659485373375507971875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226212647164500677295833 169659485373375507971875)
            ·
              refine ⟨254489228060063261957813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169659485373375507971875 254489228060063261957813)
              ·
                refine ⟨23858365130630930808545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254489228060063261957813 23858365130630930808545)
                ·
                  refine ⟨17893773847973198106409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23858365130630930808545 17893773847973198106409)
                  ·
                    rfl

theorem cell20_39204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_39204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39204 prefixEnd_39204 := by exact prefixLift 39204
  have htrace : WordTrace (prefixWord ++ tailWord_39204) baseStart_39204 baseEnd_39204 := by
    simpa [prefixWord, tailWord_39204, baseEnd_39204] using wordTrace_append hprefix tailTrace_39204
  have hstable : (prefixWord ++ tailWord_39204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39204).length < 2 ^ (prefixWord ++ tailWord_39204).sum := by decide
  have hdescent : baseEnd_39204 < baseStart_39204 := by decide
  rcases family_descends (prefixWord ++ tailWord_39204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39218 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_39218 : Nat := 118140960795 + 39218 * 2 ^ 59
def prefixEnd_39218 : Nat := 4983230072969 + 3 ^ 40 * 39218 * 2
def baseEnd_39218 : Nat := 17900163829451371639685

theorem tailTrace_39218 : CollatzResearch.WordTrace tailWord_39218 prefixEnd_39218 17900163829451371639685 := by
  unfold tailWord_39218
  simp only [CollatzResearch.WordTrace]
  refine ⟨357599492981839686565577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 953598647951572497508205 357599492981839686565577)
  ·
    refine ⟨268199619736379764924183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 357599492981839686565577 268199619736379764924183)
    ·
      refine ⟨402299429604569647386275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268199619736379764924183 402299429604569647386275)
      ·
        refine ⟨603449144406854471079413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402299429604569647386275 603449144406854471079413)
        ·
          refine ⟨56573357288142606663695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 603449144406854471079413 56573357288142606663695)
          ·
            refine ⟨84860035932213909995543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56573357288142606663695 84860035932213909995543)
            ·
              refine ⟨127290053898320864993315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84860035932213909995543 127290053898320864993315)
              ·
                refine ⟨190935080847481297489973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127290053898320864993315 190935080847481297489973)
                ·
                  refine ⟨17900163829451371639685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190935080847481297489973 17900163829451371639685)
                  ·
                    rfl

theorem cell20_39218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_39218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39218 prefixEnd_39218 := by exact prefixLift 39218
  have htrace : WordTrace (prefixWord ++ tailWord_39218) baseStart_39218 baseEnd_39218 := by
    simpa [prefixWord, tailWord_39218, baseEnd_39218] using wordTrace_append hprefix tailTrace_39218
  have hstable : (prefixWord ++ tailWord_39218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39218).length < 2 ^ (prefixWord ++ tailWord_39218).sum := by decide
  have hdescent : baseEnd_39218 < baseStart_39218 := by decide
  rcases family_descends (prefixWord ++ tailWord_39218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39225 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_39225 : Nat := 118140960795 + 39225 * 2 ^ 59
def prefixEnd_39225 : Nat := 4983230072969 + 3 ^ 40 * 39225 * 2
def baseEnd_39225 : Nat := 17903358820190458406323

theorem tailTrace_39225 : CollatzResearch.WordTrace tailWord_39225 prefixEnd_39225 17903358820190458406323 := by
  unfold tailWord_39225
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430653282901998941767129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 953768855267999294511419 1430653282901998941767129)
  ·
    refine ⟨1072989962176499206325347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1430653282901998941767129 1072989962176499206325347)
    ·
      refine ⟨1609484943264748809488021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1072989962176499206325347 1609484943264748809488021)
      ·
        refine ⟨75444606715535100444751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1609484943264748809488021 75444606715535100444751)
        ·
          refine ⟨113166910073302650667127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75444606715535100444751 113166910073302650667127)
          ·
            refine ⟨169750365109953976000691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113166910073302650667127 169750365109953976000691)
            ·
              refine ⟨254625547664930964001037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169750365109953976000691 254625547664930964001037)
              ·
                refine ⟨95484580374349111500389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254625547664930964001037 95484580374349111500389)
                ·
                  refine ⟨17903358820190458406323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95484580374349111500389 17903358820190458406323)
                  ·
                    rfl

theorem cell20_39225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_39225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39225 prefixEnd_39225 := by exact prefixLift 39225
  have htrace : WordTrace (prefixWord ++ tailWord_39225) baseStart_39225 baseEnd_39225 := by
    simpa [prefixWord, tailWord_39225, baseEnd_39225] using wordTrace_append hprefix tailTrace_39225
  have hstable : (prefixWord ++ tailWord_39225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39225).length < 2 ^ (prefixWord ++ tailWord_39225).sum := by decide
  have hdescent : baseEnd_39225 < baseStart_39225 := by decide
  rcases family_descends (prefixWord ++ tailWord_39225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39246 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_39246 : Nat := 118140960795 + 39246 * 2 ^ 59
def prefixEnd_39246 : Nat := 4983230072969 + 3 ^ 40 * 39246 * 2
def baseEnd_39246 : Nat := 17912943792407718706237

theorem tailTrace_39246 : CollatzResearch.WordTrace tailWord_39246 prefixEnd_39246 17912943792407718706237 := by
  unfold tailWord_39246
  simp only [CollatzResearch.WordTrace]
  refine ⟨178927401978239941035199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 954279477217279685521061 178927401978239941035199)
  ·
    refine ⟨268391102967359911552799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178927401978239941035199 268391102967359911552799)
    ·
      refine ⟨402586654451039867329199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268391102967359911552799 402586654451039867329199)
      ·
        refine ⟨603879981676559800993799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402586654451039867329199 603879981676559800993799)
        ·
          refine ⟨905819972514839701490699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603879981676559800993799 905819972514839701490699)
          ·
            refine ⟨1358729958772259552236049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905819972514839701490699 1358729958772259552236049)
            ·
              refine ⟨1019047469079194664177037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358729958772259552236049 1019047469079194664177037)
              ·
                refine ⟨382142800904697999066389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1019047469079194664177037 382142800904697999066389)
                ·
                  refine ⟨17912943792407718706237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 382142800904697999066389 17912943792407718706237)
                  ·
                    rfl

theorem cell20_39246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_39246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39246 prefixEnd_39246 := by exact prefixLift 39246
  have htrace : WordTrace (prefixWord ++ tailWord_39246) baseStart_39246 baseEnd_39246 := by
    simpa [prefixWord, tailWord_39246, baseEnd_39246] using wordTrace_append hprefix tailTrace_39246
  have hstable : (prefixWord ++ tailWord_39246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39246).length < 2 ^ (prefixWord ++ tailWord_39246).sum := by decide
  have hdescent : baseEnd_39246 < baseStart_39246 := by decide
  rcases family_descends (prefixWord ++ tailWord_39246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39249 : List Nat := [1, 2, 2, 1, 4, 4, 2, 4]
def baseStart_39249 : Nat := 118140960795 + 39249 * 2 ^ 59
def prefixEnd_39249 : Nat := 4983230072969 + 3 ^ 40 * 39249 * 2
def baseEnd_39249 : Nat := 5971437691384347202075

theorem tailTrace_39249 : CollatzResearch.WordTrace tailWord_39249 prefixEnd_39249 5971437691384347202075 := by
  unfold tailWord_39249
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431528634815051040640801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 954352423210034027093867 1431528634815051040640801)
  ·
    refine ⟨1073646476111288280480601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1431528634815051040640801 1073646476111288280480601)
    ·
      refine ⟨805234857083466210360451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1073646476111288280480601 805234857083466210360451)
      ·
        refine ⟨1207852285625199315540677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805234857083466210360451 1207852285625199315540677)
        ·
          refine ⟨226472303554724871663877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1207852285625199315540677 226472303554724871663877)
          ·
            refine ⟨42463556916510913436977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226472303554724871663877 42463556916510913436977)
            ·
              refine ⟨31847667687383185077733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42463556916510913436977 31847667687383185077733)
              ·
                refine ⟨5971437691384347202075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31847667687383185077733 5971437691384347202075)
                ·
                  rfl

theorem cell20_39249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_39249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39249 prefixEnd_39249 := by exact prefixLift 39249
  have htrace : WordTrace (prefixWord ++ tailWord_39249) baseStart_39249 baseEnd_39249 := by
    simpa [prefixWord, tailWord_39249, baseEnd_39249] using wordTrace_append hprefix tailTrace_39249
  have hstable : (prefixWord ++ tailWord_39249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39249).length < 2 ^ (prefixWord ++ tailWord_39249).sum := by decide
  have hdescent : baseEnd_39249 < baseStart_39249 := by decide
  rcases family_descends (prefixWord ++ tailWord_39249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39262 : List Nat := [4, 4, 2, 1, 1, 2, 6]
def baseStart_39262 : Nat := 118140960795 + 39262 * 2 ^ 59
def prefixEnd_39262 : Nat := 4983230072969 + 3 ^ 40 * 39262 * 2
def baseEnd_39262 : Nat := 1991138514264752685871

theorem tailTrace_39262 : CollatzResearch.WordTrace tailWord_39262 prefixEnd_39262 1991138514264752685871 := by
  unfold tailWord_39262
  simp only [CollatzResearch.WordTrace]
  refine ⟨179000347970994282608005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 954668522511969507242693 179000347970994282608005)
  ·
    refine ⟨33562565244561427989001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179000347970994282608005 33562565244561427989001)
    ·
      refine ⟨25171923933421070991751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33562565244561427989001 25171923933421070991751)
      ·
        refine ⟨37757885900131606487627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25171923933421070991751 37757885900131606487627)
        ·
          refine ⟨56636828850197409731441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37757885900131606487627 56636828850197409731441)
          ·
            refine ⟨42477621637648057298581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56636828850197409731441 42477621637648057298581)
            ·
              refine ⟨1991138514264752685871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42477621637648057298581 1991138514264752685871)
              ·
                rfl

theorem cell20_39262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 6].length) (baseStart_39262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39262 prefixEnd_39262 := by exact prefixLift 39262
  have htrace : WordTrace (prefixWord ++ tailWord_39262) baseStart_39262 baseEnd_39262 := by
    simpa [prefixWord, tailWord_39262, baseEnd_39262] using wordTrace_append hprefix tailTrace_39262
  have hstable : (prefixWord ++ tailWord_39262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39262).length < 2 ^ (prefixWord ++ tailWord_39262).sum := by decide
  have hdescent : baseEnd_39262 < baseStart_39262 := by decide
  rcases family_descends (prefixWord ++ tailWord_39262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39277 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_39277 : Nat := 118140960795 + 39277 * 2 ^ 59
def prefixEnd_39277 : Nat := 4983230072969 + 3 ^ 40 * 39277 * 2
def baseEnd_39277 : Nat := 17927093037109388672777

theorem tailTrace_39277 : CollatzResearch.WordTrace tailWord_39277 prefixEnd_39277 17927093037109388672777 := by
  unfold tailWord_39277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432549878713611822660085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 955033252475741215106723 1432549878713611822660085)
  ·
    refine ⟨134301551129401108374383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1432549878713611822660085 134301551129401108374383)
    ·
      refine ⟨201452326694101662561575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134301551129401108374383 201452326694101662561575)
      ·
        refine ⟨302178490041152493842363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201452326694101662561575 302178490041152493842363)
        ·
          refine ⟨453267735061728740763545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302178490041152493842363 453267735061728740763545)
          ·
            refine ⟨339950801296296555572659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453267735061728740763545 339950801296296555572659)
            ·
              refine ⟨509926201944444833358989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339950801296296555572659 509926201944444833358989)
              ·
                refine ⟨191222325729166812509621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 509926201944444833358989 191222325729166812509621)
                ·
                  refine ⟨17927093037109388672777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191222325729166812509621 17927093037109388672777)
                  ·
                    rfl

theorem cell20_39277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_39277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39277 prefixEnd_39277 := by exact prefixLift 39277
  have htrace : WordTrace (prefixWord ++ tailWord_39277) baseStart_39277 baseEnd_39277 := by
    simpa [prefixWord, tailWord_39277, baseEnd_39277] using wordTrace_append hprefix tailTrace_39277
  have hstable : (prefixWord ++ tailWord_39277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39277).length < 2 ^ (prefixWord ++ tailWord_39277).sum := by decide
  have hdescent : baseEnd_39277 < baseStart_39277 := by decide
  rcases family_descends (prefixWord ++ tailWord_39277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39286 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_39286 : Nat := 118140960795 + 39286 * 2 ^ 59
def prefixEnd_39286 : Nat := 4983230072969 + 3 ^ 40 * 39286 * 2
def baseEnd_39286 : Nat := 17931200882345357372741

theorem tailTrace_39286 : CollatzResearch.WordTrace tailWord_39286 prefixEnd_39286 17931200882345357372741 := by
  unfold tailWord_39286
  simp only [CollatzResearch.WordTrace]
  refine ⟨89554883480062897483607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 955252090454004239825141 89554883480062897483607)
  ·
    refine ⟨134332325220094346225411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89554883480062897483607 134332325220094346225411)
    ·
      refine ⟨201498487830141519338117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134332325220094346225411 201498487830141519338117)
      ·
        refine ⟨37780966468151534875897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201498487830141519338117 37780966468151534875897)
        ·
          refine ⟨28335724851113651156923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37780966468151534875897 28335724851113651156923)
          ·
            refine ⟨42503587276670476735385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28335724851113651156923 42503587276670476735385)
            ·
              refine ⟨31877690457502857551539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42503587276670476735385 31877690457502857551539)
              ·
                refine ⟨47816535686254286327309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31877690457502857551539 47816535686254286327309)
                ·
                  refine ⟨17931200882345357372741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47816535686254286327309 17931200882345357372741)
                  ·
                    rfl

theorem cell20_39286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_39286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39286 prefixEnd_39286 := by exact prefixLift 39286
  have htrace : WordTrace (prefixWord ++ tailWord_39286) baseStart_39286 baseEnd_39286 := by
    simpa [prefixWord, tailWord_39286, baseEnd_39286] using wordTrace_append hprefix tailTrace_39286
  have hstable : (prefixWord ++ tailWord_39286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39286).length < 2 ^ (prefixWord ++ tailWord_39286).sum := by decide
  have hdescent : baseEnd_39286 < baseStart_39286 := by decide
  rcases family_descends (prefixWord ++ tailWord_39286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39291 : List Nat := [1, 1, 1, 1, 1, 7, 1, 7]
def baseStart_39291 : Nat := 118140960795 + 39291 * 2 ^ 59
def prefixEnd_39291 : Nat := 4983230072969 + 3 ^ 40 * 39291 * 2
def baseEnd_39291 : Nat := 5977827672862520735351

theorem tailTrace_39291 : CollatzResearch.WordTrace tailWord_39291 prefixEnd_39291 5977827672862520735351 := by
  unfold tailWord_39291
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433060500662892213669727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 955373667108594809113151 1433060500662892213669727)
  ·
    refine ⟨2149590750994338320504591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1433060500662892213669727 2149590750994338320504591)
    ·
      refine ⟨3224386126491507480756887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2149590750994338320504591 3224386126491507480756887)
      ·
        refine ⟨4836579189737261221135331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224386126491507480756887 4836579189737261221135331)
        ·
          refine ⟨7254868784605891831702997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4836579189737261221135331 7254868784605891831702997)
          ·
            refine ⟨170035987139200589805539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7254868784605891831702997 170035987139200589805539)
            ·
              refine ⟨255053980708800884708309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170035987139200589805539 255053980708800884708309)
              ·
                refine ⟨5977827672862520735351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 255053980708800884708309 5977827672862520735351)
                ·
                  rfl

theorem cell20_39291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_39291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39291 prefixEnd_39291 := by exact prefixLift 39291
  have htrace : WordTrace (prefixWord ++ tailWord_39291) baseStart_39291 baseEnd_39291 := by
    simpa [prefixWord, tailWord_39291, baseEnd_39291] using wordTrace_append hprefix tailTrace_39291
  have hstable : (prefixWord ++ tailWord_39291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39291).length < 2 ^ (prefixWord ++ tailWord_39291).sum := by decide
  have hdescent : baseEnd_39291 < baseStart_39291 := by decide
  rcases family_descends (prefixWord ++ tailWord_39291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39335 : List Nat := [1, 1, 6, 1, 1, 2, 4, 2, 2]
def baseStart_39335 : Nat := 118140960795 + 39335 * 2 ^ 59
def prefixEnd_39335 : Nat := 4983230072969 + 3 ^ 40 * 39335 * 2
def baseEnd_39335 : Nat := 17953565817518964739207

theorem tailTrace_39335 : CollatzResearch.WordTrace tailWord_39335 prefixEnd_39335 17953565817518964739207 := by
  unfold tailWord_39335
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434665312503487728271459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 956443541668991818847639 1434665312503487728271459)
  ·
    refine ⟨2151997968755231592407189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1434665312503487728271459 2151997968755231592407189)
    ·
      refine ⟨100874904785401480894087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2151997968755231592407189 100874904785401480894087)
      ·
        refine ⟨151312357178102221341131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100874904785401480894087 151312357178102221341131)
        ·
          refine ⟨226968535767153332011697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151312357178102221341131 226968535767153332011697)
          ·
            refine ⟨170226401825364999008773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226968535767153332011697 170226401825364999008773)
            ·
              refine ⟨31917450342255937314145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170226401825364999008773 31917450342255937314145)
              ·
                refine ⟨23938087756691952985609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31917450342255937314145 23938087756691952985609)
                ·
                  refine ⟨17953565817518964739207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23938087756691952985609 17953565817518964739207)
                  ·
                    rfl

theorem cell20_39335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 2].length) (baseStart_39335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39335 prefixEnd_39335 := by exact prefixLift 39335
  have htrace : WordTrace (prefixWord ++ tailWord_39335) baseStart_39335 baseEnd_39335 := by
    simpa [prefixWord, tailWord_39335, baseEnd_39335] using wordTrace_append hprefix tailTrace_39335
  have hstable : (prefixWord ++ tailWord_39335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39335).length < 2 ^ (prefixWord ++ tailWord_39335).sum := by decide
  have hdescent : baseEnd_39335 < baseStart_39335 := by decide
  rcases family_descends (prefixWord ++ tailWord_39335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39338 : List Nat := [3, 1, 6, 1, 2, 1, 1, 5]
def baseStart_39338 : Nat := 118140960795 + 39338 * 2 ^ 59
def prefixEnd_39338 : Nat := 4983230072969 + 3 ^ 40 * 39338 * 2
def baseEnd_39338 : Nat := 5984978366421429213065

theorem tailTrace_39338 : CollatzResearch.WordTrace tailWord_39338 prefixEnd_39338 5984978366421429213065 := by
  unfold tailWord_39338
  simp only [CollatzResearch.WordTrace]
  refine ⟨358693682873154810157667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 956516487661746160420445 358693682873154810157667)
  ·
    refine ⟨538040524309732215236501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 358693682873154810157667 538040524309732215236501)
    ·
      refine ⟨25220649577018697589211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 538040524309732215236501 25220649577018697589211)
      ·
        refine ⟨37830974365528046383817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25220649577018697589211 37830974365528046383817)
        ·
          refine ⟨28373230774146034787863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37830974365528046383817 28373230774146034787863)
          ·
            refine ⟨42559846161219052181795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28373230774146034787863 42559846161219052181795)
            ·
              refine ⟨63839769241828578272693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42559846161219052181795 63839769241828578272693)
              ·
                refine ⟨5984978366421429213065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63839769241828578272693 5984978366421429213065)
                ·
                  rfl

theorem cell20_39338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_39338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39338 prefixEnd_39338 := by exact prefixLift 39338
  have htrace : WordTrace (prefixWord ++ tailWord_39338) baseStart_39338 baseEnd_39338 := by
    simpa [prefixWord, tailWord_39338, baseEnd_39338] using wordTrace_append hprefix tailTrace_39338
  have hstable : (prefixWord ++ tailWord_39338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39338).length < 2 ^ (prefixWord ++ tailWord_39338).sum := by decide
  have hdescent : baseEnd_39338 < baseStart_39338 := by decide
  rcases family_descends (prefixWord ++ tailWord_39338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39391 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_39391 : Nat := 118140960795 + 39391 * 2 ^ 59
def prefixEnd_39391 : Nat := 4983230072969 + 3 ^ 40 * 39391 * 2
def baseEnd_39391 : Nat := 17979125743431658872311

theorem tailTrace_39391 : CollatzResearch.WordTrace tailWord_39391 prefixEnd_39391 17979125743431658872311 := by
  unfold tailWord_39391
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436707800300609292310027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 957805200200406194873351 1436707800300609292310027)
  ·
    refine ⟨2155061700450913938465041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1436707800300609292310027 2155061700450913938465041)
    ·
      refine ⟨1616296275338185453848781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155061700450913938465041 1616296275338185453848781)
      ·
        refine ⟨606111103251819545193293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1616296275338185453848781 606111103251819545193293)
        ·
          refine ⟨227291663719432329447485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606111103251819545193293 227291663719432329447485)
          ·
            refine ⟨85234373894787123542807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227291663719432329447485 85234373894787123542807)
            ·
              refine ⟨127851560842180685314211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85234373894787123542807 127851560842180685314211)
              ·
                refine ⟨191777341263271027971317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127851560842180685314211 191777341263271027971317)
                ·
                  refine ⟨17979125743431658872311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191777341263271027971317 17979125743431658872311)
                  ·
                    rfl

theorem cell20_39391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_39391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39391 prefixEnd_39391 := by exact prefixLift 39391
  have htrace : WordTrace (prefixWord ++ tailWord_39391) baseStart_39391 baseEnd_39391 := by
    simpa [prefixWord, tailWord_39391, baseEnd_39391] using wordTrace_append hprefix tailTrace_39391
  have hstable : (prefixWord ++ tailWord_39391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39391).length < 2 ^ (prefixWord ++ tailWord_39391).sum := by decide
  have hdescent : baseEnd_39391 < baseStart_39391 := by decide
  rcases family_descends (prefixWord ++ tailWord_39391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39408 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_39408 : Nat := 118140960795 + 39408 * 2 ^ 59
def prefixEnd_39408 : Nat := 4983230072969 + 3 ^ 40 * 39408 * 2
def baseEnd_39408 : Nat := 17986885006655155305575

theorem tailTrace_39408 : CollatzResearch.WordTrace tailWord_39408 prefixEnd_39408 17986885006655155305575 := by
  unfold tailWord_39408
  simp only [CollatzResearch.WordTrace]
  refine ⟨718663920619510597839439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 958218560826014130452585 718663920619510597839439)
  ·
    refine ⟨1077995880929265896759159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 718663920619510597839439 1077995880929265896759159)
    ·
      refine ⟨1616993821393898845138739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1077995880929265896759159 1616993821393898845138739)
      ·
        refine ⟨2425490732090848267708109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616993821393898845138739 2425490732090848267708109)
        ·
          refine ⟨909559024534068100390541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2425490732090848267708109 909559024534068100390541)
          ·
            refine ⟨341084634200275537646453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 909559024534068100390541 341084634200275537646453)
            ·
              refine ⟨31976684456275831654355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 341084634200275537646453 31976684456275831654355)
              ·
                refine ⟨47965026684413747481533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31976684456275831654355 47965026684413747481533)
                ·
                  refine ⟨17986885006655155305575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47965026684413747481533 17986885006655155305575)
                  ·
                    rfl

theorem cell20_39408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_39408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39408 prefixEnd_39408 := by exact prefixLift 39408
  have htrace : WordTrace (prefixWord ++ tailWord_39408) baseStart_39408 baseEnd_39408 := by
    simpa [prefixWord, tailWord_39408, baseEnd_39408] using wordTrace_append hprefix tailTrace_39408
  have hstable : (prefixWord ++ tailWord_39408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39408).length < 2 ^ (prefixWord ++ tailWord_39408).sum := by decide
  have hdescent : baseEnd_39408 < baseStart_39408 := by decide
  rcases family_descends (prefixWord ++ tailWord_39408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39453 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_39453 : Nat := 118140960795 + 39453 * 2 ^ 59
def prefixEnd_39453 : Nat := 4983230072969 + 3 ^ 40 * 39453 * 2
def baseEnd_39453 : Nat := 18007424232834998805391

theorem tailTrace_39453 : CollatzResearch.WordTrace tailWord_39453 prefixEnd_39453 18007424232834998805391 := by
  unfold tailWord_39453
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438969126075993881067013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 959312750717329254044675 1438969126075993881067013)
  ·
    refine ⟨269806711139248852700065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1438969126075993881067013 269806711139248852700065)
    ·
      refine ⟨202355033354436639525049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269806711139248852700065 202355033354436639525049)
      ·
        refine ⟨151766275015827479643787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202355033354436639525049 151766275015827479643787)
        ·
          refine ⟨227649412523741219465681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151766275015827479643787 227649412523741219465681)
          ·
            refine ⟨170737059392805914599261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227649412523741219465681 170737059392805914599261)
            ·
              refine ⟨64026397272302217974723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170737059392805914599261 64026397272302217974723)
              ·
                refine ⟨96039595908453326962085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64026397272302217974723 96039595908453326962085)
                ·
                  refine ⟨18007424232834998805391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96039595908453326962085 18007424232834998805391)
                  ·
                    rfl

theorem cell20_39453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_39453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39453 prefixEnd_39453 := by exact prefixLift 39453
  have htrace : WordTrace (prefixWord ++ tailWord_39453) baseStart_39453 baseEnd_39453 := by
    simpa [prefixWord, tailWord_39453, baseEnd_39453] using wordTrace_append hprefix tailTrace_39453
  have hstable : (prefixWord ++ tailWord_39453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39453).length < 2 ^ (prefixWord ++ tailWord_39453).sum := by decide
  have hdescent : baseEnd_39453 < baseStart_39453 := by decide
  rcases family_descends (prefixWord ++ tailWord_39453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39474 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_39474 : Nat := 118140960795 + 39474 * 2 ^ 59
def prefixEnd_39474 : Nat := 4983230072969 + 3 ^ 40 * 39474 * 2
def baseEnd_39474 : Nat := 18017009205052259105305

theorem tailTrace_39474 : CollatzResearch.WordTrace tailWord_39474 prefixEnd_39474 18017009205052259105305 := by
  unfold tailWord_39474
  simp only [CollatzResearch.WordTrace]
  refine ⟨359933764749978616895369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 959823372666609645054317 359933764749978616895369)
  ·
    refine ⟨269950323562483962671527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 359933764749978616895369 269950323562483962671527)
    ·
      refine ⟨404925485343725944007291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269950323562483962671527 404925485343725944007291)
      ·
        refine ⟨607388228015588916010937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404925485343725944007291 607388228015588916010937)
        ·
          refine ⟨455541171011691687008203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607388228015588916010937 455541171011691687008203)
          ·
            refine ⟨683311756517537530512305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455541171011691687008203 683311756517537530512305)
            ·
              refine ⟨512483817388153147884229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683311756517537530512305 512483817388153147884229)
              ·
                refine ⟨96090715760278715228293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512483817388153147884229 96090715760278715228293)
                ·
                  refine ⟨18017009205052259105305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96090715760278715228293 18017009205052259105305)
                  ·
                    rfl

theorem cell20_39474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_39474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39474 prefixEnd_39474 := by exact prefixLift 39474
  have htrace : WordTrace (prefixWord ++ tailWord_39474) baseStart_39474 baseEnd_39474 := by
    simpa [prefixWord, tailWord_39474, baseEnd_39474] using wordTrace_append hprefix tailTrace_39474
  have hstable : (prefixWord ++ tailWord_39474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39474).length < 2 ^ (prefixWord ++ tailWord_39474).sum := by decide
  have hdescent : baseEnd_39474 < baseStart_39474 := by decide
  rcases family_descends (prefixWord ++ tailWord_39474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39481 : List Nat := [1, 2, 1, 5, 1, 1, 1, 8]
def baseStart_39481 : Nat := 118140960795 + 39481 * 2 ^ 59
def prefixEnd_39481 : Nat := 4983230072969 + 3 ^ 40 * 39481 * 2
def baseEnd_39481 : Nat := 6006734731930448623981

theorem tailTrace_39481 : CollatzResearch.WordTrace tailWord_39481 prefixEnd_39481 6006734731930448623981 := by
  unfold tailWord_39481
  simp only [CollatzResearch.WordTrace]
  refine ⟨1439990369974554663086297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 959993579983036442057531 1439990369974554663086297)
  ·
    refine ⟨1079992777480915997314723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1439990369974554663086297 1079992777480915997314723)
    ·
      refine ⟨1619989166221373995972085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079992777480915997314723 1619989166221373995972085)
      ·
        refine ⟨151873984333253812122383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1619989166221373995972085 151873984333253812122383)
        ·
          refine ⟨227810976499880718183575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151873984333253812122383 227810976499880718183575)
          ·
            refine ⟨341716464749821077275363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227810976499880718183575 341716464749821077275363)
            ·
              refine ⟨512574697124731615913045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341716464749821077275363 512574697124731615913045)
              ·
                refine ⟨6006734731930448623981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 512574697124731615913045 6006734731930448623981)
                ·
                  rfl

theorem cell20_39481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_39481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39481 prefixEnd_39481 := by exact prefixLift 39481
  have htrace : WordTrace (prefixWord ++ tailWord_39481) baseStart_39481 baseEnd_39481 := by
    simpa [prefixWord, tailWord_39481, baseEnd_39481] using wordTrace_append hprefix tailTrace_39481
  have hstable : (prefixWord ++ tailWord_39481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39481).length < 2 ^ (prefixWord ++ tailWord_39481).sum := by decide
  have hdescent : baseEnd_39481 < baseStart_39481 := by decide
  rcases family_descends (prefixWord ++ tailWord_39481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39488 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_39488 : Nat := 118140960795 + 39488 * 2 ^ 59
def prefixEnd_39488 : Nat := 4983230072969 + 3 ^ 40 * 39488 * 2
def baseEnd_39488 : Nat := 18023399186530432638581

theorem tailTrace_39488 : CollatzResearch.WordTrace tailWord_39488 prefixEnd_39488 18023399186530432638581 := by
  unfold tailWord_39488
  simp only [CollatzResearch.WordTrace]
  refine ⟨720122840474597429295559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 960163787299463239060745 720122840474597429295559)
  ·
    refine ⟨1080184260711896143943339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720122840474597429295559 1080184260711896143943339)
    ·
      refine ⟨1620276391067844215915009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080184260711896143943339 1620276391067844215915009)
      ·
        refine ⟨1215207293300883161936257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1620276391067844215915009 1215207293300883161936257)
        ·
          refine ⟨911405469975662371452193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1215207293300883161936257 911405469975662371452193)
          ·
            refine ⟨683554102481746778589145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911405469975662371452193 683554102481746778589145)
            ·
              refine ⟨512665576861310083941859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683554102481746778589145 512665576861310083941859)
              ·
                refine ⟨768998365291965125912789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512665576861310083941859 768998365291965125912789)
                ·
                  refine ⟨18023399186530432638581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 768998365291965125912789 18023399186530432638581)
                  ·
                    rfl

theorem cell20_39488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_39488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39488 prefixEnd_39488 := by exact prefixLift 39488
  have htrace : WordTrace (prefixWord ++ tailWord_39488) baseStart_39488 baseEnd_39488 := by
    simpa [prefixWord, tailWord_39488, baseEnd_39488] using wordTrace_append hprefix tailTrace_39488
  have hstable : (prefixWord ++ tailWord_39488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39488).length < 2 ^ (prefixWord ++ tailWord_39488).sum := by decide
  have hdescent : baseEnd_39488 < baseStart_39488 := by decide
  rcases family_descends (prefixWord ++ tailWord_39488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39501 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 3]
def baseStart_39501 : Nat := 118140960795 + 39501 * 2 ^ 59
def prefixEnd_39501 : Nat := 4983230072969 + 3 ^ 40 * 39501 * 2
def baseEnd_39501 : Nat := 18029332740760165205195

theorem tailTrace_39501 : CollatzResearch.WordTrace tailWord_39501 prefixEnd_39501 18029332740760165205195 := by
  unfold tailWord_39501
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440719829902098078814357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 960479886601398719209571 1440719829902098078814357)
  ·
    refine ⟨67533742026660847444423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1440719829902098078814357 67533742026660847444423)
    ·
      refine ⟨101300613039991271166635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67533742026660847444423 101300613039991271166635)
      ·
        refine ⟨151950919559986906749953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101300613039991271166635 151950919559986906749953)
        ·
          refine ⟨113963189669990180062465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151950919559986906749953 113963189669990180062465)
          ·
            refine ⟨85472392252492635046849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113963189669990180062465 85472392252492635046849)
            ·
              refine ⟨64104294189369476285137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85472392252492635046849 64104294189369476285137)
              ·
                refine ⟨48078220642027107213853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64104294189369476285137 48078220642027107213853)
                ·
                  refine ⟨18029332740760165205195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48078220642027107213853 18029332740760165205195)
                  ·
                    rfl

theorem cell20_39501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_39501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39501 prefixEnd_39501 := by exact prefixLift 39501
  have htrace : WordTrace (prefixWord ++ tailWord_39501) baseStart_39501 baseEnd_39501 := by
    simpa [prefixWord, tailWord_39501, baseEnd_39501] using wordTrace_append hprefix tailTrace_39501
  have hstable : (prefixWord ++ tailWord_39501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39501).length < 2 ^ (prefixWord ++ tailWord_39501).sum := by decide
  have hdescent : baseEnd_39501 < baseStart_39501 := by decide
  rcases family_descends (prefixWord ++ tailWord_39501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39505 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 3]
def baseStart_39505 : Nat := 118140960795 + 39505 * 2 ^ 59
def prefixEnd_39505 : Nat := 4983230072969 + 3 ^ 40 * 39505 * 2
def baseEnd_39505 : Nat := 18031158449753929071845

theorem tailTrace_39505 : CollatzResearch.WordTrace tailWord_39505 prefixEnd_39505 18031158449753929071845 := by
  unfold tailWord_39505
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440865721887606761959969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 960577147925071174639979 1440865721887606761959969)
  ·
    refine ⟨1080649291415705071469977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1440865721887606761959969 1080649291415705071469977)
    ·
      refine ⟨810486968561778803602483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1080649291415705071469977 810486968561778803602483)
      ·
        refine ⟨1215730452842668205403725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810486968561778803602483 1215730452842668205403725)
        ·
          refine ⟨455898919816000577026397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1215730452842668205403725 455898919816000577026397)
          ·
            refine ⟨170962094931000216384899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455898919816000577026397 170962094931000216384899)
            ·
              refine ⟨256443142396500324577349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170962094931000216384899 256443142396500324577349)
              ·
                refine ⟨48083089199343810858253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256443142396500324577349 48083089199343810858253)
                ·
                  refine ⟨18031158449753929071845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48083089199343810858253 18031158449753929071845)
                  ·
                    rfl

theorem cell20_39505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_39505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39505 prefixEnd_39505 := by exact prefixLift 39505
  have htrace : WordTrace (prefixWord ++ tailWord_39505) baseStart_39505 baseEnd_39505 := by
    simpa [prefixWord, tailWord_39505, baseEnd_39505] using wordTrace_append hprefix tailTrace_39505
  have hstable : (prefixWord ++ tailWord_39505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39505).length < 2 ^ (prefixWord ++ tailWord_39505).sum := by decide
  have hdescent : baseEnd_39505 < baseStart_39505 := by decide
  rcases family_descends (prefixWord ++ tailWord_39505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39508 : List Nat := [2, 4, 1, 1, 1, 4, 1, 4, 2]
def baseStart_39508 : Nat := 118140960795 + 39508 * 2 ^ 59
def prefixEnd_39508 : Nat := 4983230072969 + 3 ^ 40 * 39508 * 2
def baseEnd_39508 : Nat := 18032527731499251971833

theorem tailTrace_39508 : CollatzResearch.WordTrace tailWord_39508 prefixEnd_39508 18032527731499251971833 := by
  unfold tailWord_39508
  simp only [CollatzResearch.WordTrace]
  refine ⟨720487570438369137159589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 960650093917825516212785 720487570438369137159589)
  ·
    refine ⟨135091419457194213217423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 720487570438369137159589 135091419457194213217423)
    ·
      refine ⟨202637129185791319826135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135091419457194213217423 202637129185791319826135)
      ·
        refine ⟨303955693778686979739203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202637129185791319826135 303955693778686979739203)
        ·
          refine ⟨455933540668030469608805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303955693778686979739203 455933540668030469608805)
          ·
            refine ⟨85487538875255713051651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 455933540668030469608805 85487538875255713051651)
            ·
              refine ⟨128231308312883569577477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85487538875255713051651 128231308312883569577477)
              ·
                refine ⟨24043370308665669295777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128231308312883569577477 24043370308665669295777)
                ·
                  refine ⟨18032527731499251971833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24043370308665669295777 18032527731499251971833)
                  ·
                    rfl

theorem cell20_39508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_39508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39508 prefixEnd_39508 := by exact prefixLift 39508
  have htrace : WordTrace (prefixWord ++ tailWord_39508) baseStart_39508 baseEnd_39508 := by
    simpa [prefixWord, tailWord_39508, baseEnd_39508] using wordTrace_append hprefix tailTrace_39508
  have hstable : (prefixWord ++ tailWord_39508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39508).length < 2 ^ (prefixWord ++ tailWord_39508).sum := by decide
  have hdescent : baseEnd_39508 < baseStart_39508 := by decide
  rcases family_descends (prefixWord ++ tailWord_39508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39557 : List Nat := [1, 3, 1, 1, 4, 3, 7]
def baseStart_39557 : Nat := 118140960795 + 39557 * 2 ^ 59
def prefixEnd_39557 : Nat := 4983230072969 + 3 ^ 40 * 39557 * 2
def baseEnd_39557 : Nat := 2006099185185873259811

theorem tailTrace_39557 : CollatzResearch.WordTrace tailWord_39557 prefixEnd_39557 2006099185185873259811 := by
  unfold tailWord_39557
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442762317699219642852925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 961841545132813095235283 1442762317699219642852925)
  ·
    refine ⟨541035869137207366069847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1442762317699219642852925 541035869137207366069847)
    ·
      refine ⟨811553803705811049104771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541035869137207366069847 811553803705811049104771)
      ·
        refine ⟨1217330705558716573657157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811553803705811049104771 1217330705558716573657157)
        ·
          refine ⟨228249507292259357560717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1217330705558716573657157 228249507292259357560717)
          ·
            refine ⟨85593565234597259085269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228249507292259357560717 85593565234597259085269)
            ·
              refine ⟨2006099185185873259811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85593565234597259085269 2006099185185873259811)
              ·
                rfl

theorem cell20_39557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_39557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39557 prefixEnd_39557 := by exact prefixLift 39557
  have htrace : WordTrace (prefixWord ++ tailWord_39557) baseStart_39557 baseEnd_39557 := by
    simpa [prefixWord, tailWord_39557, baseEnd_39557] using wordTrace_append hprefix tailTrace_39557
  have hstable : (prefixWord ++ tailWord_39557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39557).length < 2 ^ (prefixWord ++ tailWord_39557).sum := by decide
  have hdescent : baseEnd_39557 < baseStart_39557 := by decide
  rcases family_descends (prefixWord ++ tailWord_39557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39571 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_39571 : Nat := 118140960795 + 39571 * 2 ^ 59
def prefixEnd_39571 : Nat := 4983230072969 + 3 ^ 40 * 39571 * 2
def baseEnd_39571 : Nat := 18061282648151032871575

theorem tailTrace_39571 : CollatzResearch.WordTrace tailWord_39571 prefixEnd_39571 18061282648151032871575 := by
  unfold tailWord_39571
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443272939648500033862567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 962181959765666689241711 1443272939648500033862567)
  ·
    refine ⟨2164909409472750050793851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1443272939648500033862567 2164909409472750050793851)
    ·
      refine ⟨3247364114209125076190777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164909409472750050793851 3247364114209125076190777)
      ·
        refine ⟨2435523085656843807143083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3247364114209125076190777 2435523085656843807143083)
        ·
          refine ⟨3653284628485265710714625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435523085656843807143083 3653284628485265710714625)
          ·
            refine ⟨2739963471363949283035969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3653284628485265710714625 2739963471363949283035969)
            ·
              refine ⟨2054972603522961962276977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2739963471363949283035969 2054972603522961962276977)
              ·
                refine ⟨1541229452642221471707733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054972603522961962276977 1541229452642221471707733)
                ·
                  refine ⟨18061282648151032871575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1541229452642221471707733 18061282648151032871575)
                  ·
                    rfl

theorem cell20_39571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_39571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39571 prefixEnd_39571 := by exact prefixLift 39571
  have htrace : WordTrace (prefixWord ++ tailWord_39571) baseStart_39571 baseEnd_39571 := by
    simpa [prefixWord, tailWord_39571, baseEnd_39571] using wordTrace_append hprefix tailTrace_39571
  have hstable : (prefixWord ++ tailWord_39571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39571).length < 2 ^ (prefixWord ++ tailWord_39571).sum := by decide
  have hdescent : baseEnd_39571 < baseStart_39571 := by decide
  rcases family_descends (prefixWord ++ tailWord_39571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39581 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 3]
def baseStart_39581 : Nat := 118140960795 + 39581 * 2 ^ 59
def prefixEnd_39581 : Nat := 4983230072969 + 3 ^ 40 * 39581 * 2
def baseEnd_39581 : Nat := 18065846920635442538201

theorem tailTrace_39581 : CollatzResearch.WordTrace tailWord_39581 prefixEnd_39581 18065846920635442538201 := by
  unfold tailWord_39581
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443637669612271741726597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 962425113074847827817731 1443637669612271741726597)
  ·
    refine ⟨270682063052300951573737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1443637669612271741726597 270682063052300951573737)
    ·
      refine ⟨203011547289225713680303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270682063052300951573737 203011547289225713680303)
      ·
        refine ⟨304517320933838570520455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203011547289225713680303 304517320933838570520455)
        ·
          refine ⟨456775981400757855780683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304517320933838570520455 456775981400757855780683)
          ·
            refine ⟨685163972101136783671025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456775981400757855780683 685163972101136783671025)
            ·
              refine ⟨513872979075852587753269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685163972101136783671025 513872979075852587753269)
              ·
                refine ⟨48175591788361180101869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513872979075852587753269 48175591788361180101869)
                ·
                  refine ⟨18065846920635442538201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48175591788361180101869 18065846920635442538201)
                  ·
                    rfl

theorem cell20_39581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_39581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39581 prefixEnd_39581 := by exact prefixLift 39581
  have htrace : WordTrace (prefixWord ++ tailWord_39581) baseStart_39581 baseEnd_39581 := by
    simpa [prefixWord, tailWord_39581, baseEnd_39581] using wordTrace_append hprefix tailTrace_39581
  have hstable : (prefixWord ++ tailWord_39581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39581).length < 2 ^ (prefixWord ++ tailWord_39581).sum := by decide
  have hdescent : baseEnd_39581 < baseStart_39581 := by decide
  rcases family_descends (prefixWord ++ tailWord_39581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39588 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_39588 : Nat := 118140960795 + 39588 * 2 ^ 59
def prefixEnd_39588 : Nat := 4983230072969 + 3 ^ 40 * 39588 * 2
def baseEnd_39588 : Nat := 18069041911374529304839

theorem tailTrace_39588 : CollatzResearch.WordTrace tailWord_39588 prefixEnd_39588 18069041911374529304839 := by
  unfold tailWord_39588
  simp only [CollatzResearch.WordTrace]
  refine ⟨721946490293455968615709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 962595320391274624820945 721946490293455968615709)
  ·
    refine ⟨270729933860045988230891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 721946490293455968615709 270729933860045988230891)
    ·
      refine ⟨406094900790068982346337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270729933860045988230891 406094900790068982346337)
      ·
        refine ⟨304571175592551736759753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406094900790068982346337 304571175592551736759753)
        ·
          refine ⟨228428381694413802569815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304571175592551736759753 228428381694413802569815)
          ·
            refine ⟨342642572541620703854723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228428381694413802569815 342642572541620703854723)
            ·
              refine ⟨513963858812431055782085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342642572541620703854723 513963858812431055782085)
              ·
                refine ⟨96368223527330822959141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513963858812431055782085 96368223527330822959141)
                ·
                  refine ⟨18069041911374529304839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96368223527330822959141 18069041911374529304839)
                  ·
                    rfl

theorem cell20_39588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_39588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39588 prefixEnd_39588 := by exact prefixLift 39588
  have htrace : WordTrace (prefixWord ++ tailWord_39588) baseStart_39588 baseEnd_39588 := by
    simpa [prefixWord, tailWord_39588, baseEnd_39588] using wordTrace_append hprefix tailTrace_39588
  have hstable : (prefixWord ++ tailWord_39588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39588).length < 2 ^ (prefixWord ++ tailWord_39588).sum := by decide
  have hdescent : baseEnd_39588 < baseStart_39588 := by decide
  rcases family_descends (prefixWord ++ tailWord_39588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39591 : List Nat := [1, 1, 6, 3, 1, 1, 1, 6]
def baseStart_39591 : Nat := 118140960795 + 39591 * 2 ^ 59
def prefixEnd_39591 : Nat := 4983230072969 + 3 ^ 40 * 39591 * 2
def baseEnd_39591 : Nat := 6023470397706617401609

theorem tailTrace_39591 : CollatzResearch.WordTrace tailWord_39591 prefixEnd_39591 6023470397706617401609 := by
  unfold tailWord_39591
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444002399576043449590627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 962668266384028966393751 1444002399576043449590627)
  ·
    refine ⟨2166003599364065174385941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1444002399576043449590627 2166003599364065174385941)
    ·
      refine ⟨101531418720190555049341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2166003599364065174385941 101531418720190555049341)
      ·
        refine ⟨38074282020071458143503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101531418720190555049341 38074282020071458143503)
        ·
          refine ⟨57111423030107187215255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38074282020071458143503 57111423030107187215255)
          ·
            refine ⟨85667134545160780822883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57111423030107187215255 85667134545160780822883)
            ·
              refine ⟨128500701817741171234325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85667134545160780822883 128500701817741171234325)
              ·
                refine ⟨6023470397706617401609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128500701817741171234325 6023470397706617401609)
                ·
                  rfl

theorem cell20_39591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_39591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39591 prefixEnd_39591 := by exact prefixLift 39591
  have htrace : WordTrace (prefixWord ++ tailWord_39591) baseStart_39591 baseEnd_39591 := by
    simpa [prefixWord, tailWord_39591, baseEnd_39591] using wordTrace_append hprefix tailTrace_39591
  have hstable : (prefixWord ++ tailWord_39591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39591).length < 2 ^ (prefixWord ++ tailWord_39591).sum := by decide
  have hdescent : baseEnd_39591 < baseStart_39591 := by decide
  rcases family_descends (prefixWord ++ tailWord_39591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39598 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_39598 : Nat := 118140960795 + 39598 * 2 ^ 59
def prefixEnd_39598 : Nat := 4983230072969 + 3 ^ 40 * 39598 * 2
def baseEnd_39598 : Nat := 18073606183858938971465

theorem tailTrace_39598 : CollatzResearch.WordTrace tailWord_39598 prefixEnd_39598 18073606183858938971465 := by
  unfold tailWord_39598
  simp only [CollatzResearch.WordTrace]
  refine ⟨180532213818835455636931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 962838473700455763396965 180532213818835455636931)
  ·
    refine ⟨270798320728253183455397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180532213818835455636931 270798320728253183455397)
    ·
      refine ⟨50774685136547471897887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 270798320728253183455397 50774685136547471897887)
      ·
        refine ⟨76162027704821207846831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50774685136547471897887 76162027704821207846831)
        ·
          refine ⟨114243041557231811770247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76162027704821207846831 114243041557231811770247)
          ·
            refine ⟨171364562335847717655371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114243041557231811770247 171364562335847717655371)
            ·
              refine ⟨257046843503771576483057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171364562335847717655371 257046843503771576483057)
              ·
                refine ⟨192785132627828682362293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257046843503771576483057 192785132627828682362293)
                ·
                  refine ⟨18073606183858938971465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192785132627828682362293 18073606183858938971465)
                  ·
                    rfl

theorem cell20_39598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_39598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39598 prefixEnd_39598 := by exact prefixLift 39598
  have htrace : WordTrace (prefixWord ++ tailWord_39598) baseStart_39598 baseEnd_39598 := by
    simpa [prefixWord, tailWord_39598, baseEnd_39598] using wordTrace_append hprefix tailTrace_39598
  have hstable : (prefixWord ++ tailWord_39598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39598).length < 2 ^ (prefixWord ++ tailWord_39598).sum := by decide
  have hdescent : baseEnd_39598 < baseStart_39598 := by decide
  rcases family_descends (prefixWord ++ tailWord_39598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39633 : List Nat := [1, 2, 2, 1, 2, 3, 4, 5]
def baseStart_39633 : Nat := 118140960795 + 39633 * 2 ^ 59
def prefixEnd_39633 : Nat := 4983230072969 + 3 ^ 40 * 39633 * 2
def baseEnd_39633 : Nat := 6029860379184790934885

theorem tailTrace_39633 : CollatzResearch.WordTrace tailWord_39633 prefixEnd_39633 6029860379184790934885 := by
  unfold tailWord_39633
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445534265423884622619553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 963689510282589748413035 1445534265423884622619553)
  ·
    refine ⟨1084150699067913466964665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1445534265423884622619553 1084150699067913466964665)
    ·
      refine ⟨813113024300935100223499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1084150699067913466964665 813113024300935100223499)
      ·
        refine ⟨1219669536451402650335249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813113024300935100223499 1219669536451402650335249)
        ·
          refine ⟨914752152338551987751437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1219669536451402650335249 914752152338551987751437)
          ·
            refine ⟨343032057126956995406789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 914752152338551987751437 343032057126956995406789)
            ·
              refine ⟨64318510711304436638773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 343032057126956995406789 64318510711304436638773)
              ·
                refine ⟨6029860379184790934885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64318510711304436638773 6029860379184790934885)
                ·
                  rfl

theorem cell20_39633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_39633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39633 prefixEnd_39633 := by exact prefixLift 39633
  have htrace : WordTrace (prefixWord ++ tailWord_39633) baseStart_39633 baseEnd_39633 := by
    simpa [prefixWord, tailWord_39633, baseEnd_39633] using wordTrace_append hprefix tailTrace_39633
  have hstable : (prefixWord ++ tailWord_39633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39633).length < 2 ^ (prefixWord ++ tailWord_39633).sum := by decide
  have hdescent : baseEnd_39633 < baseStart_39633 := by decide
  rcases family_descends (prefixWord ++ tailWord_39633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39685 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_39685 : Nat := 118140960795 + 39685 * 2 ^ 59
def prefixEnd_39685 : Nat := 4983230072969 + 3 ^ 40 * 39685 * 2
def baseEnd_39685 : Nat := 18113315354473303071109

theorem tailTrace_39685 : CollatzResearch.WordTrace tailWord_39685 prefixEnd_39685 18113315354473303071109 := by
  unfold tailWord_39685
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447430861235497503512509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 964953907490331669008339 1447430861235497503512509)
  ·
    refine ⟨542786572963311563817191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1447430861235497503512509 542786572963311563817191)
    ·
      refine ⟨814179859444967345725787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542786572963311563817191 814179859444967345725787)
      ·
        refine ⟨1221269789167451018588681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814179859444967345725787 1221269789167451018588681)
        ·
          refine ⟨915952341875588263941511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221269789167451018588681 915952341875588263941511)
          ·
            refine ⟨1373928512813382395912267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915952341875588263941511 1373928512813382395912267)
            ·
              refine ⟨2060892769220073593868401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373928512813382395912267 2060892769220073593868401)
              ·
                refine ⟨1545669576915055195401301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060892769220073593868401 1545669576915055195401301)
                ·
                  refine ⟨18113315354473303071109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1545669576915055195401301 18113315354473303071109)
                  ·
                    rfl

theorem cell20_39685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_39685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39685 prefixEnd_39685 := by exact prefixLift 39685
  have htrace : WordTrace (prefixWord ++ tailWord_39685) baseStart_39685 baseEnd_39685 := by
    simpa [prefixWord, tailWord_39685, baseEnd_39685] using wordTrace_append hprefix tailTrace_39685
  have hstable : (prefixWord ++ tailWord_39685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39685).length < 2 ^ (prefixWord ++ tailWord_39685).sum := by decide
  have hdescent : baseEnd_39685 < baseStart_39685 := by decide
  rcases family_descends (prefixWord ++ tailWord_39685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39688 : List Nat := [2, 1, 3, 2, 2, 4, 1, 5]
def baseStart_39688 : Nat := 118140960795 + 39688 * 2 ^ 59
def prefixEnd_39688 : Nat := 4983230072969 + 3 ^ 40 * 39688 * 2
def baseEnd_39688 : Nat := 6038228212072875323699

theorem tailTrace_39688 : CollatzResearch.WordTrace tailWord_39688 prefixEnd_39688 6038228212072875323699 := by
  unfold tailWord_39688
  simp only [CollatzResearch.WordTrace]
  refine ⟨723770140112314507935859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 965026853483086010581145 723770140112314507935859)
  ·
    refine ⟨1085655210168471761903789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723770140112314507935859 1085655210168471761903789)
    ·
      refine ⟨407120703813176910713921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1085655210168471761903789 407120703813176910713921)
      ·
        refine ⟨305340527859882683035441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407120703813176910713921 305340527859882683035441)
        ·
          refine ⟨229005395894912012276581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305340527859882683035441 229005395894912012276581)
          ·
            refine ⟨42938511730296002301859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229005395894912012276581 42938511730296002301859)
            ·
              refine ⟨64407767595444003452789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42938511730296002301859 64407767595444003452789)
              ·
                refine ⟨6038228212072875323699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64407767595444003452789 6038228212072875323699)
                ·
                  rfl

theorem cell20_39688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_39688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39688 prefixEnd_39688 := by exact prefixLift 39688
  have htrace : WordTrace (prefixWord ++ tailWord_39688) baseStart_39688 baseEnd_39688 := by
    simpa [prefixWord, tailWord_39688, baseEnd_39688] using wordTrace_append hprefix tailTrace_39688
  have hstable : (prefixWord ++ tailWord_39688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39688).length < 2 ^ (prefixWord ++ tailWord_39688).sum := by decide
  have hdescent : baseEnd_39688 < baseStart_39688 := by decide
  rcases family_descends (prefixWord ++ tailWord_39688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39698 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_39698 : Nat := 118140960795 + 39698 * 2 ^ 59
def prefixEnd_39698 : Nat := 4983230072969 + 3 ^ 40 * 39698 * 2
def baseEnd_39698 : Nat := 18119248908703035637723

theorem tailTrace_39698 : CollatzResearch.WordTrace tailWord_39698 prefixEnd_39698 18119248908703035637723 := by
  unfold tailWord_39698
  simp only [CollatzResearch.WordTrace]
  refine ⟨361976252547100180933937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 965270006792267149157165 361976252547100180933937)
  ·
    refine ⟨271482189410325135700453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 361976252547100180933937 271482189410325135700453)
    ·
      refine ⟨50902910514435962943835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271482189410325135700453 50902910514435962943835)
      ·
        refine ⟨76354365771653944415753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50902910514435962943835 76354365771653944415753)
        ·
          refine ⟨57265774328740458311815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76354365771653944415753 57265774328740458311815)
          ·
            refine ⟨85898661493110687467723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57265774328740458311815 85898661493110687467723)
            ·
              refine ⟨128847992239666031201585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85898661493110687467723 128847992239666031201585)
              ·
                refine ⟨96635994179749523401189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128847992239666031201585 96635994179749523401189)
                ·
                  refine ⟨18119248908703035637723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96635994179749523401189 18119248908703035637723)
                  ·
                    rfl

theorem cell20_39698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_39698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39698 prefixEnd_39698 := by exact prefixLift 39698
  have htrace : WordTrace (prefixWord ++ tailWord_39698) baseStart_39698 baseEnd_39698 := by
    simpa [prefixWord, tailWord_39698, baseEnd_39698] using wordTrace_append hprefix tailTrace_39698
  have hstable : (prefixWord ++ tailWord_39698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39698).length < 2 ^ (prefixWord ++ tailWord_39698).sum := by decide
  have hdescent : baseEnd_39698 < baseStart_39698 := by decide
  rcases family_descends (prefixWord ++ tailWord_39698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39725 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 3]
def baseStart_39725 : Nat := 118140960795 + 39725 * 2 ^ 59
def prefixEnd_39725 : Nat := 4983230072969 + 3 ^ 40 * 39725 * 2
def baseEnd_39725 : Nat := 18131572444410941737613

theorem tailTrace_39725 : CollatzResearch.WordTrace tailWord_39725 prefixEnd_39725 18131572444410941737613 := by
  unfold tailWord_39725
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448889781090584334968629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 965926520727056223312419 1448889781090584334968629)
  ·
    refine ⟨135833416977242281403309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1448889781090584334968629 135833416977242281403309)
    ·
      refine ⟨50937531366465855526241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135833416977242281403309 50937531366465855526241)
      ·
        refine ⟨38203148524849391644681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50937531366465855526241 38203148524849391644681)
        ·
          refine ⟨28652361393637043733511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38203148524849391644681 28652361393637043733511)
          ·
            refine ⟨42978542090455565600267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28652361393637043733511 42978542090455565600267)
            ·
              refine ⟨64467813135683348400401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42978542090455565600267 64467813135683348400401)
              ·
                refine ⟨48350859851762511300301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64467813135683348400401 48350859851762511300301)
                ·
                  refine ⟨18131572444410941737613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48350859851762511300301 18131572444410941737613)
                  ·
                    rfl

theorem cell20_39725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_39725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39725 prefixEnd_39725 := by exact prefixLift 39725
  have htrace : WordTrace (prefixWord ++ tailWord_39725) baseStart_39725 baseEnd_39725 := by
    simpa [prefixWord, tailWord_39725, baseEnd_39725] using wordTrace_append hprefix tailTrace_39725
  have hstable : (prefixWord ++ tailWord_39725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39725).length < 2 ^ (prefixWord ++ tailWord_39725).sum := by decide
  have hdescent : baseEnd_39725 < baseStart_39725 := by decide
  rcases family_descends (prefixWord ++ tailWord_39725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39726 : List Nat := [4, 1, 3, 2, 1, 2, 7]
def baseStart_39726 : Nat := 118140960795 + 39726 * 2 ^ 59
def prefixEnd_39726 : Nat := 4983230072969 + 3 ^ 40 * 39726 * 2
def baseEnd_39726 : Nat := 2014669874628820300475

theorem tailTrace_39726 : CollatzResearch.WordTrace tailWord_39726 prefixEnd_39726 2014669874628820300475 := by
  unfold tailWord_39726
  simp only [CollatzResearch.WordTrace]
  refine ⟨181115781760870188219379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 965950836057974337170021 181115781760870188219379)
  ·
    refine ⟨271673672641305282329069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181115781760870188219379 271673672641305282329069)
    ·
      refine ⟨101877627240489480873401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271673672641305282329069 101877627240489480873401)
      ·
        refine ⟨76408220430367110655051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101877627240489480873401 76408220430367110655051)
        ·
          refine ⟨114612330645550665982577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76408220430367110655051 114612330645550665982577)
          ·
            refine ⟨85959247984162999486933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114612330645550665982577 85959247984162999486933)
            ·
              refine ⟨2014669874628820300475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85959247984162999486933 2014669874628820300475)
              ·
                rfl

theorem cell20_39726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 7].length) (baseStart_39726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39726 prefixEnd_39726 := by exact prefixLift 39726
  have htrace : WordTrace (prefixWord ++ tailWord_39726) baseStart_39726 baseEnd_39726 := by
    simpa [prefixWord, tailWord_39726, baseEnd_39726] using wordTrace_append hprefix tailTrace_39726
  have hstable : (prefixWord ++ tailWord_39726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39726).length < 2 ^ (prefixWord ++ tailWord_39726).sum := by decide
  have hdescent : baseEnd_39726 < baseStart_39726 := by decide
  rcases family_descends (prefixWord ++ tailWord_39726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39733 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_39733 : Nat := 118140960795 + 39733 * 2 ^ 59
def prefixEnd_39733 : Nat := 4983230072969 + 3 ^ 40 * 39733 * 2
def baseEnd_39733 : Nat := 18135223862398469470913

theorem tailTrace_39733 : CollatzResearch.WordTrace tailWord_39733 prefixEnd_39733 18135223862398469470913 := by
  unfold tailWord_39733
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449181565061601701259853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 966121043374401134173235 1449181565061601701259853)
  ·
    refine ⟨543443086898100637972445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1449181565061601701259853 543443086898100637972445)
    ·
      refine ⟨203791157586787739239667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 543443086898100637972445 203791157586787739239667)
      ·
        refine ⟨305686736380181608859501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203791157586787739239667 305686736380181608859501)
        ·
          refine ⟨114632526142568103322313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305686736380181608859501 114632526142568103322313)
          ·
            refine ⟨85974394606926077491735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114632526142568103322313 85974394606926077491735)
            ·
              refine ⟨128961591910389116237603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85974394606926077491735 128961591910389116237603)
              ·
                refine ⟨193442387865583674356405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128961591910389116237603 193442387865583674356405)
                ·
                  refine ⟨18135223862398469470913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193442387865583674356405 18135223862398469470913)
                  ·
                    rfl

theorem cell20_39733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_39733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39733 prefixEnd_39733 := by exact prefixLift 39733
  have htrace : WordTrace (prefixWord ++ tailWord_39733) baseStart_39733 baseEnd_39733 := by
    simpa [prefixWord, tailWord_39733, baseEnd_39733] using wordTrace_append hprefix tailTrace_39733
  have hstable : (prefixWord ++ tailWord_39733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39733).length < 2 ^ (prefixWord ++ tailWord_39733).sum := by decide
  have hdescent : baseEnd_39733 < baseStart_39733 := by decide
  rcases family_descends (prefixWord ++ tailWord_39733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39764 : List Nat := [2, 4, 1, 1, 4, 1, 1, 6]
def baseStart_39764 : Nat := 118140960795 + 39764 * 2 ^ 59
def prefixEnd_39764 : Nat := 4983230072969 + 3 ^ 40 * 39764 * 2
def baseEnd_39764 : Nat := 6049791035700046479151

theorem tailTrace_39764 : CollatzResearch.WordTrace tailWord_39764 prefixEnd_39764 6049791035700046479151 := by
  unfold tailWord_39764
  simp only [CollatzResearch.WordTrace]
  refine ⟨725156113974646997819173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 966874818632862663758897 725156113974646997819173)
  ·
    refine ⟨135966771370246312091095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 725156113974646997819173 135966771370246312091095)
    ·
      refine ⟨203950157055369468136643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135966771370246312091095 203950157055369468136643)
      ·
        refine ⟨305925235583054202204965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203950157055369468136643 305925235583054202204965)
        ·
          refine ⟨57360981671822662913431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305925235583054202204965 57360981671822662913431)
          ·
            refine ⟨86041472507733994370147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57360981671822662913431 86041472507733994370147)
            ·
              refine ⟨129062208761600991555221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86041472507733994370147 129062208761600991555221)
              ·
                refine ⟨6049791035700046479151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129062208761600991555221 6049791035700046479151)
                ·
                  rfl

theorem cell20_39764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_39764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39764 prefixEnd_39764 := by exact prefixLift 39764
  have htrace : WordTrace (prefixWord ++ tailWord_39764) baseStart_39764 baseEnd_39764 := by
    simpa [prefixWord, tailWord_39764, baseEnd_39764] using wordTrace_append hprefix tailTrace_39764
  have hstable : (prefixWord ++ tailWord_39764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39764).length < 2 ^ (prefixWord ++ tailWord_39764).sum := by decide
  have hdescent : baseEnd_39764 < baseStart_39764 := by decide
  rcases family_descends (prefixWord ++ tailWord_39764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39792 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_39792 : Nat := 118140960795 + 39792 * 2 ^ 59
def prefixEnd_39792 : Nat := 4983230072969 + 3 ^ 40 * 39792 * 2
def baseEnd_39792 : Nat := 18162153070056486504005

theorem tailTrace_39792 : CollatzResearch.WordTrace tailWord_39792 prefixEnd_39792 18162153070056486504005 := by
  unfold tailWord_39792
  simp only [CollatzResearch.WordTrace]
  refine ⟨725666735923927388828815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 967555647898569851771753 725666735923927388828815)
  ·
    refine ⟨1088500103885891083243223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725666735923927388828815 1088500103885891083243223)
    ·
      refine ⟨1632750155828836624864835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1088500103885891083243223 1632750155828836624864835)
      ·
        refine ⟨2449125233743254937297253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632750155828836624864835 2449125233743254937297253)
        ·
          refine ⟨459210981326860300743235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2449125233743254937297253 459210981326860300743235)
          ·
            refine ⟨688816471990290451114853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459210981326860300743235 688816471990290451114853)
            ·
              refine ⟨129153088498179459584035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 688816471990290451114853 129153088498179459584035)
              ·
                refine ⟨193729632747269189376053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129153088498179459584035 193729632747269189376053)
                ·
                  refine ⟨18162153070056486504005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193729632747269189376053 18162153070056486504005)
                  ·
                    rfl

theorem cell20_39792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_39792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39792 prefixEnd_39792 := by exact prefixLift 39792
  have htrace : WordTrace (prefixWord ++ tailWord_39792) baseStart_39792 baseEnd_39792 := by
    simpa [prefixWord, tailWord_39792, baseEnd_39792] using wordTrace_append hprefix tailTrace_39792
  have hstable : (prefixWord ++ tailWord_39792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39792).length < 2 ^ (prefixWord ++ tailWord_39792).sum := by decide
  have hdescent : baseEnd_39792 < baseStart_39792 := by decide
  rcases family_descends (prefixWord ++ tailWord_39792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39857 : List Nat := [1, 2, 2, 4, 4, 1, 1, 5]
def baseStart_39857 : Nat := 118140960795 + 39857 * 2 ^ 59
def prefixEnd_39857 : Nat := 4983230072969 + 3 ^ 40 * 39857 * 2
def baseEnd_39857 : Nat := 6063940280401716445691

theorem tailTrace_39857 : CollatzResearch.WordTrace tailWord_39857 prefixEnd_39857 6063940280401716445691 := by
  unfold tailWord_39857
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453704216612370878773825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 969136144408247252515883 1453704216612370878773825)
  ·
    refine ⟨1090278162459278159080369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1453704216612370878773825 1090278162459278159080369)
    ·
      refine ⟨817708621844458619310277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1090278162459278159080369 817708621844458619310277)
      ·
        refine ⟨153320366595835991120677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 817708621844458619310277 153320366595835991120677)
        ·
          refine ⟨28747568736719248335127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153320366595835991120677 28747568736719248335127)
          ·
            refine ⟨43121353105078872502691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28747568736719248335127 43121353105078872502691)
            ·
              refine ⟨64682029657618308754037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43121353105078872502691 64682029657618308754037)
              ·
                refine ⟨6063940280401716445691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64682029657618308754037 6063940280401716445691)
                ·
                  rfl

theorem cell20_39857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 5].length) (baseStart_39857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39857 prefixEnd_39857 := by exact prefixLift 39857
  have htrace : WordTrace (prefixWord ++ tailWord_39857) baseStart_39857 baseEnd_39857 := by
    simpa [prefixWord, tailWord_39857, baseEnd_39857] using wordTrace_append hprefix tailTrace_39857
  have hstable : (prefixWord ++ tailWord_39857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39857).length < 2 ^ (prefixWord ++ tailWord_39857).sum := by decide
  have hdescent : baseEnd_39857 < baseStart_39857 := by decide
  rcases family_descends (prefixWord ++ tailWord_39857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39875 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_39875 : Nat := 118140960795 + 39875 * 2 ^ 59
def prefixEnd_39875 : Nat := 4983230072969 + 3 ^ 40 * 39875 * 2
def baseEnd_39875 : Nat := 18200036531677086736999

theorem tailTrace_39875 : CollatzResearch.WordTrace tailWord_39875 prefixEnd_39875 18200036531677086736999 := by
  unfold tailWord_39875
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454360730547159952929079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 969573820364773301952719 1454360730547159952929079)
  ·
    refine ⟨2181541095820739929393619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1454360730547159952929079 2181541095820739929393619)
    ·
      refine ⟨3272311643731109894090429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181541095820739929393619 3272311643731109894090429)
      ·
        refine ⟨1227116866399166210283911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3272311643731109894090429 1227116866399166210283911)
        ·
          refine ⟨1840675299598749315425867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227116866399166210283911 1840675299598749315425867)
          ·
            refine ⟨2761012949398123973138801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840675299598749315425867 2761012949398123973138801)
            ·
              refine ⟨2070759712048592979854101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2761012949398123973138801 2070759712048592979854101)
              ·
                refine ⟨97066861502277795930661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2070759712048592979854101 97066861502277795930661)
                ·
                  refine ⟨18200036531677086736999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97066861502277795930661 18200036531677086736999)
                  ·
                    rfl

theorem cell20_39875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_39875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39875 prefixEnd_39875 := by exact prefixLift 39875
  have htrace : WordTrace (prefixWord ++ tailWord_39875) baseStart_39875 baseEnd_39875 := by
    simpa [prefixWord, tailWord_39875, baseEnd_39875] using wordTrace_append hprefix tailTrace_39875
  have hstable : (prefixWord ++ tailWord_39875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39875).length < 2 ^ (prefixWord ++ tailWord_39875).sum := by decide
  have hdescent : baseEnd_39875 < baseStart_39875 := by decide
  rcases family_descends (prefixWord ++ tailWord_39875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39920 : List Nat := [2, 1, 1, 1, 3, 2, 1, 9]
def baseStart_39920 : Nat := 118140960795 + 39920 * 2 ^ 59
def prefixEnd_39920 : Nat := 4983230072969 + 3 ^ 40 * 39920 * 2
def baseEnd_39920 : Nat := 6073525252618976745605

theorem tailTrace_39920 : CollatzResearch.WordTrace tailWord_39920 prefixEnd_39920 6073525252618976745605 := by
  unfold tailWord_39920
  simp only [CollatzResearch.WordTrace]
  refine ⟨728001007692066319158607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 970668010256088425544809 728001007692066319158607)
  ·
    refine ⟨1092001511538099478737911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 728001007692066319158607 1092001511538099478737911)
    ·
      refine ⟨1638002267307149218106867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092001511538099478737911 1638002267307149218106867)
      ·
        refine ⟨2457003400960723827160301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638002267307149218106867 2457003400960723827160301)
        ·
          refine ⟨921376275360271435185113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2457003400960723827160301 921376275360271435185113)
          ·
            refine ⟨691032206520203576388835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 921376275360271435185113 691032206520203576388835)
            ·
              refine ⟨1036548309780305364583253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691032206520203576388835 1036548309780305364583253)
              ·
                refine ⟨6073525252618976745605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1036548309780305364583253 6073525252618976745605)
                ·
                  rfl

theorem cell20_39920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_39920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39920 prefixEnd_39920 := by exact prefixLift 39920
  have htrace : WordTrace (prefixWord ++ tailWord_39920) baseStart_39920 baseEnd_39920 := by
    simpa [prefixWord, tailWord_39920, baseEnd_39920] using wordTrace_append hprefix tailTrace_39920
  have hstable : (prefixWord ++ tailWord_39920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39920).length < 2 ^ (prefixWord ++ tailWord_39920).sum := by decide
  have hdescent : baseEnd_39920 < baseStart_39920 := by decide
  rcases family_descends (prefixWord ++ tailWord_39920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39937 : List Nat := [1, 2, 4, 1, 2, 3, 1, 6]
def baseStart_39937 : Nat := 118140960795 + 39937 * 2 ^ 59
def prefixEnd_39937 : Nat := 4983230072969 + 3 ^ 40 * 39937 * 2
def baseEnd_39937 : Nat := 6076111673693475556693

theorem tailTrace_39937 : CollatzResearch.WordTrace tailWord_39937 prefixEnd_39937 6076111673693475556693 := by
  unfold tailWord_39937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456622056322544541686065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 971081370881696361124043 1456622056322544541686065)
  ·
    refine ⟨1092466542241908406264549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1456622056322544541686065 1092466542241908406264549)
    ·
      refine ⟨204837476670357826174603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1092466542241908406264549 204837476670357826174603)
      ·
        refine ⟨307256215005536739261905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204837476670357826174603 307256215005536739261905)
        ·
          refine ⟨230442161254152554446429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307256215005536739261905 230442161254152554446429)
          ·
            refine ⟨86415810470307207917411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230442161254152554446429 86415810470307207917411)
            ·
              refine ⟨129623715705460811876117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86415810470307207917411 129623715705460811876117)
              ·
                refine ⟨6076111673693475556693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129623715705460811876117 6076111673693475556693)
                ·
                  rfl

theorem cell20_39937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_39937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39937 prefixEnd_39937 := by exact prefixLift 39937
  have htrace : WordTrace (prefixWord ++ tailWord_39937) baseStart_39937 baseEnd_39937 := by
    simpa [prefixWord, tailWord_39937, baseEnd_39937] using wordTrace_append hprefix tailTrace_39937
  have hstable : (prefixWord ++ tailWord_39937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39937).length < 2 ^ (prefixWord ++ tailWord_39937).sum := by decide
  have hdescent : baseEnd_39937 < baseStart_39937 := by decide
  rcases family_descends (prefixWord ++ tailWord_39937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39944 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_39944 : Nat := 118140960795 + 39944 * 2 ^ 59
def prefixEnd_39944 : Nat := 4983230072969 + 3 ^ 40 * 39944 * 2
def baseEnd_39944 : Nat := 18231530011819513436717

theorem tailTrace_39944 : CollatzResearch.WordTrace tailWord_39944 prefixEnd_39944 18231530011819513436717 := by
  unfold tailWord_39944
  simp only [CollatzResearch.WordTrace]
  refine ⟨728438683648592368595443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 971251578198123158127257 728438683648592368595443)
  ·
    refine ⟨1092658025472888552893165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 728438683648592368595443 1092658025472888552893165)
    ·
      refine ⟨409746759552333207334937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1092658025472888552893165 409746759552333207334937)
      ·
        refine ⟨307310069664249905501203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409746759552333207334937 307310069664249905501203)
        ·
          refine ⟨460965104496374858251805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307310069664249905501203 460965104496374858251805)
          ·
            refine ⟨172861914186140571844427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460965104496374858251805 172861914186140571844427)
            ·
              refine ⟨259292871279210857766641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172861914186140571844427 259292871279210857766641)
              ·
                refine ⟨194469653459408143324981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259292871279210857766641 194469653459408143324981)
                ·
                  refine ⟨18231530011819513436717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194469653459408143324981 18231530011819513436717)
                  ·
                    rfl

theorem cell20_39944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_39944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39944 prefixEnd_39944 := by exact prefixLift 39944
  have htrace : WordTrace (prefixWord ++ tailWord_39944) baseStart_39944 baseEnd_39944 := by
    simpa [prefixWord, tailWord_39944, baseEnd_39944] using wordTrace_append hprefix tailTrace_39944
  have hstable : (prefixWord ++ tailWord_39944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39944).length < 2 ^ (prefixWord ++ tailWord_39944).sum := by decide
  have hdescent : baseEnd_39944 < baseStart_39944 := by decide
  rcases family_descends (prefixWord ++ tailWord_39944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39947 : List Nat := [1, 1, 1, 1, 6, 2, 3, 3, 2]
def baseStart_39947 : Nat := 118140960795 + 39947 * 2 ^ 59
def prefixEnd_39947 : Nat := 4983230072969 + 3 ^ 40 * 39947 * 2
def baseEnd_39947 : Nat := 18232899293564836336705

theorem tailTrace_39947 : CollatzResearch.WordTrace tailWord_39947 prefixEnd_39947 18232899293564836336705 := by
  unfold tailWord_39947
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456986786286316249550095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 971324524190877499700063 1456986786286316249550095)
  ·
    refine ⟨2185480179429474374325143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1456986786286316249550095 2185480179429474374325143)
    ·
      refine ⟨3278220269144211561487715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2185480179429474374325143 3278220269144211561487715)
      ·
        refine ⟨4917330403716317342231573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3278220269144211561487715 4917330403716317342231573)
        ·
          refine ⟨230499862674202375417105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4917330403716317342231573 230499862674202375417105)
          ·
            refine ⟨172874897005651781562829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230499862674202375417105 172874897005651781562829)
            ·
              refine ⟨64828086377119418086061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172874897005651781562829 64828086377119418086061)
              ·
                refine ⟨24310532391419781782273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64828086377119418086061 24310532391419781782273)
                ·
                  refine ⟨18232899293564836336705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24310532391419781782273 18232899293564836336705)
                  ·
                    rfl

theorem cell20_39947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 2].length) (baseStart_39947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39947 prefixEnd_39947 := by exact prefixLift 39947
  have htrace : WordTrace (prefixWord ++ tailWord_39947) baseStart_39947 baseEnd_39947 := by
    simpa [prefixWord, tailWord_39947, baseEnd_39947] using wordTrace_append hprefix tailTrace_39947
  have hstable : (prefixWord ++ tailWord_39947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39947).length < 2 ^ (prefixWord ++ tailWord_39947).sum := by decide
  have hdescent : baseEnd_39947 < baseStart_39947 := by decide
  rcases family_descends (prefixWord ++ tailWord_39947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39964 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 4]
def baseStart_39964 : Nat := 118140960795 + 39964 * 2 ^ 59
def prefixEnd_39964 : Nat := 4983230072969 + 3 ^ 40 * 39964 * 2
def baseEnd_39964 : Nat := 18240658556788332769969

theorem tailTrace_39964 : CollatzResearch.WordTrace tailWord_39964 prefixEnd_39964 18240658556788332769969 := by
  unfold tailWord_39964
  simp only [CollatzResearch.WordTrace]
  refine ⟨728803413612364076459473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 971737884816485435279297 728803413612364076459473)
  ·
    refine ⟨546602560209273057344605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 728803413612364076459473 546602560209273057344605)
    ·
      refine ⟨204975960078477396504227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 546602560209273057344605 204975960078477396504227)
      ·
        refine ⟨307463940117716094756341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204975960078477396504227 307463940117716094756341)
        ·
          refine ⟨28824744386035883883407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307463940117716094756341 28824744386035883883407)
          ·
            refine ⟨43237116579053825825111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28824744386035883883407 43237116579053825825111)
            ·
              refine ⟨64855674868580738737667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43237116579053825825111 64855674868580738737667)
              ·
                refine ⟨97283512302871108106501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64855674868580738737667 97283512302871108106501)
                ·
                  refine ⟨18240658556788332769969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97283512302871108106501 18240658556788332769969)
                  ·
                    rfl

theorem cell20_39964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_39964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39964 prefixEnd_39964 := by exact prefixLift 39964
  have htrace : WordTrace (prefixWord ++ tailWord_39964) baseStart_39964 baseEnd_39964 := by
    simpa [prefixWord, tailWord_39964, baseEnd_39964] using wordTrace_append hprefix tailTrace_39964
  have hstable : (prefixWord ++ tailWord_39964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39964).length < 2 ^ (prefixWord ++ tailWord_39964).sum := by decide
  have hdescent : baseEnd_39964 < baseStart_39964 := by decide
  rcases family_descends (prefixWord ++ tailWord_39964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39978 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_39978 : Nat := 118140960795 + 39978 * 2 ^ 59
def prefixEnd_39978 : Nat := 4983230072969 + 3 ^ 40 * 39978 * 2
def baseEnd_39978 : Nat := 18247048538266506303245

theorem tailTrace_39978 : CollatzResearch.WordTrace tailWord_39978 prefixEnd_39978 18247048538266506303245 := by
  unfold tailWord_39978
  simp only [CollatzResearch.WordTrace]
  refine ⟨364529362293502135982147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 972078299449339029285725 364529362293502135982147)
  ·
    refine ⟨546794043440253203973221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 364529362293502135982147 546794043440253203973221)
    ·
      refine ⟨102523883145047475744979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 546794043440253203973221 102523883145047475744979)
      ·
        refine ⟨153785824717571213617469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102523883145047475744979 153785824717571213617469)
        ·
          refine ⟨57669684269089205106551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153785824717571213617469 57669684269089205106551)
          ·
            refine ⟨86504526403633807659827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57669684269089205106551 86504526403633807659827)
            ·
              refine ⟨129756789605450711489741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86504526403633807659827 129756789605450711489741)
              ·
                refine ⟨48658796102044016808653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129756789605450711489741 48658796102044016808653)
                ·
                  refine ⟨18247048538266506303245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48658796102044016808653 18247048538266506303245)
                  ·
                    rfl

theorem cell20_39978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_39978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39978 prefixEnd_39978 := by exact prefixLift 39978
  have htrace : WordTrace (prefixWord ++ tailWord_39978) baseStart_39978 baseEnd_39978 := by
    simpa [prefixWord, tailWord_39978, baseEnd_39978] using wordTrace_append hprefix tailTrace_39978
  have hstable : (prefixWord ++ tailWord_39978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39978).length < 2 ^ (prefixWord ++ tailWord_39978).sum := by decide
  have hdescent : baseEnd_39978 < baseStart_39978 := by decide
  rcases family_descends (prefixWord ++ tailWord_39978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39989 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_39989 : Nat := 118140960795 + 39989 * 2 ^ 59
def prefixEnd_39989 : Nat := 4983230072969 + 3 ^ 40 * 39989 * 2
def baseEnd_39989 : Nat := 18252069237999356936533

theorem tailTrace_39989 : CollatzResearch.WordTrace tailWord_39989 prefixEnd_39989 18252069237999356936533 := by
  unfold tailWord_39989
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458518652134157422579021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 972345768089438281719347 1458518652134157422579021)
  ·
    refine ⟨546944494550309033467133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1458518652134157422579021 546944494550309033467133)
    ·
      refine ⟨205104185456365887550175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 546944494550309033467133 205104185456365887550175)
      ·
        refine ⟨307656278184548831325263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205104185456365887550175 307656278184548831325263)
        ·
          refine ⟨461484417276823246987895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307656278184548831325263 461484417276823246987895)
          ·
            refine ⟨692226625915234870481843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461484417276823246987895 692226625915234870481843)
            ·
              refine ⟨1038339938872852305722765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692226625915234870481843 1038339938872852305722765)
              ·
                refine ⟨389377477077319614646037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1038339938872852305722765 389377477077319614646037)
                ·
                  refine ⟨18252069237999356936533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 389377477077319614646037 18252069237999356936533)
                  ·
                    rfl

theorem cell20_39989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_39989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_39989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_39989 prefixEnd_39989 := by exact prefixLift 39989
  have htrace : WordTrace (prefixWord ++ tailWord_39989) baseStart_39989 baseEnd_39989 := by
    simpa [prefixWord, tailWord_39989, baseEnd_39989] using wordTrace_append hprefix tailTrace_39989
  have hstable : (prefixWord ++ tailWord_39989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39989).length < 2 ^ (prefixWord ++ tailWord_39989).sum := by decide
  have hdescent : baseEnd_39989 < baseStart_39989 := by decide
  rcases family_descends (prefixWord ++ tailWord_39989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40013 : List Nat := [1, 6, 1, 1, 1, 10]
def baseStart_40013 : Nat := 118140960795 + 40013 * 2 ^ 59
def prefixEnd_40013 : Nat := 4983230072969 + 3 ^ 40 * 40013 * 2
def baseEnd_40013 : Nat := 676408277480071856905

theorem tailTrace_40013 : CollatzResearch.WordTrace tailWord_40013 prefixEnd_40013 676408277480071856905 := by
  unfold tailWord_40013
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459394004047209521452693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 972929336031473014301795 1459394004047209521452693)
  ·
    refine ⟨68409093939712946318095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1459394004047209521452693 68409093939712946318095)
    ·
      refine ⟨102613640909569419477143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68409093939712946318095 102613640909569419477143)
      ·
        refine ⟨153920461364354129215715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102613640909569419477143 153920461364354129215715)
        ·
          refine ⟨230880692046531193823573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153920461364354129215715 230880692046531193823573)
          ·
            refine ⟨676408277480071856905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 230880692046531193823573 676408277480071856905)
            ·
              rfl

theorem cell20_40013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 10].length) (baseStart_40013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40013 prefixEnd_40013 := by exact prefixLift 40013
  have htrace : WordTrace (prefixWord ++ tailWord_40013) baseStart_40013 baseEnd_40013 := by
    simpa [prefixWord, tailWord_40013, baseEnd_40013] using wordTrace_append hprefix tailTrace_40013
  have hstable : (prefixWord ++ tailWord_40013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40013).length < 2 ^ (prefixWord ++ tailWord_40013).sum := by decide
  have hdescent : baseEnd_40013 < baseStart_40013 := by decide
  rcases family_descends (prefixWord ++ tailWord_40013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40020 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_40020 : Nat := 118140960795 + 40020 * 2 ^ 59
def prefixEnd_40020 : Nat := 4983230072969 + 3 ^ 40 * 40020 * 2
def baseEnd_40020 : Nat := 18266218482701026903073

theorem tailTrace_40020 : CollatzResearch.WordTrace tailWord_40020 prefixEnd_40020 18266218482701026903073 := by
  unfold tailWord_40020
  simp only [CollatzResearch.WordTrace]
  refine ⟨729824657510924858478757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 973099543347899811305009 729824657510924858478757)
  ·
    refine ⟨136842123283298410964767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 729824657510924858478757 136842123283298410964767)
    ·
      refine ⟨205263184924947616447151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136842123283298410964767 205263184924947616447151)
      ·
        refine ⟨307894777387421424670727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205263184924947616447151 307894777387421424670727)
        ·
          refine ⟨461842166081132137006091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307894777387421424670727 461842166081132137006091)
          ·
            refine ⟨692763249121698205509137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461842166081132137006091 692763249121698205509137)
            ·
              refine ⟨519572436841273654131853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692763249121698205509137 519572436841273654131853)
              ·
                refine ⟨194839663815477620299445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 519572436841273654131853 194839663815477620299445)
                ·
                  refine ⟨18266218482701026903073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194839663815477620299445 18266218482701026903073)
                  ·
                    rfl

theorem cell20_40020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_40020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40020 prefixEnd_40020 := by exact prefixLift 40020
  have htrace : WordTrace (prefixWord ++ tailWord_40020) baseStart_40020 baseEnd_40020 := by
    simpa [prefixWord, tailWord_40020, baseEnd_40020] using wordTrace_append hprefix tailTrace_40020
  have hstable : (prefixWord ++ tailWord_40020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40020).length < 2 ^ (prefixWord ++ tailWord_40020).sum := by decide
  have hdescent : baseEnd_40020 < baseStart_40020 := by decide
  rcases family_descends (prefixWord ++ tailWord_40020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40061 : List Nat := [1, 4, 1, 1, 3, 1, 4, 3, 2]
def baseStart_40061 : Nat := 118140960795 + 40061 * 2 ^ 59
def prefixEnd_40061 : Nat := 4983230072969 + 3 ^ 40 * 40061 * 2
def baseEnd_40061 : Nat := 18284931999887106536239

theorem tailTrace_40061 : CollatzResearch.WordTrace tailWord_40061 prefixEnd_40061 18284931999887106536239 := by
  unfold tailWord_40061
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461144707873313719200037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 974096471915542479466691 1461144707873313719200037)
  ·
    refine ⟨273964632726246322350007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1461144707873313719200037 273964632726246322350007)
    ·
      refine ⟨410946949089369483525011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273964632726246322350007 410946949089369483525011)
      ·
        refine ⟨616420423634054225287517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410946949089369483525011 616420423634054225287517)
        ·
          refine ⟨231157658862770334482819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 616420423634054225287517 231157658862770334482819)
          ·
            refine ⟨346736488294155501724229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231157658862770334482819 346736488294155501724229)
            ·
              refine ⟨65013091555154156573293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346736488294155501724229 65013091555154156573293)
              ·
                refine ⟨24379909333182808714985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65013091555154156573293 24379909333182808714985)
                ·
                  refine ⟨18284931999887106536239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24379909333182808714985 18284931999887106536239)
                  ·
                    rfl

theorem cell20_40061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_40061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40061 prefixEnd_40061 := by exact prefixLift 40061
  have htrace : WordTrace (prefixWord ++ tailWord_40061) baseStart_40061 baseEnd_40061 := by
    simpa [prefixWord, tailWord_40061, baseEnd_40061] using wordTrace_append hprefix tailTrace_40061
  have hstable : (prefixWord ++ tailWord_40061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40061).length < 2 ^ (prefixWord ++ tailWord_40061).sum := by decide
  have hdescent : baseEnd_40061 < baseStart_40061 := by decide
  rcases family_descends (prefixWord ++ tailWord_40061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40082 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_40082 : Nat := 118140960795 + 40082 * 2 ^ 59
def prefixEnd_40082 : Nat := 4983230072969 + 3 ^ 40 * 40082 * 2
def baseEnd_40082 : Nat := 18294516972104366836153

theorem tailTrace_40082 : CollatzResearch.WordTrace tailWord_40082 prefixEnd_40082 18294516972104366836153 := by
  unfold tailWord_40082
  simp only [CollatzResearch.WordTrace]
  refine ⟨365477660199308576428625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 974607093864822870476333 365477660199308576428625)
  ·
    refine ⟨274108245149481432321469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 365477660199308576428625 274108245149481432321469)
    ·
      refine ⟨102790591931055537120551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274108245149481432321469 102790591931055537120551)
      ·
        refine ⟨154185887896583305680827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102790591931055537120551 154185887896583305680827)
        ·
          refine ⟨231278831844874958521241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154185887896583305680827 231278831844874958521241)
          ·
            refine ⟨173459123883656218890931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231278831844874958521241 173459123883656218890931)
            ·
              refine ⟨260188685825484328336397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173459123883656218890931 260188685825484328336397)
              ·
                refine ⟨97570757184556623126149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260188685825484328336397 97570757184556623126149)
                ·
                  refine ⟨18294516972104366836153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97570757184556623126149 18294516972104366836153)
                  ·
                    rfl

theorem cell20_40082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_40082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40082 prefixEnd_40082 := by exact prefixLift 40082
  have htrace : WordTrace (prefixWord ++ tailWord_40082) baseStart_40082 baseEnd_40082 := by
    simpa [prefixWord, tailWord_40082, baseEnd_40082] using wordTrace_append hprefix tailTrace_40082
  have hstable : (prefixWord ++ tailWord_40082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40082).length < 2 ^ (prefixWord ++ tailWord_40082).sum := by decide
  have hdescent : baseEnd_40082 < baseStart_40082 := by decide
  rcases family_descends (prefixWord ++ tailWord_40082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40092 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_40092 : Nat := 118140960795 + 40092 * 2 ^ 59
def prefixEnd_40092 : Nat := 4983230072969 + 3 ^ 40 * 40092 * 2
def baseEnd_40092 : Nat := 18299081244588776502779

theorem tailTrace_40092 : CollatzResearch.WordTrace tailWord_40092 prefixEnd_40092 18299081244588776502779 := by
  unfold tailWord_40092
  simp only [CollatzResearch.WordTrace]
  refine ⟨731137685380503006789265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 974850247174004009052353 731137685380503006789265)
  ·
    refine ⟨548353264035377255091949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 731137685380503006789265 548353264035377255091949)
    ·
      refine ⟨205632474013266470659481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 548353264035377255091949 205632474013266470659481)
      ·
        refine ⟨154224355509949852994611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205632474013266470659481 154224355509949852994611)
        ·
          refine ⟨231336533264924779491917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154224355509949852994611 231336533264924779491917)
          ·
            refine ⟨86751199974346792309469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231336533264924779491917 86751199974346792309469)
            ·
              refine ⟨32531699990380047116051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86751199974346792309469 32531699990380047116051)
              ·
                refine ⟨48797549985570070674077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32531699990380047116051 48797549985570070674077)
                ·
                  refine ⟨18299081244588776502779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48797549985570070674077 18299081244588776502779)
                  ·
                    rfl

theorem cell20_40092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_40092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40092 prefixEnd_40092 := by exact prefixLift 40092
  have htrace : WordTrace (prefixWord ++ tailWord_40092) baseStart_40092 baseEnd_40092 := by
    simpa [prefixWord, tailWord_40092, baseEnd_40092] using wordTrace_append hprefix tailTrace_40092
  have hstable : (prefixWord ++ tailWord_40092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40092).length < 2 ^ (prefixWord ++ tailWord_40092).sum := by decide
  have hdescent : baseEnd_40092 < baseStart_40092 := by decide
  rcases family_descends (prefixWord ++ tailWord_40092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40106 : List Nat := [3, 1, 5, 1, 1, 2, 1, 6]
def baseStart_40106 : Nat := 118140960795 + 40106 * 2 ^ 59
def prefixEnd_40106 : Nat := 4983230072969 + 3 ^ 40 * 40106 * 2
def baseEnd_40106 : Nat := 6101823742022316678685

theorem tailTrace_40106 : CollatzResearch.WordTrace tailWord_40106 prefixEnd_40106 6101823742022316678685 := by
  unfold tailWord_40106
  simp only [CollatzResearch.WordTrace]
  refine ⟨365696498177571601147043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 975190661806857603058781 365696498177571601147043)
  ·
    refine ⟨548544747266357401720565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 365696498177571601147043 548544747266357401720565)
    ·
      refine ⟨51426070056221006411303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 548544747266357401720565 51426070056221006411303)
      ·
        refine ⟨77139105084331509616955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51426070056221006411303 77139105084331509616955)
        ·
          refine ⟨115708657626497264425433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77139105084331509616955 115708657626497264425433)
          ·
            refine ⟨86781493219872948319075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115708657626497264425433 86781493219872948319075)
            ·
              refine ⟨130172239829809422478613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86781493219872948319075 130172239829809422478613)
              ·
                refine ⟨6101823742022316678685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130172239829809422478613 6101823742022316678685)
                ·
                  rfl

theorem cell20_40106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_40106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40106 prefixEnd_40106 := by exact prefixLift 40106
  have htrace : WordTrace (prefixWord ++ tailWord_40106) baseStart_40106 baseEnd_40106 := by
    simpa [prefixWord, tailWord_40106, baseEnd_40106] using wordTrace_append hprefix tailTrace_40106
  have hstable : (prefixWord ++ tailWord_40106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40106).length < 2 ^ (prefixWord ++ tailWord_40106).sum := by decide
  have hdescent : baseEnd_40106 < baseStart_40106 := by decide
  rcases family_descends (prefixWord ++ tailWord_40106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40120 : List Nat := [2, 1, 2, 1, 2, 1, 2, 7, 2]
def baseStart_40120 : Nat := 118140960795 + 40120 * 2 ^ 59
def prefixEnd_40120 : Nat := 4983230072969 + 3 ^ 40 * 40120 * 2
def baseEnd_40120 : Nat := 18311861207545123569331

theorem tailTrace_40120 : CollatzResearch.WordTrace tailWord_40120 prefixEnd_40120 18311861207545123569331 := by
  unfold tailWord_40120
  simp only [CollatzResearch.WordTrace]
  refine ⟨731648307329783397798907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 975531076439711197065209 731648307329783397798907)
  ·
    refine ⟨1097472460994675096698361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 731648307329783397798907 1097472460994675096698361)
    ·
      refine ⟨823104345746006322523771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1097472460994675096698361 823104345746006322523771)
      ·
        refine ⟨1234656518619009483785657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823104345746006322523771 1234656518619009483785657)
        ·
          refine ⟨925992388964257112839243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1234656518619009483785657 925992388964257112839243)
          ·
            refine ⟨1388988583446385669258865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925992388964257112839243 1388988583446385669258865)
            ·
              refine ⟨1041741437584789251944149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388988583446385669258865 1041741437584789251944149)
              ·
                refine ⟨24415814943393498092441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1041741437584789251944149 24415814943393498092441)
                ·
                  refine ⟨18311861207545123569331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24415814943393498092441 18311861207545123569331)
                  ·
                    rfl

theorem cell20_40120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_40120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40120 prefixEnd_40120 := by exact prefixLift 40120
  have htrace : WordTrace (prefixWord ++ tailWord_40120) baseStart_40120 baseEnd_40120 := by
    simpa [prefixWord, tailWord_40120, baseEnd_40120] using wordTrace_append hprefix tailTrace_40120
  have hstable : (prefixWord ++ tailWord_40120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40120).length < 2 ^ (prefixWord ++ tailWord_40120).sum := by decide
  have hdescent : baseEnd_40120 < baseStart_40120 := by decide
  rcases family_descends (prefixWord ++ tailWord_40120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40151 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 3]
def baseStart_40151 : Nat := 118140960795 + 40151 * 2 ^ 59
def prefixEnd_40151 : Nat := 4983230072969 + 3 ^ 40 * 40151 * 2
def baseEnd_40151 : Nat := 18326010452246793535871

theorem tailTrace_40151 : CollatzResearch.WordTrace tailWord_40151 prefixEnd_40151 18326010452246793535871 := by
  unfold tailWord_40151
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464427277547259089976307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 976284851698172726650871 1464427277547259089976307)
  ·
    refine ⟨2196640916320888634964461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1464427277547259089976307 2196640916320888634964461)
    ·
      refine ⟨823740343620333238111673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2196640916320888634964461 823740343620333238111673)
      ·
        refine ⟨617805257715249928583755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 823740343620333238111673 617805257715249928583755)
        ·
          refine ⟨926707886572874892875633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617805257715249928583755 926707886572874892875633)
          ·
            refine ⟨695030914929656169656725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926707886572874892875633 695030914929656169656725)
            ·
              refine ⟨32579574137327632952659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 695030914929656169656725 32579574137327632952659)
              ·
                refine ⟨48869361205991449428989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32579574137327632952659 48869361205991449428989)
                ·
                  refine ⟨18326010452246793535871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48869361205991449428989 18326010452246793535871)
                  ·
                    rfl

theorem cell20_40151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 3].length) (baseStart_40151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40151 prefixEnd_40151 := by exact prefixLift 40151
  have htrace : WordTrace (prefixWord ++ tailWord_40151) baseStart_40151 baseEnd_40151 := by
    simpa [prefixWord, tailWord_40151, baseEnd_40151] using wordTrace_append hprefix tailTrace_40151
  have hstable : (prefixWord ++ tailWord_40151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40151).length < 2 ^ (prefixWord ++ tailWord_40151).sum := by decide
  have hdescent : baseEnd_40151 < baseStart_40151 := by decide
  rcases family_descends (prefixWord ++ tailWord_40151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40203 : List Nat := [1, 1, 1, 1, 5, 5, 1, 5]
def baseStart_40203 : Nat := 118140960795 + 40203 * 2 ^ 59
def prefixEnd_40203 : Nat := 4983230072969 + 3 ^ 40 * 40203 * 2
def baseEnd_40203 : Nat := 6116581556388574600775

theorem tailTrace_40203 : CollatzResearch.WordTrace tailWord_40203 prefixEnd_40203 6116581556388574600775 := by
  unfold tailWord_40203
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466323873358871970869263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 977549248905914647246175 1466323873358871970869263)
  ·
    refine ⟨2199485810038307956303895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1466323873358871970869263 2199485810038307956303895)
    ·
      refine ⟨3299228715057461934455843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199485810038307956303895 3299228715057461934455843)
      ·
        refine ⟨4948843072586192901683765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299228715057461934455843 4948843072586192901683765)
        ·
          refine ⟨463954038054955584532853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4948843072586192901683765 463954038054955584532853)
          ·
            refine ⟨43495691067652086049955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 463954038054955584532853 43495691067652086049955)
            ·
              refine ⟨65243536601478129074933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43495691067652086049955 65243536601478129074933)
              ·
                refine ⟨6116581556388574600775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65243536601478129074933 6116581556388574600775)
                ·
                  rfl

theorem cell20_40203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_40203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40203 prefixEnd_40203 := by exact prefixLift 40203
  have htrace : WordTrace (prefixWord ++ tailWord_40203) baseStart_40203 baseEnd_40203 := by
    simpa [prefixWord, tailWord_40203, baseEnd_40203] using wordTrace_append hprefix tailTrace_40203
  have hstable : (prefixWord ++ tailWord_40203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40203).length < 2 ^ (prefixWord ++ tailWord_40203).sum := by decide
  have hdescent : baseEnd_40203 < baseStart_40203 := by decide
  rcases family_descends (prefixWord ++ tailWord_40203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40255 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_40255 : Nat := 118140960795 + 40255 * 2 ^ 59
def prefixEnd_40255 : Nat := 4983230072969 + 3 ^ 40 * 40255 * 2
def baseEnd_40255 : Nat := 18373478886084654068779

theorem tailTrace_40255 : CollatzResearch.WordTrace tailWord_40255 prefixEnd_40255 18373478886084654068779 := by
  unfold tailWord_40255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468220469170484851762219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 978813646113656567841479 1468220469170484851762219)
  ·
    refine ⟨2202330703755727277643329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468220469170484851762219 2202330703755727277643329)
    ·
      refine ⟨1651748027816795458232497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2202330703755727277643329 1651748027816795458232497)
      ·
        refine ⟨1238811020862596593674373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1651748027816795458232497 1238811020862596593674373)
        ·
          refine ⟨232277066411736861313945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1238811020862596593674373 232277066411736861313945)
          ·
            refine ⟨174207799808802645985459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232277066411736861313945 174207799808802645985459)
            ·
              refine ⟨261311699713203968978189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174207799808802645985459 261311699713203968978189)
              ·
                refine ⟨97991887392451488366821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261311699713203968978189 97991887392451488366821)
                ·
                  refine ⟨18373478886084654068779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97991887392451488366821 18373478886084654068779)
                  ·
                    rfl

theorem cell20_40255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_40255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40255 prefixEnd_40255 := by exact prefixLift 40255
  have htrace : WordTrace (prefixWord ++ tailWord_40255) baseStart_40255 baseEnd_40255 := by
    simpa [prefixWord, tailWord_40255, baseEnd_40255] using wordTrace_append hprefix tailTrace_40255
  have hstable : (prefixWord ++ tailWord_40255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40255).length < 2 ^ (prefixWord ++ tailWord_40255).sum := by decide
  have hdescent : baseEnd_40255 < baseStart_40255 := by decide
  rcases family_descends (prefixWord ++ tailWord_40255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40279 : List Nat := [1, 1, 3, 2, 3, 2, 4, 4]
def baseStart_40279 : Nat := 118140960795 + 40279 * 2 ^ 59
def prefixEnd_40279 : Nat := 4983230072969 + 3 ^ 40 * 40279 * 2
def baseEnd_40279 : Nat := 6128144380015745756227

theorem tailTrace_40279 : CollatzResearch.WordTrace tailWord_40279 prefixEnd_40279 6128144380015745756227 := by
  unfold tailWord_40279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469095821083536950635891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 979397214055691300423927 1469095821083536950635891)
  ·
    refine ⟨2203643731625305425953837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1469095821083536950635891 2203643731625305425953837)
    ·
      refine ⟨826366399359489534732689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2203643731625305425953837 826366399359489534732689)
      ·
        refine ⟨619774799519617151049517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 826366399359489534732689 619774799519617151049517)
        ·
          refine ⟨232415549819856431643569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 619774799519617151049517 232415549819856431643569)
          ·
            refine ⟨174311662364892323732677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232415549819856431643569 174311662364892323732677)
            ·
              refine ⟨32683436693417310699877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174311662364892323732677 32683436693417310699877)
              ·
                refine ⟨6128144380015745756227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32683436693417310699877 6128144380015745756227)
                ·
                  rfl

theorem cell20_40279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_40279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40279 prefixEnd_40279 := by exact prefixLift 40279
  have htrace : WordTrace (prefixWord ++ tailWord_40279) baseStart_40279 baseEnd_40279 := by
    simpa [prefixWord, tailWord_40279, baseEnd_40279] using wordTrace_append hprefix tailTrace_40279
  have hstable : (prefixWord ++ tailWord_40279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40279).length < 2 ^ (prefixWord ++ tailWord_40279).sum := by decide
  have hdescent : baseEnd_40279 < baseStart_40279 := by decide
  rcases family_descends (prefixWord ++ tailWord_40279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40296 : List Nat := [2, 1, 4, 2, 4, 1, 6]
def baseStart_40296 : Nat := 118140960795 + 40296 * 2 ^ 59
def prefixEnd_40296 : Nat := 4983230072969 + 3 ^ 40 * 40296 * 2
def baseEnd_40296 : Nat := 2043576933696748189105

theorem tailTrace_40296 : CollatzResearch.WordTrace tailWord_40296 prefixEnd_40296 2043576933696748189105 := by
  unfold tailWord_40296
  simp only [CollatzResearch.WordTrace]
  refine ⟨734857931010974427002371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 979810574681299236003161 734857931010974427002371)
  ·
    refine ⟨1102286896516461640503557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 734857931010974427002371 1102286896516461640503557)
    ·
      refine ⟨206678793096836557594417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1102286896516461640503557 206678793096836557594417)
      ·
        refine ⟨155009094822627418195813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206678793096836557594417 155009094822627418195813)
        ·
          refine ⟨29064205279242640911715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155009094822627418195813 29064205279242640911715)
          ·
            refine ⟨43596307918863961367573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29064205279242640911715 43596307918863961367573)
            ·
              refine ⟨2043576933696748189105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43596307918863961367573 2043576933696748189105)
              ·
                rfl

theorem cell20_40296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 6].length) (baseStart_40296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40296 prefixEnd_40296 := by exact prefixLift 40296
  have htrace : WordTrace (prefixWord ++ tailWord_40296) baseStart_40296 baseEnd_40296 := by
    simpa [prefixWord, tailWord_40296, baseEnd_40296] using wordTrace_append hprefix tailTrace_40296
  have hstable : (prefixWord ++ tailWord_40296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40296).length < 2 ^ (prefixWord ++ tailWord_40296).sum := by decide
  have hdescent : baseEnd_40296 < baseStart_40296 := by decide
  rcases family_descends (prefixWord ++ tailWord_40296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40300 : List Nat := [2, 2, 1, 1, 5, 1, 8]
def baseStart_40300 : Nat := 118140960795 + 40300 * 2 ^ 59
def prefixEnd_40300 : Nat := 4983230072969 + 3 ^ 40 * 40300 * 2
def baseEnd_40300 : Nat := 2043779790251610840955

theorem tailTrace_40300 : CollatzResearch.WordTrace tailWord_40300 prefixEnd_40300 2043779790251610840955 := by
  unfold tailWord_40300
  simp only [CollatzResearch.WordTrace]
  refine ⟨734930877003728768575177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 979907836004971691433569 734930877003728768575177)
  ·
    refine ⟨551198157752796576431383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 734930877003728768575177 551198157752796576431383)
    ·
      refine ⟨826797236629194864647075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551198157752796576431383 826797236629194864647075)
      ·
        refine ⟨1240195854943792296970613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826797236629194864647075 1240195854943792296970613)
        ·
          refine ⟨116268361400980527840995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1240195854943792296970613 116268361400980527840995)
          ·
            refine ⟨174402542101470791761493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116268361400980527840995 174402542101470791761493)
            ·
              refine ⟨2043779790251610840955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 174402542101470791761493 2043779790251610840955)
              ·
                rfl

theorem cell20_40300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 8].length) (baseStart_40300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40300 prefixEnd_40300 := by exact prefixLift 40300
  have htrace : WordTrace (prefixWord ++ tailWord_40300) baseStart_40300 baseEnd_40300 := by
    simpa [prefixWord, tailWord_40300, baseEnd_40300] using wordTrace_append hprefix tailTrace_40300
  have hstable : (prefixWord ++ tailWord_40300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40300).length < 2 ^ (prefixWord ++ tailWord_40300).sum := by decide
  have hdescent : baseEnd_40300 < baseStart_40300 := by decide
  rcases family_descends (prefixWord ++ tailWord_40300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40369 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_40369 : Nat := 118140960795 + 40369 * 2 ^ 59
def prefixEnd_40369 : Nat := 4983230072969 + 3 ^ 40 * 40369 * 2
def baseEnd_40369 : Nat := 18425511592406924268313

theorem tailTrace_40369 : CollatzResearch.WordTrace tailWord_40369 prefixEnd_40369 18425511592406924268313 := by
  unfold tailWord_40369
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472378390757482321412161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 981585593838321547608107 1472378390757482321412161)
  ·
    refine ⟨1104283793068111741059121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1472378390757482321412161 1104283793068111741059121)
    ·
      refine ⟨828212844801083805794341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104283793068111741059121 828212844801083805794341)
      ·
        refine ⟨155289908400203213586439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 828212844801083805794341 155289908400203213586439)
        ·
          refine ⟨232934862600304820379659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155289908400203213586439 232934862600304820379659)
          ·
            refine ⟨349402293900457230569489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232934862600304820379659 349402293900457230569489)
            ·
              refine ⟨262051720425342922927117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349402293900457230569489 262051720425342922927117)
              ·
                refine ⟨98269395159503596097669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262051720425342922927117 98269395159503596097669)
                ·
                  refine ⟨18425511592406924268313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98269395159503596097669 18425511592406924268313)
                  ·
                    rfl

theorem cell20_40369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_40369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40369 prefixEnd_40369 := by exact prefixLift 40369
  have htrace : WordTrace (prefixWord ++ tailWord_40369) baseStart_40369 baseEnd_40369 := by
    simpa [prefixWord, tailWord_40369, baseEnd_40369] using wordTrace_append hprefix tailTrace_40369
  have hstable : (prefixWord ++ tailWord_40369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40369).length < 2 ^ (prefixWord ++ tailWord_40369).sum := by decide
  have hdescent : baseEnd_40369 < baseStart_40369 := by decide
  rcases family_descends (prefixWord ++ tailWord_40369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40376 : List Nat := [2, 1, 2, 1, 2, 2, 5, 5]
def baseStart_40376 : Nat := 118140960795 + 40376 * 2 ^ 59
def prefixEnd_40376 : Nat := 4983230072969 + 3 ^ 40 * 40376 * 2
def baseEnd_40376 : Nat := 6142902194382003678317

theorem tailTrace_40376 : CollatzResearch.WordTrace tailWord_40376 prefixEnd_40376 6142902194382003678317 := by
  unfold tailWord_40376
  simp only [CollatzResearch.WordTrace]
  refine ⟨736316850866061258458491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 981755801154748344611321 736316850866061258458491)
  ·
    refine ⟨1104475276299091887687737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 736316850866061258458491 1104475276299091887687737)
    ·
      refine ⟨828356457224318915765803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104475276299091887687737 828356457224318915765803)
      ·
        refine ⟨1242534685836478373648705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828356457224318915765803 1242534685836478373648705)
        ·
          refine ⟨931901014377358780236529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1242534685836478373648705 931901014377358780236529)
          ·
            refine ⟨698925760783019085177397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931901014377358780236529 698925760783019085177397)
            ·
              refine ⟨65524290073408039235381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 698925760783019085177397 65524290073408039235381)
              ·
                refine ⟨6142902194382003678317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65524290073408039235381 6142902194382003678317)
                ·
                  rfl

theorem cell20_40376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_40376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40376 prefixEnd_40376 := by exact prefixLift 40376
  have htrace : WordTrace (prefixWord ++ tailWord_40376) baseStart_40376 baseEnd_40376 := by
    simpa [prefixWord, tailWord_40376, baseEnd_40376] using wordTrace_append hprefix tailTrace_40376
  have hstable : (prefixWord ++ tailWord_40376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40376).length < 2 ^ (prefixWord ++ tailWord_40376).sum := by decide
  have hdescent : baseEnd_40376 < baseStart_40376 := by decide
  rcases family_descends (prefixWord ++ tailWord_40376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40417 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 3]
def baseStart_40417 : Nat := 118140960795 + 40417 * 2 ^ 59
def prefixEnd_40417 : Nat := 4983230072969 + 3 ^ 40 * 40417 * 2
def baseEnd_40417 : Nat := 18447420100332090668117

theorem tailTrace_40417 : CollatzResearch.WordTrace tailWord_40417 prefixEnd_40417 18447420100332090668117 := by
  unfold tailWord_40417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474129094583586519159505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 982752729722391012773003 1474129094583586519159505)
  ·
    refine ⟨1105596820937689889369629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1474129094583586519159505 1105596820937689889369629)
    ·
      refine ⟨414598807851633708513611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1105596820937689889369629 414598807851633708513611)
      ·
        refine ⟨621898211777450562770417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414598807851633708513611 621898211777450562770417)
        ·
          refine ⟨466423658833087922077813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621898211777450562770417 466423658833087922077813)
          ·
            refine ⟨43727218015601992694795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 466423658833087922077813 43727218015601992694795)
            ·
              refine ⟨65590827023402989042193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43727218015601992694795 65590827023402989042193)
              ·
                refine ⟨49193120267552241781645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65590827023402989042193 49193120267552241781645)
                ·
                  refine ⟨18447420100332090668117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49193120267552241781645 18447420100332090668117)
                  ·
                    rfl

theorem cell20_40417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_40417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40417 prefixEnd_40417 := by exact prefixLift 40417
  have htrace : WordTrace (prefixWord ++ tailWord_40417) baseStart_40417 baseEnd_40417 := by
    simpa [prefixWord, tailWord_40417, baseEnd_40417] using wordTrace_append hprefix tailTrace_40417
  have hstable : (prefixWord ++ tailWord_40417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40417).length < 2 ^ (prefixWord ++ tailWord_40417).sum := by decide
  have hdescent : baseEnd_40417 < baseStart_40417 := by decide
  rcases family_descends (prefixWord ++ tailWord_40417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40424 : List Nat := [2, 1, 4, 1, 1, 2, 1, 6, 2]
def baseStart_40424 : Nat := 118140960795 + 40424 * 2 ^ 59
def prefixEnd_40424 : Nat := 4983230072969 + 3 ^ 40 * 40424 * 2
def baseEnd_40424 : Nat := 18450615091071177434755

theorem tailTrace_40424 : CollatzResearch.WordTrace tailWord_40424 prefixEnd_40424 18450615091071177434755 := by
  unfold tailWord_40424
  simp only [CollatzResearch.WordTrace]
  refine ⟨737192202779113357332163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 982922937038817809776217 737192202779113357332163)
  ·
    refine ⟨1105788304168670035998245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 737192202779113357332163 1105788304168670035998245)
    ·
      refine ⟨207335307031625631749671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1105788304168670035998245 207335307031625631749671)
      ·
        refine ⟨311002960547438447624507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207335307031625631749671 311002960547438447624507)
        ·
          refine ⟨466504440821157671436761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311002960547438447624507 466504440821157671436761)
          ·
            refine ⟨349878330615868253577571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466504440821157671436761 349878330615868253577571)
            ·
              refine ⟨524817495923802380366357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349878330615868253577571 524817495923802380366357)
              ·
                refine ⟨24600820121428236579673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 524817495923802380366357 24600820121428236579673)
                ·
                  refine ⟨18450615091071177434755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24600820121428236579673 18450615091071177434755)
                  ·
                    rfl

theorem cell20_40424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_40424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40424 prefixEnd_40424 := by exact prefixLift 40424
  have htrace : WordTrace (prefixWord ++ tailWord_40424) baseStart_40424 baseEnd_40424 := by
    simpa [prefixWord, tailWord_40424, baseEnd_40424] using wordTrace_append hprefix tailTrace_40424
  have hstable : (prefixWord ++ tailWord_40424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40424).length < 2 ^ (prefixWord ++ tailWord_40424).sum := by decide
  have hdescent : baseEnd_40424 < baseStart_40424 := by decide
  rcases family_descends (prefixWord ++ tailWord_40424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40434 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_40434 : Nat := 118140960795 + 40434 * 2 ^ 59
def prefixEnd_40434 : Nat := 4983230072969 + 3 ^ 40 * 40434 * 2
def baseEnd_40434 : Nat := 18455179363555587101381

theorem tailTrace_40434 : CollatzResearch.WordTrace tailWord_40434 prefixEnd_40434 18455179363555587101381 := by
  unfold tailWord_40434
  simp only [CollatzResearch.WordTrace]
  refine ⟨368687283880499605632089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 983166090347998948352237 368687283880499605632089)
  ·
    refine ⟨276515462910374704224067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 368687283880499605632089 276515462910374704224067)
    ·
      refine ⟨414773194365562056336101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276515462910374704224067 414773194365562056336101)
      ·
        refine ⟨77769973943542885563019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 414773194365562056336101 77769973943542885563019)
        ·
          refine ⟨116654960915314328344529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77769973943542885563019 116654960915314328344529)
          ·
            refine ⟨87491220686485746258397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116654960915314328344529 87491220686485746258397)
            ·
              refine ⟨32809207757432154846899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87491220686485746258397 32809207757432154846899)
              ·
                refine ⟨49213811636148232270349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32809207757432154846899 49213811636148232270349)
                ·
                  refine ⟨18455179363555587101381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49213811636148232270349 18455179363555587101381)
                  ·
                    rfl

theorem cell20_40434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_40434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40434 prefixEnd_40434 := by exact prefixLift 40434
  have htrace : WordTrace (prefixWord ++ tailWord_40434) baseStart_40434 baseEnd_40434 := by
    simpa [prefixWord, tailWord_40434, baseEnd_40434] using wordTrace_append hprefix tailTrace_40434
  have hstable : (prefixWord ++ tailWord_40434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40434).length < 2 ^ (prefixWord ++ tailWord_40434).sum := by decide
  have hdescent : baseEnd_40434 < baseStart_40434 := by decide
  rcases family_descends (prefixWord ++ tailWord_40434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40445 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_40445 : Nat := 118140960795 + 40445 * 2 ^ 59
def prefixEnd_40445 : Nat := 4983230072969 + 3 ^ 40 * 40445 * 2
def baseEnd_40445 : Nat := 18460200063288437734669

theorem tailTrace_40445 : CollatzResearch.WordTrace tailWord_40445 prefixEnd_40445 18460200063288437734669 := by
  unfold tailWord_40445
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475150338482147301178789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 983433558988098200785859 1475150338482147301178789)
  ·
    refine ⟨276590688465402618971023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1475150338482147301178789 276590688465402618971023)
    ·
      refine ⟨414886032698103928456535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276590688465402618971023 414886032698103928456535)
      ·
        refine ⟨622329049047155892684803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414886032698103928456535 622329049047155892684803)
        ·
          refine ⟨933493573570733839027205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622329049047155892684803 933493573570733839027205)
          ·
            refine ⟨175030045044512594817601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 933493573570733839027205 175030045044512594817601)
            ·
              refine ⟨131272533783384446113201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175030045044512594817601 131272533783384446113201)
              ·
                refine ⟨98454400337538334584901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131272533783384446113201 98454400337538334584901)
                ·
                  refine ⟨18460200063288437734669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98454400337538334584901 18460200063288437734669)
                  ·
                    rfl

theorem cell20_40445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_40445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40445 prefixEnd_40445 := by exact prefixLift 40445
  have htrace : WordTrace (prefixWord ++ tailWord_40445) baseStart_40445 baseEnd_40445 := by
    simpa [prefixWord, tailWord_40445, baseEnd_40445] using wordTrace_append hprefix tailTrace_40445
  have hstable : (prefixWord ++ tailWord_40445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40445).length < 2 ^ (prefixWord ++ tailWord_40445).sum := by decide
  have hdescent : baseEnd_40445 < baseStart_40445 := by decide
  rcases family_descends (prefixWord ++ tailWord_40445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40476 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_40476 : Nat := 118140960795 + 40476 * 2 ^ 59
def prefixEnd_40476 : Nat := 4983230072969 + 3 ^ 40 * 40476 * 2
def baseEnd_40476 : Nat := 18474349307990107701209

theorem tailTrace_40476 : CollatzResearch.WordTrace tailWord_40476 prefixEnd_40476 18474349307990107701209 := by
  unfold tailWord_40476
  simp only [CollatzResearch.WordTrace]
  refine ⟨738140500684919797778641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 984187334246559730371521 738140500684919797778641)
  ·
    refine ⟨553605375513689848333981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 738140500684919797778641 553605375513689848333981)
    ·
      refine ⟨207602015817633693125243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 553605375513689848333981 207602015817633693125243)
      ·
        refine ⟨311403023726450539687865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207602015817633693125243 311403023726450539687865)
        ·
          refine ⟨233552267794837904765899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311403023726450539687865 233552267794837904765899)
          ·
            refine ⟨350328401692256857148849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233552267794837904765899 350328401692256857148849)
            ·
              refine ⟨262746301269192642861637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350328401692256857148849 262746301269192642861637)
              ·
                refine ⟨49264931487973620536557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262746301269192642861637 49264931487973620536557)
                ·
                  refine ⟨18474349307990107701209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49264931487973620536557 18474349307990107701209)
                  ·
                    rfl

theorem cell20_40476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_40476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40476 prefixEnd_40476 := by exact prefixLift 40476
  have htrace : WordTrace (prefixWord ++ tailWord_40476) baseStart_40476 baseEnd_40476 := by
    simpa [prefixWord, tailWord_40476, baseEnd_40476] using wordTrace_append hprefix tailTrace_40476
  have hstable : (prefixWord ++ tailWord_40476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40476).length < 2 ^ (prefixWord ++ tailWord_40476).sum := by decide
  have hdescent : baseEnd_40476 < baseStart_40476 := by decide
  rcases family_descends (prefixWord ++ tailWord_40476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40541 : List Nat := [1, 4, 4, 2, 1, 2, 1, 5]
def baseStart_40541 : Nat := 118140960795 + 40541 * 2 ^ 59
def prefixEnd_40541 : Nat := 4983230072969 + 3 ^ 40 * 40541 * 2
def baseEnd_40541 : Nat := 6168005693046256844759

theorem tailTrace_40541 : CollatzResearch.WordTrace tailWord_40541 prefixEnd_40541 6168005693046256844759 := by
  unfold tailWord_40541
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478651746134355696673477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 985767830756237131115651 1478651746134355696673477)
  ·
    refine ⟨277247202400191693126277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1478651746134355696673477 277247202400191693126277)
    ·
      refine ⟨51983850450035942461177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 277247202400191693126277 51983850450035942461177)
      ·
        refine ⟨38987887837526956845883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51983850450035942461177 38987887837526956845883)
        ·
          refine ⟨58481831756290435268825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38987887837526956845883 58481831756290435268825)
          ·
            refine ⟨43861373817217826451619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58481831756290435268825 43861373817217826451619)
            ·
              refine ⟨65792060725826739677429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43861373817217826451619 65792060725826739677429)
              ·
                refine ⟨6168005693046256844759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65792060725826739677429 6168005693046256844759)
                ·
                  rfl

theorem cell20_40541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_40541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40541 prefixEnd_40541 := by exact prefixLift 40541
  have htrace : WordTrace (prefixWord ++ tailWord_40541) baseStart_40541 baseEnd_40541 := by
    simpa [prefixWord, tailWord_40541, baseEnd_40541] using wordTrace_append hprefix tailTrace_40541
  have hstable : (prefixWord ++ tailWord_40541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40541).length < 2 ^ (prefixWord ++ tailWord_40541).sum := by decide
  have hdescent : baseEnd_40541 < baseStart_40541 := by decide
  rcases family_descends (prefixWord ++ tailWord_40541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40576 : List Nat := [2, 1, 1, 2, 1, 4, 4, 3, 2]
def baseStart_40576 : Nat := 118140960795 + 40576 * 2 ^ 59
def prefixEnd_40576 : Nat := 4983230072969 + 3 ^ 40 * 40576 * 2
def baseEnd_40576 : Nat := 18519992032834204367467

theorem tailTrace_40576 : CollatzResearch.WordTrace tailWord_40576 prefixEnd_40576 18519992032834204367467 := by
  unfold tailWord_40576
  simp only [CollatzResearch.WordTrace]
  refine ⟨739964150503778337098791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 986618867338371116131721 739964150503778337098791)
  ·
    refine ⟨1109946225755667505648187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 739964150503778337098791 1109946225755667505648187)
    ·
      refine ⟨1664919338633501258472281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109946225755667505648187 1664919338633501258472281)
      ·
        refine ⟨1248689503975125943854211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664919338633501258472281 1248689503975125943854211)
        ·
          refine ⟨1873034255962688915781317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248689503975125943854211 1873034255962688915781317)
          ·
            refine ⟨351193922993004171708997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1873034255962688915781317 351193922993004171708997)
            ·
              refine ⟨65848860561188282195437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 351193922993004171708997 65848860561188282195437)
              ·
                refine ⟨24693322710445605823289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65848860561188282195437 24693322710445605823289)
                ·
                  refine ⟨18519992032834204367467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24693322710445605823289 18519992032834204367467)
                  ·
                    rfl

theorem cell20_40576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_40576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40576 prefixEnd_40576 := by exact prefixLift 40576
  have htrace : WordTrace (prefixWord ++ tailWord_40576) baseStart_40576 baseEnd_40576 := by
    simpa [prefixWord, tailWord_40576, baseEnd_40576] using wordTrace_append hprefix tailTrace_40576
  have hstable : (prefixWord ++ tailWord_40576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40576).length < 2 ^ (prefixWord ++ tailWord_40576).sum := by decide
  have hdescent : baseEnd_40576 < baseStart_40576 := by decide
  rcases family_descends (prefixWord ++ tailWord_40576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40587 : List Nat := [1, 1, 1, 1, 4, 1, 11]
def baseStart_40587 : Nat := 118140960795 + 40587 * 2 ^ 59
def prefixEnd_40587 : Nat := 4983230072969 + 3 ^ 40 * 40587 * 2
def baseEnd_40587 : Nat := 2058334748063006111195

theorem tailTrace_40587 : CollatzResearch.WordTrace tailWord_40587 prefixEnd_40587 2058334748063006111195 := by
  unfold tailWord_40587
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480329503967705552848015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 986886335978470368565343 1480329503967705552848015)
  ·
    refine ⟨2220494255951558329272023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1480329503967705552848015 2220494255951558329272023)
    ·
      refine ⟨3330741383927337493908035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220494255951558329272023 3330741383927337493908035)
      ·
        refine ⟨4996112075891006240862053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330741383927337493908035 4996112075891006240862053)
        ·
          refine ⟨936771014229563670161635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4996112075891006240862053 936771014229563670161635)
          ·
            refine ⟨1405156521344345505242453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936771014229563670161635 1405156521344345505242453)
            ·
              refine ⟨2058334748063006111195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1405156521344345505242453 2058334748063006111195)
              ·
                rfl

theorem cell20_40587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 11].length) (baseStart_40587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40587 prefixEnd_40587 := by exact prefixLift 40587
  have htrace : WordTrace (prefixWord ++ tailWord_40587) baseStart_40587 baseEnd_40587 := by
    simpa [prefixWord, tailWord_40587, baseEnd_40587] using wordTrace_append hprefix tailTrace_40587
  have hstable : (prefixWord ++ tailWord_40587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40587).length < 2 ^ (prefixWord ++ tailWord_40587).sum := by decide
  have hdescent : baseEnd_40587 < baseStart_40587 := by decide
  rcases family_descends (prefixWord ++ tailWord_40587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40590 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_40590 : Nat := 118140960795 + 40590 * 2 ^ 59
def prefixEnd_40590 : Nat := 4983230072969 + 3 ^ 40 * 40590 * 2
def baseEnd_40590 : Nat := 18526382014312377900743

theorem tailTrace_40590 : CollatzResearch.WordTrace tailWord_40590 prefixEnd_40590 18526382014312377900743 := by
  unfold tailWord_40590
  simp only [CollatzResearch.WordTrace]
  refine ⟨185054865369604633150903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 986959281971224710138149 185054865369604633150903)
  ·
    refine ⟨277582298054406949726355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185054865369604633150903 277582298054406949726355)
    ·
      refine ⟨416373447081610424589533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277582298054406949726355 416373447081610424589533)
      ·
        refine ⟨156140042655603909221075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416373447081610424589533 156140042655603909221075)
        ·
          refine ⟨234210063983405863831613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156140042655603909221075 234210063983405863831613)
          ·
            refine ⟨87828773993777198936855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234210063983405863831613 87828773993777198936855)
            ·
              refine ⟨131743160990665798405283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87828773993777198936855 131743160990665798405283)
              ·
                refine ⟨197614741485998697607925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131743160990665798405283 197614741485998697607925)
                ·
                  refine ⟨18526382014312377900743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197614741485998697607925 18526382014312377900743)
                  ·
                    rfl

theorem cell20_40590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_40590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40590 prefixEnd_40590 := by exact prefixLift 40590
  have htrace : WordTrace (prefixWord ++ tailWord_40590) baseStart_40590 baseEnd_40590 := by
    simpa [prefixWord, tailWord_40590, baseEnd_40590] using wordTrace_append hprefix tailTrace_40590
  have hstable : (prefixWord ++ tailWord_40590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40590).length < 2 ^ (prefixWord ++ tailWord_40590).sum := by decide
  have hdescent : baseEnd_40590 < baseStart_40590 := by decide
  rcases family_descends (prefixWord ++ tailWord_40590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40631 : List Nat := [1, 1, 3, 1, 5, 3, 1, 3, 2]
def baseStart_40631 : Nat := 118140960795 + 40631 * 2 ^ 59
def prefixEnd_40631 : Nat := 4983230072969 + 3 ^ 40 * 40631 * 2
def baseEnd_40631 : Nat := 18545095531498457533909

theorem tailTrace_40631 : CollatzResearch.WordTrace tailWord_40631 prefixEnd_40631 18545095531498457533909 := by
  unfold tailWord_40631
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481934315808301067449747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 987956210538867378299831 1481934315808301067449747)
  ·
    refine ⟨2222901473712451601174621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1481934315808301067449747 2222901473712451601174621)
    ·
      refine ⟨833588052642169350440483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2222901473712451601174621 833588052642169350440483)
      ·
        refine ⟨1250382078963254025660725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833588052642169350440483 1250382078963254025660725)
        ·
          refine ⟨117223319902805064905693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1250382078963254025660725 117223319902805064905693)
          ·
            refine ⟨43958744963551899339635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117223319902805064905693 43958744963551899339635)
            ·
              refine ⟨65938117445327849009453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43958744963551899339635 65938117445327849009453)
              ·
                refine ⟨24726794041997943378545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65938117445327849009453 24726794041997943378545)
                ·
                  refine ⟨18545095531498457533909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24726794041997943378545 18545095531498457533909)
                  ·
                    rfl

theorem cell20_40631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 2].length) (baseStart_40631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40631 prefixEnd_40631 := by exact prefixLift 40631
  have htrace : WordTrace (prefixWord ++ tailWord_40631) baseStart_40631 baseEnd_40631 := by
    simpa [prefixWord, tailWord_40631, baseEnd_40631] using wordTrace_append hprefix tailTrace_40631
  have hstable : (prefixWord ++ tailWord_40631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40631).length < 2 ^ (prefixWord ++ tailWord_40631).sum := by decide
  have hdescent : baseEnd_40631 < baseStart_40631 := by decide
  rcases family_descends (prefixWord ++ tailWord_40631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40656 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_40656 : Nat := 118140960795 + 40656 * 2 ^ 59
def prefixEnd_40656 : Nat := 4983230072969 + 3 ^ 40 * 40656 * 2
def baseEnd_40656 : Nat := 18556506212709481700473

theorem tailTrace_40656 : CollatzResearch.WordTrace tailWord_40656 prefixEnd_40656 18556506212709481700473 := by
  unfold tailWord_40656
  simp only [CollatzResearch.WordTrace]
  refine ⟨741423070358865168554911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 988564093811820224739881 741423070358865168554911)
  ·
    refine ⟨1112134605538297752832367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741423070358865168554911 1112134605538297752832367)
    ·
      refine ⟨1668201908307446629248551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112134605538297752832367 1668201908307446629248551)
      ·
        refine ⟨2502302862461169943872827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668201908307446629248551 2502302862461169943872827)
        ·
          refine ⟨3753454293691754915809241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502302862461169943872827 3753454293691754915809241)
          ·
            refine ⟨2815090720268816186856931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753454293691754915809241 2815090720268816186856931)
            ·
              refine ⟨4222636080403224280285397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815090720268816186856931 4222636080403224280285397)
              ·
                refine ⟨98968033134450569069189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4222636080403224280285397 98968033134450569069189)
                ·
                  refine ⟨18556506212709481700473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98968033134450569069189 18556506212709481700473)
                  ·
                    rfl

theorem cell20_40656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_40656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40656 prefixEnd_40656 := by exact prefixLift 40656
  have htrace : WordTrace (prefixWord ++ tailWord_40656) baseStart_40656 baseEnd_40656 := by
    simpa [prefixWord, tailWord_40656, baseEnd_40656] using wordTrace_append hprefix tailTrace_40656
  have hstable : (prefixWord ++ tailWord_40656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40656).length < 2 ^ (prefixWord ++ tailWord_40656).sum := by decide
  have hdescent : baseEnd_40656 < baseStart_40656 := by decide
  rcases family_descends (prefixWord ++ tailWord_40656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40666 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_40666 : Nat := 118140960795 + 40666 * 2 ^ 59
def prefixEnd_40666 : Nat := 4983230072969 + 3 ^ 40 * 40666 * 2
def baseEnd_40666 : Nat := 18561070485193891367099

theorem tailTrace_40666 : CollatzResearch.WordTrace tailWord_40666 prefixEnd_40666 18561070485193891367099 := by
  unfold tailWord_40666
  simp only [CollatzResearch.WordTrace]
  refine ⟨370802717670375511243463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 988807247121001363315901 370802717670375511243463)
  ·
    refine ⟨556204076505563266865195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 370802717670375511243463 556204076505563266865195)
    ·
      refine ⟨834306114758344900297793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556204076505563266865195 834306114758344900297793)
      ·
        refine ⟨625729586068758675223345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 834306114758344900297793 625729586068758675223345)
        ·
          refine ⟨469297189551569006417509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625729586068758675223345 469297189551569006417509)
          ·
            refine ⟨87993223040919188703283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 469297189551569006417509 87993223040919188703283)
            ·
              refine ⟨131989834561378783054925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87993223040919188703283 131989834561378783054925)
              ·
                refine ⟨49496187960517043645597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131989834561378783054925 49496187960517043645597)
                ·
                  refine ⟨18561070485193891367099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49496187960517043645597 18561070485193891367099)
                  ·
                    rfl

theorem cell20_40666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_40666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40666 prefixEnd_40666 := by exact prefixLift 40666
  have htrace : WordTrace (prefixWord ++ tailWord_40666) baseStart_40666 baseEnd_40666 := by
    simpa [prefixWord, tailWord_40666, baseEnd_40666] using wordTrace_append hprefix tailTrace_40666
  have hstable : (prefixWord ++ tailWord_40666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40666).length < 2 ^ (prefixWord ++ tailWord_40666).sum := by decide
  have hdescent : baseEnd_40666 < baseStart_40666 := by decide
  rcases family_descends (prefixWord ++ tailWord_40666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40680 : List Nat := [2, 1, 4, 1, 3, 1, 2, 6]
def baseStart_40680 : Nat := 118140960795 + 40680 * 2 ^ 59
def prefixEnd_40680 : Nat := 4983230072969 + 3 ^ 40 * 40680 * 2
def baseEnd_40680 : Nat := 6189153488890688300125

theorem tailTrace_40680 : CollatzResearch.WordTrace tailWord_40680 prefixEnd_40680 6189153488890688300125 := by
  unfold tailWord_40680
  simp only [CollatzResearch.WordTrace]
  refine ⟨741860746315391217991747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 989147661753854957322329 741860746315391217991747)
  ·
    refine ⟨1112791119473086826987621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741860746315391217991747 1112791119473086826987621)
    ·
      refine ⟨208648334901203780060179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1112791119473086826987621 208648334901203780060179)
      ·
        refine ⟨312972502351805670090269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208648334901203780060179 312972502351805670090269)
        ·
          refine ⟨117364688381927126283851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312972502351805670090269 117364688381927126283851)
          ·
            refine ⟨176047032572890689425777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117364688381927126283851 176047032572890689425777)
            ·
              refine ⟨132035274429668017069333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176047032572890689425777 132035274429668017069333)
              ·
                refine ⟨6189153488890688300125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132035274429668017069333 6189153488890688300125)
                ·
                  rfl

theorem cell20_40680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_40680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40680 prefixEnd_40680 := by exact prefixLift 40680
  have htrace : WordTrace (prefixWord ++ tailWord_40680) baseStart_40680 baseEnd_40680 := by
    simpa [prefixWord, tailWord_40680, baseEnd_40680] using wordTrace_append hprefix tailTrace_40680
  have hstable : (prefixWord ++ tailWord_40680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40680).length < 2 ^ (prefixWord ++ tailWord_40680).sum := by decide
  have hdescent : baseEnd_40680 < baseStart_40680 := by decide
  rcases family_descends (prefixWord ++ tailWord_40680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40690 : List Nat := [3, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_40690 : Nat := 118140960795 + 40690 * 2 ^ 59
def prefixEnd_40690 : Nat := 4983230072969 + 3 ^ 40 * 40690 * 2
def baseEnd_40690 : Nat := 18572024739156474567001

theorem tailTrace_40690 : CollatzResearch.WordTrace tailWord_40690 prefixEnd_40690 18572024739156474567001 := by
  unfold tailWord_40690
  simp only [CollatzResearch.WordTrace]
  refine ⟨371021555648638535961881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 989390815063036095898349 371021555648638535961881)
  ·
    refine ⟨278266166736478901971411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 371021555648638535961881 278266166736478901971411)
    ·
      refine ⟨417399250104718352957117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278266166736478901971411 417399250104718352957117)
      ·
        refine ⟨156524718789269382358919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417399250104718352957117 156524718789269382358919)
        ·
          refine ⟨234787078183904073538379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156524718789269382358919 234787078183904073538379)
          ·
            refine ⟨352180617275856110307569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234787078183904073538379 352180617275856110307569)
            ·
              refine ⟨264135462956892082730677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352180617275856110307569 264135462956892082730677)
              ·
                refine ⟨24762699652208632756001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264135462956892082730677 24762699652208632756001)
                ·
                  refine ⟨18572024739156474567001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24762699652208632756001 18572024739156474567001)
                  ·
                    rfl

theorem cell20_40690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_40690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40690 prefixEnd_40690 := by exact prefixLift 40690
  have htrace : WordTrace (prefixWord ++ tailWord_40690) baseStart_40690 baseEnd_40690 := by
    simpa [prefixWord, tailWord_40690, baseEnd_40690] using wordTrace_append hprefix tailTrace_40690
  have hstable : (prefixWord ++ tailWord_40690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40690).length < 2 ^ (prefixWord ++ tailWord_40690).sum := by decide
  have hdescent : baseEnd_40690 < baseStart_40690 := by decide
  rcases family_descends (prefixWord ++ tailWord_40690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40718 : List Nat := [4, 1, 1, 2, 1, 1, 5, 5]
def baseStart_40718 : Nat := 118140960795 + 40718 * 2 ^ 59
def prefixEnd_40718 : Nat := 4983230072969 + 3 ^ 40 * 40718 * 2
def baseEnd_40718 : Nat := 6194934900704273877851

theorem tailTrace_40718 : CollatzResearch.WordTrace tailWord_40718 prefixEnd_40718 6194934900704273877851 := by
  unfold tailWord_40718
  simp only [CollatzResearch.WordTrace]
  refine ⟨185638433311639365733351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 990071644328743283911205 185638433311639365733351)
  ·
    refine ⟨278457649967459048600027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185638433311639365733351 278457649967459048600027)
    ·
      refine ⟨417686474951188572900041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278457649967459048600027 417686474951188572900041)
      ·
        refine ⟨313264856213391429675031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417686474951188572900041 313264856213391429675031)
        ·
          refine ⟨469897284320087144512547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313264856213391429675031 469897284320087144512547)
          ·
            refine ⟨704845926480130716768821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469897284320087144512547 704845926480130716768821)
            ·
              refine ⟨66079305607512254697077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 704845926480130716768821 66079305607512254697077)
              ·
                refine ⟨6194934900704273877851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66079305607512254697077 6194934900704273877851)
                ·
                  rfl

theorem cell20_40718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_40718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40718 prefixEnd_40718 := by exact prefixLift 40718
  have htrace : WordTrace (prefixWord ++ tailWord_40718) baseStart_40718 baseEnd_40718 := by
    simpa [prefixWord, tailWord_40718, baseEnd_40718] using wordTrace_append hprefix tailTrace_40718
  have hstable : (prefixWord ++ tailWord_40718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40718).length < 2 ^ (prefixWord ++ tailWord_40718).sum := by decide
  have hdescent : baseEnd_40718 < baseStart_40718 := by decide
  rcases family_descends (prefixWord ++ tailWord_40718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40724 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 4]
def baseStart_40724 : Nat := 118140960795 + 40724 * 2 ^ 59
def prefixEnd_40724 : Nat := 4983230072969 + 3 ^ 40 * 40724 * 2
def baseEnd_40724 : Nat := 18587543265603467433529

theorem tailTrace_40724 : CollatzResearch.WordTrace tailWord_40724 prefixEnd_40724 18587543265603467433529 := by
  unfold tailWord_40724
  simp only [CollatzResearch.WordTrace]
  refine ⟨742663152235688975292613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 990217536314251967056817 742663152235688975292613)
  ·
    refine ⟨139249341044191682867365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 742663152235688975292613 139249341044191682867365)
    ·
      refine ⟨26109251445785940537631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139249341044191682867365 26109251445785940537631)
      ·
        refine ⟨39163877168678910806447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26109251445785940537631 39163877168678910806447)
        ·
          refine ⟨58745815753018366209671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39163877168678910806447 58745815753018366209671)
          ·
            refine ⟨88118723629527549314507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58745815753018366209671 88118723629527549314507)
            ·
              refine ⟨132178085444291323971761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88118723629527549314507 132178085444291323971761)
              ·
                refine ⟨99133564083218492978821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132178085444291323971761 99133564083218492978821)
                ·
                  refine ⟨18587543265603467433529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99133564083218492978821 18587543265603467433529)
                  ·
                    rfl

theorem cell20_40724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_40724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40724 prefixEnd_40724 := by exact prefixLift 40724
  have htrace : WordTrace (prefixWord ++ tailWord_40724) baseStart_40724 baseEnd_40724 := by
    simpa [prefixWord, tailWord_40724, baseEnd_40724] using wordTrace_append hprefix tailTrace_40724
  have hstable : (prefixWord ++ tailWord_40724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40724).length < 2 ^ (prefixWord ++ tailWord_40724).sum := by decide
  have hdescent : baseEnd_40724 < baseStart_40724 := by decide
  rcases family_descends (prefixWord ++ tailWord_40724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40739 : List Nat := [1, 1, 1, 4, 2, 1, 2, 8]
def baseStart_40739 : Nat := 118140960795 + 40739 * 2 ^ 59
def prefixEnd_40739 : Nat := 4983230072969 + 3 ^ 40 * 40739 * 2
def baseEnd_40739 : Nat := 6198129891443360644489

theorem tailTrace_40739 : CollatzResearch.WordTrace tailWord_40739 prefixEnd_40739 6198129891443360644489 := by
  unfold tailWord_40739
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485873399417035512381271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 990582266278023674920847 1485873399417035512381271)
  ·
    refine ⟨2228810099125553268571907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1485873399417035512381271 2228810099125553268571907)
    ·
      refine ⟨3343215148688329902857861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228810099125553268571907 3343215148688329902857861)
      ·
        refine ⟨626852840379061856785849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3343215148688329902857861 626852840379061856785849)
        ·
          refine ⟨470139630284296392589387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626852840379061856785849 470139630284296392589387)
          ·
            refine ⟨705209445426444588884081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470139630284296392589387 705209445426444588884081)
            ·
              refine ⟨528907084069833441663061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705209445426444588884081 528907084069833441663061)
              ·
                refine ⟨6198129891443360644489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 528907084069833441663061 6198129891443360644489)
                ·
                  rfl

theorem cell20_40739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_40739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40739 prefixEnd_40739 := by exact prefixLift 40739
  have htrace : WordTrace (prefixWord ++ tailWord_40739) baseStart_40739 baseEnd_40739 := by
    simpa [prefixWord, tailWord_40739, baseEnd_40739] using wordTrace_append hprefix tailTrace_40739
  have hstable : (prefixWord ++ tailWord_40739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40739).length < 2 ^ (prefixWord ++ tailWord_40739).sum := by decide
  have hdescent : baseEnd_40739 < baseStart_40739 := by decide
  rcases family_descends (prefixWord ++ tailWord_40739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40766 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_40766 : Nat := 118140960795 + 40766 * 2 ^ 59
def prefixEnd_40766 : Nat := 4983230072969 + 3 ^ 40 * 40766 * 2
def baseEnd_40766 : Nat := 18606713210037988033357

theorem tailTrace_40766 : CollatzResearch.WordTrace tailWord_40766 prefixEnd_40766 18606713210037988033357 := by
  unfold tailWord_40766
  simp only [CollatzResearch.WordTrace]
  refine ⟨185857271289902390451769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 991238780212812749076101 185857271289902390451769)
  ·
    refine ⟨139392953467426792838827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185857271289902390451769 139392953467426792838827)
    ·
      refine ⟨209089430201140189258241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139392953467426792838827 209089430201140189258241)
      ·
        refine ⟨156817072650855141943681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209089430201140189258241 156817072650855141943681)
        ·
          refine ⟨117612804488141356457761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156817072650855141943681 117612804488141356457761)
          ·
            refine ⟨88209603366106017343321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117612804488141356457761 88209603366106017343321)
            ·
              refine ⟨66157202524579513007491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88209603366106017343321 66157202524579513007491)
              ·
                refine ⟨99235803786869269511237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66157202524579513007491 99235803786869269511237)
                ·
                  refine ⟨18606713210037988033357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99235803786869269511237 18606713210037988033357)
                  ·
                    rfl

theorem cell20_40766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_40766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40766 prefixEnd_40766 := by exact prefixLift 40766
  have htrace : WordTrace (prefixWord ++ tailWord_40766) baseStart_40766 baseEnd_40766 := by
    simpa [prefixWord, tailWord_40766, baseEnd_40766] using wordTrace_append hprefix tailTrace_40766
  have hstable : (prefixWord ++ tailWord_40766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40766).length < 2 ^ (prefixWord ++ tailWord_40766).sum := by decide
  have hdescent : baseEnd_40766 < baseStart_40766 := by decide
  rcases family_descends (prefixWord ++ tailWord_40766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40777 : List Nat := [1, 2, 1, 1, 2, 4, 2, 7]
def baseStart_40777 : Nat := 118140960795 + 40777 * 2 ^ 59
def prefixEnd_40777 : Nat := 4983230072969 + 3 ^ 40 * 40777 * 2
def baseEnd_40777 : Nat := 6203911303256946222215

theorem tailTrace_40777 : CollatzResearch.WordTrace tailWord_40777 prefixEnd_40777 6203911303256946222215 := by
  unfold tailWord_40777
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487259373279368002264585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 991506248852912001509723 1487259373279368002264585)
  ·
    refine ⟨1115444529959526001698439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1487259373279368002264585 1115444529959526001698439)
    ·
      refine ⟨1673166794939289002547659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115444529959526001698439 1673166794939289002547659)
      ·
        refine ⟨2509750192408933503821489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673166794939289002547659 2509750192408933503821489)
        ·
          refine ⟨1882312644306700127866117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2509750192408933503821489 1882312644306700127866117)
          ·
            refine ⟨352933620807506273974897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1882312644306700127866117 352933620807506273974897)
            ·
              refine ⟨264700215605629705481173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352933620807506273974897 264700215605629705481173)
              ·
                refine ⟨6203911303256946222215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 264700215605629705481173 6203911303256946222215)
                ·
                  rfl

theorem cell20_40777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_40777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40777 prefixEnd_40777 := by exact prefixLift 40777
  have htrace : WordTrace (prefixWord ++ tailWord_40777) baseStart_40777 baseEnd_40777 := by
    simpa [prefixWord, tailWord_40777, baseEnd_40777] using wordTrace_append hprefix tailTrace_40777
  have hstable : (prefixWord ++ tailWord_40777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40777).length < 2 ^ (prefixWord ++ tailWord_40777).sum := by decide
  have hdescent : baseEnd_40777 < baseStart_40777 := by decide
  rcases family_descends (prefixWord ++ tailWord_40777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40821 : List Nat := [1, 3, 4, 1, 1, 1, 5, 2, 2]
def baseStart_40821 : Nat := 118140960795 + 40821 * 2 ^ 59
def prefixEnd_40821 : Nat := 4983230072969 + 3 ^ 40 * 40821 * 2
def baseEnd_40821 : Nat := 18631816708702241199799

theorem tailTrace_40821 : CollatzResearch.WordTrace tailWord_40821 prefixEnd_40821 18631816708702241199799 := by
  unfold tailWord_40821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488864185119963516866317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 992576123413309011244211 1488864185119963516866317)
  ·
    refine ⟨558324069419986318824869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1488864185119963516866317 558324069419986318824869)
    ·
      refine ⟨104685763016247434779663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 558324069419986318824869 104685763016247434779663)
      ·
        refine ⟨157028644524371152169495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104685763016247434779663 157028644524371152169495)
        ·
          refine ⟨235542966786556728254243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157028644524371152169495 235542966786556728254243)
          ·
            refine ⟨353314450179835092381365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235542966786556728254243 353314450179835092381365)
            ·
              refine ⟨33123229704359539910753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353314450179835092381365 33123229704359539910753)
              ·
                refine ⟨24842422278269654933065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33123229704359539910753 24842422278269654933065)
                ·
                  refine ⟨18631816708702241199799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24842422278269654933065 18631816708702241199799)
                  ·
                    rfl

theorem cell20_40821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_40821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40821 prefixEnd_40821 := by exact prefixLift 40821
  have htrace : WordTrace (prefixWord ++ tailWord_40821) baseStart_40821 baseEnd_40821 := by
    simpa [prefixWord, tailWord_40821, baseEnd_40821] using wordTrace_append hprefix tailTrace_40821
  have hstable : (prefixWord ++ tailWord_40821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40821).length < 2 ^ (prefixWord ++ tailWord_40821).sum := by decide
  have hdescent : baseEnd_40821 < baseStart_40821 := by decide
  rcases family_descends (prefixWord ++ tailWord_40821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40835 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 3]
def baseStart_40835 : Nat := 118140960795 + 40835 * 2 ^ 59
def prefixEnd_40835 : Nat := 4983230072969 + 3 ^ 40 * 40835 * 2
def baseEnd_40835 : Nat := 18638206690180414733075

theorem tailTrace_40835 : CollatzResearch.WordTrace tailWord_40835 prefixEnd_40835 18638206690180414733075 := by
  unfold tailWord_40835
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489374807069243907875959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 992916538046162605250639 1489374807069243907875959)
  ·
    refine ⟨2234062210603865861813939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1489374807069243907875959 2234062210603865861813939)
    ·
      refine ⟨3351093315905798792720909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234062210603865861813939 3351093315905798792720909)
      ·
        refine ⟨1256659993464674547270341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3351093315905798792720909 1256659993464674547270341)
        ·
          refine ⟨235623748774626477613189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1256659993464674547270341 235623748774626477613189)
          ·
            refine ⟨44179452895242464552473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235623748774626477613189 44179452895242464552473)
            ·
              refine ⟨33134589671431848414355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44179452895242464552473 33134589671431848414355)
              ·
                refine ⟨49701884507147772621533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33134589671431848414355 49701884507147772621533)
                ·
                  refine ⟨18638206690180414733075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49701884507147772621533 18638206690180414733075)
                  ·
                    rfl

theorem cell20_40835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 3].length) (baseStart_40835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40835 prefixEnd_40835 := by exact prefixLift 40835
  have htrace : WordTrace (prefixWord ++ tailWord_40835) baseStart_40835 baseEnd_40835 := by
    simpa [prefixWord, tailWord_40835, baseEnd_40835] using wordTrace_append hprefix tailTrace_40835
  have hstable : (prefixWord ++ tailWord_40835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40835).length < 2 ^ (prefixWord ++ tailWord_40835).sum := by decide
  have hdescent : baseEnd_40835 < baseStart_40835 := by decide
  rcases family_descends (prefixWord ++ tailWord_40835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40853 : List Nat := [1, 3, 2, 1, 1, 3, 1, 8]
def baseStart_40853 : Nat := 118140960795 + 40853 * 2 ^ 59
def prefixEnd_40853 : Nat := 4983230072969 + 3 ^ 40 * 40853 * 2
def baseEnd_40853 : Nat := 6215474126884117377667

theorem tailTrace_40853 : CollatzResearch.WordTrace tailWord_40853 prefixEnd_40853 6215474126884117377667 := by
  unfold tailWord_40853
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490031321004032982031213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 993354214002688654687475 1490031321004032982031213)
  ·
    refine ⟨558761745376512368261705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1490031321004032982031213 558761745376512368261705)
    ·
      refine ⟨419071309032384276196279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 558761745376512368261705 419071309032384276196279)
      ·
        refine ⟨628606963548576414294419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419071309032384276196279 628606963548576414294419)
        ·
          refine ⟨942910445322864621441629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628606963548576414294419 942910445322864621441629)
          ·
            refine ⟨353591416996074233040611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 942910445322864621441629 353591416996074233040611)
            ·
              refine ⟨530387125494111349560917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353591416996074233040611 530387125494111349560917)
              ·
                refine ⟨6215474126884117377667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 530387125494111349560917 6215474126884117377667)
                ·
                  rfl

theorem cell20_40853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_40853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40853 prefixEnd_40853 := by exact prefixLift 40853
  have htrace : WordTrace (prefixWord ++ tailWord_40853) baseStart_40853 baseEnd_40853 := by
    simpa [prefixWord, tailWord_40853, baseEnd_40853] using wordTrace_append hprefix tailTrace_40853
  have hstable : (prefixWord ++ tailWord_40853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40853).length < 2 ^ (prefixWord ++ tailWord_40853).sum := by decide
  have hdescent : baseEnd_40853 < baseStart_40853 := by decide
  rcases family_descends (prefixWord ++ tailWord_40853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40872 : List Nat := [2, 1, 6, 2, 2, 1, 2, 2, 2]
def baseStart_40872 : Nat := 118140960795 + 40872 * 2 ^ 59
def prefixEnd_40872 : Nat := 4983230072969 + 3 ^ 40 * 40872 * 2
def baseEnd_40872 : Nat := 18655094498372730499591

theorem tailTrace_40872 : CollatzResearch.WordTrace tailWord_40872 prefixEnd_40872 18655094498372730499591 := by
  unfold tailWord_40872
  simp only [CollatzResearch.WordTrace]
  refine ⟨745362153967599613486435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 993816205290132817981913 745362153967599613486435)
  ·
    refine ⟨1118043230951399420229653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745362153967599613486435 1118043230951399420229653)
    ·
      refine ⟨52408276450846847823265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1118043230951399420229653 52408276450846847823265)
      ·
        refine ⟨39306207338135135867449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52408276450846847823265 39306207338135135867449)
        ·
          refine ⟨29479655503601351900587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39306207338135135867449 29479655503601351900587)
          ·
            refine ⟨44219483255402027850881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29479655503601351900587 44219483255402027850881)
            ·
              refine ⟨33164612441551520888161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44219483255402027850881 33164612441551520888161)
              ·
                refine ⟨24873459331163640666121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33164612441551520888161 24873459331163640666121)
                ·
                  refine ⟨18655094498372730499591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24873459331163640666121 18655094498372730499591)
                  ·
                    rfl

theorem cell20_40872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_40872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40872 prefixEnd_40872 := by exact prefixLift 40872
  have htrace : WordTrace (prefixWord ++ tailWord_40872) baseStart_40872 baseEnd_40872 := by
    simpa [prefixWord, tailWord_40872, baseEnd_40872] using wordTrace_append hprefix tailTrace_40872
  have hstable : (prefixWord ++ tailWord_40872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40872).length < 2 ^ (prefixWord ++ tailWord_40872).sum := by decide
  have hdescent : baseEnd_40872 < baseStart_40872 := by decide
  rcases family_descends (prefixWord ++ tailWord_40872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40894 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_40894 : Nat := 118140960795 + 40894 * 2 ^ 59
def prefixEnd_40894 : Nat := 4983230072969 + 3 ^ 40 * 40894 * 2
def baseEnd_40894 : Nat := 18665135897838431766167

theorem tailTrace_40894 : CollatzResearch.WordTrace tailWord_40894 prefixEnd_40894 18665135897838431766167 := by
  unfold tailWord_40894
  simp only [CollatzResearch.WordTrace]
  refine ⟨186440839231937123034217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 994351142570331322849157 186440839231937123034217)
  ·
    refine ⟨139830629423952842275663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186440839231937123034217 139830629423952842275663)
    ·
      refine ⟨209745944135929263413495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139830629423952842275663 209745944135929263413495)
      ·
        refine ⟨314618916203893895120243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209745944135929263413495 314618916203893895120243)
        ·
          refine ⟨471928374305840842680365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314618916203893895120243 471928374305840842680365)
          ·
            refine ⟨176973140364690316005137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471928374305840842680365 176973140364690316005137)
            ·
              refine ⟨132729855273517737003853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176973140364690316005137 132729855273517737003853)
              ·
                refine ⟨49773695727569151376445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132729855273517737003853 49773695727569151376445)
                ·
                  refine ⟨18665135897838431766167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49773695727569151376445 18665135897838431766167)
                  ·
                    rfl

theorem cell20_40894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_40894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40894 prefixEnd_40894 := by exact prefixLift 40894
  have htrace : WordTrace (prefixWord ++ tailWord_40894) baseStart_40894 baseEnd_40894 := by
    simpa [prefixWord, tailWord_40894, baseEnd_40894] using wordTrace_append hprefix tailTrace_40894
  have hstable : (prefixWord ++ tailWord_40894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40894).length < 2 ^ (prefixWord ++ tailWord_40894).sum := by decide
  have hdescent : baseEnd_40894 < baseStart_40894 := by decide
  rcases family_descends (prefixWord ++ tailWord_40894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40924 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 3]
def baseStart_40924 : Nat := 118140960795 + 40924 * 2 ^ 59
def prefixEnd_40924 : Nat := 4983230072969 + 3 ^ 40 * 40924 * 2
def baseEnd_40924 : Nat := 18678828715291660766045

theorem tailTrace_40924 : CollatzResearch.WordTrace tailWord_40924 prefixEnd_40924 18678828715291660766045 := by
  unfold tailWord_40924
  simp only [CollatzResearch.WordTrace]
  refine ⟨746310451873406053932913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 995080602497874738577217 746310451873406053932913)
  ·
    refine ⟨559732838905054540449685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 746310451873406053932913 559732838905054540449685)
    ·
      refine ⟨26237476823674431583579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 559732838905054540449685 26237476823674431583579)
      ·
        refine ⟨39356215235511647375369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26237476823674431583579 39356215235511647375369)
        ·
          refine ⟨29517161426633735531527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39356215235511647375369 29517161426633735531527)
          ·
            refine ⟨44275742139950603297291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29517161426633735531527 44275742139950603297291)
            ·
              refine ⟨66413613209925904945937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44275742139950603297291 66413613209925904945937)
              ·
                refine ⟨49810209907444428709453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66413613209925904945937 49810209907444428709453)
                ·
                  refine ⟨18678828715291660766045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49810209907444428709453 18678828715291660766045)
                  ·
                    rfl

theorem cell20_40924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_40924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40924 prefixEnd_40924 := by exact prefixLift 40924
  have htrace : WordTrace (prefixWord ++ tailWord_40924) baseStart_40924 baseEnd_40924 := by
    simpa [prefixWord, tailWord_40924, baseEnd_40924] using wordTrace_append hprefix tailTrace_40924
  have hstable : (prefixWord ++ tailWord_40924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40924).length < 2 ^ (prefixWord ++ tailWord_40924).sum := by decide
  have hdescent : baseEnd_40924 < baseStart_40924 := by decide
  rcases family_descends (prefixWord ++ tailWord_40924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40980 : List Nat := [2, 4, 3, 2, 1, 2, 6]
def baseStart_40980 : Nat := 118140960795 + 40980 * 2 ^ 59
def prefixEnd_40980 : Nat := 4983230072969 + 3 ^ 40 * 40980 * 2
def baseEnd_40980 : Nat := 2078265404578261655461

theorem tailTrace_40980 : CollatzResearch.WordTrace tailWord_40980 prefixEnd_40980 2078265404578261655461 := by
  unfold tailWord_40980
  simp only [CollatzResearch.WordTrace]
  refine ⟨747331695771966835952197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 996442261029289114602929 747331695771966835952197)
  ·
    refine ⟨140124692957243781741037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 747331695771966835952197 140124692957243781741037)
    ·
      refine ⟨52546759858966418152889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140124692957243781741037 52546759858966418152889)
      ·
        refine ⟨39410069894224813614667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52546759858966418152889 39410069894224813614667)
        ·
          refine ⟨59115104841337220422001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39410069894224813614667 59115104841337220422001)
          ·
            refine ⟨44336328631002915316501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59115104841337220422001 44336328631002915316501)
            ·
              refine ⟨2078265404578261655461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44336328631002915316501 2078265404578261655461)
              ·
                rfl

theorem cell20_40980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 6].length) (baseStart_40980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40980 prefixEnd_40980 := by exact prefixLift 40980
  have htrace : WordTrace (prefixWord ++ tailWord_40980) baseStart_40980 baseEnd_40980 := by
    simpa [prefixWord, tailWord_40980, baseEnd_40980] using wordTrace_append hprefix tailTrace_40980
  have hstable : (prefixWord ++ tailWord_40980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40980).length < 2 ^ (prefixWord ++ tailWord_40980).sum := by decide
  have hdescent : baseEnd_40980 < baseStart_40980 := by decide
  rcases family_descends (prefixWord ++ tailWord_40980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40991 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 3]
def baseStart_40991 : Nat := 118140960795 + 40991 * 2 ^ 59
def prefixEnd_40991 : Nat := 4983230072969 + 3 ^ 40 * 40991 * 2
def baseEnd_40991 : Nat := 18709409340937205532437

theorem tailTrace_40991 : CollatzResearch.WordTrace tailWord_40991 prefixEnd_40991 18709409340937205532437 := by
  unfold tailWord_40991
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495064594504082550554827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 996709729669388367036551 1495064594504082550554827)
  ·
    refine ⟨2242596891756123825832241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1495064594504082550554827 2242596891756123825832241)
    ·
      refine ⟨1681947668817092869374181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2242596891756123825832241 1681947668817092869374181)
      ·
        refine ⟨315365187903204913007659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1681947668817092869374181 315365187903204913007659)
        ·
          refine ⟨473047781854807369511489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315365187903204913007659 473047781854807369511489)
          ·
            refine ⟨354785836391105527133617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473047781854807369511489 354785836391105527133617)
            ·
              refine ⟨266089377293329145350213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354785836391105527133617 266089377293329145350213)
              ·
                refine ⟨49891758242499214753165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266089377293329145350213 49891758242499214753165)
                ·
                  refine ⟨18709409340937205532437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49891758242499214753165 18709409340937205532437)
                  ·
                    rfl

theorem cell20_40991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_40991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_40991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_40991 prefixEnd_40991 := by exact prefixLift 40991
  have htrace : WordTrace (prefixWord ++ tailWord_40991) baseStart_40991 baseEnd_40991 := by
    simpa [prefixWord, tailWord_40991, baseEnd_40991] using wordTrace_append hprefix tailTrace_40991
  have hstable : (prefixWord ++ tailWord_40991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40991).length < 2 ^ (prefixWord ++ tailWord_40991).sum := by decide
  have hdescent : baseEnd_40991 < baseStart_40991 := by decide
  rcases family_descends (prefixWord ++ tailWord_40991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41008 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_41008 : Nat := 118140960795 + 41008 * 2 ^ 59
def prefixEnd_41008 : Nat := 4983230072969 + 3 ^ 40 * 41008 * 2
def baseEnd_41008 : Nat := 18717168604160701965701

theorem tailTrace_41008 : CollatzResearch.WordTrace tailWord_41008 prefixEnd_41008 18717168604160701965701 := by
  unfold tailWord_41008
  simp only [CollatzResearch.WordTrace]
  refine ⟨747842317721247226961839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 997123090294996302615785 747842317721247226961839)
  ·
    refine ⟨1121763476581870840442759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 747842317721247226961839 1121763476581870840442759)
    ·
      refine ⟨1682645214872806260664139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1121763476581870840442759 1682645214872806260664139)
      ·
        refine ⟨2523967822309209390996209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682645214872806260664139 2523967822309209390996209)
        ·
          refine ⟨1892975866731907043247157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2523967822309209390996209 1892975866731907043247157)
          ·
            refine ⟨177466487506116285304421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1892975866731907043247157 177466487506116285304421)
            ·
              refine ⟨33274966407396803494579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177466487506116285304421 33274966407396803494579)
              ·
                refine ⟨49912449611095205241869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33274966407396803494579 49912449611095205241869)
                ·
                  refine ⟨18717168604160701965701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49912449611095205241869 18717168604160701965701)
                  ·
                    rfl

theorem cell20_41008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_41008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41008 prefixEnd_41008 := by exact prefixLift 41008
  have htrace : WordTrace (prefixWord ++ tailWord_41008) baseStart_41008 baseEnd_41008 := by
    simpa [prefixWord, tailWord_41008, baseEnd_41008] using wordTrace_append hprefix tailTrace_41008
  have hstable : (prefixWord ++ tailWord_41008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41008).length < 2 ^ (prefixWord ++ tailWord_41008).sum := by decide
  have hdescent : baseEnd_41008 < baseStart_41008 := by decide
  rcases family_descends (prefixWord ++ tailWord_41008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41074 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_41074 : Nat := 118140960795 + 41074 * 2 ^ 59
def prefixEnd_41074 : Nat := 4983230072969 + 3 ^ 40 * 41074 * 2
def baseEnd_41074 : Nat := 18747292802557805765431

theorem tailTrace_41074 : CollatzResearch.WordTrace tailWord_41074 prefixEnd_41074 18747292802557805765431 := by
  unfold tailWord_41074
  simp only [CollatzResearch.WordTrace]
  refine ⟨374522963300846931456569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 998727902135591817217517 374522963300846931456569)
  ·
    refine ⟨280892222475635198592427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 374522963300846931456569 280892222475635198592427)
    ·
      refine ⟨421338333713452797888641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280892222475635198592427 421338333713452797888641)
      ·
        refine ⟨316003750285089598416481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421338333713452797888641 316003750285089598416481)
        ·
          refine ⟨237002812713817198812361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316003750285089598416481 237002812713817198812361)
          ·
            refine ⟨177752109535362899109271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237002812713817198812361 177752109535362899109271)
            ·
              refine ⟨266628164303044348663907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177752109535362899109271 266628164303044348663907)
              ·
                refine ⟨399942246454566522995861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266628164303044348663907 399942246454566522995861)
                ·
                  refine ⟨18747292802557805765431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 399942246454566522995861 18747292802557805765431)
                  ·
                    rfl

theorem cell20_41074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_41074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41074 prefixEnd_41074 := by exact prefixLift 41074
  have htrace : WordTrace (prefixWord ++ tailWord_41074) baseStart_41074 baseEnd_41074 := by
    simpa [prefixWord, tailWord_41074, baseEnd_41074] using wordTrace_append hprefix tailTrace_41074
  have hstable : (prefixWord ++ tailWord_41074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41074).length < 2 ^ (prefixWord ++ tailWord_41074).sum := by decide
  have hdescent : baseEnd_41074 < baseStart_41074 := by decide
  rcases family_descends (prefixWord ++ tailWord_41074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41088 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_41088 : Nat := 118140960795 + 41088 * 2 ^ 59
def prefixEnd_41088 : Nat := 4983230072969 + 3 ^ 40 * 41088 * 2
def baseEnd_41088 : Nat := 18753682784035979298707

theorem tailTrace_41088 : CollatzResearch.WordTrace tailWord_41088 prefixEnd_41088 18753682784035979298707 := by
  unfold tailWord_41088
  simp only [CollatzResearch.WordTrace]
  refine ⟨749301237576334058417959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 999068316768445411223945 749301237576334058417959)
  ·
    refine ⟨1123951856364501087626939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 749301237576334058417959 1123951856364501087626939)
    ·
      refine ⟨1685927784546751631440409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123951856364501087626939 1685927784546751631440409)
      ·
        refine ⟨1264445838410063723580307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1685927784546751631440409 1264445838410063723580307)
        ·
          refine ⟨1896668757615095585370461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264445838410063723580307 1896668757615095585370461)
          ·
            refine ⟨711250784105660844513923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1896668757615095585370461 711250784105660844513923)
            ·
              refine ⟨1066876176158491266770885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711250784105660844513923 1066876176158491266770885)
              ·
                refine ⟨200039283029717112519541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1066876176158491266770885 200039283029717112519541)
                ·
                  refine ⟨18753682784035979298707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200039283029717112519541 18753682784035979298707)
                  ·
                    rfl

theorem cell20_41088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_41088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41088 prefixEnd_41088 := by exact prefixLift 41088
  have htrace : WordTrace (prefixWord ++ tailWord_41088) baseStart_41088 baseEnd_41088 := by
    simpa [prefixWord, tailWord_41088, baseEnd_41088] using wordTrace_append hprefix tailTrace_41088
  have hstable : (prefixWord ++ tailWord_41088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41088).length < 2 ^ (prefixWord ++ tailWord_41088).sum := by decide
  have hdescent : baseEnd_41088 < baseStart_41088 := by decide
  rcases family_descends (prefixWord ++ tailWord_41088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41091 : List Nat := [1, 1, 1, 3, 3, 3, 1, 5, 2]
def baseStart_41091 : Nat := 118140960795 + 41091 * 2 ^ 59
def prefixEnd_41091 : Nat := 4983230072969 + 3 ^ 40 * 41091 * 2
def baseEnd_41091 : Nat := 18755052065781302198695

theorem tailTrace_41091 : CollatzResearch.WordTrace tailWord_41091 prefixEnd_41091 18755052065781302198695 := by
  unfold tailWord_41091
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498711894141799629195127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 999141262761199752796751 1498711894141799629195127)
  ·
    refine ⟨2248067841212699443792691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498711894141799629195127 2248067841212699443792691)
    ·
      refine ⟨3372101761819049165689037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248067841212699443792691 3372101761819049165689037)
      ·
        refine ⟨1264538160682143437133389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3372101761819049165689037 1264538160682143437133389)
        ·
          refine ⟨474201810255803788925021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1264538160682143437133389 474201810255803788925021)
          ·
            refine ⟨177825678845926420846883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474201810255803788925021 177825678845926420846883)
            ·
              refine ⟨266738518268889631270325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177825678845926420846883 266738518268889631270325)
              ·
                refine ⟨25006736087708402931593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266738518268889631270325 25006736087708402931593)
                ·
                  refine ⟨18755052065781302198695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25006736087708402931593 18755052065781302198695)
                  ·
                    rfl

theorem cell20_41091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 2].length) (baseStart_41091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41091 prefixEnd_41091 := by exact prefixLift 41091
  have htrace : WordTrace (prefixWord ++ tailWord_41091) baseStart_41091 baseEnd_41091 := by
    simpa [prefixWord, tailWord_41091, baseEnd_41091] using wordTrace_append hprefix tailTrace_41091
  have hstable : (prefixWord ++ tailWord_41091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41091).length < 2 ^ (prefixWord ++ tailWord_41091).sum := by decide
  have hdescent : baseEnd_41091 < baseStart_41091 := by decide
  rcases family_descends (prefixWord ++ tailWord_41091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41118 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_41118 : Nat := 118140960795 + 41118 * 2 ^ 59
def prefixEnd_41118 : Nat := 4983230072969 + 3 ^ 40 * 41118 * 2
def baseEnd_41118 : Nat := 18767375601489208298585

theorem tailTrace_41118 : CollatzResearch.WordTrace tailWord_41118 prefixEnd_41118 18767375601489208298585 := by
  unfold tailWord_41118
  simp only [CollatzResearch.WordTrace]
  refine ⟨187462083130497905053501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 999797776695988826952005 187462083130497905053501)
  ·
    refine ⟨70298281173936714395063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187462083130497905053501 70298281173936714395063)
    ·
      refine ⟨105447421760905071592595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70298281173936714395063 105447421760905071592595)
      ·
        refine ⟨158171132641357607388893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105447421760905071592595 158171132641357607388893)
        ·
          refine ⟨59314174740509102770835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158171132641357607388893 59314174740509102770835)
          ·
            refine ⟨88971262110763654156253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59314174740509102770835 88971262110763654156253)
            ·
              refine ⟨33364223291536370308595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88971262110763654156253 33364223291536370308595)
              ·
                refine ⟨50046334937304555462893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33364223291536370308595 50046334937304555462893)
                ·
                  refine ⟨18767375601489208298585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50046334937304555462893 18767375601489208298585)
                  ·
                    rfl

theorem cell20_41118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_41118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41118 prefixEnd_41118 := by exact prefixLift 41118
  have htrace : WordTrace (prefixWord ++ tailWord_41118) baseStart_41118 baseEnd_41118 := by
    simpa [prefixWord, tailWord_41118, baseEnd_41118] using wordTrace_append hprefix tailTrace_41118
  have hstable : (prefixWord ++ tailWord_41118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41118).length < 2 ^ (prefixWord ++ tailWord_41118).sum := by decide
  have hdescent : baseEnd_41118 < baseStart_41118 := by decide
  rcases family_descends (prefixWord ++ tailWord_41118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41153 : List Nat := [1, 2, 6, 1, 2, 2, 6]
def baseStart_41153 : Nat := 118140960795 + 41153 * 2 ^ 59
def prefixEnd_41153 : Nat := 4983230072969 + 3 ^ 40 * 41153 * 2
def baseEnd_41153 : Nat := 2087038950576071347975

theorem tailTrace_41153 : CollatzResearch.WordTrace tailWord_41153 prefixEnd_41153 2087038950576071347975 := by
  unfold tailWord_41153
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500973219917184217952113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1000648813278122811968075 1500973219917184217952113)
  ·
    refine ⟨1125729914937888163464085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1500973219917184217952113 1125729914937888163464085)
    ·
      refine ⟨52768589762713507662379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1125729914937888163464085 52768589762713507662379)
      ·
        refine ⟨79152884644070261493569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52768589762713507662379 79152884644070261493569)
        ·
          refine ⟨59364663483052696120177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79152884644070261493569 59364663483052696120177)
          ·
            refine ⟨44523497612289522090133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59364663483052696120177 44523497612289522090133)
            ·
              refine ⟨2087038950576071347975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44523497612289522090133 2087038950576071347975)
              ·
                rfl

theorem cell20_41153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 6].length) (baseStart_41153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41153 prefixEnd_41153 := by exact prefixLift 41153
  have htrace : WordTrace (prefixWord ++ tailWord_41153) baseStart_41153 baseEnd_41153 := by
    simpa [prefixWord, tailWord_41153, baseEnd_41153] using wordTrace_append hprefix tailTrace_41153
  have hstable : (prefixWord ++ tailWord_41153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41153).length < 2 ^ (prefixWord ++ tailWord_41153).sum := by decide
  have hdescent : baseEnd_41153 < baseStart_41153 := by decide
  rcases family_descends (prefixWord ++ tailWord_41153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41209 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_41209 : Nat := 118140960795 + 41209 * 2 ^ 59
def prefixEnd_41209 : Nat := 4983230072969 + 3 ^ 40 * 41209 * 2
def baseEnd_41209 : Nat := 18808910481097336264879

theorem tailTrace_41209 : CollatzResearch.WordTrace tailWord_41209 prefixEnd_41209 18808910481097336264879 := by
  unfold tailWord_41209
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503015707714305781990681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1002010471809537187993787 1503015707714305781990681)
  ·
    refine ⟨1127261780785729336493011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1503015707714305781990681 1127261780785729336493011)
    ·
      refine ⟨1690892671178594004739517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127261780785729336493011 1690892671178594004739517)
      ·
        refine ⟨634084751691972751777319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1690892671178594004739517 634084751691972751777319)
        ·
          refine ⟨951127127537959127665979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634084751691972751777319 951127127537959127665979)
          ·
            refine ⟨1426690691306938691498969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951127127537959127665979 1426690691306938691498969)
            ·
              refine ⟨1070018018480204018624227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426690691306938691498969 1070018018480204018624227)
              ·
                refine ⟨1605027027720306027936341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070018018480204018624227 1605027027720306027936341)
                ·
                  refine ⟨18808910481097336264879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1605027027720306027936341 18808910481097336264879)
                  ·
                    rfl

theorem cell20_41209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_41209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41209 prefixEnd_41209 := by exact prefixLift 41209
  have htrace : WordTrace (prefixWord ++ tailWord_41209) baseStart_41209 baseEnd_41209 := by
    simpa [prefixWord, tailWord_41209, baseEnd_41209] using wordTrace_append hprefix tailTrace_41209
  have hstable : (prefixWord ++ tailWord_41209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41209).length < 2 ^ (prefixWord ++ tailWord_41209).sum := by decide
  have hdescent : baseEnd_41209 < baseStart_41209 := by decide
  rcases family_descends (prefixWord ++ tailWord_41209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41218 : List Nat := [3, 4, 1, 1, 2, 3, 2, 2, 2]
def baseStart_41218 : Nat := 118140960795 + 41218 * 2 ^ 59
def prefixEnd_41218 : Nat := 4983230072969 + 3 ^ 40 * 41218 * 2
def baseEnd_41218 : Nat := 18813018326333304964843

theorem tailTrace_41218 : CollatzResearch.WordTrace tailWord_41218 prefixEnd_41218 18813018326333304964843 := by
  unfold tailWord_41218
  simp only [CollatzResearch.WordTrace]
  refine ⟨375835991170425079767077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1002229309787800212712205 375835991170425079767077)
  ·
    refine ⟨70469248344454702456327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 375835991170425079767077 70469248344454702456327)
    ·
      refine ⟨105703872516682053684491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70469248344454702456327 105703872516682053684491)
      ·
        refine ⟨158555808775023080526737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105703872516682053684491 158555808775023080526737)
        ·
          refine ⟨118916856581267310395053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158555808775023080526737 118916856581267310395053)
          ·
            refine ⟨44593821217975241398145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118916856581267310395053 44593821217975241398145)
            ·
              refine ⟨33445365913481431048609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44593821217975241398145 33445365913481431048609)
              ·
                refine ⟨25084024435111073286457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33445365913481431048609 25084024435111073286457)
                ·
                  refine ⟨18813018326333304964843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25084024435111073286457 18813018326333304964843)
                  ·
                    rfl

theorem cell20_41218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_41218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41218 prefixEnd_41218 := by exact prefixLift 41218
  have htrace : WordTrace (prefixWord ++ tailWord_41218) baseStart_41218 baseEnd_41218 := by
    simpa [prefixWord, tailWord_41218, baseEnd_41218] using wordTrace_append hprefix tailTrace_41218
  have hstable : (prefixWord ++ tailWord_41218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41218).length < 2 ^ (prefixWord ++ tailWord_41218).sum := by decide
  have hdescent : baseEnd_41218 < baseStart_41218 := by decide
  rcases family_descends (prefixWord ++ tailWord_41218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41219 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 3]
def baseStart_41219 : Nat := 118140960795 + 41219 * 2 ^ 59
def prefixEnd_41219 : Nat := 4983230072969 + 3 ^ 40 * 41219 * 2
def baseEnd_41219 : Nat := 18813474753581745931505

theorem tailTrace_41219 : CollatzResearch.WordTrace tailWord_41219 prefixEnd_41219 18813474753581745931505 := by
  unfold tailWord_41219
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503380437678077489854711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1002253625118718326569807 1503380437678077489854711)
  ·
    refine ⟨2255070656517116234782067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1503380437678077489854711 2255070656517116234782067)
    ·
      refine ⟨3382605984775674352173101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255070656517116234782067 3382605984775674352173101)
      ·
        refine ⟨1268477244290877882064913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3382605984775674352173101 1268477244290877882064913)
        ·
          refine ⟨951357933218158411548685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1268477244290877882064913 951357933218158411548685)
          ·
            refine ⟨356759224956809404330757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 951357933218158411548685 356759224956809404330757)
            ·
              refine ⟨66892354679401763312017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 356759224956809404330757 66892354679401763312017)
              ·
                refine ⟨50169266009551322484013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66892354679401763312017 50169266009551322484013)
                ·
                  refine ⟨18813474753581745931505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50169266009551322484013 18813474753581745931505)
                  ·
                    rfl

theorem cell20_41219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_41219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41219 prefixEnd_41219 := by exact prefixLift 41219
  have htrace : WordTrace (prefixWord ++ tailWord_41219) baseStart_41219 baseEnd_41219 := by
    simpa [prefixWord, tailWord_41219, baseEnd_41219] using wordTrace_append hprefix tailTrace_41219
  have hstable : (prefixWord ++ tailWord_41219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41219).length < 2 ^ (prefixWord ++ tailWord_41219).sum := by decide
  have hdescent : baseEnd_41219 < baseStart_41219 := by decide
  rcases family_descends (prefixWord ++ tailWord_41219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41233 : List Nat := [1, 2, 2, 1, 1, 5, 3, 5]
def baseStart_41233 : Nat := 118140960795 + 41233 * 2 ^ 59
def prefixEnd_41233 : Nat := 4983230072969 + 3 ^ 40 * 41233 * 2
def baseEnd_41233 : Nat := 6273288245019973154927

theorem tailTrace_41233 : CollatzResearch.WordTrace tailWord_41233 prefixEnd_41233 6273288245019973154927 := by
  unfold tailWord_41233
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503891059627357880864353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1002594039751571920576235 1503891059627357880864353)
  ·
    refine ⟨1127918294720518410648265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1503891059627357880864353 1127918294720518410648265)
    ·
      refine ⟨845938721040388807986199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1127918294720518410648265 845938721040388807986199)
      ·
        refine ⟨1268908081560583211979299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845938721040388807986199 1268908081560583211979299)
        ·
          refine ⟨1903362122340874817968949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268908081560583211979299 1903362122340874817968949)
          ·
            refine ⟨178440198969457014184589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1903362122340874817968949 178440198969457014184589)
            ·
              refine ⟨66915074613546380319221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178440198969457014184589 66915074613546380319221)
              ·
                refine ⟨6273288245019973154927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66915074613546380319221 6273288245019973154927)
                ·
                  rfl

theorem cell20_41233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_41233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41233 prefixEnd_41233 := by exact prefixLift 41233
  have htrace : WordTrace (prefixWord ++ tailWord_41233) baseStart_41233 baseEnd_41233 := by
    simpa [prefixWord, tailWord_41233, baseEnd_41233] using wordTrace_append hprefix tailTrace_41233
  have hstable : (prefixWord ++ tailWord_41233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41233).length < 2 ^ (prefixWord ++ tailWord_41233).sum := by decide
  have hdescent : baseEnd_41233 < baseStart_41233 := by decide
  rcases family_descends (prefixWord ++ tailWord_41233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41246 : List Nat := [4, 3, 2, 1, 1, 2, 3, 4]
def baseStart_41246 : Nat := 118140960795 + 41246 * 2 ^ 59
def prefixEnd_41246 : Nat := 4983230072969 + 3 ^ 40 * 41246 * 2
def baseEnd_41246 : Nat := 6275266096429884010465

theorem tailTrace_41246 : CollatzResearch.WordTrace tailWord_41246 prefixEnd_41246 6275266096429884010465 := by
  unfold tailWord_41246
  simp only [CollatzResearch.WordTrace]
  refine ⟨188045651072532637635949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1002910139053507400725061 188045651072532637635949)
  ·
    refine ⟨70517119152199739113481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188045651072532637635949 70517119152199739113481)
    ·
      refine ⟨52887839364149804335111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70517119152199739113481 52887839364149804335111)
      ·
        refine ⟨79331759046224706502667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52887839364149804335111 79331759046224706502667)
        ·
          refine ⟨118997638569337059754001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79331759046224706502667 118997638569337059754001)
          ·
            refine ⟨89248228927002794815501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118997638569337059754001 89248228927002794815501)
            ·
              refine ⟨33468085847626048055813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89248228927002794815501 33468085847626048055813)
              ·
                refine ⟨6275266096429884010465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33468085847626048055813 6275266096429884010465)
                ·
                  rfl

theorem cell20_41246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_41246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41246 prefixEnd_41246 := by exact prefixLift 41246
  have htrace : WordTrace (prefixWord ++ tailWord_41246) baseStart_41246 baseEnd_41246 := by
    simpa [prefixWord, tailWord_41246, baseEnd_41246] using wordTrace_append hprefix tailTrace_41246
  have hstable : (prefixWord ++ tailWord_41246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41246).length < 2 ^ (prefixWord ++ tailWord_41246).sum := by decide
  have hdescent : baseEnd_41246 < baseStart_41246 := by decide
  rcases family_descends (prefixWord ++ tailWord_41246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41274 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_41274 : Nat := 118140960795 + 41274 * 2 ^ 59
def prefixEnd_41274 : Nat := 4983230072969 + 3 ^ 40 * 41274 * 2
def baseEnd_41274 : Nat := 18838578252245999097947

theorem tailTrace_41274 : CollatzResearch.WordTrace tailWord_41274 prefixEnd_41274 18838578252245999097947 := by
  unfold tailWord_41274
  simp only [CollatzResearch.WordTrace]
  refine ⟨376346613119705470776719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1003590968319214588737917 376346613119705470776719)
  ·
    refine ⟨564519919679558206165079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 376346613119705470776719 564519919679558206165079)
    ·
      refine ⟨846779879519337309247619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564519919679558206165079 846779879519337309247619)
      ·
        refine ⟨1270169819279005963871429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846779879519337309247619 1270169819279005963871429)
        ·
          refine ⟨238156841114813618225893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1270169819279005963871429 238156841114813618225893)
          ·
            refine ⟨44654407709027553417355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238156841114813618225893 44654407709027553417355)
            ·
              refine ⟨66981611563541330126033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44654407709027553417355 66981611563541330126033)
              ·
                refine ⟨50236208672655997594525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66981611563541330126033 50236208672655997594525)
                ·
                  refine ⟨18838578252245999097947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50236208672655997594525 18838578252245999097947)
                  ·
                    rfl

theorem cell20_41274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_41274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41274 prefixEnd_41274 := by exact prefixLift 41274
  have htrace : WordTrace (prefixWord ++ tailWord_41274) baseStart_41274 baseEnd_41274 := by
    simpa [prefixWord, tailWord_41274, baseEnd_41274] using wordTrace_append hprefix tailTrace_41274
  have hstable : (prefixWord ++ tailWord_41274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41274).length < 2 ^ (prefixWord ++ tailWord_41274).sum := by decide
  have hdescent : baseEnd_41274 < baseStart_41274 := by decide
  rcases family_descends (prefixWord ++ tailWord_41274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41316 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_41316 : Nat := 118140960795 + 41316 * 2 ^ 59
def prefixEnd_41316 : Nat := 4983230072969 + 3 ^ 40 * 41316 * 2
def baseEnd_41316 : Nat := 18857748196680519697775

theorem tailTrace_41316 : CollatzResearch.WordTrace tailWord_41316 prefixEnd_41316 18857748196680519697775 := by
  unfold tailWord_41316
  simp only [CollatzResearch.WordTrace]
  refine ⟨753459159163331528067901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1004612212217775370757201 753459159163331528067901)
  ·
    refine ⟨282547184686249323025463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 753459159163331528067901 282547184686249323025463)
    ·
      refine ⟨423820777029373984538195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282547184686249323025463 423820777029373984538195)
      ·
        refine ⟨635731165544060976807293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423820777029373984538195 635731165544060976807293)
        ·
          refine ⟨238399187079022866302735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 635731165544060976807293 238399187079022866302735)
          ·
            refine ⟨357598780618534299454103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238399187079022866302735 357598780618534299454103)
            ·
              refine ⟨536398170927801449181155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357598780618534299454103 536398170927801449181155)
              ·
                refine ⟨804597256391702173771733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536398170927801449181155 804597256391702173771733)
                ·
                  refine ⟨18857748196680519697775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 804597256391702173771733 18857748196680519697775)
                  ·
                    rfl

theorem cell20_41316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_41316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41316 prefixEnd_41316 := by exact prefixLift 41316
  have htrace : WordTrace (prefixWord ++ tailWord_41316) baseStart_41316 baseEnd_41316 := by
    simpa [prefixWord, tailWord_41316, baseEnd_41316] using wordTrace_append hprefix tailTrace_41316
  have hstable : (prefixWord ++ tailWord_41316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41316).length < 2 ^ (prefixWord ++ tailWord_41316).sum := by decide
  have hdescent : baseEnd_41316 < baseStart_41316 := by decide
  rcases family_descends (prefixWord ++ tailWord_41316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41333 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_41333 : Nat := 118140960795 + 41333 * 2 ^ 59
def prefixEnd_41333 : Nat := 4983230072969 + 3 ^ 40 * 41333 * 2
def baseEnd_41333 : Nat := 18865507459904016131039

theorem tailTrace_41333 : CollatzResearch.WordTrace tailWord_41333 prefixEnd_41333 18865507459904016131039 := by
  unfold tailWord_41333
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507538359265074959504653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1005025572843383306336435 1507538359265074959504653)
  ·
    refine ⟨565326884724403109814245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1507538359265074959504653 565326884724403109814245)
    ·
      refine ⟨105998790885825583090171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 565326884724403109814245 105998790885825583090171)
      ·
        refine ⟨158998186328738374635257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105998790885825583090171 158998186328738374635257)
        ·
          refine ⟨119248639746553780976443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158998186328738374635257 119248639746553780976443)
          ·
            refine ⟨178872959619830671464665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119248639746553780976443 178872959619830671464665)
            ·
              refine ⟨134154719714873003598499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178872959619830671464665 134154719714873003598499)
              ·
                refine ⟨201232079572309505397749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134154719714873003598499 201232079572309505397749)
                ·
                  refine ⟨18865507459904016131039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201232079572309505397749 18865507459904016131039)
                  ·
                    rfl

theorem cell20_41333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_41333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41333 prefixEnd_41333 := by exact prefixLift 41333
  have htrace : WordTrace (prefixWord ++ tailWord_41333) baseStart_41333 baseEnd_41333 := by
    simpa [prefixWord, tailWord_41333, baseEnd_41333] using wordTrace_append hprefix tailTrace_41333
  have hstable : (prefixWord ++ tailWord_41333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41333).length < 2 ^ (prefixWord ++ tailWord_41333).sum := by decide
  have hdescent : baseEnd_41333 < baseStart_41333 := by decide
  rcases family_descends (prefixWord ++ tailWord_41333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41416 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_41416 : Nat := 118140960795 + 41416 * 2 ^ 59
def prefixEnd_41416 : Nat := 4983230072969 + 3 ^ 40 * 41416 * 2
def baseEnd_41416 : Nat := 18903390921524616364033

theorem tailTrace_41416 : CollatzResearch.WordTrace tailWord_41416 prefixEnd_41416 18903390921524616364033 := by
  unfold tailWord_41416
  simp only [CollatzResearch.WordTrace]
  refine ⟨755282808982190067388051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1007043745309586756517401 755282808982190067388051)
  ·
    refine ⟨1132924213473285101082077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 755282808982190067388051 1132924213473285101082077)
    ·
      refine ⟨424846580052481912905779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1132924213473285101082077 424846580052481912905779)
      ·
        refine ⟨637269870078722869358669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424846580052481912905779 637269870078722869358669)
        ·
          refine ⟨238976201279521076009501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 637269870078722869358669 238976201279521076009501)
          ·
            refine ⟨89616075479820403503563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238976201279521076009501 89616075479820403503563)
            ·
              refine ⟨134424113219730605255345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89616075479820403503563 134424113219730605255345)
              ·
                refine ⟨100818084914797953941509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134424113219730605255345 100818084914797953941509)
                ·
                  refine ⟨18903390921524616364033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100818084914797953941509 18903390921524616364033)
                  ·
                    rfl

theorem cell20_41416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_41416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41416 prefixEnd_41416 := by exact prefixLift 41416
  have htrace : WordTrace (prefixWord ++ tailWord_41416) baseStart_41416 baseEnd_41416 := by
    simpa [prefixWord, tailWord_41416, baseEnd_41416] using wordTrace_append hprefix tailTrace_41416
  have hstable : (prefixWord ++ tailWord_41416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41416).length < 2 ^ (prefixWord ++ tailWord_41416).sum := by decide
  have hdescent : baseEnd_41416 < baseStart_41416 := by decide
  rcases family_descends (prefixWord ++ tailWord_41416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41433 : List Nat := [1, 2, 1, 2, 4, 1, 4, 3, 2]
def baseStart_41433 : Nat := 118140960795 + 41433 * 2 ^ 59
def prefixEnd_41433 : Nat := 4983230072969 + 3 ^ 40 * 41433 * 2
def baseEnd_41433 : Nat := 18911150184748112797297

theorem tailTrace_41433 : CollatzResearch.WordTrace tailWord_41433 prefixEnd_41433 18911150184748112797297 := by
  unfold tailWord_41433
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511185658902792038144953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1007457105935194692096635 1511185658902792038144953)
  ·
    refine ⟨1133389244177094028608715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1511185658902792038144953 1133389244177094028608715)
    ·
      refine ⟨1700083866265641042913073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133389244177094028608715 1700083866265641042913073)
      ·
        refine ⟨1275062899699230782184805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1700083866265641042913073 1275062899699230782184805)
        ·
          refine ⟨239074293693605771659651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1275062899699230782184805 239074293693605771659651)
          ·
            refine ⟨358611440540408657489477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239074293693605771659651 358611440540408657489477)
            ·
              refine ⟨67239645101326623279277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 358611440540408657489477 67239645101326623279277)
              ·
                refine ⟨25214866912997483729729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67239645101326623279277 25214866912997483729729)
                ·
                  refine ⟨18911150184748112797297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25214866912997483729729 18911150184748112797297)
                  ·
                    rfl

theorem cell20_41433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_41433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41433 prefixEnd_41433 := by exact prefixLift 41433
  have htrace : WordTrace (prefixWord ++ tailWord_41433) baseStart_41433 baseEnd_41433 := by
    simpa [prefixWord, tailWord_41433, baseEnd_41433] using wordTrace_append hprefix tailTrace_41433
  have hstable : (prefixWord ++ tailWord_41433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41433).length < 2 ^ (prefixWord ++ tailWord_41433).sum := by decide
  have hdescent : baseEnd_41433 < baseStart_41433 := by decide
  rcases family_descends (prefixWord ++ tailWord_41433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41443 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 3]
def baseStart_41443 : Nat := 118140960795 + 41443 * 2 ^ 59
def prefixEnd_41443 : Nat := 4983230072969 + 3 ^ 40 * 41443 * 2
def baseEnd_41443 : Nat := 18915714457232522463923

theorem tailTrace_41443 : CollatzResearch.WordTrace tailWord_41443 prefixEnd_41443 18915714457232522463923 := by
  unfold tailWord_41443
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511550388866563746008983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1007700259244375830672655 1511550388866563746008983)
  ·
    refine ⟨2267325583299845619013475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511550388866563746008983 2267325583299845619013475)
    ·
      refine ⟨3400988374949768428520213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267325583299845619013475 3400988374949768428520213)
      ·
        refine ⟨159421330075770395086885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3400988374949768428520213 159421330075770395086885)
        ·
          refine ⟨29891499389206949078791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159421330075770395086885 29891499389206949078791)
          ·
            refine ⟨44837249083810423618187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29891499389206949078791 44837249083810423618187)
            ·
              refine ⟨67255873625715635427281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44837249083810423618187 67255873625715635427281)
              ·
                refine ⟨50441905219286726570461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67255873625715635427281 50441905219286726570461)
                ·
                  refine ⟨18915714457232522463923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50441905219286726570461 18915714457232522463923)
                  ·
                    rfl

theorem cell20_41443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 3].length) (baseStart_41443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41443 prefixEnd_41443 := by exact prefixLift 41443
  have htrace : WordTrace (prefixWord ++ tailWord_41443) baseStart_41443 baseEnd_41443 := by
    simpa [prefixWord, tailWord_41443, baseEnd_41443] using wordTrace_append hprefix tailTrace_41443
  have hstable : (prefixWord ++ tailWord_41443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41443).length < 2 ^ (prefixWord ++ tailWord_41443).sum := by decide
  have hdescent : baseEnd_41443 < baseStart_41443 := by decide
  rcases family_descends (prefixWord ++ tailWord_41443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41454 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_41454 : Nat := 118140960795 + 41454 * 2 ^ 59
def prefixEnd_41454 : Nat := 4983230072969 + 3 ^ 40 * 41454 * 2
def baseEnd_41454 : Nat := 18920735156965373097211

theorem tailTrace_41454 : CollatzResearch.WordTrace tailWord_41454 prefixEnd_41454 18920735156965373097211 := by
  unfold tailWord_41454
  simp only [CollatzResearch.WordTrace]
  refine ⟨188993948978339078082427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1007967727884475083106277 188993948978339078082427)
  ·
    refine ⟨283490923467508617123641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188993948978339078082427 283490923467508617123641)
    ·
      refine ⟨212618192600631462842731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283490923467508617123641 212618192600631462842731)
      ·
        refine ⟨318927288900947194264097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212618192600631462842731 318927288900947194264097)
        ·
          refine ⟨239195466675710395698073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318927288900947194264097 239195466675710395698073)
          ·
            refine ⟨179396600006782796773555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239195466675710395698073 179396600006782796773555)
            ·
              refine ⟨269094900010174195160333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179396600006782796773555 269094900010174195160333)
              ·
                refine ⟨100910587503815323185125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269094900010174195160333 100910587503815323185125)
                ·
                  refine ⟨18920735156965373097211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100910587503815323185125 18920735156965373097211)
                  ·
                    rfl

theorem cell20_41454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_41454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41454 prefixEnd_41454 := by exact prefixLift 41454
  have htrace : WordTrace (prefixWord ++ tailWord_41454) baseStart_41454 baseEnd_41454 := by
    simpa [prefixWord, tailWord_41454, baseEnd_41454] using wordTrace_append hprefix tailTrace_41454
  have hstable : (prefixWord ++ tailWord_41454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41454).length < 2 ^ (prefixWord ++ tailWord_41454).sum := by decide
  have hdescent : baseEnd_41454 < baseStart_41454 := by decide
  rcases family_descends (prefixWord ++ tailWord_41454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41474 : List Nat := [3, 4, 1, 2, 2, 2, 2, 4]
def baseStart_41474 : Nat := 118140960795 + 41474 * 2 ^ 59
def prefixEnd_41474 : Nat := 4983230072969 + 3 ^ 40 * 41474 * 2
def baseEnd_41474 : Nat := 6309954567311397476821

theorem tailTrace_41474 : CollatzResearch.WordTrace tailWord_41474 prefixEnd_41474 6309954567311397476821 := by
  unfold tailWord_41474
  simp only [CollatzResearch.WordTrace]
  refine ⟨378170262938564010096869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1008454034502837360258317 378170262938564010096869)
  ·
    refine ⟨70906924300980751893163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 378170262938564010096869 70906924300980751893163)
    ·
      refine ⟨106360386451471127839745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70906924300980751893163 106360386451471127839745)
      ·
        refine ⟨79770289838603345879809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106360386451471127839745 79770289838603345879809)
        ·
          refine ⟨59827717378952509409857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79770289838603345879809 59827717378952509409857)
          ·
            refine ⟨44870788034214382057393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59827717378952509409857 44870788034214382057393)
            ·
              refine ⟨33653091025660786543045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44870788034214382057393 33653091025660786543045)
              ·
                refine ⟨6309954567311397476821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33653091025660786543045 6309954567311397476821)
                ·
                  rfl

theorem cell20_41474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_41474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41474 prefixEnd_41474 := by exact prefixLift 41474
  have htrace : WordTrace (prefixWord ++ tailWord_41474) baseStart_41474 baseEnd_41474 := by
    simpa [prefixWord, tailWord_41474, baseEnd_41474] using wordTrace_append hprefix tailTrace_41474
  have hstable : (prefixWord ++ tailWord_41474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41474).length < 2 ^ (prefixWord ++ tailWord_41474).sum := by decide
  have hdescent : baseEnd_41474 < baseStart_41474 := by decide
  rcases family_descends (prefixWord ++ tailWord_41474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41475 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_41475 : Nat := 118140960795 + 41475 * 2 ^ 59
def prefixEnd_41475 : Nat := 4983230072969 + 3 ^ 40 * 41475 * 2
def baseEnd_41475 : Nat := 18930320129182633397125

theorem tailTrace_41475 : CollatzResearch.WordTrace tailWord_41475 prefixEnd_41475 18930320129182633397125 := by
  unfold tailWord_41475
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512717524750633211173879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1008478349833755474115919 1512717524750633211173879)
  ·
    refine ⟨2269076287125949816760819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512717524750633211173879 2269076287125949816760819)
    ·
      refine ⟨3403614430688924725141229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269076287125949816760819 3403614430688924725141229)
      ·
        refine ⟨1276355411508346771927961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3403614430688924725141229 1276355411508346771927961)
        ·
          refine ⟨957266558631260078945971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276355411508346771927961 957266558631260078945971)
          ·
            refine ⟨1435899837946890118418957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957266558631260078945971 1435899837946890118418957)
            ·
              refine ⟨538462439230083794407109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1435899837946890118418957 538462439230083794407109)
              ·
                refine ⟨100961707355640711451333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538462439230083794407109 100961707355640711451333)
                ·
                  refine ⟨18930320129182633397125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100961707355640711451333 18930320129182633397125)
                  ·
                    rfl

theorem cell20_41475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_41475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41475 prefixEnd_41475 := by exact prefixLift 41475
  have htrace : WordTrace (prefixWord ++ tailWord_41475) baseStart_41475 baseEnd_41475 := by
    simpa [prefixWord, tailWord_41475, baseEnd_41475] using wordTrace_append hprefix tailTrace_41475
  have hstable : (prefixWord ++ tailWord_41475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41475).length < 2 ^ (prefixWord ++ tailWord_41475).sum := by decide
  have hdescent : baseEnd_41475 < baseStart_41475 := by decide
  rcases family_descends (prefixWord ++ tailWord_41475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41495 : List Nat := [1, 1, 3, 6, 2, 1, 6]
def baseStart_41495 : Nat := 118140960795 + 41495 * 2 ^ 59
def prefixEnd_41495 : Nat := 4983230072969 + 3 ^ 40 * 41495 * 2
def baseEnd_41495 : Nat := 2104383186016828081153

theorem tailTrace_41495 : CollatzResearch.WordTrace tailWord_41495 prefixEnd_41495 2104383186016828081153 := by
  unfold tailWord_41495
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513446984678176626901939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1008964656452117751267959 1513446984678176626901939)
  ·
    refine ⟨2270170477017264940352909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1513446984678176626901939 2270170477017264940352909)
    ·
      refine ⟨851313928881474352632341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2270170477017264940352909 851313928881474352632341)
      ·
        refine ⟨39905340416319110279641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 851313928881474352632341 39905340416319110279641)
        ·
          refine ⟨29929005312239332709731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39905340416319110279641 29929005312239332709731)
          ·
            refine ⟨44893507968358999064597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29929005312239332709731 44893507968358999064597)
            ·
              refine ⟨2104383186016828081153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44893507968358999064597 2104383186016828081153)
              ·
                rfl

theorem cell20_41495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 6].length) (baseStart_41495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41495 prefixEnd_41495 := by exact prefixLift 41495
  have htrace : WordTrace (prefixWord ++ tailWord_41495) baseStart_41495 baseEnd_41495 := by
    simpa [prefixWord, tailWord_41495, baseEnd_41495] using wordTrace_append hprefix tailTrace_41495
  have hstable : (prefixWord ++ tailWord_41495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41495).length < 2 ^ (prefixWord ++ tailWord_41495).sum := by decide
  have hdescent : baseEnd_41495 < baseStart_41495 := by decide
  rcases family_descends (prefixWord ++ tailWord_41495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41520 : List Nat := [2, 1, 1, 1, 2, 3, 3, 7]
def baseStart_41520 : Nat := 118140960795 + 41520 * 2 ^ 59
def prefixEnd_41520 : Nat := 4983230072969 + 3 ^ 40 * 41520 * 2
def baseEnd_41520 : Nat := 6316953118454158965647

theorem tailTrace_41520 : CollatzResearch.WordTrace tailWord_41520 prefixEnd_41520 6316953118454158965647 := by
  unfold tailWord_41520
  simp only [CollatzResearch.WordTrace]
  refine ⟨757179404793802948281007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1009572539725070597708009 757179404793802948281007)
  ·
    refine ⟨1135769107190704422421511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 757179404793802948281007 1135769107190704422421511)
    ·
      refine ⟨1703653660786056633632267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135769107190704422421511 1703653660786056633632267)
      ·
        refine ⟨2555480491179084950448401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703653660786056633632267 2555480491179084950448401)
        ·
          refine ⟨1916610368384313712836301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2555480491179084950448401 1916610368384313712836301)
          ·
            refine ⟨718728888144117642313613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1916610368384313712836301 718728888144117642313613)
            ·
              refine ⟨269523333054044115867605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 718728888144117642313613 269523333054044115867605)
              ·
                refine ⟨6316953118454158965647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 269523333054044115867605 6316953118454158965647)
                ·
                  rfl

theorem cell20_41520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_41520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41520 prefixEnd_41520 := by exact prefixLift 41520
  have htrace : WordTrace (prefixWord ++ tailWord_41520) baseStart_41520 baseEnd_41520 := by
    simpa [prefixWord, tailWord_41520, baseEnd_41520] using wordTrace_append hprefix tailTrace_41520
  have hstable : (prefixWord ++ tailWord_41520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41520).length < 2 ^ (prefixWord ++ tailWord_41520).sum := by decide
  have hdescent : baseEnd_41520 < baseStart_41520 := by decide
  rcases family_descends (prefixWord ++ tailWord_41520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41537 : List Nat := [1, 2, 5, 1, 1, 2, 2, 6]
def baseStart_41537 : Nat := 118140960795 + 41537 * 2 ^ 59
def prefixEnd_41537 : Nat := 4983230072969 + 3 ^ 40 * 41537 * 2
def baseEnd_41537 : Nat := 6319539539528657776735

theorem tailTrace_41537 : CollatzResearch.WordTrace tailWord_41537 prefixEnd_41537 6319539539528657776735 := by
  unfold tailWord_41537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514978850526017799930865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1009985900350678533287243 1514978850526017799930865)
  ·
    refine ⟨1136234137894513349948149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1514978850526017799930865 1136234137894513349948149)
    ·
      refine ⟨106521950427610626557639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1136234137894513349948149 106521950427610626557639)
      ·
        refine ⟨159782925641415939836459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106521950427610626557639 159782925641415939836459)
        ·
          refine ⟨239674388462123909754689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159782925641415939836459 239674388462123909754689)
          ·
            refine ⟨179755791346592932316017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239674388462123909754689 179755791346592932316017)
            ·
              refine ⟨134816843509944699237013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179755791346592932316017 134816843509944699237013)
              ·
                refine ⟨6319539539528657776735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134816843509944699237013 6319539539528657776735)
                ·
                  rfl

theorem cell20_41537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_41537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41537 prefixEnd_41537 := by exact prefixLift 41537
  have htrace : WordTrace (prefixWord ++ tailWord_41537) baseStart_41537 baseEnd_41537 := by
    simpa [prefixWord, tailWord_41537, baseEnd_41537] using wordTrace_append hprefix tailTrace_41537
  have hstable : (prefixWord ++ tailWord_41537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41537).length < 2 ^ (prefixWord ++ tailWord_41537).sum := by decide
  have hdescent : baseEnd_41537 < baseStart_41537 := by decide
  rcases family_descends (prefixWord ++ tailWord_41537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41564 : List Nat := [2, 2, 4, 1, 3, 1, 1, 4, 2]
def baseStart_41564 : Nat := 118140960795 + 41564 * 2 ^ 59
def prefixEnd_41564 : Nat := 4983230072969 + 3 ^ 40 * 41564 * 2
def baseEnd_41564 : Nat := 18970942154293879430095

theorem tailTrace_41564 : CollatzResearch.WordTrace tailWord_41564 prefixEnd_41564 18970942154293879430095 := by
  unfold tailWord_41564
  simp only [CollatzResearch.WordTrace]
  refine ⟨757981810714100705581873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1010642414285467607442497 757981810714100705581873)
  ·
    refine ⟨568486358035575529186405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 757981810714100705581873 568486358035575529186405)
    ·
      refine ⟨106591192131670411722451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 568486358035575529186405 106591192131670411722451)
      ·
        refine ⟨159886788197505617583677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106591192131670411722451 159886788197505617583677)
        ·
          refine ⟨59957545574064606593879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159886788197505617583677 59957545574064606593879)
          ·
            refine ⟨89936318361096909890819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59957545574064606593879 89936318361096909890819)
            ·
              refine ⟨134904477541645364836229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89936318361096909890819 134904477541645364836229)
              ·
                refine ⟨25294589539058505906793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134904477541645364836229 25294589539058505906793)
                ·
                  refine ⟨18970942154293879430095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25294589539058505906793 18970942154293879430095)
                  ·
                    rfl

theorem cell20_41564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_41564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41564 prefixEnd_41564 := by exact prefixLift 41564
  have htrace : WordTrace (prefixWord ++ tailWord_41564) baseStart_41564 baseEnd_41564 := by
    simpa [prefixWord, tailWord_41564, baseEnd_41564] using wordTrace_append hprefix tailTrace_41564
  have hstable : (prefixWord ++ tailWord_41564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41564).length < 2 ^ (prefixWord ++ tailWord_41564).sum := by decide
  have hdescent : baseEnd_41564 < baseStart_41564 := by decide
  rcases family_descends (prefixWord ++ tailWord_41564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41596 : List Nat := [2, 2, 2, 1, 1, 2, 2, 8]
def baseStart_41596 : Nat := 118140960795 + 41596 * 2 ^ 59
def prefixEnd_41596 : Nat := 4983230072969 + 3 ^ 40 * 41596 * 2
def baseEnd_41596 : Nat := 6328515942081330121099

theorem tailTrace_41596 : CollatzResearch.WordTrace tailWord_41596 prefixEnd_41596 6328515942081330121099 := by
  unfold tailWord_41596
  simp only [CollatzResearch.WordTrace]
  refine ⟨758565378656135438164321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1011420504874847250885761 758565378656135438164321)
  ·
    refine ⟨568924033992101578623241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 758565378656135438164321 568924033992101578623241)
    ·
      refine ⟨426693025494076183967431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 568924033992101578623241 426693025494076183967431)
      ·
        refine ⟨640039538241114275951147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426693025494076183967431 640039538241114275951147)
        ·
          refine ⟨960059307361671413926721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640039538241114275951147 960059307361671413926721)
          ·
            refine ⟨720044480521253560445041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960059307361671413926721 720044480521253560445041)
            ·
              refine ⟨540033360390940170333781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720044480521253560445041 540033360390940170333781)
              ·
                refine ⟨6328515942081330121099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 540033360390940170333781 6328515942081330121099)
                ·
                  rfl

theorem cell20_41596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_41596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41596 prefixEnd_41596 := by exact prefixLift 41596
  have htrace : WordTrace (prefixWord ++ tailWord_41596) baseStart_41596 baseEnd_41596 := by
    simpa [prefixWord, tailWord_41596, baseEnd_41596] using wordTrace_append hprefix tailTrace_41596
  have hstable : (prefixWord ++ tailWord_41596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41596).length < 2 ^ (prefixWord ++ tailWord_41596).sum := by decide
  have hdescent : baseEnd_41596 < baseStart_41596 := by decide
  rcases family_descends (prefixWord ++ tailWord_41596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41641 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_41641 : Nat := 118140960795 + 41641 * 2 ^ 59
def prefixEnd_41641 : Nat := 4983230072969 + 3 ^ 40 * 41641 * 2
def baseEnd_41641 : Nat := 19006087052423833863113

theorem tailTrace_41641 : CollatzResearch.WordTrace tailWord_41641 prefixEnd_41641 19006087052423833863113 := by
  unfold tailWord_41641
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518772042149243561716777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1012514694766162374477851 1518772042149243561716777)
  ·
    refine ⟨1139079031611932671287583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1518772042149243561716777 1139079031611932671287583)
    ·
      refine ⟨1708618547417899006931375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1139079031611932671287583 1708618547417899006931375)
      ·
        refine ⟨2562927821126848510397063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708618547417899006931375 2562927821126848510397063)
        ·
          refine ⟨3844391731690272765595595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562927821126848510397063 3844391731690272765595595)
          ·
            refine ⟨5766587597535409148393393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3844391731690272765595595 5766587597535409148393393)
            ·
              refine ⟨4324940698151556861295045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5766587597535409148393393 4324940698151556861295045)
              ·
                refine ⟨810926380903416911492821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4324940698151556861295045 810926380903416911492821)
                ·
                  refine ⟨19006087052423833863113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 810926380903416911492821 19006087052423833863113)
                  ·
                    rfl

theorem cell20_41641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_41641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41641 prefixEnd_41641 := by exact prefixLift 41641
  have htrace : WordTrace (prefixWord ++ tailWord_41641) baseStart_41641 baseEnd_41641 := by
    simpa [prefixWord, tailWord_41641, baseEnd_41641] using wordTrace_append hprefix tailTrace_41641
  have hstable : (prefixWord ++ tailWord_41641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41641).length < 2 ^ (prefixWord ++ tailWord_41641).sum := by decide
  have hdescent : baseEnd_41641 < baseStart_41641 := by decide
  rcases family_descends (prefixWord ++ tailWord_41641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41651 : List Nat := [1, 1, 1, 2, 3, 4, 4, 4]
def baseStart_41651 : Nat := 118140960795 + 41651 * 2 ^ 59
def prefixEnd_41651 : Nat := 4983230072969 + 3 ^ 40 * 41651 * 2
def baseEnd_41651 : Nat := 6336883774969414509913

theorem tailTrace_41651 : CollatzResearch.WordTrace tailWord_41651 prefixEnd_41651 6336883774969414509913 := by
  unfold tailWord_41651
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519136772113015269580807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1012757848075343513053871 1519136772113015269580807)
  ·
    refine ⟨2278705158169522904371211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1519136772113015269580807 2278705158169522904371211)
    ·
      refine ⟨3418057737254284356556817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278705158169522904371211 3418057737254284356556817)
      ·
        refine ⟨2563543302940713267417613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3418057737254284356556817 2563543302940713267417613)
        ·
          refine ⟨961328738602767475281605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2563543302940713267417613 961328738602767475281605)
          ·
            refine ⟨180249138488018901615301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 961328738602767475281605 180249138488018901615301)
            ·
              refine ⟨33796713466503544052869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180249138488018901615301 33796713466503544052869)
              ·
                refine ⟨6336883774969414509913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33796713466503544052869 6336883774969414509913)
                ·
                  rfl

theorem cell20_41651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_41651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41651 prefixEnd_41651 := by exact prefixLift 41651
  have htrace : WordTrace (prefixWord ++ tailWord_41651) baseStart_41651 baseEnd_41651 := by
    simpa [prefixWord, tailWord_41651, baseEnd_41651] using wordTrace_append hprefix tailTrace_41651
  have hstable : (prefixWord ++ tailWord_41651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41651).length < 2 ^ (prefixWord ++ tailWord_41651).sum := by decide
  have hdescent : baseEnd_41651 < baseStart_41651 := by decide
  rcases family_descends (prefixWord ++ tailWord_41651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41661 : List Nat := [1, 4, 1, 2, 1, 3, 3, 3, 2]
def baseStart_41661 : Nat := 118140960795 + 41661 * 2 ^ 59
def prefixEnd_41661 : Nat := 4983230072969 + 3 ^ 40 * 41661 * 2
def baseEnd_41661 : Nat := 19015215597392653196365

theorem tailTrace_41661 : CollatzResearch.WordTrace tailWord_41661 prefixEnd_41661 19015215597392653196365 := by
  unfold tailWord_41661
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519501502076786977444837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1013001001384524651629891 1519501502076786977444837)
  ·
    refine ⟨284906531639397558270907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1519501502076786977444837 284906531639397558270907)
    ·
      refine ⟨427359797459096337406361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284906531639397558270907 427359797459096337406361)
      ·
        refine ⟨320519848094322253054771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427359797459096337406361 320519848094322253054771)
        ·
          refine ⟨480779772141483379582157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320519848094322253054771 480779772141483379582157)
          ·
            refine ⟨180292414553056267343309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 480779772141483379582157 180292414553056267343309)
            ·
              refine ⟨67609655457396100253741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180292414553056267343309 67609655457396100253741)
              ·
                refine ⟨25353620796523537595153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67609655457396100253741 25353620796523537595153)
                ·
                  refine ⟨19015215597392653196365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25353620796523537595153 19015215597392653196365)
                  ·
                    rfl

theorem cell20_41661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_41661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41661 prefixEnd_41661 := by exact prefixLift 41661
  have htrace : WordTrace (prefixWord ++ tailWord_41661) baseStart_41661 baseEnd_41661 := by
    simpa [prefixWord, tailWord_41661, baseEnd_41661] using wordTrace_append hprefix tailTrace_41661
  have hstable : (prefixWord ++ tailWord_41661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41661).length < 2 ^ (prefixWord ++ tailWord_41661).sum := by decide
  have hdescent : baseEnd_41661 < baseStart_41661 := by decide
  rcases family_descends (prefixWord ++ tailWord_41661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41672 : List Nat := [2, 1, 3, 1, 2, 3, 8]
def baseStart_41672 : Nat := 118140960795 + 41672 * 2 ^ 59
def prefixEnd_41672 : Nat := 4983230072969 + 3 ^ 40 * 41672 * 2
def baseEnd_41672 : Nat := 2113359588569500425517

theorem tailTrace_41672 : CollatzResearch.WordTrace tailWord_41672 prefixEnd_41672 2113359588569500425517 := by
  unfold tailWord_41672
  simp only [CollatzResearch.WordTrace]
  refine ⟨759951352518467928047635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1013268470024623904063513 759951352518467928047635)
  ·
    refine ⟨1139927028777701892071453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 759951352518467928047635 1139927028777701892071453)
    ·
      refine ⟨427472635791638209526795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1139927028777701892071453 427472635791638209526795)
      ·
        refine ⟨641208953687457314290193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427472635791638209526795 641208953687457314290193)
        ·
          refine ⟨480906715265592985717645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641208953687457314290193 480906715265592985717645)
          ·
            refine ⟨180340018224597369644117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 480906715265592985717645 180340018224597369644117)
            ·
              refine ⟨2113359588569500425517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 180340018224597369644117 2113359588569500425517)
              ·
                rfl

theorem cell20_41672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 8].length) (baseStart_41672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41672 prefixEnd_41672 := by exact prefixLift 41672
  have htrace : WordTrace (prefixWord ++ tailWord_41672) baseStart_41672 baseEnd_41672 := by
    simpa [prefixWord, tailWord_41672, baseEnd_41672] using wordTrace_append hprefix tailTrace_41672
  have hstable : (prefixWord ++ tailWord_41672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41672).length < 2 ^ (prefixWord ++ tailWord_41672).sum := by decide
  have hdescent : baseEnd_41672 < baseStart_41672 := by decide
  rcases family_descends (prefixWord ++ tailWord_41672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41678 : List Nat := [4, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_41678 : Nat := 118140960795 + 41678 * 2 ^ 59
def prefixEnd_41678 : Nat := 4983230072969 + 3 ^ 40 * 41678 * 2
def baseEnd_41678 : Nat := 19022974860616149629629

theorem tailTrace_41678 : CollatzResearch.WordTrace tailWord_41678 prefixEnd_41678 19022974860616149629629 := by
  unfold tailWord_41678
  simp only [CollatzResearch.WordTrace]
  refine ⟨190015192876899860101711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1013414362010132587209125 190015192876899860101711)
  ·
    refine ⟨285022789315349790152567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190015192876899860101711 285022789315349790152567)
    ·
      refine ⟨427534183973024685228851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285022789315349790152567 427534183973024685228851)
      ·
        refine ⟨641301275959537027843277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427534183973024685228851 641301275959537027843277)
        ·
          refine ⟨240487978484826385441229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 641301275959537027843277 240487978484826385441229)
          ·
            refine ⟨90182991931809894540461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240487978484826385441229 90182991931809894540461)
            ·
              refine ⟨33818621974428710452673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90182991931809894540461 33818621974428710452673)
              ·
                refine ⟨25363966480821532839505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33818621974428710452673 25363966480821532839505)
                ·
                  refine ⟨19022974860616149629629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25363966480821532839505 19022974860616149629629)
                  ·
                    rfl

theorem cell20_41678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_41678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41678 prefixEnd_41678 := by exact prefixLift 41678
  have htrace : WordTrace (prefixWord ++ tailWord_41678) baseStart_41678 baseEnd_41678 := by
    simpa [prefixWord, tailWord_41678, baseEnd_41678] using wordTrace_append hprefix tailTrace_41678
  have hstable : (prefixWord ++ tailWord_41678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41678).length < 2 ^ (prefixWord ++ tailWord_41678).sum := by decide
  have hdescent : baseEnd_41678 < baseStart_41678 := by decide
  rcases family_descends (prefixWord ++ tailWord_41678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41692 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_41692 : Nat := 118140960795 + 41692 * 2 ^ 59
def prefixEnd_41692 : Nat := 4983230072969 + 3 ^ 40 * 41692 * 2
def baseEnd_41692 : Nat := 19029364842094323162905

theorem tailTrace_41692 : CollatzResearch.WordTrace tailWord_41692 prefixEnd_41692 19029364842094323162905 := by
  unfold tailWord_41692
  simp only [CollatzResearch.WordTrace]
  refine ⟨760316082482239635911665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1013754776642986181215553 760316082482239635911665)
  ·
    refine ⟨570237061861679726933749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 760316082482239635911665 570237061861679726933749)
    ·
      refine ⟨53459724549532474400039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 570237061861679726933749 53459724549532474400039)
      ·
        refine ⟨80189586824298711600059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53459724549532474400039 80189586824298711600059)
        ·
          refine ⟨120284380236448067400089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80189586824298711600059 120284380236448067400089)
          ·
            refine ⟨90213285177336050550067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120284380236448067400089 90213285177336050550067)
            ·
              refine ⟨135319927766004075825101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90213285177336050550067 135319927766004075825101)
              ·
                refine ⟨50744972912251528434413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135319927766004075825101 50744972912251528434413)
                ·
                  refine ⟨19029364842094323162905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50744972912251528434413 19029364842094323162905)
                  ·
                    rfl

theorem cell20_41692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_41692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41692 prefixEnd_41692 := by exact prefixLift 41692
  have htrace : WordTrace (prefixWord ++ tailWord_41692) baseStart_41692 baseEnd_41692 := by
    simpa [prefixWord, tailWord_41692, baseEnd_41692] using wordTrace_append hprefix tailTrace_41692
  have hstable : (prefixWord ++ tailWord_41692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41692).length < 2 ^ (prefixWord ++ tailWord_41692).sum := by decide
  have hdescent : baseEnd_41692 < baseStart_41692 := by decide
  rcases family_descends (prefixWord ++ tailWord_41692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41720 : List Nat := [2, 1, 2, 1, 1, 2, 4, 5, 2]
def baseStart_41720 : Nat := 118140960795 + 41720 * 2 ^ 59
def prefixEnd_41720 : Nat := 4983230072969 + 3 ^ 40 * 41720 * 2
def baseEnd_41720 : Nat := 19042144805050670229457

theorem tailTrace_41720 : CollatzResearch.WordTrace tailWord_41720 prefixEnd_41720 19042144805050670229457 := by
  unfold tailWord_41720
  simp only [CollatzResearch.WordTrace]
  refine ⟨760826704431520026921307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1014435605908693369228409 760826704431520026921307)
  ·
    refine ⟨1141240056647280040381961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 760826704431520026921307 1141240056647280040381961)
    ·
      refine ⟨855930042485460030286471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1141240056647280040381961 855930042485460030286471)
      ·
        refine ⟨1283895063728190045429707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855930042485460030286471 1283895063728190045429707)
        ·
          refine ⟨1925842595592285068144561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283895063728190045429707 1925842595592285068144561)
          ·
            refine ⟨1444381946694213801108421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1925842595592285068144561 1444381946694213801108421)
            ·
              refine ⟨270821615005165087707829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1444381946694213801108421 270821615005165087707829)
              ·
                refine ⟨25389526406734226972609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270821615005165087707829 25389526406734226972609)
                ·
                  refine ⟨19042144805050670229457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25389526406734226972609 19042144805050670229457)
                  ·
                    rfl

theorem cell20_41720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_41720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41720 prefixEnd_41720 := by exact prefixLift 41720
  have htrace : WordTrace (prefixWord ++ tailWord_41720) baseStart_41720 baseEnd_41720 := by
    simpa [prefixWord, tailWord_41720, baseEnd_41720] using wordTrace_append hprefix tailTrace_41720
  have hstable : (prefixWord ++ tailWord_41720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41720).length < 2 ^ (prefixWord ++ tailWord_41720).sum := by decide
  have hdescent : baseEnd_41720 < baseStart_41720 := by decide
  rcases family_descends (prefixWord ++ tailWord_41720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41730 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_41730 : Nat := 118140960795 + 41730 * 2 ^ 59
def prefixEnd_41730 : Nat := 4983230072969 + 3 ^ 40 * 41730 * 2
def baseEnd_41730 : Nat := 19046709077535079896083

theorem tailTrace_41730 : CollatzResearch.WordTrace tailWord_41730 prefixEnd_41730 19046709077535079896083 := by
  unfold tailWord_41730
  simp only [CollatzResearch.WordTrace]
  refine ⟨380504534706702940426661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1014678759217874507804429 380504534706702940426661)
  ·
    refine ⟨71344600257506801329999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 380504534706702940426661 71344600257506801329999)
    ·
      refine ⟨107016900386260201994999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71344600257506801329999 107016900386260201994999)
      ·
        refine ⟨160525350579390302992499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107016900386260201994999 160525350579390302992499)
        ·
          refine ⟨240788025869085454488749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160525350579390302992499 240788025869085454488749)
          ·
            refine ⟨90295509700907045433281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240788025869085454488749 90295509700907045433281)
            ·
              refine ⟨67721632275680284074961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90295509700907045433281 67721632275680284074961)
              ·
                refine ⟨50791224206760213056221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67721632275680284074961 50791224206760213056221)
                ·
                  refine ⟨19046709077535079896083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50791224206760213056221 19046709077535079896083)
                  ·
                    rfl

theorem cell20_41730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_41730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41730 prefixEnd_41730 := by exact prefixLift 41730
  have htrace : WordTrace (prefixWord ++ tailWord_41730) baseStart_41730 baseEnd_41730 := by
    simpa [prefixWord, tailWord_41730, baseEnd_41730] using wordTrace_append hprefix tailTrace_41730
  have hstable : (prefixWord ++ tailWord_41730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41730).length < 2 ^ (prefixWord ++ tailWord_41730).sum := by decide
  have hdescent : baseEnd_41730 < baseStart_41730 := by decide
  rcases family_descends (prefixWord ++ tailWord_41730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41737 : List Nat := [1, 2, 1, 1, 3, 2, 6, 2, 2]
def baseStart_41737 : Nat := 118140960795 + 41737 * 2 ^ 59
def prefixEnd_41737 : Nat := 4983230072969 + 3 ^ 40 * 41737 * 2
def baseEnd_41737 : Nat := 19049904068274166662721

theorem tailTrace_41737 : CollatzResearch.WordTrace tailWord_41737 prefixEnd_41737 19049904068274166662721 := by
  unfold tailWord_41737
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522273449801451957211465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1014848966534301304807643 1522273449801451957211465)
  ·
    refine ⟨1141705087351088967908599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1522273449801451957211465 1141705087351088967908599)
    ·
      refine ⟨1712557631026633451862899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141705087351088967908599 1712557631026633451862899)
      ·
        refine ⟨2568836446539950177794349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712557631026633451862899 2568836446539950177794349)
        ·
          refine ⟨963313667452481316672881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2568836446539950177794349 963313667452481316672881)
          ·
            refine ⟨722485250589360987504661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963313667452481316672881 722485250589360987504661)
            ·
              refine ⟨33866496121376296289281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 722485250589360987504661 33866496121376296289281)
              ·
                refine ⟨25399872091032222216961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33866496121376296289281 25399872091032222216961)
                ·
                  refine ⟨19049904068274166662721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25399872091032222216961 19049904068274166662721)
                  ·
                    rfl

theorem cell20_41737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_41737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41737 prefixEnd_41737 := by exact prefixLift 41737
  have htrace : WordTrace (prefixWord ++ tailWord_41737) baseStart_41737 baseEnd_41737 := by
    simpa [prefixWord, tailWord_41737, baseEnd_41737] using wordTrace_append hprefix tailTrace_41737
  have hstable : (prefixWord ++ tailWord_41737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41737).length < 2 ^ (prefixWord ++ tailWord_41737).sum := by decide
  have hdescent : baseEnd_41737 < baseStart_41737 := by decide
  rcases family_descends (prefixWord ++ tailWord_41737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41765 : List Nat := [1, 3, 1, 2, 3, 1, 5, 4]
def baseStart_41765 : Nat := 118140960795 + 41765 * 2 ^ 59
def prefixEnd_41765 : Nat := 4983230072969 + 3 ^ 40 * 41765 * 2
def baseEnd_41765 : Nat := 6354228010410171243091

theorem tailTrace_41765 : CollatzResearch.WordTrace tailWord_41765 prefixEnd_41765 6354228010410171243091 := by
  unfold tailWord_41765
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523294693700012739230749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1015529795800008492820499 1523294693700012739230749)
  ·
    refine ⟨571235510137504777211531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1523294693700012739230749 571235510137504777211531)
    ·
      refine ⟨856853265206257165817297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571235510137504777211531 856853265206257165817297)
      ·
        refine ⟨642639948904692874362973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856853265206257165817297 642639948904692874362973)
        ·
          refine ⟨240989980839259827886115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642639948904692874362973 240989980839259827886115)
          ·
            refine ⟨361484971258889741829173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240989980839259827886115 361484971258889741829173)
            ·
              refine ⟨33889216055520913296485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 361484971258889741829173 33889216055520913296485)
              ·
                refine ⟨6354228010410171243091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33889216055520913296485 6354228010410171243091)
                ·
                  rfl

theorem cell20_41765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_41765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41765 prefixEnd_41765 := by exact prefixLift 41765
  have htrace : WordTrace (prefixWord ++ tailWord_41765) baseStart_41765 baseEnd_41765 := by
    simpa [prefixWord, tailWord_41765, baseEnd_41765] using wordTrace_append hprefix tailTrace_41765
  have hstable : (prefixWord ++ tailWord_41765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41765).length < 2 ^ (prefixWord ++ tailWord_41765).sum := by decide
  have hdescent : baseEnd_41765 < baseStart_41765 := by decide
  rcases family_descends (prefixWord ++ tailWord_41765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41782 : List Nat := [5, 1, 2, 2, 2, 1, 7]
def baseStart_41782 : Nat := 118140960795 + 41782 * 2 ^ 59
def prefixEnd_41782 : Nat := 4983230072969 + 3 ^ 40 * 41782 * 2
def baseEnd_41782 : Nat := 2118938143828223351393

theorem tailTrace_41782 : CollatzResearch.WordTrace tailWord_41782 prefixEnd_41782 2118938143828223351393 := by
  unfold tailWord_41782
  simp only [CollatzResearch.WordTrace]
  refine ⟨95244670914901540162475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1015943156425616428399733 95244670914901540162475)
  ·
    refine ⟨142867006372352310243713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95244670914901540162475 142867006372352310243713)
    ·
      refine ⟨107150254779264232682785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142867006372352310243713 107150254779264232682785)
      ·
        refine ⟨80362691084448174512089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107150254779264232682785 80362691084448174512089)
        ·
          refine ⟨60272018313336130884067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80362691084448174512089 60272018313336130884067)
          ·
            refine ⟨90408027470004196326101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60272018313336130884067 90408027470004196326101)
            ·
              refine ⟨2118938143828223351393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 90408027470004196326101 2118938143828223351393)
              ·
                rfl

theorem cell20_41782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 7].length) (baseStart_41782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41782 prefixEnd_41782 := by exact prefixLift 41782
  have htrace : WordTrace (prefixWord ++ tailWord_41782) baseStart_41782 baseEnd_41782 := by
    simpa [prefixWord, tailWord_41782, baseEnd_41782] using wordTrace_append hprefix tailTrace_41782
  have hstable : (prefixWord ++ tailWord_41782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41782).length < 2 ^ (prefixWord ++ tailWord_41782).sum := by decide
  have hdescent : baseEnd_41782 < baseStart_41782 := by decide
  rcases family_descends (prefixWord ++ tailWord_41782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41789 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 5]
def baseStart_41789 : Nat := 118140960795 + 41789 * 2 ^ 59
def prefixEnd_41789 : Nat := 4983230072969 + 3 ^ 40 * 41789 * 2
def baseEnd_41789 : Nat := 19073638285193096929175

theorem tailTrace_41789 : CollatzResearch.WordTrace tailWord_41789 prefixEnd_41789 19073638285193096929175 := by
  unfold tailWord_41789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524170045613064838104421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1016113363742043225402947 1524170045613064838104421)
  ·
    refine ⟨285781883552449657144579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1524170045613064838104421 285781883552449657144579)
    ·
      refine ⟨428672825328674485716869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285781883552449657144579 428672825328674485716869)
      ·
        refine ⟨80376154749126466071913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428672825328674485716869 80376154749126466071913)
        ·
          refine ⟨60282116061844849553935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80376154749126466071913 60282116061844849553935)
          ·
            refine ⟨90423174092767274330903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60282116061844849553935 90423174092767274330903)
            ·
              refine ⟨135634761139150911496355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90423174092767274330903 135634761139150911496355)
              ·
                refine ⟨203452141708726367244533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135634761139150911496355 203452141708726367244533)
                ·
                  refine ⟨19073638285193096929175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203452141708726367244533 19073638285193096929175)
                  ·
                    rfl

theorem cell20_41789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_41789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41789 prefixEnd_41789 := by exact prefixLift 41789
  have htrace : WordTrace (prefixWord ++ tailWord_41789) baseStart_41789 baseEnd_41789 := by
    simpa [prefixWord, tailWord_41789, baseEnd_41789] using wordTrace_append hprefix tailTrace_41789
  have hstable : (prefixWord ++ tailWord_41789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41789).length < 2 ^ (prefixWord ++ tailWord_41789).sum := by decide
  have hdescent : baseEnd_41789 < baseStart_41789 := by decide
  rcases family_descends (prefixWord ++ tailWord_41789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41817 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_41817 : Nat := 118140960795 + 41817 * 2 ^ 59
def prefixEnd_41817 : Nat := 4983230072969 + 3 ^ 40 * 41817 * 2
def baseEnd_41817 : Nat := 19086418248149443995727

theorem tailTrace_41817 : CollatzResearch.WordTrace tailWord_41817 prefixEnd_41817 19086418248149443995727 := by
  unfold tailWord_41817
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525191289511625620123705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1016794193007750413415803 1525191289511625620123705)
  ·
    refine ⟨1143893467133719215092779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1525191289511625620123705 1143893467133719215092779)
    ·
      refine ⟨1715840200700578822639169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143893467133719215092779 1715840200700578822639169)
      ·
        refine ⟨1286880150525434116979377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1715840200700578822639169 1286880150525434116979377)
        ·
          refine ⟨965160112894075587734533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1286880150525434116979377 965160112894075587734533)
          ·
            refine ⟨180967521167639172700225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 965160112894075587734533 180967521167639172700225)
            ·
              refine ⟨135725640875729379525169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180967521167639172700225 135725640875729379525169)
              ·
                refine ⟨101794230656797034643877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135725640875729379525169 101794230656797034643877)
                ·
                  refine ⟨19086418248149443995727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101794230656797034643877 19086418248149443995727)
                  ·
                    rfl

theorem cell20_41817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_41817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41817 prefixEnd_41817 := by exact prefixLift 41817
  have htrace : WordTrace (prefixWord ++ tailWord_41817) baseStart_41817 baseEnd_41817 := by
    simpa [prefixWord, tailWord_41817, baseEnd_41817] using wordTrace_append hprefix tailTrace_41817
  have hstable : (prefixWord ++ tailWord_41817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41817).length < 2 ^ (prefixWord ++ tailWord_41817).sum := by decide
  have hdescent : baseEnd_41817 < baseStart_41817 := by decide
  rcases family_descends (prefixWord ++ tailWord_41817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41820 : List Nat := [2, 2, 4, 2, 1, 1, 4, 4]
def baseStart_41820 : Nat := 118140960795 + 41820 * 2 ^ 59
def prefixEnd_41820 : Nat := 4983230072969 + 3 ^ 40 * 41820 * 2
def baseEnd_41820 : Nat := 6362595843298255631905

theorem tailTrace_41820 : CollatzResearch.WordTrace tailWord_41820 prefixEnd_41820 6362595843298255631905 := by
  unfold tailWord_41820
  simp only [CollatzResearch.WordTrace]
  refine ⟨762650354250378566241457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1016867139000504754988609 762650354250378566241457)
  ·
    refine ⟨571987765687783924681093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 762650354250378566241457 571987765687783924681093)
    ·
      refine ⟨107247706066459485877705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 571987765687783924681093 107247706066459485877705)
      ·
        refine ⟨80435779549844614408279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107247706066459485877705 80435779549844614408279)
        ·
          refine ⟨120653669324766921612419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80435779549844614408279 120653669324766921612419)
          ·
            refine ⟨180980503987150382418629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120653669324766921612419 180980503987150382418629)
            ·
              refine ⟨33933844497590696703493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180980503987150382418629 33933844497590696703493)
              ·
                refine ⟨6362595843298255631905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33933844497590696703493 6362595843298255631905)
                ·
                  rfl

theorem cell20_41820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_41820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41820 prefixEnd_41820 := by exact prefixLift 41820
  have htrace : WordTrace (prefixWord ++ tailWord_41820) baseStart_41820 baseEnd_41820 := by
    simpa [prefixWord, tailWord_41820, baseEnd_41820] using wordTrace_append hprefix tailTrace_41820
  have hstable : (prefixWord ++ tailWord_41820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41820).length < 2 ^ (prefixWord ++ tailWord_41820).sum := by decide
  have hdescent : baseEnd_41820 < baseStart_41820 := by decide
  rcases family_descends (prefixWord ++ tailWord_41820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41824 : List Nat := [2, 1, 1, 3, 3, 1, 3, 6]
def baseStart_41824 : Nat := 118140960795 + 41824 * 2 ^ 59
def prefixEnd_41824 : Nat := 4983230072969 + 3 ^ 40 * 41824 * 2
def baseEnd_41824 : Nat := 6363204412962843587455

theorem tailTrace_41824 : CollatzResearch.WordTrace tailWord_41824 prefixEnd_41824 6363204412962843587455 := by
  unfold tailWord_41824
  simp only [CollatzResearch.WordTrace]
  refine ⟨762723300243132907814263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1016964400324177210419017 762723300243132907814263)
  ·
    refine ⟨1144084950364699361721395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762723300243132907814263 1144084950364699361721395)
    ·
      refine ⟨1716127425547049042582093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144084950364699361721395 1716127425547049042582093)
      ·
        refine ⟨643547784580143390968285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1716127425547049042582093 643547784580143390968285)
        ·
          refine ⟨241330419217553771613107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 643547784580143390968285 241330419217553771613107)
          ·
            refine ⟨361995628826330657419661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241330419217553771613107 361995628826330657419661)
            ·
              refine ⟨135748360809873996532373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361995628826330657419661 135748360809873996532373)
              ·
                refine ⟨6363204412962843587455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135748360809873996532373 6363204412962843587455)
                ·
                  rfl

theorem cell20_41824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_41824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41824 prefixEnd_41824 := by exact prefixLift 41824
  have htrace : WordTrace (prefixWord ++ tailWord_41824) baseStart_41824 baseEnd_41824 := by
    simpa [prefixWord, tailWord_41824, baseEnd_41824] using wordTrace_append hprefix tailTrace_41824
  have hstable : (prefixWord ++ tailWord_41824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41824).length < 2 ^ (prefixWord ++ tailWord_41824).sum := by decide
  have hdescent : baseEnd_41824 < baseStart_41824 := by decide
  rcases family_descends (prefixWord ++ tailWord_41824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41855 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_41855 : Nat := 118140960795 + 41855 * 2 ^ 59
def prefixEnd_41855 : Nat := 4983230072969 + 3 ^ 40 * 41855 * 2
def baseEnd_41855 : Nat := 19103762483590200728905

theorem tailTrace_41855 : CollatzResearch.WordTrace tailWord_41855 prefixEnd_41855 19103762483590200728905 := by
  unfold tailWord_41855
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526577263373958110007019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1017718175582638740004679 1526577263373958110007019)
  ·
    refine ⟨2289865895060937165010529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526577263373958110007019 2289865895060937165010529)
    ·
      refine ⟨1717399421295702873757897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2289865895060937165010529 1717399421295702873757897)
      ·
        refine ⟨1288049565971777155318423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717399421295702873757897 1288049565971777155318423)
        ·
          refine ⟨1932074348957665732977635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288049565971777155318423 1932074348957665732977635)
          ·
            refine ⟨2898111523436498599466453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932074348957665732977635 2898111523436498599466453)
            ·
              refine ⟨67924488830542935924995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2898111523436498599466453 67924488830542935924995)
              ·
                refine ⟨101886733245814403887493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67924488830542935924995 101886733245814403887493)
                ·
                  refine ⟨19103762483590200728905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101886733245814403887493 19103762483590200728905)
                  ·
                    rfl

theorem cell20_41855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_41855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41855 prefixEnd_41855 := by exact prefixLift 41855
  have htrace : WordTrace (prefixWord ++ tailWord_41855) baseStart_41855 baseEnd_41855 := by
    simpa [prefixWord, tailWord_41855, baseEnd_41855] using wordTrace_append hprefix tailTrace_41855
  have hstable : (prefixWord ++ tailWord_41855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41855).length < 2 ^ (prefixWord ++ tailWord_41855).sum := by decide
  have hdescent : baseEnd_41855 < baseStart_41855 := by decide
  rcases family_descends (prefixWord ++ tailWord_41855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41865 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 3]
def baseStart_41865 : Nat := 118140960795 + 41865 * 2 ^ 59
def prefixEnd_41865 : Nat := 4983230072969 + 3 ^ 40 * 41865 * 2
def baseEnd_41865 : Nat := 19108326756074610395531

theorem tailTrace_41865 : CollatzResearch.WordTrace tailWord_41865 prefixEnd_41865 19108326756074610395531 := by
  unfold tailWord_41865
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526941993337729817871049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1017961328891819878580699 1526941993337729817871049)
  ·
    refine ⟨1145206495003297363403287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1526941993337729817871049 1145206495003297363403287)
    ·
      refine ⟨1717809742504946045104931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145206495003297363403287 1717809742504946045104931)
      ·
        refine ⟨2576714613757419067657397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717809742504946045104931 2576714613757419067657397)
        ·
          refine ⟨241566995039758037592881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2576714613757419067657397 241566995039758037592881)
          ·
            refine ⟨181175246279818528194661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241566995039758037592881 181175246279818528194661)
            ·
              refine ⟨33970358677465974036499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181175246279818528194661 33970358677465974036499)
              ·
                refine ⟨50955538016198961054749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33970358677465974036499 50955538016198961054749)
                ·
                  refine ⟨19108326756074610395531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50955538016198961054749 19108326756074610395531)
                  ·
                    rfl

theorem cell20_41865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_41865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41865 prefixEnd_41865 := by exact prefixLift 41865
  have htrace : WordTrace (prefixWord ++ tailWord_41865) baseStart_41865 baseEnd_41865 := by
    simpa [prefixWord, tailWord_41865, baseEnd_41865] using wordTrace_append hprefix tailTrace_41865
  have hstable : (prefixWord ++ tailWord_41865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41865).length < 2 ^ (prefixWord ++ tailWord_41865).sum := by decide
  have hdescent : baseEnd_41865 < baseStart_41865 := by decide
  rcases family_descends (prefixWord ++ tailWord_41865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41931 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_41931 : Nat := 118140960795 + 41931 * 2 ^ 59
def prefixEnd_41931 : Nat := 4983230072969 + 3 ^ 40 * 41931 * 2
def baseEnd_41931 : Nat := 19138450954471714195261

theorem tailTrace_41931 : CollatzResearch.WordTrace tailWord_41931 prefixEnd_41931 19138450954471714195261 := by
  unfold tailWord_41931
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529349211098623089773647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1019566140732415393182431 1529349211098623089773647)
  ·
    refine ⟨2294023816647934634660471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529349211098623089773647 2294023816647934634660471)
    ·
      refine ⟨3441035724971901951990707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294023816647934634660471 3441035724971901951990707)
      ·
        refine ⟨5161553587457852927986061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441035724971901951990707 5161553587457852927986061)
        ·
          refine ⟨1935582595296694847994773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5161553587457852927986061 1935582595296694847994773)
          ·
            refine ⟨90730434154532570999755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1935582595296694847994773 90730434154532570999755)
            ·
              refine ⟨136095651231798856499633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90730434154532570999755 136095651231798856499633)
              ·
                refine ⟨102071738423849142374725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136095651231798856499633 102071738423849142374725)
                ·
                  refine ⟨19138450954471714195261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102071738423849142374725 19138450954471714195261)
                  ·
                    rfl

theorem cell20_41931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_41931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41931 prefixEnd_41931 := by exact prefixLift 41931
  have htrace : WordTrace (prefixWord ++ tailWord_41931) baseStart_41931 baseEnd_41931 := by
    simpa [prefixWord, tailWord_41931, baseEnd_41931] using wordTrace_append hprefix tailTrace_41931
  have hstable : (prefixWord ++ tailWord_41931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41931).length < 2 ^ (prefixWord ++ tailWord_41931).sum := by decide
  have hdescent : baseEnd_41931 < baseStart_41931 := by decide
  rcases family_descends (prefixWord ++ tailWord_41931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41962 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_41962 : Nat := 118140960795 + 41962 * 2 ^ 59
def prefixEnd_41962 : Nat := 4983230072969 + 3 ^ 40 * 41962 * 2
def baseEnd_41962 : Nat := 19152600199173384161801

theorem tailTrace_41962 : CollatzResearch.WordTrace tailWord_41962 prefixEnd_41962 19152600199173384161801 := by
  unfold tailWord_41962
  simp only [CollatzResearch.WordTrace]
  refine ⟨382619968496578846038035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1020319915990876922768093 382619968496578846038035)
  ·
    refine ⟨573929952744868269057053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 382619968496578846038035 573929952744868269057053)
    ·
      refine ⟨215223732279325600896395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 573929952744868269057053 215223732279325600896395)
      ·
        refine ⟨322835598418988401344593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215223732279325600896395 322835598418988401344593)
        ·
          refine ⟨242126698814241301008445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322835598418988401344593 242126698814241301008445)
          ·
            refine ⟨90797512055340487878167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242126698814241301008445 90797512055340487878167)
            ·
              refine ⟨136196268083010731817251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90797512055340487878167 136196268083010731817251)
              ·
                refine ⟨204294402124516097725877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136196268083010731817251 204294402124516097725877)
                ·
                  refine ⟨19152600199173384161801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204294402124516097725877 19152600199173384161801)
                  ·
                    rfl

theorem cell20_41962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_41962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41962 prefixEnd_41962 := by exact prefixLift 41962
  have htrace : WordTrace (prefixWord ++ tailWord_41962) baseStart_41962 baseEnd_41962 := by
    simpa [prefixWord, tailWord_41962, baseEnd_41962] using wordTrace_append hprefix tailTrace_41962
  have hstable : (prefixWord ++ tailWord_41962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41962).length < 2 ^ (prefixWord ++ tailWord_41962).sum := by decide
  have hdescent : baseEnd_41962 < baseStart_41962 := by decide
  rcases family_descends (prefixWord ++ tailWord_41962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41969 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_41969 : Nat := 118140960795 + 41969 * 2 ^ 59
def prefixEnd_41969 : Nat := 4983230072969 + 3 ^ 40 * 41969 * 2
def baseEnd_41969 : Nat := 19155795189912470928439

theorem tailTrace_41969 : CollatzResearch.WordTrace tailWord_41969 prefixEnd_41969 19155795189912470928439 := by
  unfold tailWord_41969
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530735184960955579656961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1020490123307303719771307 1530735184960955579656961)
  ·
    refine ⟨1148051388720716684742721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1530735184960955579656961 1148051388720716684742721)
    ·
      refine ⟨861038541540537513557041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1148051388720716684742721 861038541540537513557041)
      ·
        refine ⟨645778906155403135167781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 861038541540537513557041 645778906155403135167781)
        ·
          refine ⟨121083544904138087843959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 645778906155403135167781 121083544904138087843959)
          ·
            refine ⟨181625317356207131765939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121083544904138087843959 181625317356207131765939)
            ·
              refine ⟨272437976034310697648909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181625317356207131765939 272437976034310697648909)
              ·
                refine ⟨102164241012866511618341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272437976034310697648909 102164241012866511618341)
                ·
                  refine ⟨19155795189912470928439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102164241012866511618341 19155795189912470928439)
                  ·
                    rfl

theorem cell20_41969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_41969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_41969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_41969 prefixEnd_41969 := by exact prefixLift 41969
  have htrace : WordTrace (prefixWord ++ tailWord_41969) baseStart_41969 baseEnd_41969 := by
    simpa [prefixWord, tailWord_41969, baseEnd_41969] using wordTrace_append hprefix tailTrace_41969
  have hstable : (prefixWord ++ tailWord_41969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41969).length < 2 ^ (prefixWord ++ tailWord_41969).sum := by decide
  have hdescent : baseEnd_41969 < baseStart_41969 := by decide
  rcases family_descends (prefixWord ++ tailWord_41969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42020 : List Nat := [2, 3, 1, 4, 1, 2, 3, 2, 2]
def baseStart_42020 : Nat := 118140960795 + 42020 * 2 ^ 59
def prefixEnd_42020 : Nat := 4983230072969 + 3 ^ 40 * 42020 * 2
def baseEnd_42020 : Nat := 19179072979582960228231

theorem tailTrace_42020 : CollatzResearch.WordTrace tailWord_42020 prefixEnd_42020 19179072979582960228231 := by
  unfold tailWord_42020
  simp only [CollatzResearch.WordTrace]
  refine ⟨766297653888095644881757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1021730205184127526509009 766297653888095644881757)
  ·
    refine ⟨287361620208035866830659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 766297653888095644881757 287361620208035866830659)
    ·
      refine ⟨431042430312053800245989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287361620208035866830659 431042430312053800245989)
      ·
        refine ⟨80820455683510087546123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 431042430312053800245989 80820455683510087546123)
        ·
          refine ⟨121230683525265131319185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80820455683510087546123 121230683525265131319185)
          ·
            refine ⟨90923012643948848489389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121230683525265131319185 90923012643948848489389)
            ·
              refine ⟨34096129741480818183521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90923012643948848489389 34096129741480818183521)
              ·
                refine ⟨25572097306110613637641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34096129741480818183521 25572097306110613637641)
                ·
                  refine ⟨19179072979582960228231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25572097306110613637641 19179072979582960228231)
                  ·
                    rfl

theorem cell20_42020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_42020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42020 prefixEnd_42020 := by exact prefixLift 42020
  have htrace : WordTrace (prefixWord ++ tailWord_42020) baseStart_42020 baseEnd_42020 := by
    simpa [prefixWord, tailWord_42020, baseEnd_42020] using wordTrace_append hprefix tailTrace_42020
  have hstable : (prefixWord ++ tailWord_42020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42020).length < 2 ^ (prefixWord ++ tailWord_42020).sum := by decide
  have hdescent : baseEnd_42020 < baseStart_42020 := by decide
  rcases family_descends (prefixWord ++ tailWord_42020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42021 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_42021 : Nat := 118140960795 + 42021 * 2 ^ 59
def prefixEnd_42021 : Nat := 4983230072969 + 3 ^ 40 * 42021 * 2
def baseEnd_42021 : Nat := 19179529406831401194893

theorem tailTrace_42021 : CollatzResearch.WordTrace tailWord_42021 prefixEnd_42021 19179529406831401194893 := by
  unfold tailWord_42021
  simp only [CollatzResearch.WordTrace]
  refine ⟨1532631780772568460549917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1021754520515045640366611 1532631780772568460549917)
  ·
    refine ⟨574736917789713172706219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1532631780772568460549917 574736917789713172706219)
    ·
      refine ⟨862105376684569759059329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574736917789713172706219 862105376684569759059329)
      ·
        refine ⟨646579032513427319294497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 862105376684569759059329 646579032513427319294497)
        ·
          refine ⟨484934274385070489470873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646579032513427319294497 484934274385070489470873)
          ·
            refine ⟨363700705788802867103155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484934274385070489470873 363700705788802867103155)
            ·
              refine ⟨545551058683204300654733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363700705788802867103155 545551058683204300654733)
              ·
                refine ⟨204581647006201612745525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 545551058683204300654733 204581647006201612745525)
                ·
                  refine ⟨19179529406831401194893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204581647006201612745525 19179529406831401194893)
                  ·
                    rfl

theorem cell20_42021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_42021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42021 prefixEnd_42021 := by exact prefixLift 42021
  have htrace : WordTrace (prefixWord ++ tailWord_42021) baseStart_42021 baseEnd_42021 := by
    simpa [prefixWord, tailWord_42021, baseEnd_42021] using wordTrace_append hprefix tailTrace_42021
  have hstable : (prefixWord ++ tailWord_42021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42021).length < 2 ^ (prefixWord ++ tailWord_42021).sum := by decide
  have hdescent : baseEnd_42021 < baseStart_42021 := by decide
  rcases family_descends (prefixWord ++ tailWord_42021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42062 : List Nat := [4, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_42062 : Nat := 118140960795 + 42062 * 2 ^ 59
def prefixEnd_42062 : Nat := 4983230072969 + 3 ^ 40 * 42062 * 2
def baseEnd_42062 : Nat := 19198242924017480828059

theorem tailTrace_42062 : CollatzResearch.WordTrace tailWord_42062 prefixEnd_42062 19198242924017480828059 := by
  unfold tailWord_42062
  simp only [CollatzResearch.WordTrace]
  refine ⟨191765896703004057849055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1022751449082688308528293 191765896703004057849055)
  ·
    refine ⟨287648845054506086773583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191765896703004057849055 287648845054506086773583)
    ·
      refine ⟨431473267581759130160375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287648845054506086773583 431473267581759130160375)
      ·
        refine ⟨647209901372638695240563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431473267581759130160375 647209901372638695240563)
        ·
          refine ⟨970814852058958042860845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647209901372638695240563 970814852058958042860845)
          ·
            refine ⟨364055569522109266072817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 970814852058958042860845 364055569522109266072817)
            ·
              refine ⟨273041677141581949554613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364055569522109266072817 273041677141581949554613)
              ·
                refine ⟨25597657232023307770745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 273041677141581949554613 25597657232023307770745)
                ·
                  refine ⟨19198242924017480828059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25597657232023307770745 19198242924017480828059)
                  ·
                    rfl

theorem cell20_42062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_42062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42062 prefixEnd_42062 := by exact prefixLift 42062
  have htrace : WordTrace (prefixWord ++ tailWord_42062) baseStart_42062 baseEnd_42062 := by
    simpa [prefixWord, tailWord_42062, baseEnd_42062] using wordTrace_append hprefix tailTrace_42062
  have hstable : (prefixWord ++ tailWord_42062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42062).length < 2 ^ (prefixWord ++ tailWord_42062).sum := by decide
  have hdescent : baseEnd_42062 < baseStart_42062 := by decide
  rcases family_descends (prefixWord ++ tailWord_42062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42104 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_42104 : Nat := 118140960795 + 42104 * 2 ^ 59
def prefixEnd_42104 : Nat := 4983230072969 + 3 ^ 40 * 42104 * 2
def baseEnd_42104 : Nat := 19217412868452001427887

theorem tailTrace_42104 : CollatzResearch.WordTrace tailWord_42104 prefixEnd_42104 19217412868452001427887 := by
  unfold tailWord_42104
  simp only [CollatzResearch.WordTrace]
  refine ⟨767829519735936817910683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1023772692981249090547577 767829519735936817910683)
  ·
    refine ⟨1151744279603905226866025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767829519735936817910683 1151744279603905226866025)
    ·
      refine ⟨863808209702928920149519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1151744279603905226866025 863808209702928920149519)
      ·
        refine ⟨1295712314554393380224279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863808209702928920149519 1295712314554393380224279)
        ·
          refine ⟨1943568471831590070336419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295712314554393380224279 1943568471831590070336419)
          ·
            refine ⟨2915352707747385105504629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943568471831590070336419 2915352707747385105504629)
            ·
              refine ⟨273314316351317353641059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2915352707747385105504629 273314316351317353641059)
              ·
                refine ⟨409971474526976030461589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273314316351317353641059 409971474526976030461589)
                ·
                  refine ⟨19217412868452001427887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 409971474526976030461589 19217412868452001427887)
                  ·
                    rfl

theorem cell20_42104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_42104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42104 prefixEnd_42104 := by exact prefixLift 42104
  have htrace : WordTrace (prefixWord ++ tailWord_42104) baseStart_42104 baseEnd_42104 := by
    simpa [prefixWord, tailWord_42104, baseEnd_42104] using wordTrace_append hprefix tailTrace_42104
  have hstable : (prefixWord ++ tailWord_42104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42104).length < 2 ^ (prefixWord ++ tailWord_42104).sum := by decide
  have hdescent : baseEnd_42104 < baseStart_42104 := by decide
  rcases family_descends (prefixWord ++ tailWord_42104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42117 : List Nat := [1, 3, 1, 1, 6, 1, 2, 3, 2]
def baseStart_42117 : Nat := 118140960795 + 42117 * 2 ^ 59
def prefixEnd_42117 : Nat := 4983230072969 + 3 ^ 40 * 42117 * 2
def baseEnd_42117 : Nat := 19223346422681733994501

theorem tailTrace_42117 : CollatzResearch.WordTrace tailWord_42117 prefixEnd_42117 19223346422681733994501 := by
  unfold tailWord_42117
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536133188424776856044605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1024088792283184570696403 1536133188424776856044605)
  ·
    refine ⟨576049945659291321016727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1536133188424776856044605 576049945659291321016727)
    ·
      refine ⟨864074918488936981525091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576049945659291321016727 864074918488936981525091)
      ·
        refine ⟨1296112377733405472287637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864074918488936981525091 1296112377733405472287637)
        ·
          refine ⟨60755267706253381513483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1296112377733405472287637 60755267706253381513483)
          ·
            refine ⟨91132901559380072270225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60755267706253381513483 91132901559380072270225)
            ·
              refine ⟨68349676169535054202669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91132901559380072270225 68349676169535054202669)
              ·
                refine ⟨25631128563575645326001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68349676169535054202669 25631128563575645326001)
                ·
                  refine ⟨19223346422681733994501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25631128563575645326001 19223346422681733994501)
                  ·
                    rfl

theorem cell20_42117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_42117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42117 prefixEnd_42117 := by exact prefixLift 42117
  have htrace : WordTrace (prefixWord ++ tailWord_42117) baseStart_42117 baseEnd_42117 := by
    simpa [prefixWord, tailWord_42117, baseEnd_42117] using wordTrace_append hprefix tailTrace_42117
  have hstable : (prefixWord ++ tailWord_42117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42117).length < 2 ^ (prefixWord ++ tailWord_42117).sum := by decide
  have hdescent : baseEnd_42117 < baseStart_42117 := by decide
  rcases family_descends (prefixWord ++ tailWord_42117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42138 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_42138 : Nat := 118140960795 + 42138 * 2 ^ 59
def prefixEnd_42138 : Nat := 4983230072969 + 3 ^ 40 * 42138 * 2
def baseEnd_42138 : Nat := 19232931394898994294415

theorem tailTrace_42138 : CollatzResearch.WordTrace tailWord_42138 prefixEnd_42138 19232931394898994294415 := by
  unfold tailWord_42138
  simp only [CollatzResearch.WordTrace]
  refine ⟨384224780337174360639767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1024599414232464961706045 384224780337174360639767)
  ·
    refine ⟨576337170505761540959651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384224780337174360639767 576337170505761540959651)
    ·
      refine ⟨864505755758642311439477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576337170505761540959651 864505755758642311439477)
      ·
        refine ⟨81047414602372716697451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 864505755758642311439477 81047414602372716697451)
        ·
          refine ⟨121571121903559075046177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81047414602372716697451 121571121903559075046177)
          ·
            refine ⟨91178341427669306284633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121571121903559075046177 91178341427669306284633)
            ·
              refine ⟨68383756070751979713475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91178341427669306284633 68383756070751979713475)
              ·
                refine ⟨102575634106127969570213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68383756070751979713475 102575634106127969570213)
                ·
                  refine ⟨19232931394898994294415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102575634106127969570213 19232931394898994294415)
                  ·
                    rfl

theorem cell20_42138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_42138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42138 prefixEnd_42138 := by exact prefixLift 42138
  have htrace : WordTrace (prefixWord ++ tailWord_42138) baseStart_42138 baseEnd_42138 := by
    simpa [prefixWord, tailWord_42138, baseEnd_42138] using wordTrace_append hprefix tailTrace_42138
  have hstable : (prefixWord ++ tailWord_42138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42138).length < 2 ^ (prefixWord ++ tailWord_42138).sum := by decide
  have hdescent : baseEnd_42138 < baseStart_42138 := by decide
  rcases family_descends (prefixWord ++ tailWord_42138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42173 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_42173 : Nat := 118140960795 + 42173 * 2 ^ 59
def prefixEnd_42173 : Nat := 4983230072969 + 3 ^ 40 * 42173 * 2
def baseEnd_42173 : Nat := 19248906348594428127605

theorem tailTrace_42173 : CollatzResearch.WordTrace tailWord_42173 prefixEnd_42173 19248906348594428127605 := by
  unfold tailWord_42173
  simp only [CollatzResearch.WordTrace]
  refine ⟨1538175676221898420083173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1025450450814598946722115 1538175676221898420083173)
  ·
    refine ⟨288407939291605953765595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1538175676221898420083173 288407939291605953765595)
    ·
      refine ⟨432611908937408930648393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288407939291605953765595 432611908937408930648393)
      ·
        refine ⟨324458931703056697986295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432611908937408930648393 324458931703056697986295)
        ·
          refine ⟨486688397554585046979443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324458931703056697986295 486688397554585046979443)
          ·
            refine ⟨730032596331877570469165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486688397554585046979443 730032596331877570469165)
            ·
              refine ⟨273762223624454088925937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 730032596331877570469165 273762223624454088925937)
              ·
                refine ⟨205321667718340566694453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273762223624454088925937 205321667718340566694453)
                ·
                  refine ⟨19248906348594428127605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205321667718340566694453 19248906348594428127605)
                  ·
                    rfl

theorem cell20_42173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_42173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42173 prefixEnd_42173 := by exact prefixLift 42173
  have htrace : WordTrace (prefixWord ++ tailWord_42173) baseStart_42173 baseEnd_42173 := by
    simpa [prefixWord, tailWord_42173, baseEnd_42173] using wordTrace_append hprefix tailTrace_42173
  have hstable : (prefixWord ++ tailWord_42173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42173).length < 2 ^ (prefixWord ++ tailWord_42173).sum := by decide
  have hdescent : baseEnd_42173 < baseStart_42173 := by decide
  rcases family_descends (prefixWord ++ tailWord_42173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42189 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 4]
def baseStart_42189 : Nat := 118140960795 + 42189 * 2 ^ 59
def prefixEnd_42189 : Nat := 4983230072969 + 3 ^ 40 * 42189 * 2
def baseEnd_42189 : Nat := 19256209184569483594207

theorem tailTrace_42189 : CollatzResearch.WordTrace tailWord_42189 prefixEnd_42189 19256209184569483594207 := by
  unfold tailWord_42189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1538759244163933152665621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1025839496109288768443747 1538759244163933152665621)
  ·
    refine ⟨72129339570184366531201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1538759244163933152665621 72129339570184366531201)
    ·
      refine ⟨54097004677638274898401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72129339570184366531201 54097004677638274898401)
      ·
        refine ⟨40572753508228706173801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54097004677638274898401 40572753508228706173801)
        ·
          refine ⟨30429565131171529630351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40572753508228706173801 30429565131171529630351)
          ·
            refine ⟨45644347696757294445527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30429565131171529630351 45644347696757294445527)
            ·
              refine ⟨68466521545135941668291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45644347696757294445527 68466521545135941668291)
              ·
                refine ⟨102699782317703912502437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68466521545135941668291 102699782317703912502437)
                ·
                  refine ⟨19256209184569483594207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102699782317703912502437 19256209184569483594207)
                  ·
                    rfl

theorem cell20_42189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_42189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42189 prefixEnd_42189 := by exact prefixLift 42189
  have htrace : WordTrace (prefixWord ++ tailWord_42189) baseStart_42189 baseEnd_42189 := by
    simpa [prefixWord, tailWord_42189, baseEnd_42189] using wordTrace_append hprefix tailTrace_42189
  have hstable : (prefixWord ++ tailWord_42189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42189).length < 2 ^ (prefixWord ++ tailWord_42189).sum := by decide
  have hdescent : baseEnd_42189 < baseStart_42189 := by decide
  rcases family_descends (prefixWord ++ tailWord_42189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42242 : List Nat := [3, 4, 1, 1, 11]
def baseStart_42242 : Nat := 118140960795 + 42242 * 2 ^ 59
def prefixEnd_42242 : Nat := 4983230072969 + 3 ^ 40 * 42242 * 2
def baseEnd_42242 : Nat := 238029627515269812683

theorem tailTrace_42242 : CollatzResearch.WordTrace tailWord_42242 prefixEnd_42242 238029627515269812683 := by
  unfold tailWord_42242
  simp only [CollatzResearch.WordTrace]
  refine ⟨385173078242980801086245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1027128208647948802896653 385173078242980801086245)
  ·
    refine ⟨72219952170558900203671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 385173078242980801086245 72219952170558900203671)
    ·
      refine ⟨108329928255838350305507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72219952170558900203671 108329928255838350305507)
      ·
        refine ⟨162494892383757525458261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108329928255838350305507 162494892383757525458261)
        ·
          refine ⟨238029627515269812683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 162494892383757525458261 238029627515269812683)
          ·
            rfl

theorem cell20_42242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 11].length) (baseStart_42242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42242 prefixEnd_42242 := by exact prefixLift 42242
  have htrace : WordTrace (prefixWord ++ tailWord_42242) baseStart_42242 baseEnd_42242 := by
    simpa [prefixWord, tailWord_42242, baseEnd_42242] using wordTrace_append hprefix tailTrace_42242
  have hstable : (prefixWord ++ tailWord_42242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42242).length < 2 ^ (prefixWord ++ tailWord_42242).sum := by decide
  have hdescent : baseEnd_42242 < baseStart_42242 := by decide
  rcases family_descends (prefixWord ++ tailWord_42242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42248 : List Nat := [2, 1, 3, 2, 4, 2, 2, 2, 2]
def baseStart_42248 : Nat := 118140960795 + 42248 * 2 ^ 59
def prefixEnd_42248 : Nat := 4983230072969 + 3 ^ 40 * 42248 * 2
def baseEnd_42248 : Nat := 19283138392227500627299

theorem tailTrace_42248 : CollatzResearch.WordTrace tailWord_42248 prefixEnd_42248 19283138392227500627299 := by
  unfold tailWord_42248
  simp only [CollatzResearch.WordTrace]
  refine ⟨770455575475093114531699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1027274100633457486042265 770455575475093114531699)
  ·
    refine ⟨1155683363212639671797549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770455575475093114531699 1155683363212639671797549)
    ·
      refine ⟨433381261204739876924081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1155683363212639671797549 433381261204739876924081)
      ·
        refine ⟨325035945903554907693061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433381261204739876924081 325035945903554907693061)
        ·
          refine ⟨60944239856916545192449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325035945903554907693061 60944239856916545192449)
          ·
            refine ⟨45708179892687408894337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60944239856916545192449 45708179892687408894337)
            ·
              refine ⟨34281134919515556670753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45708179892687408894337 34281134919515556670753)
              ·
                refine ⟨25710851189636667503065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34281134919515556670753 25710851189636667503065)
                ·
                  refine ⟨19283138392227500627299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25710851189636667503065 19283138392227500627299)
                  ·
                    rfl

theorem cell20_42248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_42248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42248 prefixEnd_42248 := by exact prefixLift 42248
  have htrace : WordTrace (prefixWord ++ tailWord_42248) baseStart_42248 baseEnd_42248 := by
    simpa [prefixWord, tailWord_42248, baseEnd_42248] using wordTrace_append hprefix tailTrace_42248
  have hstable : (prefixWord ++ tailWord_42248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42248).length < 2 ^ (prefixWord ++ tailWord_42248).sum := by decide
  have hdescent : baseEnd_42248 < baseStart_42248 := by decide
  rcases family_descends (prefixWord ++ tailWord_42248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42252 : List Nat := [2, 2, 1, 2, 2, 4, 1, 4, 2]
def baseStart_42252 : Nat := 118140960795 + 42252 * 2 ^ 59
def prefixEnd_42252 : Nat := 4983230072969 + 3 ^ 40 * 42252 * 2
def baseEnd_42252 : Nat := 19284964101221264493949

theorem tailTrace_42252 : CollatzResearch.WordTrace tailWord_42252 prefixEnd_42252 19284964101221264493949 := by
  unfold tailWord_42252
  simp only [CollatzResearch.WordTrace]
  refine ⟨770528521467847456104505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1027371361957129941472673 770528521467847456104505)
  ·
    refine ⟨577896391100885592078379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 770528521467847456104505 577896391100885592078379)
    ·
      refine ⟨866844586651328388117569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577896391100885592078379 866844586651328388117569)
      ·
        refine ⟨650133439988496291088177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 866844586651328388117569 650133439988496291088177)
        ·
          refine ⟨487600079991372218316133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650133439988496291088177 487600079991372218316133)
          ·
            refine ⟨91425014998382290934275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 487600079991372218316133 91425014998382290934275)
            ·
              refine ⟨137137522497573436401413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91425014998382290934275 137137522497573436401413)
              ·
                refine ⟨25713285468295019325265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137137522497573436401413 25713285468295019325265)
                ·
                  refine ⟨19284964101221264493949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25713285468295019325265 19284964101221264493949)
                  ·
                    rfl

theorem cell20_42252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_42252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42252 prefixEnd_42252 := by exact prefixLift 42252
  have htrace : WordTrace (prefixWord ++ tailWord_42252) baseStart_42252 baseEnd_42252 := by
    simpa [prefixWord, tailWord_42252, baseEnd_42252] using wordTrace_append hprefix tailTrace_42252
  have hstable : (prefixWord ++ tailWord_42252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42252).length < 2 ^ (prefixWord ++ tailWord_42252).sum := by decide
  have hdescent : baseEnd_42252 < baseStart_42252 := by decide
  rcases family_descends (prefixWord ++ tailWord_42252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42266 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_42266 : Nat := 118140960795 + 42266 * 2 ^ 59
def prefixEnd_42266 : Nat := 4983230072969 + 3 ^ 40 * 42266 * 2
def baseEnd_42266 : Nat := 19291354082699438027225

theorem tailTrace_42266 : CollatzResearch.WordTrace tailWord_42266 prefixEnd_42266 19291354082699438027225 := by
  unfold tailWord_42266
  simp only [CollatzResearch.WordTrace]
  refine ⟨385391916221243825804663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1027711776589983535479101 385391916221243825804663)
  ·
    refine ⟨578087874331865738706995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385391916221243825804663 578087874331865738706995)
    ·
      refine ⟨867131811497798608060493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 578087874331865738706995 867131811497798608060493)
      ·
        refine ⟨325174429311674478022685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 867131811497798608060493 325174429311674478022685)
        ·
          refine ⟨121940410991877929258507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325174429311674478022685 121940410991877929258507)
          ·
            refine ⟨182910616487816893887761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121940410991877929258507 182910616487816893887761)
            ·
              refine ⟨137182962365862670415821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182910616487816893887761 137182962365862670415821)
              ·
                refine ⟨51443610887198501405933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137182962365862670415821 51443610887198501405933)
                ·
                  refine ⟨19291354082699438027225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51443610887198501405933 19291354082699438027225)
                  ·
                    rfl

theorem cell20_42266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_42266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42266 prefixEnd_42266 := by exact prefixLift 42266
  have htrace : WordTrace (prefixWord ++ tailWord_42266) baseStart_42266 baseEnd_42266 := by
    simpa [prefixWord, tailWord_42266, baseEnd_42266] using wordTrace_append hprefix tailTrace_42266
  have hstable : (prefixWord ++ tailWord_42266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42266).length < 2 ^ (prefixWord ++ tailWord_42266).sum := by decide
  have hdescent : baseEnd_42266 < baseStart_42266 := by decide
  rcases family_descends (prefixWord ++ tailWord_42266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42290 : List Nat := [3, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_42290 : Nat := 118140960795 + 42290 * 2 ^ 59
def prefixEnd_42290 : Nat := 4983230072969 + 3 ^ 40 * 42290 * 2
def baseEnd_42290 : Nat := 19302308336662021227127

theorem tailTrace_42290 : CollatzResearch.WordTrace tailWord_42290 prefixEnd_42290 19302308336662021227127 := by
  unfold tailWord_42290
  simp only [CollatzResearch.WordTrace]
  refine ⟨385610754199506850523081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1028295344532018268061549 385610754199506850523081)
  ·
    refine ⟨289208065649630137892311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 385610754199506850523081 289208065649630137892311)
    ·
      refine ⟨433812098474445206838467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289208065649630137892311 433812098474445206838467)
      ·
        refine ⟨650718147711667810257701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433812098474445206838467 650718147711667810257701)
        ·
          refine ⟨122009652695937714423319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 650718147711667810257701 122009652695937714423319)
          ·
            refine ⟨183014479043906571634979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122009652695937714423319 183014479043906571634979)
            ·
              refine ⟨274521718565859857452469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183014479043906571634979 274521718565859857452469)
              ·
                refine ⟨25736411115549361636169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274521718565859857452469 25736411115549361636169)
                ·
                  refine ⟨19302308336662021227127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25736411115549361636169 19302308336662021227127)
                  ·
                    rfl

theorem cell20_42290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_42290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42290 prefixEnd_42290 := by exact prefixLift 42290
  have htrace : WordTrace (prefixWord ++ tailWord_42290) baseStart_42290 baseEnd_42290 := by
    simpa [prefixWord, tailWord_42290, baseEnd_42290] using wordTrace_append hprefix tailTrace_42290
  have hstable : (prefixWord ++ tailWord_42290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42290).length < 2 ^ (prefixWord ++ tailWord_42290).sum := by decide
  have hdescent : baseEnd_42290 < baseStart_42290 := by decide
  rcases family_descends (prefixWord ++ tailWord_42290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42311 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_42311 : Nat := 118140960795 + 42311 * 2 ^ 59
def prefixEnd_42311 : Nat := 4983230072969 + 3 ^ 40 * 42311 * 2
def baseEnd_42311 : Nat := 19311893308879281527041

theorem tailTrace_42311 : CollatzResearch.WordTrace tailWord_42311 prefixEnd_42311 19311893308879281527041 := by
  unfold tailWord_42311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543208949721947988606787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1028805966481298659071191 1543208949721947988606787)
  ·
    refine ⟨2314813424582921982910181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1543208949721947988606787 2314813424582921982910181)
    ·
      refine ⟨434027517109297871795659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2314813424582921982910181 434027517109297871795659)
      ·
        refine ⟨651041275663946807693489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434027517109297871795659 651041275663946807693489)
        ·
          refine ⟨488280956747960105770117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651041275663946807693489 488280956747960105770117)
          ·
            refine ⟨91552679390242519831897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 488280956747960105770117 91552679390242519831897)
            ·
              refine ⟨68664509542681889873923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91552679390242519831897 68664509542681889873923)
              ·
                refine ⟨102996764314022834810885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68664509542681889873923 102996764314022834810885)
                ·
                  refine ⟨19311893308879281527041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102996764314022834810885 19311893308879281527041)
                  ·
                    rfl

theorem cell20_42311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_42311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42311 prefixEnd_42311 := by exact prefixLift 42311
  have htrace : WordTrace (prefixWord ++ tailWord_42311) baseStart_42311 baseEnd_42311 := by
    simpa [prefixWord, tailWord_42311, baseEnd_42311] using wordTrace_append hprefix tailTrace_42311
  have hstable : (prefixWord ++ tailWord_42311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42311).length < 2 ^ (prefixWord ++ tailWord_42311).sum := by decide
  have hdescent : baseEnd_42311 < baseStart_42311 := by decide
  rcases family_descends (prefixWord ++ tailWord_42311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42317 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 3]
def baseStart_42317 : Nat := 118140960795 + 42317 * 2 ^ 59
def prefixEnd_42317 : Nat := 4983230072969 + 3 ^ 40 * 42317 * 2
def baseEnd_42317 : Nat := 19314631872369927327017

theorem tailTrace_42317 : CollatzResearch.WordTrace tailWord_42317 prefixEnd_42317 19314631872369927327017 := by
  unfold tailWord_42317
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543427787700211013325205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1028951858466807342216803 1543427787700211013325205)
  ·
    refine ⟨72348177548447391249619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1543427787700211013325205 72348177548447391249619)
    ·
      refine ⟨108522266322671086874429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72348177548447391249619 108522266322671086874429)
      ·
        refine ⟨40695849871001657577911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108522266322671086874429 40695849871001657577911)
        ·
          refine ⟨61043774806502486366867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40695849871001657577911 61043774806502486366867)
          ·
            refine ⟨91565662209753729550301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61043774806502486366867 91565662209753729550301)
            ·
              refine ⟨34337123328657648581363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91565662209753729550301 34337123328657648581363)
              ·
                refine ⟨51505684992986472872045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34337123328657648581363 51505684992986472872045)
                ·
                  refine ⟨19314631872369927327017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51505684992986472872045 19314631872369927327017)
                  ·
                    rfl

theorem cell20_42317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_42317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42317 prefixEnd_42317 := by exact prefixLift 42317
  have htrace : WordTrace (prefixWord ++ tailWord_42317) baseStart_42317 baseEnd_42317 := by
    simpa [prefixWord, tailWord_42317, baseEnd_42317] using wordTrace_append hprefix tailTrace_42317
  have hstable : (prefixWord ++ tailWord_42317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42317).length < 2 ^ (prefixWord ++ tailWord_42317).sum := by decide
  have hdescent : baseEnd_42317 < baseStart_42317 := by decide
  rcases family_descends (prefixWord ++ tailWord_42317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42363 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 3]
def baseStart_42363 : Nat := 118140960795 + 42363 * 2 ^ 59
def prefixEnd_42363 : Nat := 4983230072969 + 3 ^ 40 * 42363 * 2
def baseEnd_42363 : Nat := 19335627525798211793495

theorem tailTrace_42363 : CollatzResearch.WordTrace tailWord_42363 prefixEnd_42363 19335627525798211793495 := by
  unfold tailWord_42363
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545105545533560869499743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1030070363689040579666495 1545105545533560869499743)
  ·
    refine ⟨2317658318300341304249615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545105545533560869499743 2317658318300341304249615)
    ·
      refine ⟨3476487477450511956374423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317658318300341304249615 3476487477450511956374423)
      ·
        refine ⟨5214731216175767934561635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476487477450511956374423 5214731216175767934561635)
        ·
          refine ⟨7822096824263651901842453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214731216175767934561635 7822096824263651901842453)
          ·
            refine ⟨366660788637358682898865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7822096824263651901842453 366660788637358682898865)
            ·
              refine ⟨274995591478019012174149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366660788637358682898865 274995591478019012174149)
              ·
                refine ⟨51561673402128564782653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274995591478019012174149 51561673402128564782653)
                ·
                  refine ⟨19335627525798211793495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51561673402128564782653 19335627525798211793495)
                  ·
                    rfl

theorem cell20_42363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_42363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42363 prefixEnd_42363 := by exact prefixLift 42363
  have htrace : WordTrace (prefixWord ++ tailWord_42363) baseStart_42363 baseEnd_42363 := by
    simpa [prefixWord, tailWord_42363, baseEnd_42363] using wordTrace_append hprefix tailTrace_42363
  have hstable : (prefixWord ++ tailWord_42363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42363).length < 2 ^ (prefixWord ++ tailWord_42363).sum := by decide
  have hdescent : baseEnd_42363 < baseStart_42363 := by decide
  rcases family_descends (prefixWord ++ tailWord_42363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
