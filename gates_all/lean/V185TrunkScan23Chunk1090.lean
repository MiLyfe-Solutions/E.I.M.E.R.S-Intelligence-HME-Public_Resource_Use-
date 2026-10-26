import V185TrunkScan23Chunk1089

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6453458 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_6453458 : Nat := 118140960795 + 6453458 * 2 ^ 59
def prefixEnd_6453458 : Nat := 4983230072969 + 3 ^ 40 * 6453458 * 2
def baseEnd_6453458 : Nat := 1104575279201039016532031

theorem tailTrace_6453458 : CollatzResearch.WordTrace tailWord_6453458 prefixEnd_6453458 1104575279201039016532031 := by
  unfold tailWord_6453458
  simp only [CollatzResearch.WordTrace]
  refine ⟨58844237563557825930960257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156917966836154202482560685 58844237563557825930960257)
  ·
    refine ⟨44133178172668369448220193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58844237563557825930960257 44133178172668369448220193)
    ·
      refine ⟨33099883629501277086165145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44133178172668369448220193 33099883629501277086165145)
      ·
        refine ⟨24824912722125957814623859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33099883629501277086165145 24824912722125957814623859)
        ·
          refine ⟨37237369083188936721935789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24824912722125957814623859 37237369083188936721935789)
          ·
            refine ⟨13964013406195851270725921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37237369083188936721935789 13964013406195851270725921)
            ·
              refine ⟨10473010054646888453044441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13964013406195851270725921 10473010054646888453044441)
              ·
                refine ⟨7854757540985166339783331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10473010054646888453044441 7854757540985166339783331)
                ·
                  refine ⟨11782136311477749509674997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7854757540985166339783331 11782136311477749509674997)
                  ·
                    refine ⟨1104575279201039016532031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11782136311477749509674997 1104575279201039016532031)
                    ·
                      rfl

theorem cell23_6453458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_6453458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453458 prefixEnd_6453458 := by exact prefixLift 6453458
  have htrace : WordTrace (prefixWord ++ tailWord_6453458) baseStart_6453458 baseEnd_6453458 := by
    simpa [prefixWord, tailWord_6453458, baseEnd_6453458] using wordTrace_append hprefix tailTrace_6453458
  have hstable : (prefixWord ++ tailWord_6453458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453458).length < 2 ^ (prefixWord ++ tailWord_6453458).sum := by decide
  have hdescent : baseEnd_6453458 < baseStart_6453458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453561 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 1, 8]
def baseStart_6453561 : Nat := 118140960795 + 6453561 * 2 ^ 59
def prefixEnd_6453561 : Nat := 4983230072969 + 3 ^ 40 * 6453561 * 2
def baseEnd_6453561 : Nat := 1104592908703510048869373

theorem tailTrace_6453561 : CollatzResearch.WordTrace tailWord_6453561 prefixEnd_6453561 1104592908703510048869373 := by
  unfold tailWord_6453561
  simp only [CollatzResearch.WordTrace]
  refine ⟨235380706972858152314840537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156920471315238768209893691 235380706972858152314840537)
  ·
    refine ⟨176535530229643614236130403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235380706972858152314840537 176535530229643614236130403)
    ·
      refine ⟨264803295344465421354195605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176535530229643614236130403 264803295344465421354195605)
      ·
        refine ⟨12412654469271816625977919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 264803295344465421354195605 12412654469271816625977919)
        ·
          refine ⟨18618981703907724938966879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12412654469271816625977919 18618981703907724938966879)
          ·
            refine ⟨27928472555861587408450319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18618981703907724938966879 27928472555861587408450319)
            ·
              refine ⟨41892708833792381112675479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27928472555861587408450319 41892708833792381112675479)
              ·
                refine ⟨62839063250688571669013219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41892708833792381112675479 62839063250688571669013219)
                ·
                  refine ⟨94258594876032857503519829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62839063250688571669013219 94258594876032857503519829)
                  ·
                    refine ⟨1104592908703510048869373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94258594876032857503519829 1104592908703510048869373)
                    ·
                      rfl

theorem cell23_6453561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_6453561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453561 prefixEnd_6453561 := by exact prefixLift 6453561
  have htrace : WordTrace (prefixWord ++ tailWord_6453561) baseStart_6453561 baseEnd_6453561 := by
    simpa [prefixWord, tailWord_6453561, baseEnd_6453561] using wordTrace_append hprefix tailTrace_6453561
  have hstable : (prefixWord ++ tailWord_6453561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453561).length < 2 ^ (prefixWord ++ tailWord_6453561).sum := by decide
  have hdescent : baseEnd_6453561 < baseStart_6453561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453589 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_6453589 : Nat := 118140960795 + 6453589 * 2 ^ 59
def prefixEnd_6453589 : Nat := 4983230072969 + 3 ^ 40 * 6453589 * 2
def baseEnd_6453589 : Nat := 3313793103568856037057991

theorem tailTrace_6453589 : CollatzResearch.WordTrace tailWord_6453589 prefixEnd_6453589 3313793103568856037057991 := by
  unfold tailWord_6453589
  simp only [CollatzResearch.WordTrace]
  refine ⟨235381728216756713096859821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156921152144504475397906547 235381728216756713096859821)
  ·
    refine ⟨88268148081283767411322433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235381728216756713096859821 88268148081283767411322433)
    ·
      refine ⟨66201111060962825558491825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88268148081283767411322433 66201111060962825558491825)
      ·
        refine ⟨49650833295722119168868869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66201111060962825558491825 49650833295722119168868869)
        ·
          refine ⟨9309531242947897344162913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49650833295722119168868869 9309531242947897344162913)
          ·
            refine ⟨6982148432210923008122185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9309531242947897344162913 6982148432210923008122185)
            ·
              refine ⟨5236611324158192256091639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6982148432210923008122185 5236611324158192256091639)
              ·
                refine ⟨7854916986237288384137459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5236611324158192256091639 7854916986237288384137459)
                ·
                  refine ⟨11782375479355932576206189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7854916986237288384137459 11782375479355932576206189)
                  ·
                    refine ⟨4418390804758474716077321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11782375479355932576206189 4418390804758474716077321)
                    ·
                      refine ⟨3313793103568856037057991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418390804758474716077321 3313793103568856037057991)
                      ·
                        rfl

theorem cell23_6453589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_6453589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453589 prefixEnd_6453589 := by exact prefixLift 6453589
  have htrace : WordTrace (prefixWord ++ tailWord_6453589) baseStart_6453589 baseEnd_6453589 := by
    simpa [prefixWord, tailWord_6453589, baseEnd_6453589] using wordTrace_append hprefix tailTrace_6453589
  have hstable : (prefixWord ++ tailWord_6453589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453589).length < 2 ^ (prefixWord ++ tailWord_6453589).sum := by decide
  have hdescent : baseEnd_6453589 < baseStart_6453589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453596 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6453596 : Nat := 118140960795 + 6453596 * 2 ^ 59
def prefixEnd_6453596 : Nat := 4983230072969 + 3 ^ 40 * 6453596 * 2
def baseEnd_6453596 : Nat := 3313796697933437509670459

theorem tailTrace_6453596 : CollatzResearch.WordTrace tailWord_6453596 prefixEnd_6453596 3313796697933437509670459 := by
  unfold tailWord_6453596
  simp only [CollatzResearch.WordTrace]
  refine ⟨117690991763865676646182321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156921322351820902194909761 117690991763865676646182321)
  ·
    refine ⟨88268243822899257484636741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117690991763865676646182321 88268243822899257484636741)
    ·
      refine ⟨16550295716793610778369389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88268243822899257484636741 16550295716793610778369389)
      ·
        refine ⟨6206360893797604041888521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16550295716793610778369389 6206360893797604041888521)
        ·
          refine ⟨4654770670348203031416391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6206360893797604041888521 4654770670348203031416391)
          ·
            refine ⟨6982156005522304547124587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4654770670348203031416391 6982156005522304547124587)
            ·
              refine ⟨10473234008283456820686881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982156005522304547124587 10473234008283456820686881)
              ·
                refine ⟨7854925506212592615515161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10473234008283456820686881 7854925506212592615515161)
                ·
                  refine ⟨5891194129659444461636371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7854925506212592615515161 5891194129659444461636371)
                  ·
                    refine ⟨8836791194489166692454557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5891194129659444461636371 8836791194489166692454557)
                    ·
                      refine ⟨3313796697933437509670459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836791194489166692454557 3313796697933437509670459)
                      ·
                        rfl

theorem cell23_6453596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6453596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453596 prefixEnd_6453596 := by exact prefixLift 6453596
  have htrace : WordTrace (prefixWord ++ tailWord_6453596) baseStart_6453596 baseEnd_6453596 := by
    simpa [prefixWord, tailWord_6453596, baseEnd_6453596] using wordTrace_append hprefix tailTrace_6453596
  have hstable : (prefixWord ++ tailWord_6453596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453596).length < 2 ^ (prefixWord ++ tailWord_6453596).sum := by decide
  have hdescent : baseEnd_6453596 < baseStart_6453596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453602 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_6453602 : Nat := 118140960795 + 6453602 * 2 ^ 59
def prefixEnd_6453602 : Nat := 4983230072969 + 3 ^ 40 * 6453602 * 2
def baseEnd_6453602 : Nat := 3313799778817364486195431

theorem tailTrace_6453602 : CollatzResearch.WordTrace tailWord_6453602 prefixEnd_6453602 3313799778817364486195431 := by
  unfold tailWord_6453602
  simp only [CollatzResearch.WordTrace]
  refine ⟨58845550591427404079270765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156921468243806410878055373 58845550591427404079270765)
  ·
    refine ⟨22067081471785276529726537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58845550591427404079270765 22067081471785276529726537)
    ·
      refine ⟨16550311103838957397294903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22067081471785276529726537 16550311103838957397294903)
      ·
        refine ⟨24825466655758436095942355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16550311103838957397294903 24825466655758436095942355)
        ·
          refine ⟨37238199983637654143913533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24825466655758436095942355 37238199983637654143913533)
          ·
            refine ⟨13964324993864120303967575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37238199983637654143913533 13964324993864120303967575)
            ·
              refine ⟨20946487490796180455951363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13964324993864120303967575 20946487490796180455951363)
              ·
                refine ⟨31419731236194270683927045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20946487490796180455951363 31419731236194270683927045)
                ·
                  refine ⟨5891199606786425753236321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31419731236194270683927045 5891199606786425753236321)
                  ·
                    refine ⟨4418399705089819314927241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5891199606786425753236321 4418399705089819314927241)
                    ·
                      refine ⟨3313799778817364486195431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418399705089819314927241 3313799778817364486195431)
                      ·
                        rfl

theorem cell23_6453602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_6453602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453602 prefixEnd_6453602 := by exact prefixLift 6453602
  have htrace : WordTrace (prefixWord ++ tailWord_6453602) baseStart_6453602 baseEnd_6453602 := by
    simpa [prefixWord, tailWord_6453602, baseEnd_6453602] using wordTrace_append hprefix tailTrace_6453602
  have hstable : (prefixWord ++ tailWord_6453602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453602).length < 2 ^ (prefixWord ++ tailWord_6453602).sum := by decide
  have hdescent : baseEnd_6453602 < baseStart_6453602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453608 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 7]
def baseStart_6453608 : Nat := 118140960795 + 6453608 * 2 ^ 59
def prefixEnd_6453608 : Nat := 4983230072969 + 3 ^ 40 * 6453608 * 2
def baseEnd_6453608 : Nat := 368200317744587940302267

theorem tailTrace_6453608 : CollatzResearch.WordTrace tailWord_6453608 prefixEnd_6453608 368200317744587940302267 := by
  unfold tailWord_6453608
  simp only [CollatzResearch.WordTrace]
  refine ⟨117691210601843939670900739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156921614135791919561200985 117691210601843939670900739)
  ·
    refine ⟨176536815902765909506351109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117691210601843939670900739 176536815902765909506351109)
    ·
      refine ⟨33100652981768608032440833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176536815902765909506351109 33100652981768608032440833)
      ·
        refine ⟨24825489736326456024330625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33100652981768608032440833 24825489736326456024330625)
        ·
          refine ⟨18619117302244842018247969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24825489736326456024330625 18619117302244842018247969)
          ·
            refine ⟨13964337976683631513685977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18619117302244842018247969 13964337976683631513685977)
            ·
              refine ⟨10473253482512723635264483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13964337976683631513685977 10473253482512723635264483)
              ·
                refine ⟨15709880223769085452896725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10473253482512723635264483 15709880223769085452896725)
                ·
                  refine ⟨368200317744587940302267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15709880223769085452896725 368200317744587940302267)
                  ·
                    rfl

theorem cell23_6453608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 7].length) (baseStart_6453608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453608 prefixEnd_6453608 := by exact prefixLift 6453608
  have htrace : WordTrace (prefixWord ++ tailWord_6453608) baseStart_6453608 baseEnd_6453608 := by
    simpa [prefixWord, tailWord_6453608, baseEnd_6453608] using wordTrace_append hprefix tailTrace_6453608
  have hstable : (prefixWord ++ tailWord_6453608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453608).length < 2 ^ (prefixWord ++ tailWord_6453608).sum := by decide
  have hdescent : baseEnd_6453608 < baseStart_6453608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453618 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_6453618 : Nat := 118140960795 + 6453618 * 2 ^ 59
def prefixEnd_6453618 : Nat := 4983230072969 + 3 ^ 40 * 6453618 * 2
def baseEnd_6453618 : Nat := 3313807994507836423595357

theorem tailTrace_6453618 : CollatzResearch.WordTrace tailWord_6453618 prefixEnd_6453618 3313807994507836423595357 := by
  unfold tailWord_6453618
  simp only [CollatzResearch.WordTrace]
  refine ⟨58845696483412912762416377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156921857289101100699777005 58845696483412912762416377)
  ·
    refine ⟨44134272362559684571812283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58845696483412912762416377 44134272362559684571812283)
    ·
      refine ⟨66201408543839526857718425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44134272362559684571812283 66201408543839526857718425)
      ·
        refine ⟨49651056407879645143288819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66201408543839526857718425 49651056407879645143288819)
        ·
          refine ⟨74476584611819467714933229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49651056407879645143288819 74476584611819467714933229)
          ·
            refine ⟨27928719229432300393099961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74476584611819467714933229 27928719229432300393099961)
            ·
              refine ⟨20946539422074225294824971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27928719229432300393099961 20946539422074225294824971)
              ·
                refine ⟨31419809133111337942237457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20946539422074225294824971 31419809133111337942237457)
                ·
                  refine ⟨23564856849833503456678093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31419809133111337942237457 23564856849833503456678093)
                  ·
                    refine ⟨8836821318687563796254285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23564856849833503456678093 8836821318687563796254285)
                    ·
                      refine ⟨3313807994507836423595357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836821318687563796254285 3313807994507836423595357)
                      ·
                        rfl

theorem cell23_6453618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_6453618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453618 prefixEnd_6453618 := by exact prefixLift 6453618
  have htrace : WordTrace (prefixWord ++ tailWord_6453618) baseStart_6453618 baseEnd_6453618 := by
    simpa [prefixWord, tailWord_6453618, baseEnd_6453618] using wordTrace_append hprefix tailTrace_6453618
  have hstable : (prefixWord ++ tailWord_6453618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453618).length < 2 ^ (prefixWord ++ tailWord_6453618).sum := by decide
  have hdescent : baseEnd_6453618 < baseStart_6453618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453658 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6453658 : Nat := 118140960795 + 6453658 * 2 ^ 59
def prefixEnd_6453658 : Nat := 4983230072969 + 3 ^ 40 * 6453658 * 2
def baseEnd_6453658 : Nat := 3313828533734016267095173

theorem tailTrace_6453658 : CollatzResearch.WordTrace tailWord_6453658 prefixEnd_6453658 3313828533734016267095173 := by
  unfold tailWord_6453658
  simp only [CollatzResearch.WordTrace]
  refine ⟨58846061213376684470280407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156922829902337825254081085 58846061213376684470280407)
  ·
    refine ⟨88269091820065026705420611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58846061213376684470280407 88269091820065026705420611)
    ·
      refine ⟨132403637730097540058130917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88269091820065026705420611 132403637730097540058130917)
      ·
        refine ⟨24825682074393288760899547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132403637730097540058130917 24825682074393288760899547)
        ·
          refine ⟨37238523111589933141349321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24825682074393288760899547 37238523111589933141349321)
          ·
            refine ⟨27928892333692449856011991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37238523111589933141349321 27928892333692449856011991)
            ·
              refine ⟨41893338500538674784017987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27928892333692449856011991 41893338500538674784017987)
              ·
                refine ⟨62840007750808012176026981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41893338500538674784017987 62840007750808012176026981)
                ·
                  refine ⟨11782501453276502283005059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62840007750808012176026981 11782501453276502283005059)
                  ·
                    refine ⟨17673752179914753424507589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11782501453276502283005059 17673752179914753424507589)
                    ·
                      refine ⟨3313828533734016267095173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17673752179914753424507589 3313828533734016267095173)
                      ·
                        rfl

theorem cell23_6453658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6453658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453658 prefixEnd_6453658 := by exact prefixLift 6453658
  have htrace : WordTrace (prefixWord ++ tailWord_6453658) baseStart_6453658 baseEnd_6453658 := by
    simpa [prefixWord, tailWord_6453658, baseEnd_6453658] using wordTrace_append hprefix tailTrace_6453658
  have hstable : (prefixWord ++ tailWord_6453658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453658).length < 2 ^ (prefixWord ++ tailWord_6453658).sum := by decide
  have hdescent : baseEnd_6453658 < baseStart_6453658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453665 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6453665 : Nat := 118140960795 + 6453665 * 2 ^ 59
def prefixEnd_6453665 : Nat := 4983230072969 + 3 ^ 40 * 6453665 * 2
def baseEnd_6453665 : Nat := 3313832128098597739707641

theorem tailTrace_6453665 : CollatzResearch.WordTrace tailWord_6453665 prefixEnd_6453665 3313832128098597739707641 := by
  unfold tailWord_6453665
  simp only [CollatzResearch.WordTrace]
  refine ⟨235384500164481378076626449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156923000109654252051084299 235384500164481378076626449)
  ·
    refine ⟨176538375123361033557469837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235384500164481378076626449 176538375123361033557469837)
    ·
      refine ⟨66201890671260387584051189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176538375123361033557469837 66201890671260387584051189)
      ·
        refine ⟨6206427250430661336004799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66201890671260387584051189 6206427250430661336004799)
        ·
          refine ⟨9309640875645992004007199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206427250430661336004799 9309640875645992004007199)
          ·
            refine ⟨13964461313468988006010799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9309640875645992004007199 13964461313468988006010799)
            ·
              refine ⟨20946691970203482009016199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13964461313468988006010799 20946691970203482009016199)
              ·
                refine ⟨31420037955305223013524299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20946691970203482009016199 31420037955305223013524299)
                ·
                  refine ⟨47130056932957834520286449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31420037955305223013524299 47130056932957834520286449)
                  ·
                    refine ⟨35347542699718375890214837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47130056932957834520286449 35347542699718375890214837)
                    ·
                      refine ⟨3313832128098597739707641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35347542699718375890214837 3313832128098597739707641)
                      ·
                        rfl

theorem cell23_6453665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6453665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453665 prefixEnd_6453665 := by exact prefixLift 6453665
  have htrace : WordTrace (prefixWord ++ tailWord_6453665) baseStart_6453665 baseEnd_6453665 := by
    simpa [prefixWord, tailWord_6453665, baseEnd_6453665] using wordTrace_append hprefix tailTrace_6453665
  have hstable : (prefixWord ++ tailWord_6453665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453665).length < 2 ^ (prefixWord ++ tailWord_6453665).sum := by decide
  have hdescent : baseEnd_6453665 < baseStart_6453665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453735 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6453735 : Nat := 118140960795 + 6453735 * 2 ^ 59
def prefixEnd_6453735 : Nat := 4983230072969 + 3 ^ 40 * 6453735 * 2
def baseEnd_6453735 : Nat := 3313868071744412465832319

theorem tailTrace_6453735 : CollatzResearch.WordTrace tailWord_6453735 prefixEnd_6453735 3313868071744412465832319 := by
  unfold tailWord_6453735
  simp only [CollatzResearch.WordTrace]
  refine ⟨235387053274227780031674659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156924702182818520021116439 235387053274227780031674659)
  ·
    refine ⟨353080579911341670047511989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235387053274227780031674659 353080579911341670047511989)
    ·
      refine ⟨33101304366688281566954249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 353080579911341670047511989 33101304366688281566954249)
      ·
        refine ⟨24825978275016211175215687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33101304366688281566954249 24825978275016211175215687)
        ·
          refine ⟨37238967412524316762823531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24825978275016211175215687 37238967412524316762823531)
          ·
            refine ⟨55858451118786475144235297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37238967412524316762823531 55858451118786475144235297)
            ·
              refine ⟨41893838339089856358176473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55858451118786475144235297 41893838339089856358176473)
              ·
                refine ⟨31420378754317392268632355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41893838339089856358176473 31420378754317392268632355)
                ·
                  refine ⟨47130568131476088402948533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31420378754317392268632355 47130568131476088402948533)
                  ·
                    refine ⟨4418490762325883287776425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47130568131476088402948533 4418490762325883287776425)
                    ·
                      refine ⟨3313868071744412465832319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418490762325883287776425 3313868071744412465832319)
                      ·
                        rfl

theorem cell23_6453735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6453735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453735 prefixEnd_6453735 := by exact prefixLift 6453735
  have htrace : WordTrace (prefixWord ++ tailWord_6453735) baseStart_6453735 baseEnd_6453735 := by
    simpa [prefixWord, tailWord_6453735, baseEnd_6453735] using wordTrace_append hprefix tailTrace_6453735
  have hstable : (prefixWord ++ tailWord_6453735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453735).length < 2 ^ (prefixWord ++ tailWord_6453735).sum := by decide
  have hdescent : baseEnd_6453735 < baseStart_6453735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453742 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_6453742 : Nat := 118140960795 + 6453742 * 2 ^ 59
def prefixEnd_6453742 : Nat := 4983230072969 + 3 ^ 40 * 6453742 * 2
def baseEnd_6453742 : Nat := 3313871666108993938444787

theorem tailTrace_6453742 : CollatzResearch.WordTrace tailWord_6453742 prefixEnd_6453742 3313871666108993938444787 := by
  unfold tailWord_6453742
  simp only [CollatzResearch.WordTrace]
  refine ⟨29423413573150302528397435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156924872390134946818119653 29423413573150302528397435)
  ·
    refine ⟨44135120359725453792596153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29423413573150302528397435 44135120359725453792596153)
    ·
      refine ⟨33101340269794090344447115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44135120359725453792596153 33101340269794090344447115)
      ·
        refine ⟨49652010404691135516670673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33101340269794090344447115 49652010404691135516670673)
        ·
          refine ⟨37239007803518351637503005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49652010404691135516670673 37239007803518351637503005)
          ·
            refine ⟨13964627926319381864063627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37239007803518351637503005 13964627926319381864063627)
            ·
              refine ⟨20946941889479072796095441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13964627926319381864063627 20946941889479072796095441)
              ·
                refine ⟨15710206417109304597071581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20946941889479072796095441 15710206417109304597071581)
                ·
                  refine ⟨5891327406415989223901843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15710206417109304597071581 5891327406415989223901843)
                  ·
                    refine ⟨8836991109623983835852765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5891327406415989223901843 8836991109623983835852765)
                    ·
                      refine ⟨3313871666108993938444787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8836991109623983835852765 3313871666108993938444787)
                      ·
                        rfl

theorem cell23_6453742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_6453742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453742 prefixEnd_6453742 := by exact prefixLift 6453742
  have htrace : WordTrace (prefixWord ++ tailWord_6453742) baseStart_6453742 baseEnd_6453742 := by
    simpa [prefixWord, tailWord_6453742, baseEnd_6453742] using wordTrace_append hprefix tailTrace_6453742
  have hstable : (prefixWord ++ tailWord_6453742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453742).length < 2 ^ (prefixWord ++ tailWord_6453742).sum := by decide
  have hdescent : baseEnd_6453742 < baseStart_6453742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453766 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_6453766 : Nat := 118140960795 + 6453766 * 2 ^ 59
def prefixEnd_6453766 : Nat := 4983230072969 + 3 ^ 40 * 6453766 * 2
def baseEnd_6453766 : Nat := 368209332182744649393853

theorem tailTrace_6453766 : CollatzResearch.WordTrace tailWord_6453766 prefixEnd_6453766 368209332182744649393853 := by
  unfold tailWord_6453766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355880748034858510189161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156925455958076981550702101 7355880748034858510189161)
  ·
    refine ⟨5516910561026143882641871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7355880748034858510189161 5516910561026143882641871)
    ·
      refine ⟨8275365841539215823962807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5516910561026143882641871 8275365841539215823962807)
      ·
        refine ⟨12413048762308823735944211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8275365841539215823962807 12413048762308823735944211)
        ·
          refine ⟨18619573143463235603916317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12413048762308823735944211 18619573143463235603916317)
          ·
            refine ⟨6982339928798713351468619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18619573143463235603916317 6982339928798713351468619)
            ·
              refine ⟨10473509893198070027202929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982339928798713351468619 10473509893198070027202929)
              ·
                refine ⟨7855132419898552520402197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10473509893198070027202929 7855132419898552520402197)
                ·
                  refine ⟨368209332182744649393853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7855132419898552520402197 368209332182744649393853)
                  ·
                    rfl

theorem cell23_6453766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_6453766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453766 prefixEnd_6453766 := by exact prefixLift 6453766
  have htrace : WordTrace (prefixWord ++ tailWord_6453766) baseStart_6453766 baseEnd_6453766 := by
    simpa [prefixWord, tailWord_6453766, baseEnd_6453766] using wordTrace_append hprefix tailTrace_6453766
  have hstable : (prefixWord ++ tailWord_6453766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453766).length < 2 ^ (prefixWord ++ tailWord_6453766).sum := by decide
  have hdescent : baseEnd_6453766 < baseStart_6453766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453768 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_6453768 : Nat := 118140960795 + 6453768 * 2 ^ 59
def prefixEnd_6453768 : Nat := 4983230072969 + 3 ^ 40 * 6453768 * 2
def baseEnd_6453768 : Nat := 3313885016606010836719667

theorem tailTrace_6453768 : CollatzResearch.WordTrace tailWord_6453768 prefixEnd_6453768 3313885016606010836719667 := by
  unfold tailWord_6453768
  simp only [CollatzResearch.WordTrace]
  refine ⟨117694128441554113333812979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156925504588738817778417305 117694128441554113333812979)
  ·
    refine ⟨176541192662331170000719469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117694128441554113333812979 176541192662331170000719469)
    ·
      refine ⟨66202947248374188750269801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176541192662331170000719469 66202947248374188750269801)
      ·
        refine ⟨49652210436280641562702351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66202947248374188750269801 49652210436280641562702351)
        ·
          refine ⟨74478315654420962344053527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49652210436280641562702351 74478315654420962344053527)
          ·
            refine ⟨111717473481631443516080291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74478315654420962344053527 111717473481631443516080291)
            ·
              refine ⟨167576210222447165274120437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111717473481631443516080291 167576210222447165274120437)
              ·
                refine ⟨15710269708354421744448791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167576210222447165274120437 15710269708354421744448791)
                ·
                  refine ⟨23565404562531632616673187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15710269708354421744448791 23565404562531632616673187)
                  ·
                    refine ⟨35348106843797448925009781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23565404562531632616673187 35348106843797448925009781)
                    ·
                      refine ⟨3313885016606010836719667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35348106843797448925009781 3313885016606010836719667)
                      ·
                        rfl

theorem cell23_6453768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_6453768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453768 prefixEnd_6453768 := by exact prefixLift 6453768
  have htrace : WordTrace (prefixWord ++ tailWord_6453768) baseStart_6453768 baseEnd_6453768 := by
    simpa [prefixWord, tailWord_6453768, baseEnd_6453768] using wordTrace_append hprefix tailTrace_6453768
  have hstable : (prefixWord ++ tailWord_6453768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453768).length < 2 ^ (prefixWord ++ tailWord_6453768).sum := by decide
  have hdescent : baseEnd_6453768 < baseStart_6453768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453792 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 1, 6]
def baseStart_6453792 : Nat := 118140960795 + 6453792 * 2 ^ 59
def prefixEnd_6453792 : Nat := 4983230072969 + 3 ^ 40 * 6453792 * 2
def baseEnd_6453792 : Nat := 1104632446713906247606519

theorem tailTrace_6453792 : CollatzResearch.WordTrace tailWord_6453792 prefixEnd_6453792 1104632446713906247606519 := by
  unfold tailWord_6453792
  simp only [CollatzResearch.WordTrace]
  refine ⟨117694566117510639383249815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156926088156680852510999753 117694566117510639383249815)
  ·
    refine ⟨176541849176265959074874723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117694566117510639383249815 176541849176265959074874723)
    ·
      refine ⟨264812773764398938612312085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176541849176265959074874723 264812773764398938612312085)
      ·
        refine ⟨12413098770206200247452129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 264812773764398938612312085 12413098770206200247452129)
        ·
          refine ⟨9309824077654650185589097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12413098770206200247452129 9309824077654650185589097)
          ·
            refine ⟨6982368058240987639191823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9309824077654650185589097 6982368058240987639191823)
            ·
              refine ⟨10473552087361481458787735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982368058240987639191823 10473552087361481458787735)
              ·
                refine ⟨15710328131042222188181603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10473552087361481458787735 15710328131042222188181603)
                ·
                  refine ⟨23565492196563333282272405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15710328131042222188181603 23565492196563333282272405)
                  ·
                    refine ⟨1104632446713906247606519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23565492196563333282272405 1104632446713906247606519)
                    ·
                      rfl

theorem cell23_6453792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_6453792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453792 prefixEnd_6453792 := by exact prefixLift 6453792
  have htrace : WordTrace (prefixWord ++ tailWord_6453792) baseStart_6453792 baseEnd_6453792 := by
    simpa [prefixWord, tailWord_6453792, baseEnd_6453792] using wordTrace_append hprefix tailTrace_6453792
  have hstable : (prefixWord ++ tailWord_6453792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453792).length < 2 ^ (prefixWord ++ tailWord_6453792).sum := by decide
  have hdescent : baseEnd_6453792 < baseStart_6453792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453795 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 4]
def baseStart_6453795 : Nat := 118140960795 + 6453795 * 2 ^ 59
def prefixEnd_6453795 : Nat := 4983230072969 + 3 ^ 40 * 6453795 * 2
def baseEnd_6453795 : Nat := 3313898880583682231082043

theorem tailTrace_6453795 : CollatzResearch.WordTrace tailWord_6453795 prefixEnd_6453795 3313898880583682231082043 := by
  unfold tailWord_6453795
  simp only [CollatzResearch.WordTrace]
  refine ⟨235389241654010410278858839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156926161102673606852572559 235389241654010410278858839)
  ·
    refine ⟨353083862481015615418288259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235389241654010410278858839 353083862481015615418288259)
    ·
      refine ⟨529625793721523423127432389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353083862481015615418288259 529625793721523423127432389)
      ·
        refine ⟨99304836322785641836393573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 529625793721523423127432389 99304836322785641836393573)
        ·
          refine ⟨18619656810522307844323795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99304836322785641836393573 18619656810522307844323795)
          ·
            refine ⟨27929485215783461766485693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18619656810522307844323795 27929485215783461766485693)
            ·
              refine ⟨10473556955918798162432135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27929485215783461766485693 10473556955918798162432135)
              ·
                refine ⟨15710335433878197243648203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10473556955918798162432135 15710335433878197243648203)
                ·
                  refine ⟨23565503150817295865472305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15710335433878197243648203 23565503150817295865472305)
                  ·
                    refine ⟨17674127363112971899104229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23565503150817295865472305 17674127363112971899104229)
                    ·
                      refine ⟨3313898880583682231082043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17674127363112971899104229 3313898880583682231082043)
                      ·
                        rfl

theorem cell23_6453795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_6453795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453795 prefixEnd_6453795 := by exact prefixLift 6453795
  have htrace : WordTrace (prefixWord ++ tailWord_6453795) baseStart_6453795 baseEnd_6453795 := by
    simpa [prefixWord, tailWord_6453795, baseEnd_6453795] using wordTrace_append hprefix tailTrace_6453795
  have hstable : (prefixWord ++ tailWord_6453795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453795).length < 2 ^ (prefixWord ++ tailWord_6453795).sum := by decide
  have hdescent : baseEnd_6453795 < baseStart_6453795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453802 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6453802 : Nat := 118140960795 + 6453802 * 2 ^ 59
def prefixEnd_6453802 : Nat := 4983230072969 + 3 ^ 40 * 6453802 * 2
def baseEnd_6453802 : Nat := 3313902474948263703694511

theorem tailTrace_6453802 : CollatzResearch.WordTrace tailWord_6453802 prefixEnd_6453802 3313902474948263703694511 := by
  unfold tailWord_6453802
  simp only [CollatzResearch.WordTrace]
  refine ⟨58847374241246262618590915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156926331309990033649575773 58847374241246262618590915)
  ·
    refine ⟨88271061361869393927886373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58847374241246262618590915 88271061361869393927886373)
    ·
      refine ⟨16550824005350511361478695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88271061361869393927886373 16550824005350511361478695)
      ·
        refine ⟨24826236008025767042218043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16550824005350511361478695 24826236008025767042218043)
        ·
          refine ⟨37239354012038650563327065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24826236008025767042218043 37239354012038650563327065)
          ·
            refine ⟨27929515509028987922495299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37239354012038650563327065 27929515509028987922495299)
            ·
              refine ⟨41894273263543481883742949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27929515509028987922495299 41894273263543481883742949)
              ·
                refine ⟨7855176236914402853201803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41894273263543481883742949 7855176236914402853201803)
                ·
                  refine ⟨11782764355371604279802705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855176236914402853201803 11782764355371604279802705)
                  ·
                    refine ⟨8837073266528703209852029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11782764355371604279802705 8837073266528703209852029)
                    ·
                      refine ⟨3313902474948263703694511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8837073266528703209852029 3313902474948263703694511)
                      ·
                        rfl

theorem cell23_6453802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6453802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453802 prefixEnd_6453802 := by exact prefixLift 6453802
  have htrace : WordTrace (prefixWord ++ tailWord_6453802) baseStart_6453802 baseEnd_6453802 := by
    simpa [prefixWord, tailWord_6453802, baseEnd_6453802] using wordTrace_append hprefix tailTrace_6453802
  have hstable : (prefixWord ++ tailWord_6453802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453802).length < 2 ^ (prefixWord ++ tailWord_6453802).sum := by decide
  have hdescent : baseEnd_6453802 < baseStart_6453802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453815 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_6453815 : Nat := 118140960795 + 6453815 * 2 ^ 59
def prefixEnd_6453815 : Nat := 4983230072969 + 3 ^ 40 * 6453815 * 2
def baseEnd_6453815 : Nat := 3313909150196772152831951

theorem tailTrace_6453815 : CollatzResearch.WordTrace tailWord_6453815 prefixEnd_6453815 3313909150196772152831951 := by
  unfold tailWord_6453815
  simp only [CollatzResearch.WordTrace]
  refine ⟨235389971113937953694586899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156926647409291969129724599 235389971113937953694586899)
  ·
    refine ⟨353084956670906930541880349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235389971113937953694586899 353084956670906930541880349)
    ·
      refine ⟨132406858751590098953205131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353084956670906930541880349 132406858751590098953205131)
      ·
        refine ⟨198610288127385148429807697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132406858751590098953205131 198610288127385148429807697)
        ·
          refine ⟨148957716095538861322355773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198610288127385148429807697 148957716095538861322355773)
          ·
            refine ⟨55859143535827072995883415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148957716095538861322355773 55859143535827072995883415)
            ·
              refine ⟨83788715303740609493825123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55859143535827072995883415 83788715303740609493825123)
              ·
                refine ⟨125683072955610914240737685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83788715303740609493825123 125683072955610914240737685)
                ·
                  refine ⟨5891394044794261605034579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125683072955610914240737685 5891394044794261605034579)
                  ·
                    refine ⟨8837091067191392407551869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5891394044794261605034579 8837091067191392407551869)
                    ·
                      refine ⟨3313909150196772152831951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8837091067191392407551869 3313909150196772152831951)
                      ·
                        rfl

theorem cell23_6453815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_6453815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453815 prefixEnd_6453815 := by exact prefixLift 6453815
  have htrace : WordTrace (prefixWord ++ tailWord_6453815) baseStart_6453815 baseEnd_6453815 := by
    simpa [prefixWord, tailWord_6453815, baseEnd_6453815] using wordTrace_append hprefix tailTrace_6453815
  have hstable : (prefixWord ++ tailWord_6453815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453815).length < 2 ^ (prefixWord ++ tailWord_6453815).sum := by decide
  have hdescent : baseEnd_6453815 < baseStart_6453815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453822 : List Nat := [4, 2, 1, 4, 1, 2, 9]
def baseStart_6453822 : Nat := 118140960795 + 6453822 * 2 ^ 59
def prefixEnd_6453822 : Nat := 4983230072969 + 3 ^ 40 * 6453822 * 2
def baseEnd_6453822 : Nat := 40912503019275970684499

theorem tailTrace_6453822 : CollatzResearch.WordTrace tailWord_6453822 prefixEnd_6453822 40912503019275970684499 := by
  unfold tailWord_6453822
  simp only [CollatzResearch.WordTrace]
  refine ⟨29423778303114074236261465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156926817616608395926727813 29423778303114074236261465)
  ·
    refine ⟨22067833727335555677196099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29423778303114074236261465 22067833727335555677196099)
    ·
      refine ⟨33101750591003333515794149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22067833727335555677196099 33101750591003333515794149)
      ·
        refine ⟨6206578235813125034211403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33101750591003333515794149 6206578235813125034211403)
        ·
          refine ⟨9309867353719687551317105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206578235813125034211403 9309867353719687551317105)
          ·
            refine ⟨6982400515289765663487829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9309867353719687551317105 6982400515289765663487829)
            ·
              refine ⟨40912503019275970684499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6982400515289765663487829 40912503019275970684499)
              ·
                rfl

theorem cell23_6453822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 9].length) (baseStart_6453822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453822 prefixEnd_6453822 := by exact prefixLift 6453822
  have htrace : WordTrace (prefixWord ++ tailWord_6453822) baseStart_6453822 baseEnd_6453822 := by
    simpa [prefixWord, tailWord_6453822, baseEnd_6453822] using wordTrace_append hprefix tailTrace_6453822
  have hstable : (prefixWord ++ tailWord_6453822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453822).length < 2 ^ (prefixWord ++ tailWord_6453822).sum := by decide
  have hdescent : baseEnd_6453822 < baseStart_6453822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453842 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_6453842 : Nat := 118140960795 + 6453842 * 2 ^ 59
def prefixEnd_6453842 : Nat := 4983230072969 + 3 ^ 40 * 6453842 * 2
def baseEnd_6453842 : Nat := 3313923014174443547194327

theorem tailTrace_6453842 : CollatzResearch.WordTrace tailWord_6453842 prefixEnd_6453842 3313923014174443547194327 := by
  unfold tailWord_6453842
  simp only [CollatzResearch.WordTrace]
  refine ⟨58847738971210034326454945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156927303923226758203879853 58847738971210034326454945)
  ·
    refine ⟨44135804228407525744841209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58847738971210034326454945 44135804228407525744841209)
    ·
      refine ⟨33101853171305644308630907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44135804228407525744841209 33101853171305644308630907)
      ·
        refine ⟨49652779756958466462946361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33101853171305644308630907 49652779756958466462946361)
        ·
          refine ⟨37239584817718849847209771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49652779756958466462946361 37239584817718849847209771)
          ·
            refine ⟨55859377226578274770814657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37239584817718849847209771 55859377226578274770814657)
            ·
              refine ⟨41894532919933706078110993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55859377226578274770814657 41894532919933706078110993)
              ·
                refine ⟨31420899689950279558583245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41894532919933706078110993 31420899689950279558583245)
                ·
                  refine ⟨11782837383731354834468717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31420899689950279558583245 11782837383731354834468717)
                  ·
                    refine ⟨4418564018899258062925769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11782837383731354834468717 4418564018899258062925769)
                    ·
                      refine ⟨3313923014174443547194327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418564018899258062925769 3313923014174443547194327)
                      ·
                        rfl

theorem cell23_6453842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_6453842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453842 prefixEnd_6453842 := by exact prefixLift 6453842
  have htrace : WordTrace (prefixWord ++ tailWord_6453842) baseStart_6453842 baseEnd_6453842 := by
    simpa [prefixWord, tailWord_6453842, baseEnd_6453842] using wordTrace_append hprefix tailTrace_6453842
  have hstable : (prefixWord ++ tailWord_6453842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453842).length < 2 ^ (prefixWord ++ tailWord_6453842).sum := by decide
  have hdescent : baseEnd_6453842 < baseStart_6453842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453848 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 2, 6]
def baseStart_6453848 : Nat := 118140960795 + 6453848 * 2 ^ 59
def prefixEnd_6453848 : Nat := 4983230072969 + 3 ^ 40 * 6453848 * 2
def baseEnd_6453848 : Nat := 1104642031686123507906433

theorem tailTrace_6453848 : CollatzResearch.WordTrace tailWord_6453848 prefixEnd_6453848 1104642031686123507906433 := by
  unfold tailWord_6453848
  simp only [CollatzResearch.WordTrace]
  refine ⟨117695587361409200165269099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156927449815212266887025465 117695587361409200165269099)
  ·
    refine ⟨176543381042113800247903649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117695587361409200165269099 176543381042113800247903649)
    ·
      refine ⟨132407535781585350185927737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176543381042113800247903649 132407535781585350185927737)
      ·
        refine ⟨99305651836189012639445803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132407535781585350185927737 99305651836189012639445803)
        ·
          refine ⟨148958477754283518959168705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99305651836189012639445803 148958477754283518959168705)
          ·
            refine ⟨111718858315712639219376529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148958477754283518959168705 111718858315712639219376529)
            ·
              refine ⟨83789143736784479414532397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111718858315712639219376529 83789143736784479414532397)
              ·
                refine ⟨31420928901294179780449649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83789143736784479414532397 31420928901294179780449649)
                ·
                  refine ⟨23565696675970634835337237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31420928901294179780449649 23565696675970634835337237)
                  ·
                    refine ⟨1104642031686123507906433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23565696675970634835337237 1104642031686123507906433)
                    ·
                      rfl

theorem cell23_6453848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_6453848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453848 prefixEnd_6453848 := by exact prefixLift 6453848
  have htrace : WordTrace (prefixWord ++ tailWord_6453848) baseStart_6453848 baseEnd_6453848 := by
    simpa [prefixWord, tailWord_6453848, baseEnd_6453848] using wordTrace_append hprefix tailTrace_6453848
  have hstable : (prefixWord ++ tailWord_6453848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453848).length < 2 ^ (prefixWord ++ tailWord_6453848).sum := by decide
  have hdescent : baseEnd_6453848 < baseStart_6453848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453855 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 5, 4, 2]
def baseStart_6453855 : Nat := 118140960795 + 6453855 * 2 ^ 59
def prefixEnd_6453855 : Nat := 4983230072969 + 3 ^ 40 * 6453855 * 2
def baseEnd_6453855 : Nat := 3313929689422951996331767

theorem tailTrace_6453855 : CollatzResearch.WordTrace tailWord_6453855 prefixEnd_6453855 3313929689422951996331767 := by
  unfold tailWord_6453855
  simp only [CollatzResearch.WordTrace]
  refine ⟨235391430033793040526043019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156927620022528693684028679 235391430033793040526043019)
  ·
    refine ⟨353087145050689560789064529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235391430033793040526043019 353087145050689560789064529)
    ·
      refine ⟨264815358788017170591798397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353087145050689560789064529 264815358788017170591798397)
      ·
        refine ⟨99305759545506438971924399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264815358788017170591798397 99305759545506438971924399)
        ·
          refine ⟨148958639318259658457886599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99305759545506438971924399 148958639318259658457886599)
          ·
            refine ⟨223437958977389487686829899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148958639318259658457886599 223437958977389487686829899)
            ·
              refine ⟨335156938466084231530244849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223437958977389487686829899 335156938466084231530244849)
              ·
                refine ⟨251367703849563173647683637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335156938466084231530244849 251367703849563173647683637)
                ·
                  refine ⟨23565722235896547529470341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251367703849563173647683637 23565722235896547529470341)
                  ·
                    refine ⟨4418572919230602661775689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23565722235896547529470341 4418572919230602661775689)
                    ·
                      refine ⟨3313929689422951996331767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418572919230602661775689 3313929689422951996331767)
                      ·
                        rfl

theorem cell23_6453855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_6453855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453855 prefixEnd_6453855 := by exact prefixLift 6453855
  have htrace : WordTrace (prefixWord ++ tailWord_6453855) baseStart_6453855 baseEnd_6453855 := by
    simpa [prefixWord, tailWord_6453855, baseEnd_6453855] using wordTrace_append hprefix tailTrace_6453855
  have hstable : (prefixWord ++ tailWord_6453855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453855).length < 2 ^ (prefixWord ++ tailWord_6453855).sum := by decide
  have hdescent : baseEnd_6453855 < baseStart_6453855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453906 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_6453906 : Nat := 118140960795 + 6453906 * 2 ^ 59
def prefixEnd_6453906 : Nat := 4983230072969 + 3 ^ 40 * 6453906 * 2
def baseEnd_6453906 : Nat := 3313955876936331296794033

theorem tailTrace_6453906 : CollatzResearch.WordTrace tailWord_6453906 prefixEnd_6453906 3313955876936331296794033 := by
  unfold tailWord_6453906
  simp only [CollatzResearch.WordTrace]
  refine ⟨58848322539152069059037393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156928860104405517490766381 58848322539152069059037393)
  ·
    refine ⟨44136241904364051794278045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58848322539152069059037393 44136241904364051794278045)
    ·
      refine ⟨16551090714136519422854267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44136241904364051794278045 16551090714136519422854267)
      ·
        refine ⟨24826636071204779134281401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16551090714136519422854267 24826636071204779134281401)
        ·
          refine ⟨18619977053403584350711051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24826636071204779134281401 18619977053403584350711051)
          ·
            refine ⟨27929965580105376526066577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18619977053403584350711051 27929965580105376526066577)
            ·
              refine ⟨20947474185079032394549933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27929965580105376526066577 20947474185079032394549933)
              ·
                refine ⟨7855302819404637147956225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20947474185079032394549933 7855302819404637147956225)
                ·
                  refine ⟨5891477114553477860967169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7855302819404637147956225 5891477114553477860967169)
                  ·
                    refine ⟨4418607835915108395725377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5891477114553477860967169 4418607835915108395725377)
                    ·
                      refine ⟨3313955876936331296794033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418607835915108395725377 3313955876936331296794033)
                      ·
                        rfl

theorem cell23_6453906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_6453906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453906 prefixEnd_6453906 := by exact prefixLift 6453906
  have htrace : WordTrace (prefixWord ++ tailWord_6453906) baseStart_6453906 baseEnd_6453906 := by
    simpa [prefixWord, tailWord_6453906, baseEnd_6453906] using wordTrace_append hprefix tailTrace_6453906
  have hstable : (prefixWord ++ tailWord_6453906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453906).length < 2 ^ (prefixWord ++ tailWord_6453906).sum := by decide
  have hdescent : baseEnd_6453906 < baseStart_6453906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453945 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_6453945 : Nat := 118140960795 + 6453945 * 2 ^ 59
def prefixEnd_6453945 : Nat := 4983230072969 + 3 ^ 40 * 6453945 * 2
def baseEnd_6453945 : Nat := 3313975902681856644206353

theorem tailTrace_6453945 : CollatzResearch.WordTrace tailWord_6453945 prefixEnd_6453945 3313975902681856644206353 := by
  unfold tailWord_6453945
  simp only [CollatzResearch.WordTrace]
  refine ⟨235394712603466985896819289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156929808402311323931212859 235394712603466985896819289)
  ·
    refine ⟨176546034452600239422614467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235394712603466985896819289 176546034452600239422614467)
    ·
      refine ⟨264819051678900359133921701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176546034452600239422614467 264819051678900359133921701)
      ·
        refine ⟨49653572189793817337610319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264819051678900359133921701 49653572189793817337610319)
        ·
          refine ⟨74480358284690726006415479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49653572189793817337610319 74480358284690726006415479)
          ·
            refine ⟨111720537427036089009623219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74480358284690726006415479 111720537427036089009623219)
            ·
              refine ⟨167580806140554133514434829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111720537427036089009623219 167580806140554133514434829)
              ·
                refine ⟨62842802302707800067913061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167580806140554133514434829 62842802302707800067913061)
                ·
                  refine ⟨11783025431757712512733699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62842802302707800067913061 11783025431757712512733699)
                  ·
                    refine ⟨17674538147636568769100549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11783025431757712512733699 17674538147636568769100549)
                    ·
                      refine ⟨3313975902681856644206353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17674538147636568769100549 3313975902681856644206353)
                      ·
                        rfl

theorem cell23_6453945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_6453945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453945 prefixEnd_6453945 := by exact prefixLift 6453945
  have htrace : WordTrace (prefixWord ++ tailWord_6453945) baseStart_6453945 baseEnd_6453945 := by
    simpa [prefixWord, tailWord_6453945, baseEnd_6453945] using wordTrace_append hprefix tailTrace_6453945
  have hstable : (prefixWord ++ tailWord_6453945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453945).length < 2 ^ (prefixWord ++ tailWord_6453945).sum := by decide
  have hdescent : baseEnd_6453945 < baseStart_6453945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6453985 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 8]
def baseStart_6453985 : Nat := 118140960795 + 6453985 * 2 ^ 59
def prefixEnd_6453985 : Nat := 4983230072969 + 3 ^ 40 * 6453985 * 2
def baseEnd_6453985 : Nat := 368221826878670720856241

theorem tailTrace_6453985 : CollatzResearch.WordTrace tailWord_6453985 prefixEnd_6453985 368221826878670720856241 := by
  unfold tailWord_6453985
  simp only [CollatzResearch.WordTrace]
  refine ⟨235396171523322072728275409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156930781015548048485516939 235396171523322072728275409)
  ·
    refine ⟨176547128642491554546206557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235396171523322072728275409 176547128642491554546206557)
    ·
      refine ⟨66205173240934332954827459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176547128642491554546206557 66205173240934332954827459)
      ·
        refine ⟨99307759861401499432241189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66205173240934332954827459 99307759861401499432241189)
        ·
          refine ⟨18620204974012781143545223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99307759861401499432241189 18620204974012781143545223)
          ·
            refine ⟨27930307461019171715317835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18620204974012781143545223 27930307461019171715317835)
            ·
              refine ⟨41895461191528757572976753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27930307461019171715317835 41895461191528757572976753)
              ·
                refine ⟨31421595893646568179732565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41895461191528757572976753 31421595893646568179732565)
                ·
                  refine ⟨368221826878670720856241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31421595893646568179732565 368221826878670720856241)
                  ·
                    rfl

theorem cell23_6453985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 8].length) (baseStart_6453985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6453985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6453985 prefixEnd_6453985 := by exact prefixLift 6453985
  have htrace : WordTrace (prefixWord ++ tailWord_6453985) baseStart_6453985 baseEnd_6453985 := by
    simpa [prefixWord, tailWord_6453985, baseEnd_6453985] using wordTrace_append hprefix tailTrace_6453985
  have hstable : (prefixWord ++ tailWord_6453985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6453985).length < 2 ^ (prefixWord ++ tailWord_6453985).sum := by decide
  have hdescent : baseEnd_6453985 < baseStart_6453985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6453985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454015 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 3, 5]
def baseStart_6454015 : Nat := 118140960795 + 6454015 * 2 ^ 59
def prefixEnd_6454015 : Nat := 4983230072969 + 3 ^ 40 * 6454015 * 2
def baseEnd_6454015 : Nat := 1104670615442557123443677

theorem tailTrace_6454015 : CollatzResearch.WordTrace tailWord_6454015 prefixEnd_6454015 1104670615442557123443677 := by
  unfold tailWord_6454015
  simp only [CollatzResearch.WordTrace]
  refine ⟨235397265713213387851867499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156931510475475591901244999 235397265713213387851867499)
  ·
    refine ⟨353095898569820081777801249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235397265713213387851867499 353095898569820081777801249)
    ·
      refine ⟨264821923927365061333350937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353095898569820081777801249 264821923927365061333350937)
      ·
        refine ⟨198616442945523796000013203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264821923927365061333350937 198616442945523796000013203)
        ·
          refine ⟨297924664418285694000019805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198616442945523796000013203 297924664418285694000019805)
          ·
            refine ⟨111721749156857135250007427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297924664418285694000019805 111721749156857135250007427)
            ·
              refine ⟨167582623735285702875011141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111721749156857135250007427 167582623735285702875011141)
              ·
                refine ⟨31421741950366069289064589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167582623735285702875011141 31421741950366069289064589)
                ·
                  refine ⟨11783153231387275983399221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31421741950366069289064589 11783153231387275983399221)
                  ·
                    refine ⟨1104670615442557123443677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11783153231387275983399221 1104670615442557123443677)
                    ·
                      rfl

theorem cell23_6454015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_6454015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454015 prefixEnd_6454015 := by exact prefixLift 6454015
  have htrace : WordTrace (prefixWord ++ tailWord_6454015) baseStart_6454015 baseEnd_6454015 := by
    simpa [prefixWord, tailWord_6454015, baseEnd_6454015] using wordTrace_append hprefix tailTrace_6454015
  have hstable : (prefixWord ++ tailWord_6454015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454015).length < 2 ^ (prefixWord ++ tailWord_6454015).sum := by decide
  have hdescent : baseEnd_6454015 < baseStart_6454015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454049 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 1, 5]
def baseStart_6454049 : Nat := 118140960795 + 6454049 * 2 ^ 59
def prefixEnd_6454049 : Nat := 4983230072969 + 3 ^ 40 * 6454049 * 2
def baseEnd_6454049 : Nat := 1104676434889974745768625

theorem tailTrace_6454049 : CollatzResearch.WordTrace tailWord_6454049 prefixEnd_6454049 1104676434889974745768625 := by
  unfold tailWord_6454049
  simp only [CollatzResearch.WordTrace]
  refine ⟨235398505795090211658605201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156932337196726807772403467 235398505795090211658605201)
  ·
    refine ⟨176548879346317658743953901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235398505795090211658605201 176548879346317658743953901)
    ·
      refine ⟨66205829754869122028982713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176548879346317658743953901 66205829754869122028982713)
      ·
        refine ⟨49654372316151841521737035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66205829754869122028982713 49654372316151841521737035)
        ·
          refine ⟨74481558474227762282605553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49654372316151841521737035 74481558474227762282605553)
          ·
            refine ⟨55861168855670821711954165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74481558474227762282605553 55861168855670821711954165)
            ·
              refine ⟨5236984580219139535495703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55861168855670821711954165 5236984580219139535495703)
              ·
                refine ⟨7855476870328709303243555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5236984580219139535495703 7855476870328709303243555)
                ·
                  refine ⟨11783215305493063954865333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855476870328709303243555 11783215305493063954865333)
                  ·
                    refine ⟨1104676434889974745768625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11783215305493063954865333 1104676434889974745768625)
                    ·
                      rfl

theorem cell23_6454049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_6454049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454049 prefixEnd_6454049 := by exact prefixLift 6454049
  have htrace : WordTrace (prefixWord ++ tailWord_6454049) baseStart_6454049 baseEnd_6454049 := by
    simpa [prefixWord, tailWord_6454049, baseEnd_6454049] using wordTrace_append hprefix tailTrace_6454049
  have hstable : (prefixWord ++ tailWord_6454049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454049).length < 2 ^ (prefixWord ++ tailWord_6454049).sum := by decide
  have hdescent : baseEnd_6454049 < baseStart_6454049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454072 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_6454072 : Nat := 118140960795 + 6454072 * 2 ^ 59
def prefixEnd_6454072 : Nat := 4983230072969 + 3 ^ 40 * 6454072 * 2
def baseEnd_6454072 : Nat := 3314041114724977647318269

theorem tailTrace_6454072 : CollatzResearch.WordTrace tailWord_6454072 prefixEnd_6454072 3314041114724977647318269 := by
  unfold tailWord_6454072
  simp only [CollatzResearch.WordTrace]
  refine ⟨117699672337003443293346235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156932896449337924391128313 117699672337003443293346235)
  ·
    refine ⟨176549508505505164940019353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117699672337003443293346235 176549508505505164940019353)
    ·
      refine ⟨132412131379128873705014515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176549508505505164940019353 132412131379128873705014515)
      ·
        refine ⟨198618197068693310557521773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132412131379128873705014515 198618197068693310557521773)
        ·
          refine ⟨74481823900759991459070665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198618197068693310557521773 74481823900759991459070665)
          ·
            refine ⟨55861367925569993594302999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74481823900759991459070665 55861367925569993594302999)
            ·
              refine ⟨83792051888354990391454499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55861367925569993594302999 83792051888354990391454499)
              ·
                refine ⟨125688077832532485587181749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83792051888354990391454499 125688077832532485587181749)
                ·
                  refine ⟨11783257296799920523798289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125688077832532485587181749 11783257296799920523798289)
                  ·
                    refine ⟨8837442972599940392848717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11783257296799920523798289 8837442972599940392848717)
                    ·
                      refine ⟨3314041114724977647318269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8837442972599940392848717 3314041114724977647318269)
                      ·
                        rfl

theorem cell23_6454072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_6454072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454072 prefixEnd_6454072 := by exact prefixLift 6454072
  have htrace : WordTrace (prefixWord ++ tailWord_6454072) baseStart_6454072 baseEnd_6454072 := by
    simpa [prefixWord, tailWord_6454072, baseEnd_6454072] using wordTrace_append hprefix tailTrace_6454072
  have hstable : (prefixWord ++ tailWord_6454072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454072).length < 2 ^ (prefixWord ++ tailWord_6454072).sum := by decide
  have hdescent : baseEnd_6454072 < baseStart_6454072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454079 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 2, 4]
def baseStart_6454079 : Nat := 118140960795 + 6454079 * 2 ^ 59
def prefixEnd_6454079 : Nat := 4983230072969 + 3 ^ 40 * 6454079 * 2
def baseEnd_6454079 : Nat := 1104681569696519706643579

theorem tailTrace_6454079 : CollatzResearch.WordTrace tailWord_6454079 prefixEnd_6454079 1104681569696519706643579 := by
  unfold tailWord_6454079
  simp only [CollatzResearch.WordTrace]
  refine ⟨235399599984981526782197291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156933066656654351188131527 235399599984981526782197291)
  ·
    refine ⟨353099399977472290173295937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235399599984981526782197291 353099399977472290173295937)
    ·
      refine ⟨264824549983104217629971953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353099399977472290173295937 264824549983104217629971953)
      ·
        refine ⟨198618412487328163222478965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264824549983104217629971953 198618412487328163222478965)
        ·
          refine ⟨18620476170687015302107403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198618412487328163222478965 18620476170687015302107403)
          ·
            refine ⟨27930714256030522953161105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18620476170687015302107403 27930714256030522953161105)
            ·
              refine ⟨20948035692022892214870829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27930714256030522953161105 20948035692022892214870829)
              ·
                refine ⟨7855513384508584580576561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20948035692022892214870829 7855513384508584580576561)
                ·
                  refine ⟨5891635038381438435432421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7855513384508584580576561 5891635038381438435432421)
                  ·
                    refine ⟨1104681569696519706643579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5891635038381438435432421 1104681569696519706643579)
                    ·
                      rfl

theorem cell23_6454079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_6454079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454079 prefixEnd_6454079 := by exact prefixLift 6454079
  have htrace : WordTrace (prefixWord ++ tailWord_6454079) baseStart_6454079 baseEnd_6454079 := by
    simpa [prefixWord, tailWord_6454079, baseEnd_6454079] using wordTrace_append hprefix tailTrace_6454079
  have hstable : (prefixWord ++ tailWord_6454079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454079).length < 2 ^ (prefixWord ++ tailWord_6454079).sum := by decide
  have hdescent : baseEnd_6454079 < baseStart_6454079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454103 : List Nat := [1, 1, 3, 2, 4, 1, 1, 5, 1, 2, 2]
def baseStart_6454103 : Nat := 118140960795 + 6454103 * 2 ^ 59
def prefixEnd_6454103 : Nat := 4983230072969 + 3 ^ 40 * 6454103 * 2
def baseEnd_6454103 : Nat := 3314057032625267026030627

theorem tailTrace_6454103 : CollatzResearch.WordTrace tailWord_6454103 prefixEnd_6454103 3314057032625267026030627 := by
  unfold tailWord_6454103
  simp only [CollatzResearch.WordTrace]
  refine ⟨235400475336894578881070963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156933650224596385920713975 235400475336894578881070963)
  ·
    refine ⟨353100713005341868321606445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235400475336894578881070963 353100713005341868321606445)
    ·
      refine ⟨132412767377003200620602417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353100713005341868321606445 132412767377003200620602417)
      ·
        refine ⟨99309575532752400465451813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132412767377003200620602417 99309575532752400465451813)
        ·
          refine ⟨18620545412391075087272215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99309575532752400465451813 18620545412391075087272215)
          ·
            refine ⟨27930818118586612630908323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18620545412391075087272215 27930818118586612630908323)
            ·
              refine ⟨41896227177879918946362485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27930818118586612630908323 41896227177879918946362485)
              ·
                refine ⟨3927771297926242401221483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41896227177879918946362485 3927771297926242401221483)
                ·
                  refine ⟨5891656946889363601832225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927771297926242401221483 5891656946889363601832225)
                  ·
                    refine ⟨4418742710167022701374169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5891656946889363601832225 4418742710167022701374169)
                    ·
                      refine ⟨3314057032625267026030627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418742710167022701374169 3314057032625267026030627)
                      ·
                        rfl

theorem cell23_6454103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_6454103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454103 prefixEnd_6454103 := by exact prefixLift 6454103
  have htrace : WordTrace (prefixWord ++ tailWord_6454103) baseStart_6454103 baseEnd_6454103 := by
    simpa [prefixWord, tailWord_6454103, baseEnd_6454103] using wordTrace_append hprefix tailTrace_6454103
  have hstable : (prefixWord ++ tailWord_6454103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454103).length < 2 ^ (prefixWord ++ tailWord_6454103).sum := by decide
  have hdescent : baseEnd_6454103 < baseStart_6454103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454106 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3]
def baseStart_6454106 : Nat := 118140960795 + 6454106 * 2 ^ 59
def prefixEnd_6454106 : Nat := 4983230072969 + 3 ^ 40 * 6454106 * 2
def baseEnd_6454106 : Nat := 3314058573067230514293113

theorem tailTrace_6454106 : CollatzResearch.WordTrace tailWord_6454106 prefixEnd_6454106 3314058573067230514293113 := by
  unfold tailWord_6454106
  simp only [CollatzResearch.WordTrace]
  refine ⟨58850146188970927598357543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156933723170589140262286781 58850146188970927598357543)
  ·
    refine ⟨88275219283456391397536315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58850146188970927598357543 88275219283456391397536315)
    ·
      refine ⟨132412828925184587096304473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88275219283456391397536315 132412828925184587096304473)
      ·
        refine ⟨99309621693888440322228355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132412828925184587096304473 99309621693888440322228355)
        ·
          refine ⟨148964432540832660483342533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99309621693888440322228355 148964432540832660483342533)
          ·
            refine ⟨27930831101406123840626725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148964432540832660483342533 27930831101406123840626725)
            ·
              refine ⟨5237030831513648220117511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27930831101406123840626725 5237030831513648220117511)
              ·
                refine ⟨7855546247270472330176267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237030831513648220117511 7855546247270472330176267)
                ·
                  refine ⟨11783319370905708495264401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855546247270472330176267 11783319370905708495264401)
                  ·
                    refine ⟨8837489528179281371448301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11783319370905708495264401 8837489528179281371448301)
                    ·
                      refine ⟨3314058573067230514293113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8837489528179281371448301 3314058573067230514293113)
                      ·
                        rfl

theorem cell23_6454106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_6454106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454106 prefixEnd_6454106 := by exact prefixLift 6454106
  have htrace : WordTrace (prefixWord ++ tailWord_6454106) baseStart_6454106 baseEnd_6454106 := by
    simpa [prefixWord, tailWord_6454106, baseEnd_6454106] using wordTrace_append hprefix tailTrace_6454106
  have hstable : (prefixWord ++ tailWord_6454106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454106).length < 2 ^ (prefixWord ++ tailWord_6454106).sum := by decide
  have hdescent : baseEnd_6454106 < baseStart_6454106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454176 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 4, 2, 2]
def baseStart_6454176 : Nat := 118140960795 + 6454176 * 2 ^ 59
def prefixEnd_6454176 : Nat := 4983230072969 + 3 ^ 40 * 6454176 * 2
def baseEnd_6454176 : Nat := 3314094516713045240417791

theorem tailTrace_6454176 : CollatzResearch.WordTrace tailWord_6454176 prefixEnd_6454176 3314094516713045240417791 := by
  unfold tailWord_6454176
  simp only [CollatzResearch.WordTrace]
  refine ⟨117701568932815056174239191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156935425243753408232318921 117701568932815056174239191)
  ·
    refine ⟨176552353399222584261358787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117701568932815056174239191 176552353399222584261358787)
    ·
      refine ⟨264828530098833876392038181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176552353399222584261358787 264828530098833876392038181)
      ·
        refine ⟨49655349393531351823507159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264828530098833876392038181 49655349393531351823507159)
        ·
          refine ⟨74483024090297027735260739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49655349393531351823507159 74483024090297027735260739)
          ·
            refine ⟨111724536135445541602891109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74483024090297027735260739 111724536135445541602891109)
            ·
              refine ⟨20948350525396039050542083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111724536135445541602891109 20948350525396039050542083)
              ·
                refine ⟨31422525788094058575813125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20948350525396039050542083 31422525788094058575813125)
                ·
                  refine ⟨5891723585267635982964961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31422525788094058575813125 5891723585267635982964961)
                  ·
                    refine ⟨4418792688950726987223721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5891723585267635982964961 4418792688950726987223721)
                    ·
                      refine ⟨3314094516713045240417791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418792688950726987223721 3314094516713045240417791)
                      ·
                        rfl

theorem cell23_6454176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_6454176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454176 prefixEnd_6454176 := by exact prefixLift 6454176
  have htrace : WordTrace (prefixWord ++ tailWord_6454176) baseStart_6454176 baseEnd_6454176 := by
    simpa [prefixWord, tailWord_6454176, baseEnd_6454176] using wordTrace_append hprefix tailTrace_6454176
  have hstable : (prefixWord ++ tailWord_6454176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454176).length < 2 ^ (prefixWord ++ tailWord_6454176).sum := by decide
  have hdescent : baseEnd_6454176 < baseStart_6454176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454196 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6454196 : Nat := 118140960795 + 6454196 * 2 ^ 59
def prefixEnd_6454196 : Nat := 4983230072969 + 3 ^ 40 * 6454196 * 2
def baseEnd_6454196 : Nat := 3314104786326135162167699

theorem tailTrace_6454196 : CollatzResearch.WordTrace tailWord_6454196 prefixEnd_6454196 3314104786326135162167699 := by
  unfold tailWord_6454196
  simp only [CollatzResearch.WordTrace]
  refine ⟨117701933662778827882103221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156935911550371770509470961 117701933662778827882103221)
  ·
    refine ⟨11034556280885515113947177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117701933662778827882103221 11034556280885515113947177)
    ·
      refine ⟨8275917210664136335460383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11034556280885515113947177 8275917210664136335460383)
      ·
        refine ⟨12413875815996204503190575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8275917210664136335460383 12413875815996204503190575)
        ·
          refine ⟨18620813723994306754785863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12413875815996204503190575 18620813723994306754785863)
          ·
            refine ⟨27931220585991460132178795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18620813723994306754785863 27931220585991460132178795)
            ·
              refine ⟨41896830878987190198268193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27931220585991460132178795 41896830878987190198268193)
              ·
                refine ⟨31422623159240392648701145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41896830878987190198268193 31422623159240392648701145)
                ·
                  refine ⟨23566967369430294486525859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31422623159240392648701145 23566967369430294486525859)
                  ·
                    refine ⟨35350451054145441729788789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23566967369430294486525859 35350451054145441729788789)
                    ·
                      refine ⟨3314104786326135162167699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35350451054145441729788789 3314104786326135162167699)
                      ·
                        rfl

theorem cell23_6454196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6454196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454196 prefixEnd_6454196 := by exact prefixLift 6454196
  have htrace : WordTrace (prefixWord ++ tailWord_6454196) baseStart_6454196 baseEnd_6454196 := by
    simpa [prefixWord, tailWord_6454196, baseEnd_6454196] using wordTrace_append hprefix tailTrace_6454196
  have hstable : (prefixWord ++ tailWord_6454196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454196).length < 2 ^ (prefixWord ++ tailWord_6454196).sum := by decide
  have hdescent : baseEnd_6454196 < baseStart_6454196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454233 : List Nat := [1, 2, 1, 2, 5, 3, 2, 2, 5]
def baseStart_6454233 : Nat := 118140960795 + 6454233 * 2 ^ 59
def prefixEnd_6454233 : Nat := 4983230072969 + 3 ^ 40 * 6454233 * 2
def baseEnd_6454233 : Nat := 368235976123372390822781

theorem tailTrace_6454233 : CollatzResearch.WordTrace tailWord_6454233 prefixEnd_6454233 368235976123372390822781 := by
  unfold tailWord_6454233
  simp only [CollatzResearch.WordTrace]
  refine ⟨235405216826423611083303353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156936811217615740722202235 235405216826423611083303353)
  ·
    refine ⟨176553912619817708312477515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235405216826423611083303353 176553912619817708312477515)
    ·
      refine ⟨264830868929726562468716273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176553912619817708312477515 264830868929726562468716273)
      ·
        refine ⟨198623151697294921851537205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264830868929726562468716273 198623151697294921851537205)
        ·
          refine ⟨18620920471621398923581613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198623151697294921851537205 18620920471621398923581613)
          ·
            refine ⟨6982845176858024596343105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18620920471621398923581613 6982845176858024596343105)
            ·
              refine ⟨5237133882643518447257329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6982845176858024596343105 5237133882643518447257329)
              ·
                refine ⟨3927850411982638835442997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5237133882643518447257329 3927850411982638835442997)
                ·
                  refine ⟨368235976123372390822781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3927850411982638835442997 368235976123372390822781)
                  ·
                    rfl

theorem cell23_6454233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 5].length) (baseStart_6454233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454233 prefixEnd_6454233 := by exact prefixLift 6454233
  have htrace : WordTrace (prefixWord ++ tailWord_6454233) baseStart_6454233 baseEnd_6454233 := by
    simpa [prefixWord, tailWord_6454233, baseEnd_6454233] using wordTrace_append hprefix tailTrace_6454233
  have hstable : (prefixWord ++ tailWord_6454233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454233).length < 2 ^ (prefixWord ++ tailWord_6454233).sum := by decide
  have hdescent : baseEnd_6454233 < baseStart_6454233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454293 : List Nat := [1, 3, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_6454293 : Nat := 118140960795 + 6454293 * 2 ^ 59
def prefixEnd_6454293 : Nat := 4983230072969 + 3 ^ 40 * 6454293 * 2
def baseEnd_6454293 : Nat := 1104718197983207094218251

theorem tailTrace_6454293 : CollatzResearch.WordTrace tailWord_6454293 prefixEnd_6454293 1104718197983207094218251 := by
  unfold tailWord_6454293
  simp only [CollatzResearch.WordTrace]
  refine ⟨235407405206206241330487533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156938270137470827553658355 235407405206206241330487533)
  ·
    refine ⟨88277776952327340498932825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235407405206206241330487533 88277776952327340498932825)
    ·
      refine ⟨66208332714245505374199619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88277776952327340498932825 66208332714245505374199619)
      ·
        refine ⟨99312499071368258061299429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66208332714245505374199619 99312499071368258061299429)
        ·
          refine ⟨18621093575881548386493643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99312499071368258061299429 18621093575881548386493643)
          ·
            refine ⟨27931640363822322579740465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18621093575881548386493643 27931640363822322579740465)
            ·
              refine ⟨20948730272866741934805349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27931640363822322579740465 20948730272866741934805349)
              ·
                refine ⟨3927886926162514112776003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20948730272866741934805349 3927886926162514112776003)
                ·
                  refine ⟨5891830389243771169164005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927886926162514112776003 5891830389243771169164005)
                  ·
                    refine ⟨1104718197983207094218251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5891830389243771169164005 1104718197983207094218251)
                    ·
                      rfl

theorem cell23_6454293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_6454293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454293 prefixEnd_6454293 := by exact prefixLift 6454293
  have htrace : WordTrace (prefixWord ++ tailWord_6454293) baseStart_6454293 baseEnd_6454293 := by
    simpa [prefixWord, tailWord_6454293, baseEnd_6454293] using wordTrace_append hprefix tailTrace_6454293
  have hstable : (prefixWord ++ tailWord_6454293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454293).length < 2 ^ (prefixWord ++ tailWord_6454293).sum := by decide
  have hdescent : baseEnd_6454293 < baseStart_6454293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454316 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_6454316 : Nat := 118140960795 + 6454316 * 2 ^ 59
def prefixEnd_6454316 : Nat := 4983230072969 + 3 ^ 40 * 6454316 * 2
def baseEnd_6454316 : Nat := 3314166404004674692667147

theorem tailTrace_6454316 : CollatzResearch.WordTrace tailWord_6454316 prefixEnd_6454316 3314166404004674692667147 := by
  unfold tailWord_6454316
  simp only [CollatzResearch.WordTrace]
  refine ⟨117704122042561458129287401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156938829390081944172383201 117704122042561458129287401)
  ·
    refine ⟨88278091531921093596965551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117704122042561458129287401 88278091531921093596965551)
    ·
      refine ⟨132417137297881640395448327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88278091531921093596965551 132417137297881640395448327)
      ·
        refine ⟨198625705946822460593172491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132417137297881640395448327 198625705946822460593172491)
        ·
          refine ⟨297938558920233690889758737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198625705946822460593172491 297938558920233690889758737)
          ·
            refine ⟨223453919190175268167319053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297938558920233690889758737 223453919190175268167319053)
            ·
              refine ⟨83795219696315725562744645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223453919190175268167319053 83795219696315725562744645)
              ·
                refine ⟨15711603693059198543014621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83795219696315725562744645 15711603693059198543014621)
                ·
                  refine ⟨5891851384897199453630483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15711603693059198543014621 5891851384897199453630483)
                  ·
                    refine ⟨8837777077345799180445725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5891851384897199453630483 8837777077345799180445725)
                    ·
                      refine ⟨3314166404004674692667147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8837777077345799180445725 3314166404004674692667147)
                      ·
                        rfl

theorem cell23_6454316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_6454316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454316 prefixEnd_6454316 := by exact prefixLift 6454316
  have htrace : WordTrace (prefixWord ++ tailWord_6454316) baseStart_6454316 baseEnd_6454316 := by
    simpa [prefixWord, tailWord_6454316, baseEnd_6454316] using wordTrace_append hprefix tailTrace_6454316
  have hstable : (prefixWord ++ tailWord_6454316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454316).length < 2 ^ (prefixWord ++ tailWord_6454316).sum := by decide
  have hdescent : baseEnd_6454316 < baseStart_6454316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454343 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_6454343 : Nat := 118140960795 + 6454343 * 2 ^ 59
def prefixEnd_6454343 : Nat := 4983230072969 + 3 ^ 40 * 6454343 * 2
def baseEnd_6454343 : Nat := 3314180267982346087029523

theorem tailTrace_6454343 : CollatzResearch.WordTrace tailWord_6454343 prefixEnd_6454343 3314180267982346087029523 := by
  unfold tailWord_6454343
  simp only [CollatzResearch.WordTrace]
  refine ⟨235409228856025099869807683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156939485904016733246538455 235409228856025099869807683)
  ·
    refine ⟨353113843284037649804711525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235409228856025099869807683 353113843284037649804711525)
    ·
      refine ⟨66208845615757059338383411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353113843284037649804711525 66208845615757059338383411)
      ·
        refine ⟨99313268423635589007575117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66208845615757059338383411 99313268423635589007575117)
        ·
          refine ⟨37242475658863345877840669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99313268423635589007575117 37242475658863345877840669)
          ·
            refine ⟨13965928372073754704190251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37242475658863345877840669 13965928372073754704190251)
            ·
              refine ⟨20948892558110632056285377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13965928372073754704190251 20948892558110632056285377)
              ·
                refine ⟨15711669418582974042214033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20948892558110632056285377 15711669418582974042214033)
                ·
                  refine ⟨11783752063937230531660525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15711669418582974042214033 11783752063937230531660525)
                  ·
                    refine ⟨4418907023976461449372697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11783752063937230531660525 4418907023976461449372697)
                    ·
                      refine ⟨3314180267982346087029523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418907023976461449372697 3314180267982346087029523)
                      ·
                        rfl

theorem cell23_6454343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_6454343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454343 prefixEnd_6454343 := by exact prefixLift 6454343
  have htrace : WordTrace (prefixWord ++ tailWord_6454343) baseStart_6454343 baseEnd_6454343 := by
    simpa [prefixWord, tailWord_6454343, baseEnd_6454343] using wordTrace_append hprefix tailTrace_6454343
  have hstable : (prefixWord ++ tailWord_6454343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454343).length < 2 ^ (prefixWord ++ tailWord_6454343).sum := by decide
  have hdescent : baseEnd_6454343 < baseStart_6454343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454359 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_6454359 : Nat := 118140960795 + 6454359 * 2 ^ 59
def prefixEnd_6454359 : Nat := 4983230072969 + 3 ^ 40 * 6454359 * 2
def baseEnd_6454359 : Nat := 3314188483672818024429449

theorem tailTrace_6454359 : CollatzResearch.WordTrace tailWord_6454359 prefixEnd_6454359 3314188483672818024429449 := by
  unfold tailWord_6454359
  simp only [CollatzResearch.WordTrace]
  refine ⟨235409812423967134602390131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156939874949311423068260087 235409812423967134602390131)
  ·
    refine ⟨353114718635950701903585197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235409812423967134602390131 353114718635950701903585197)
    ·
      refine ⟨132418019488481513213844449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353114718635950701903585197 132418019488481513213844449)
      ·
        refine ⟨99313514616361134910383337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132418019488481513213844449 99313514616361134910383337)
        ·
          refine ⟨74485135962270851182787503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99313514616361134910383337 74485135962270851182787503)
          ·
            refine ⟨111727703943406276774181255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74485135962270851182787503 111727703943406276774181255)
            ·
              refine ⟨167591555915109415161271883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111727703943406276774181255 167591555915109415161271883)
              ·
                refine ⟨251387333872664122741907825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167591555915109415161271883 251387333872664122741907825)
                ·
                  refine ⟨188540500404498092056430869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251387333872664122741907825 188540500404498092056430869)
                  ·
                    refine ⟨8837835956460848065145197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188540500404498092056430869 8837835956460848065145197)
                    ·
                      refine ⟨3314188483672818024429449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8837835956460848065145197 3314188483672818024429449)
                      ·
                        rfl

theorem cell23_6454359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_6454359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454359 prefixEnd_6454359 := by exact prefixLift 6454359
  have htrace : WordTrace (prefixWord ++ tailWord_6454359) baseStart_6454359 baseEnd_6454359 := by
    simpa [prefixWord, tailWord_6454359, baseEnd_6454359] using wordTrace_append hprefix tailTrace_6454359
  have hstable : (prefixWord ++ tailWord_6454359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454359).length < 2 ^ (prefixWord ++ tailWord_6454359).sum := by decide
  have hdescent : baseEnd_6454359 < baseStart_6454359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454369 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_6454369 : Nat := 118140960795 + 6454369 * 2 ^ 59
def prefixEnd_6454369 : Nat := 4983230072969 + 3 ^ 40 * 6454369 * 2
def baseEnd_6454369 : Nat := 3314193618479362985304403

theorem tailTrace_6454369 : CollatzResearch.WordTrace tailWord_6454369 prefixEnd_6454369 3314193618479362985304403 := by
  unfold tailWord_6454369
  simp only [CollatzResearch.WordTrace]
  refine ⟨235410177153930906310254161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156940118102620604206836107 235410177153930906310254161)
  ·
    refine ⟨176557632865448179732690621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235410177153930906310254161 176557632865448179732690621)
    ·
      refine ⟨66209112324543067399758983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176557632865448179732690621 66209112324543067399758983)
      ·
        refine ⟨99313668486814601099638475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66209112324543067399758983 99313668486814601099638475)
        ·
          refine ⟨148970502730221901649457713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99313668486814601099638475 148970502730221901649457713)
          ·
            refine ⟨111727877047666426237093285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148970502730221901649457713 111727877047666426237093285)
            ·
              refine ⟨20948976946437454919454991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111727877047666426237093285 20948976946437454919454991)
              ·
                refine ⟨31423465419656182379182487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20948976946437454919454991 31423465419656182379182487)
                ·
                  refine ⟨47135198129484273568773731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31423465419656182379182487 47135198129484273568773731)
                  ·
                    refine ⟨70702797194226410353160597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47135198129484273568773731 70702797194226410353160597)
                    ·
                      refine ⟨3314193618479362985304403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70702797194226410353160597 3314193618479362985304403)
                      ·
                        rfl

theorem cell23_6454369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_6454369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454369 prefixEnd_6454369 := by exact prefixLift 6454369
  have htrace : WordTrace (prefixWord ++ tailWord_6454369) baseStart_6454369 baseEnd_6454369 := by
    simpa [prefixWord, tailWord_6454369, baseEnd_6454369] using wordTrace_append hprefix tailTrace_6454369
  have hstable : (prefixWord ++ tailWord_6454369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454369).length < 2 ^ (prefixWord ++ tailWord_6454369).sum := by decide
  have hdescent : baseEnd_6454369 < baseStart_6454369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454370 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6454370 : Nat := 118140960795 + 6454370 * 2 ^ 59
def prefixEnd_6454370 : Nat := 4983230072969 + 3 ^ 40 * 6454370 * 2
def baseEnd_6454370 : Nat := 1104731377320005827130633

theorem tailTrace_6454370 : CollatzResearch.WordTrace tailWord_6454370 prefixEnd_6454370 1104731377320005827130633 := by
  unfold tailWord_6454370
  simp only [CollatzResearch.WordTrace]
  refine ⟨58852553406731820870260141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156940142417951522320693709 58852553406731820870260141)
  ·
    refine ⟨22069707527524432826347553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58852553406731820870260141 22069707527524432826347553)
    ·
      refine ⟨16552280645643324619760665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22069707527524432826347553 16552280645643324619760665)
      ·
        refine ⟨12414210484232493464820499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16552280645643324619760665 12414210484232493464820499)
        ·
          refine ⟨18621315726348740197230749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12414210484232493464820499 18621315726348740197230749)
          ·
            refine ⟨6982993397380777573961531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18621315726348740197230749 6982993397380777573961531)
            ·
              refine ⟨10474490096071166360942297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982993397380777573961531 10474490096071166360942297)
              ·
                refine ⟨7855867572053374770706723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10474490096071166360942297 7855867572053374770706723)
                ·
                  refine ⟨11783801358080062156060085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855867572053374770706723 11783801358080062156060085)
                  ·
                    refine ⟨1104731377320005827130633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11783801358080062156060085 1104731377320005827130633)
                    ·
                      rfl

theorem cell23_6454370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6454370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454370 prefixEnd_6454370 := by exact prefixLift 6454370
  have htrace : WordTrace (prefixWord ++ tailWord_6454370) baseStart_6454370 baseEnd_6454370 := by
    simpa [prefixWord, tailWord_6454370, baseEnd_6454370] using wordTrace_append hprefix tailTrace_6454370
  have hstable : (prefixWord ++ tailWord_6454370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454370).length < 2 ^ (prefixWord ++ tailWord_6454370).sum := by decide
  have hdescent : baseEnd_6454370 < baseStart_6454370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454373 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 5, 2, 2]
def baseStart_6454373 : Nat := 118140960795 + 6454373 * 2 ^ 59
def prefixEnd_6454373 : Nat := 4983230072969 + 3 ^ 40 * 6454373 * 2
def baseEnd_6454373 : Nat := 3314195672401980969654385

theorem tailTrace_6454373 : CollatzResearch.WordTrace tailWord_6454373 prefixEnd_6454373 3314195672401980969654385 := by
  unfold tailWord_6454373
  simp only [CollatzResearch.WordTrace]
  refine ⟨235410323045916414993399773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156940215363944276662266515 235410323045916414993399773)
  ·
    refine ⟨88278871142218655622524915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235410323045916414993399773 88278871142218655622524915)
    ·
      refine ⟨132418306713327983433787373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88278871142218655622524915 132418306713327983433787373)
      ·
        refine ⟨49656865017497993787670265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132418306713327983433787373 49656865017497993787670265)
        ·
          refine ⟨37242648763123495340752699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49656865017497993787670265 37242648763123495340752699)
          ·
            refine ⟨55863973144685243011129049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37242648763123495340752699 55863973144685243011129049)
            ·
              refine ⟨41897979858513932258346787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55863973144685243011129049 41897979858513932258346787)
              ·
                refine ⟨62846969787770898387520181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41897979858513932258346787 62846969787770898387520181)
                ·
                  refine ⟨5891903417603521723830017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62846969787770898387520181 5891903417603521723830017)
                  ·
                    refine ⟨4418927563202641292872513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5891903417603521723830017 4418927563202641292872513)
                    ·
                      refine ⟨3314195672401980969654385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418927563202641292872513 3314195672401980969654385)
                      ·
                        rfl

theorem cell23_6454373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_6454373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454373 prefixEnd_6454373 := by exact prefixLift 6454373
  have htrace : WordTrace (prefixWord ++ tailWord_6454373) baseStart_6454373 baseEnd_6454373 := by
    simpa [prefixWord, tailWord_6454373, baseEnd_6454373] using wordTrace_append hprefix tailTrace_6454373
  have hstable : (prefixWord ++ tailWord_6454373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454373).length < 2 ^ (prefixWord ++ tailWord_6454373).sum := by decide
  have hdescent : baseEnd_6454373 < baseStart_6454373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454386 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6454386 : Nat := 118140960795 + 6454386 * 2 ^ 59
def prefixEnd_6454386 : Nat := 4983230072969 + 3 ^ 40 * 6454386 * 2
def baseEnd_6454386 : Nat := 3314202347650489418791825

theorem tailTrace_6454386 : CollatzResearch.WordTrace tailWord_6454386 prefixEnd_6454386 3314202347650489418791825 := by
  unfold tailWord_6454386
  simp only [CollatzResearch.WordTrace]
  refine ⟨58852699298717329553405753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156940531463246212142415341 58852699298717329553405753)
  ·
    refine ⟨44139524474037997165054315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58852699298717329553405753 44139524474037997165054315)
    ·
      refine ⟨66209286711056995747581473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44139524474037997165054315 66209286711056995747581473)
      ·
        refine ⟨49656965033292746810686105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66209286711056995747581473 49656965033292746810686105)
        ·
          refine ⟨37242723774969560108014579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49656965033292746810686105 37242723774969560108014579)
          ·
            refine ⟨55864085662454340162021869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37242723774969560108014579 55864085662454340162021869)
            ·
              refine ⟨20949032123420377560758201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55864085662454340162021869 20949032123420377560758201)
              ·
                refine ⟨15711774092565283170568651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20949032123420377560758201 15711774092565283170568651)
                ·
                  refine ⟨23567661138847924755852977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15711774092565283170568651 23567661138847924755852977)
                  ·
                    refine ⟨17675745854135943566889733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23567661138847924755852977 17675745854135943566889733)
                    ·
                      refine ⟨3314202347650489418791825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17675745854135943566889733 3314202347650489418791825)
                      ·
                        rfl

theorem cell23_6454386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6454386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454386 prefixEnd_6454386 := by exact prefixLift 6454386
  have htrace : WordTrace (prefixWord ++ tailWord_6454386) baseStart_6454386 baseEnd_6454386 := by
    simpa [prefixWord, tailWord_6454386, baseEnd_6454386] using wordTrace_append hprefix tailTrace_6454386
  have hstable : (prefixWord ++ tailWord_6454386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454386).length < 2 ^ (prefixWord ++ tailWord_6454386).sum := by decide
  have hdescent : baseEnd_6454386 < baseStart_6454386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454390 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_6454390 : Nat := 118140960795 + 6454390 * 2 ^ 59
def prefixEnd_6454390 : Nat := 4983230072969 + 3 ^ 40 * 6454390 * 2
def baseEnd_6454390 : Nat := 3314204401573107403141807

theorem tailTrace_6454390 : CollatzResearch.WordTrace tailWord_6454390 prefixEnd_6454390 3314204401573107403141807 := by
  unfold tailWord_6454390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14713183942928426681048039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156940628724569884597845749 14713183942928426681048039)
  ·
    refine ⟨22069775914392640021572059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14713183942928426681048039 22069775914392640021572059)
    ·
      refine ⟨33104663871588960032358089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22069775914392640021572059 33104663871588960032358089)
      ·
        refine ⟨24828497903691720024268567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33104663871588960032358089 24828497903691720024268567)
        ·
          refine ⟨37242746855537580036402851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24828497903691720024268567 37242746855537580036402851)
          ·
            refine ⟨55864120283306370054604277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37242746855537580036402851 55864120283306370054604277)
            ·
              refine ⟨5237261276559972192619151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55864120283306370054604277 5237261276559972192619151)
              ·
                refine ⟨7855891914839958288928727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237261276559972192619151 7855891914839958288928727)
                ·
                  refine ⟨11783837872259937433393091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855891914839958288928727 11783837872259937433393091)
                  ·
                    refine ⟨17675756808389906150089637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11783837872259937433393091 17675756808389906150089637)
                    ·
                      refine ⟨3314204401573107403141807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17675756808389906150089637 3314204401573107403141807)
                      ·
                        rfl

theorem cell23_6454390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_6454390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454390 prefixEnd_6454390 := by exact prefixLift 6454390
  have htrace : WordTrace (prefixWord ++ tailWord_6454390) baseStart_6454390 baseEnd_6454390 := by
    simpa [prefixWord, tailWord_6454390, baseEnd_6454390] using wordTrace_append hprefix tailTrace_6454390
  have hstable : (prefixWord ++ tailWord_6454390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454390).length < 2 ^ (prefixWord ++ tailWord_6454390).sum := by decide
  have hdescent : baseEnd_6454390 < baseStart_6454390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454393 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 5]
def baseStart_6454393 : Nat := 118140960795 + 6454393 * 2 ^ 59
def prefixEnd_6454393 : Nat := 4983230072969 + 3 ^ 40 * 6454393 * 2
def baseEnd_6454393 : Nat := 3314205942015070891404293

theorem tailTrace_6454393 : CollatzResearch.WordTrace tailWord_6454393 prefixEnd_6454393 3314205942015070891404293 := by
  unfold tailWord_6454393
  simp only [CollatzResearch.WordTrace]
  refine ⟨235411052505843958409127833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156940701670562638939418555 235411052505843958409127833)
  ·
    refine ⟨176558289379382968806845875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235411052505843958409127833 176558289379382968806845875)
    ·
      refine ⟨264837434069074453210268813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176558289379382968806845875 264837434069074453210268813)
      ·
        refine ⟨99314037775902919953850805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264837434069074453210268813 99314037775902919953850805)
        ·
          refine ⟨9310691041490898745673513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99314037775902919953850805 9310691041490898745673513)
          ·
            refine ⟨6983018281118174059255135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9310691041490898745673513 6983018281118174059255135)
            ·
              refine ⟨10474527421677261088882703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6983018281118174059255135 10474527421677261088882703)
              ·
                refine ⟨15711791132515891633324055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10474527421677261088882703 15711791132515891633324055)
                ·
                  refine ⟨23567686698773837449986083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15711791132515891633324055 23567686698773837449986083)
                  ·
                    refine ⟨35351530048160756174979125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23567686698773837449986083 35351530048160756174979125)
                    ·
                      refine ⟨3314205942015070891404293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35351530048160756174979125 3314205942015070891404293)
                      ·
                        rfl

theorem cell23_6454393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_6454393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454393 prefixEnd_6454393 := by exact prefixLift 6454393
  have htrace : WordTrace (prefixWord ++ tailWord_6454393) baseStart_6454393 baseEnd_6454393 := by
    simpa [prefixWord, tailWord_6454393, baseEnd_6454393] using wordTrace_append hprefix tailTrace_6454393
  have hstable : (prefixWord ++ tailWord_6454393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454393).length < 2 ^ (prefixWord ++ tailWord_6454393).sum := by decide
  have hdescent : baseEnd_6454393 < baseStart_6454393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454409 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 2, 7]
def baseStart_6454409 : Nat := 118140960795 + 6454409 * 2 ^ 59
def prefixEnd_6454409 : Nat := 4983230072969 + 3 ^ 40 * 6454409 * 2
def baseEnd_6454409 : Nat := 1104738052568514276268073

theorem tailTrace_6454409 : CollatzResearch.WordTrace tailWord_6454409 prefixEnd_6454409 1104738052568514276268073 := by
  unfold tailWord_6454409
  simp only [CollatzResearch.WordTrace]
  refine ⟨235411636073785993141710281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156941090715857328761140187 235411636073785993141710281)
  ·
    refine ⟨176558727055339494856282711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235411636073785993141710281 176558727055339494856282711)
    ·
      refine ⟨264838090583009242284424067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176558727055339494856282711 264838090583009242284424067)
      ·
        refine ⟨397257135874513863426636101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264838090583009242284424067 397257135874513863426636101)
        ·
          refine ⟨74485712976471349392494269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397257135874513863426636101 74485712976471349392494269)
          ·
            refine ⟨27932142366176756022185351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74485712976471349392494269 27932142366176756022185351)
            ·
              refine ⟨41898213549265134033278027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27932142366176756022185351 41898213549265134033278027)
              ·
                refine ⟨62847320323897701049917041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41898213549265134033278027 62847320323897701049917041)
                ·
                  refine ⟨47135490242923275787437781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62847320323897701049917041 47135490242923275787437781)
                  ·
                    refine ⟨1104738052568514276268073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47135490242923275787437781 1104738052568514276268073)
                    ·
                      rfl

theorem cell23_6454409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_6454409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454409 prefixEnd_6454409 := by exact prefixLift 6454409
  have htrace : WordTrace (prefixWord ++ tailWord_6454409) baseStart_6454409 baseEnd_6454409 := by
    simpa [prefixWord, tailWord_6454409, baseEnd_6454409] using wordTrace_append hprefix tailTrace_6454409
  have hstable : (prefixWord ++ tailWord_6454409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454409).length < 2 ^ (prefixWord ++ tailWord_6454409).sum := by decide
  have hdescent : baseEnd_6454409 < baseStart_6454409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454423 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_6454423 : Nat := 118140960795 + 6454423 * 2 ^ 59
def prefixEnd_6454423 : Nat := 4983230072969 + 3 ^ 40 * 6454423 * 2
def baseEnd_6454423 : Nat := 3314221346434705774029155

theorem tailTrace_6454423 : CollatzResearch.WordTrace tailWord_6454423 prefixEnd_6454423 3314221346434705774029155 := by
  unfold tailWord_6454423
  simp only [CollatzResearch.WordTrace]
  refine ⟨235412146695735273532719923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156941431130490182355146615 235412146695735273532719923)
  ·
    refine ⟨353118220043602910299079885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235412146695735273532719923 353118220043602910299079885)
    ·
      refine ⟨132419332516351091362154957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353118220043602910299079885 132419332516351091362154957)
      ·
        refine ⟨49657249693631659260808109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132419332516351091362154957 49657249693631659260808109)
        ·
          refine ⟨18621468635111872222803041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49657249693631659260808109 18621468635111872222803041)
          ·
            refine ⟨13966101476333904167102281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18621468635111872222803041 13966101476333904167102281)
            ·
              refine ⟨10474576107250428125326711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13966101476333904167102281 10474576107250428125326711)
              ·
                refine ⟨15711864160875642187990067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10474576107250428125326711 15711864160875642187990067)
                ·
                  refine ⟨23567796241313463281985101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15711864160875642187990067 23567796241313463281985101)
                  ·
                    refine ⟨8837923590492548730744413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23567796241313463281985101 8837923590492548730744413)
                    ·
                      refine ⟨3314221346434705774029155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8837923590492548730744413 3314221346434705774029155)
                      ·
                        rfl

theorem cell23_6454423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_6454423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454423 prefixEnd_6454423 := by exact prefixLift 6454423
  have htrace : WordTrace (prefixWord ++ tailWord_6454423) baseStart_6454423 baseEnd_6454423 := by
    simpa [prefixWord, tailWord_6454423, baseEnd_6454423] using wordTrace_append hprefix tailTrace_6454423
  have hstable : (prefixWord ++ tailWord_6454423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454423).length < 2 ^ (prefixWord ++ tailWord_6454423).sum := by decide
  have hdescent : baseEnd_6454423 < baseStart_6454423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454433 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6454433 : Nat := 118140960795 + 6454433 * 2 ^ 59
def prefixEnd_6454433 : Nat := 4983230072969 + 3 ^ 40 * 6454433 * 2
def baseEnd_6454433 : Nat := 3314226481241250734904109

theorem tailTrace_6454433 : CollatzResearch.WordTrace tailWord_6454433 prefixEnd_6454433 3314226481241250734904109 := by
  unfold tailWord_6454433
  simp only [CollatzResearch.WordTrace]
  refine ⟨235412511425699045240583953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156941674283799363493722635 235412511425699045240583953)
  ·
    refine ⟨176559383569274283930437965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235412511425699045240583953 176559383569274283930437965)
    ·
      refine ⟨66209768838477856473914237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176559383569274283930437965 66209768838477856473914237)
      ·
        refine ⟨24828663314429196177717839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66209768838477856473914237 24828663314429196177717839)
        ·
          refine ⟨37242994971643794266576759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24828663314429196177717839 37242994971643794266576759)
          ·
            refine ⟨55864492457465691399865139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37242994971643794266576759 55864492457465691399865139)
            ·
              refine ⟨83796738686198537099797709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55864492457465691399865139 83796738686198537099797709)
              ·
                refine ⟨31423777007324451412424141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83796738686198537099797709 31423777007324451412424141)
                ·
                  refine ⟨11783916377746669279659053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31423777007324451412424141 11783916377746669279659053)
                  ·
                    refine ⟨4418968641655000979872145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11783916377746669279659053 4418968641655000979872145)
                    ·
                      refine ⟨3314226481241250734904109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418968641655000979872145 3314226481241250734904109)
                      ·
                        rfl

theorem cell23_6454433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6454433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454433 prefixEnd_6454433 := by exact prefixLift 6454433
  have htrace : WordTrace (prefixWord ++ tailWord_6454433) baseStart_6454433 baseEnd_6454433 := by
    simpa [prefixWord, tailWord_6454433, baseEnd_6454433] using wordTrace_append hprefix tailTrace_6454433
  have hstable : (prefixWord ++ tailWord_6454433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454433).length < 2 ^ (prefixWord ++ tailWord_6454433).sum := by decide
  have hdescent : baseEnd_6454433 < baseStart_6454433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454450 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_6454450 : Nat := 118140960795 + 6454450 * 2 ^ 59
def prefixEnd_6454450 : Nat := 4983230072969 + 3 ^ 40 * 6454450 * 2
def baseEnd_6454450 : Nat := 3314235210412377168391531

theorem tailTrace_6454450 : CollatzResearch.WordTrace tailWord_6454450 prefixEnd_6454450 3314235210412377168391531 := by
  unfold tailWord_6454450
  simp only [CollatzResearch.WordTrace]
  refine ⟨58853282866659364285988201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156942087644424971429301869 58853282866659364285988201)
  ·
    refine ⟨44139962149994523214491151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58853282866659364285988201 44139962149994523214491151)
    ·
      refine ⟨66209943224991784821736727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44139962149994523214491151 66209943224991784821736727)
      ·
        refine ⟨99314914837487677232605091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66209943224991784821736727 99314914837487677232605091)
        ·
          refine ⟨148972372256231515848907637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99314914837487677232605091 148972372256231515848907637)
          ·
            refine ⟨13966159899021704610835091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148972372256231515848907637 13966159899021704610835091)
            ·
              refine ⟨20949239848532556916252637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13966159899021704610835091 20949239848532556916252637)
              ·
                refine ⟨7855964943199708843594739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20949239848532556916252637 7855964943199708843594739)
                ·
                  refine ⟨11783947414799563265392109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7855964943199708843594739 11783947414799563265392109)
                  ·
                    refine ⟨4418980280549836224522041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11783947414799563265392109 4418980280549836224522041)
                    ·
                      refine ⟨3314235210412377168391531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4418980280549836224522041 3314235210412377168391531)
                      ·
                        rfl

theorem cell23_6454450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_6454450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454450 prefixEnd_6454450 := by exact prefixLift 6454450
  have htrace : WordTrace (prefixWord ++ tailWord_6454450) baseStart_6454450 baseEnd_6454450 := by
    simpa [prefixWord, tailWord_6454450, baseEnd_6454450] using wordTrace_append hprefix tailTrace_6454450
  have hstable : (prefixWord ++ tailWord_6454450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454450).length < 2 ^ (prefixWord ++ tailWord_6454450).sum := by decide
  have hdescent : baseEnd_6454450 < baseStart_6454450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454484 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6454484 : Nat := 118140960795 + 6454484 * 2 ^ 59
def prefixEnd_6454484 : Nat := 4983230072969 + 3 ^ 40 * 6454484 * 2
def baseEnd_6454484 : Nat := 3314252668754630035366375

theorem tailTrace_6454484 : CollatzResearch.WordTrace tailWord_6454484 prefixEnd_6454484 3314252668754630035366375 := by
  unfold tailWord_6454484
  simp only [CollatzResearch.WordTrace]
  refine ⟨117707185774257140475345253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156942914365676187300460337 117707185774257140475345253)
  ·
    refine ⟨22070097332673213839127235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117707185774257140475345253 22070097332673213839127235)
    ·
      refine ⟨33105145999009820758690853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22070097332673213839127235 33105145999009820758690853)
      ·
        refine ⟨6207214874814341392254535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33105145999009820758690853 6207214874814341392254535)
        ·
          refine ⟨9310822312221512088381803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6207214874814341392254535 9310822312221512088381803)
          ·
            refine ⟨13966233468332268132572705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9310822312221512088381803 13966233468332268132572705)
            ·
              refine ⟨10474675101249201099429529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13966233468332268132572705 10474675101249201099429529)
              ·
                refine ⟨7856006325936900824572147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10474675101249201099429529 7856006325936900824572147)
                ·
                  refine ⟨11784009488905351236858221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7856006325936900824572147 11784009488905351236858221)
                  ·
                    refine ⟨4419003558339506713821833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11784009488905351236858221 4419003558339506713821833)
                    ·
                      refine ⟨3314252668754630035366375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419003558339506713821833 3314252668754630035366375)
                      ·
                        rfl

theorem cell23_6454484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6454484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454484 prefixEnd_6454484 := by exact prefixLift 6454484
  have htrace : WordTrace (prefixWord ++ tailWord_6454484) baseStart_6454484 baseEnd_6454484 := by
    simpa [prefixWord, tailWord_6454484, baseEnd_6454484] using wordTrace_append hprefix tailTrace_6454484
  have hstable : (prefixWord ++ tailWord_6454484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454484).length < 2 ^ (prefixWord ++ tailWord_6454484).sum := by decide
  have hdescent : baseEnd_6454484 < baseStart_6454484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454570 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6454570 : Nat := 118140960795 + 6454570 * 2 ^ 59
def prefixEnd_6454570 : Nat := 4983230072969 + 3 ^ 40 * 6454570 * 2
def baseEnd_6454570 : Nat := 3314296828090916698890979

theorem tailTrace_6454570 : CollatzResearch.WordTrace tailWord_6454570 prefixEnd_6454570 3314296828090916698890979 := by
  unfold tailWord_6454570
  simp only [CollatzResearch.WordTrace]
  refine ⟨58854377056550679409580291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156945005484135145092214109 58854377056550679409580291)
  ·
    refine ⟨88281565584826019114370437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58854377056550679409580291 88281565584826019114370437)
    ·
      refine ⟨16552793547154878583944457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88281565584826019114370437 16552793547154878583944457)
      ·
        refine ⟨12414595160366158937958343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16552793547154878583944457 12414595160366158937958343)
        ·
          refine ⟨18621892740549238406937515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12414595160366158937958343 18621892740549238406937515)
          ·
            refine ⟨27932839110823857610406273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18621892740549238406937515 27932839110823857610406273)
            ·
              refine ⟨20949629333117893207804705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27932839110823857610406273 20949629333117893207804705)
              ·
                refine ⟨15712221999838419905853529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20949629333117893207804705 15712221999838419905853529)
                ·
                  refine ⟨11784166499878814929390147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15712221999838419905853529 11784166499878814929390147)
                  ·
                    refine ⟨17676249749818222394085221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11784166499878814929390147 17676249749818222394085221)
                    ·
                      refine ⟨3314296828090916698890979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17676249749818222394085221 3314296828090916698890979)
                      ·
                        rfl

theorem cell23_6454570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6454570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454570 prefixEnd_6454570 := by exact prefixLift 6454570
  have htrace : WordTrace (prefixWord ++ tailWord_6454570) baseStart_6454570 baseEnd_6454570 := by
    simpa [prefixWord, tailWord_6454570, baseEnd_6454570] using wordTrace_append hprefix tailTrace_6454570
  have hstable : (prefixWord ++ tailWord_6454570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454570).length < 2 ^ (prefixWord ++ tailWord_6454570).sum := by decide
  have hdescent : baseEnd_6454570 < baseStart_6454570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454580 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_6454580 : Nat := 118140960795 + 6454580 * 2 ^ 59
def prefixEnd_6454580 : Nat := 4983230072969 + 3 ^ 40 * 6454580 * 2
def baseEnd_6454580 : Nat := 1104767320965820553255311

theorem tailTrace_6454580 : CollatzResearch.WordTrace tailWord_6454580 prefixEnd_6454580 1104767320965820553255311 := by
  unfold tailWord_6454580
  simp only [CollatzResearch.WordTrace]
  refine ⟨117708936478083244673092597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156945248637444326230790129 117708936478083244673092597)
  ·
    refine ⟨11035212794820304188102431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117708936478083244673092597 11035212794820304188102431)
    ·
      refine ⟨16552819192230456282153647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11035212794820304188102431 16552819192230456282153647)
      ·
        refine ⟨24829228788345684423230471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16552819192230456282153647 24829228788345684423230471)
        ·
          refine ⟨37243843182518526634845707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24829228788345684423230471 37243843182518526634845707)
          ·
            refine ⟨55865764773777789952268561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37243843182518526634845707 55865764773777789952268561)
            ·
              refine ⟨41899323580333342464201421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55865764773777789952268561 41899323580333342464201421)
              ·
                refine ⟨15712246342625003424075533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41899323580333342464201421 15712246342625003424075533)
                ·
                  refine ⟨5892092378484376284028325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15712246342625003424075533 5892092378484376284028325)
                  ·
                    refine ⟨1104767320965820553255311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892092378484376284028325 1104767320965820553255311)
                    ·
                      rfl

theorem cell23_6454580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_6454580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454580 prefixEnd_6454580 := by exact prefixLift 6454580
  have htrace : WordTrace (prefixWord ++ tailWord_6454580) baseStart_6454580 baseEnd_6454580 := by
    simpa [prefixWord, tailWord_6454580, baseEnd_6454580] using wordTrace_append hprefix tailTrace_6454580
  have hstable : (prefixWord ++ tailWord_6454580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454580).length < 2 ^ (prefixWord ++ tailWord_6454580).sum := by decide
  have hdescent : baseEnd_6454580 < baseStart_6454580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454637 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_6454637 : Nat := 118140960795 + 6454637 * 2 ^ 59
def prefixEnd_6454637 : Nat := 4983230072969 + 3 ^ 40 * 6454637 * 2
def baseEnd_6454637 : Nat := 3314331231294767936753171

theorem tailTrace_6454637 : CollatzResearch.WordTrace tailWord_6454637 prefixEnd_6454637 3314331231294767936753171 := by
  unfold tailWord_6454637
  simp only [CollatzResearch.WordTrace]
  refine ⟨235419951916959988081010165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156946634611306658720673443 235419951916959988081010165)
  ·
    refine ⟨22070620492214998882594703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235419951916959988081010165 22070620492214998882594703)
    ·
      refine ⟨33105930738322498323892055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22070620492214998882594703 33105930738322498323892055)
      ·
        refine ⟨49658896107483747485838083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33105930738322498323892055 49658896107483747485838083)
        ·
          refine ⟨74488344161225621228757125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49658896107483747485838083 74488344161225621228757125)
          ·
            refine ⟨13966564530229803980391961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74488344161225621228757125 13966564530229803980391961)
            ·
              refine ⟨10474923397672352985293971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13966564530229803980391961 10474923397672352985293971)
              ·
                refine ⟨15712385096508529477940957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10474923397672352985293971 15712385096508529477940957)
                ·
                  refine ⟨5892144411190698554227859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15712385096508529477940957 5892144411190698554227859)
                  ·
                    refine ⟨8838216616786047831341789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5892144411190698554227859 8838216616786047831341789)
                    ·
                      refine ⟨3314331231294767936753171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8838216616786047831341789 3314331231294767936753171)
                      ·
                        rfl

theorem cell23_6454637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_6454637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454637 prefixEnd_6454637 := by exact prefixLift 6454637
  have htrace : WordTrace (prefixWord ++ tailWord_6454637) baseStart_6454637 baseEnd_6454637 := by
    simpa [prefixWord, tailWord_6454637, baseEnd_6454637] using wordTrace_append hprefix tailTrace_6454637
  have hstable : (prefixWord ++ tailWord_6454637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454637).length < 2 ^ (prefixWord ++ tailWord_6454637).sum := by decide
  have hdescent : baseEnd_6454637 < baseStart_6454637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454643 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 4, 6, 2]
def baseStart_6454643 : Nat := 118140960795 + 6454643 * 2 ^ 59
def prefixEnd_6454643 : Nat := 4983230072969 + 3 ^ 40 * 6454643 * 2
def baseEnd_6454643 : Nat := 3314334312178694913278143

theorem tailTrace_6454643 : CollatzResearch.WordTrace tailWord_6454643 prefixEnd_6454643 3314334312178694913278143 := by
  unfold tailWord_6454643
  simp only [CollatzResearch.WordTrace]
  refine ⟨235420170754938251105728583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156946780503292167403819055 235420170754938251105728583)
  ·
    refine ⟨353130256132407376658592875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235420170754938251105728583 353130256132407376658592875)
    ·
      refine ⟨529695384198611064987889313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353130256132407376658592875 529695384198611064987889313)
      ·
        refine ⟨397271538148958298740916985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529695384198611064987889313 397271538148958298740916985)
        ·
          refine ⟨297953653611718724055687739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397271538148958298740916985 297953653611718724055687739)
          ·
            refine ⟨446930480417578086083531609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297953653611718724055687739 446930480417578086083531609)
            ·
              refine ⟨335197860313183564562648707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446930480417578086083531609 335197860313183564562648707)
              ·
                refine ⟨502796790469775346843973061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335197860313183564562648707 502796790469775346843973061)
                ·
                  refine ⟨94274398213082877533244949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502796790469775346843973061 94274398213082877533244949)
                  ·
                    refine ⟨4419112416238259884370857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94274398213082877533244949 4419112416238259884370857)
                    ·
                      refine ⟨3314334312178694913278143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419112416238259884370857 3314334312178694913278143)
                      ·
                        rfl

theorem cell23_6454643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6, 2].length) (baseStart_6454643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454643 prefixEnd_6454643 := by exact prefixLift 6454643
  have htrace : WordTrace (prefixWord ++ tailWord_6454643) baseStart_6454643 baseEnd_6454643 := by
    simpa [prefixWord, tailWord_6454643, baseEnd_6454643] using wordTrace_append hprefix tailTrace_6454643
  have hstable : (prefixWord ++ tailWord_6454643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454643).length < 2 ^ (prefixWord ++ tailWord_6454643).sum := by decide
  have hdescent : baseEnd_6454643 < baseStart_6454643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454657 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 1, 5]
def baseStart_6454657 : Nat := 118140960795 + 6454657 * 2 ^ 59
def prefixEnd_6454657 : Nat := 4983230072969 + 3 ^ 40 * 6454657 * 2
def baseEnd_6454657 : Nat := 1104780500302619286167693

theorem tailTrace_6454657 : CollatzResearch.WordTrace tailWord_6454657 prefixEnd_6454657 1104780500302619286167693 := by
  unfold tailWord_6454657
  simp only [CollatzResearch.WordTrace]
  refine ⟨235420681376887531496738225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156947120917925020997825483 235420681376887531496738225)
  ·
    refine ⟨176565511032665648622553669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235420681376887531496738225 176565511032665648622553669)
    ·
      refine ⟨33106033318624809116728813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176565511032665648622553669 33106033318624809116728813)
      ·
        refine ⟨12414762494484303418773305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33106033318624809116728813 12414762494484303418773305)
        ·
          refine ⟨9311071870863227564079979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12414762494484303418773305 9311071870863227564079979)
          ·
            refine ⟨13966607806294841346119969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9311071870863227564079979 13966607806294841346119969)
            ·
              refine ⟨10474955854721131009589977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13966607806294841346119969 10474955854721131009589977)
              ·
                refine ⟨7856216891040848257192483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10474955854721131009589977 7856216891040848257192483)
                ·
                  refine ⟨11784325336561272385788725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7856216891040848257192483 11784325336561272385788725)
                  ·
                    refine ⟨1104780500302619286167693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11784325336561272385788725 1104780500302619286167693)
                    ·
                      rfl

theorem cell23_6454657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_6454657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454657 prefixEnd_6454657 := by exact prefixLift 6454657
  have htrace : WordTrace (prefixWord ++ tailWord_6454657) baseStart_6454657 baseEnd_6454657 := by
    simpa [prefixWord, tailWord_6454657, baseEnd_6454657] using wordTrace_append hprefix tailTrace_6454657
  have hstable : (prefixWord ++ tailWord_6454657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454657).length < 2 ^ (prefixWord ++ tailWord_6454657).sum := by decide
  have hdescent : baseEnd_6454657 < baseStart_6454657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454660 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_6454660 : Nat := 118140960795 + 6454660 * 2 ^ 59
def prefixEnd_6454660 : Nat := 4983230072969 + 3 ^ 40 * 6454660 * 2
def baseEnd_6454660 : Nat := 3314343041349821346765565

theorem tailTrace_6454660 : CollatzResearch.WordTrace tailWord_6454660 prefixEnd_6454660 3314343041349821346765565 := by
  unfold tailWord_6454660
  simp only [CollatzResearch.WordTrace]
  refine ⟨117710395397938331504548717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156947193863917775339398289 117710395397938331504548717)
  ·
    refine ⟨44141398274226874314205769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117710395397938331504548717 44141398274226874314205769)
    ·
      refine ⟨33106048705670155735654327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44141398274226874314205769 33106048705670155735654327)
      ·
        refine ⟨49659073058505233603481491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33106048705670155735654327 49659073058505233603481491)
        ·
          refine ⟨74488609587757850405222237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49659073058505233603481491 74488609587757850405222237)
          ·
            refine ⟨27933228595409193901958339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74488609587757850405222237 27933228595409193901958339)
            ·
              refine ⟨41899842893113790852937509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27933228595409193901958339 41899842893113790852937509)
              ·
                refine ⟨7856220542458835784925783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41899842893113790852937509 7856220542458835784925783)
                ·
                  refine ⟨11784330813688253677388675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7856220542458835784925783 11784330813688253677388675)
                  ·
                    refine ⟨17676496220532380516083013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11784330813688253677388675 17676496220532380516083013)
                    ·
                      refine ⟨3314343041349821346765565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17676496220532380516083013 3314343041349821346765565)
                      ·
                        rfl

theorem cell23_6454660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_6454660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454660 prefixEnd_6454660 := by exact prefixLift 6454660
  have htrace : WordTrace (prefixWord ++ tailWord_6454660) baseStart_6454660 baseEnd_6454660 := by
    simpa [prefixWord, tailWord_6454660, baseEnd_6454660] using wordTrace_append hprefix tailTrace_6454660
  have hstable : (prefixWord ++ tailWord_6454660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454660).length < 2 ^ (prefixWord ++ tailWord_6454660).sum := by decide
  have hdescent : baseEnd_6454660 < baseStart_6454660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454693 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_6454693 : Nat := 118140960795 + 6454693 * 2 ^ 59
def prefixEnd_6454693 : Nat := 4983230072969 + 3 ^ 40 * 6454693 * 2
def baseEnd_6454693 : Nat := 3314359986211419717652913

theorem tailTrace_6454693 : CollatzResearch.WordTrace tailWord_6454693 prefixEnd_6454693 3314359986211419717652913 := by
  unfold tailWord_6454693
  simp only [CollatzResearch.WordTrace]
  refine ⟨235421994404757109645048733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156947996269838073096699155 235421994404757109645048733)
  ·
    refine ⟨88283247901783916116893275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235421994404757109645048733 88283247901783916116893275)
    ·
      refine ⟨132424871852675874175339913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88283247901783916116893275 132424871852675874175339913)
      ·
        refine ⟨99318653889506905631504935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132424871852675874175339913 99318653889506905631504935)
        ·
          refine ⟨148977980834260358447257403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99318653889506905631504935 148977980834260358447257403)
          ·
            refine ⟨223466971251390537670886105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148977980834260358447257403 223466971251390537670886105)
            ·
              refine ⟨167600228438542903253164579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223466971251390537670886105 167600228438542903253164579)
              ·
                refine ⟨251400342657814354879746869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167600228438542903253164579 251400342657814354879746869)
                ·
                  refine ⟨23568782124170095769976269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251400342657814354879746869 23568782124170095769976269)
                  ·
                    refine ⟨8838293296563785913741101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23568782124170095769976269 8838293296563785913741101)
                    ·
                      refine ⟨3314359986211419717652913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8838293296563785913741101 3314359986211419717652913)
                      ·
                        rfl

theorem cell23_6454693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_6454693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454693 prefixEnd_6454693 := by exact prefixLift 6454693
  have htrace : WordTrace (prefixWord ++ tailWord_6454693) baseStart_6454693 baseEnd_6454693 := by
    simpa [prefixWord, tailWord_6454693, baseEnd_6454693] using wordTrace_append hprefix tailTrace_6454693
  have hstable : (prefixWord ++ tailWord_6454693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454693).length < 2 ^ (prefixWord ++ tailWord_6454693).sum := by decide
  have hdescent : baseEnd_6454693 < baseStart_6454693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454788 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6454788 : Nat := 118140960795 + 6454788 * 2 ^ 59
def prefixEnd_6454788 : Nat := 4983230072969 + 3 ^ 40 * 6454788 * 2
def baseEnd_6454788 : Nat := 3314408766873596845964977

theorem tailTrace_6454788 : CollatzResearch.WordTrace tailWord_6454788 prefixEnd_6454788 3314408766873596845964977 := by
  unfold tailWord_6454788
  simp only [CollatzResearch.WordTrace]
  refine ⟨117712729669706470434878509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156950306226275293913171345 117712729669706470434878509)
  ·
    refine ⟨44142273626139926413079441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117712729669706470434878509 44142273626139926413079441)
    ·
      refine ⟨33106705219604944809809581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44142273626139926413079441 33106705219604944809809581)
      ·
        refine ⟨12415014457351854303678593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33106705219604944809809581 12415014457351854303678593)
        ·
          refine ⟨9311260843013890727758945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12415014457351854303678593 9311260843013890727758945)
          ·
            refine ⟨6983445632260418045819209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9311260843013890727758945 6983445632260418045819209)
            ·
              refine ⟨5237584224195313534364407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6983445632260418045819209 5237584224195313534364407)
              ·
                refine ⟨7856376336292970301546611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237584224195313534364407 7856376336292970301546611)
                ·
                  refine ⟨11784564504439455452319917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7856376336292970301546611 11784564504439455452319917)
                  ·
                    refine ⟨4419211689164795794619969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11784564504439455452319917 4419211689164795794619969)
                    ·
                      refine ⟨3314408766873596845964977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419211689164795794619969 3314408766873596845964977)
                      ·
                        rfl

theorem cell23_6454788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6454788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454788 prefixEnd_6454788 := by exact prefixLift 6454788
  have htrace : WordTrace (prefixWord ++ tailWord_6454788) baseStart_6454788 baseEnd_6454788 := by
    simpa [prefixWord, tailWord_6454788, baseEnd_6454788] using wordTrace_append hprefix tailTrace_6454788
  have hstable : (prefixWord ++ tailWord_6454788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454788).length < 2 ^ (prefixWord ++ tailWord_6454788).sum := by decide
  have hdescent : baseEnd_6454788 < baseStart_6454788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454833 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 10]
def baseStart_6454833 : Nat := 118140960795 + 6454833 * 2 ^ 59
def prefixEnd_6454833 : Nat := 4983230072969 + 3 ^ 40 * 6454833 * 2
def baseEnd_6454833 : Nat := 1104810624501016389967423

theorem tailTrace_6454833 : CollatzResearch.WordTrace tailWord_6454833 prefixEnd_6454833 1104810624501016389967423 := by
  unfold tailWord_6454833
  simp only [CollatzResearch.WordTrace]
  refine ⟨235427100624249913555145153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156951400416166609036763435 235427100624249913555145153)
  ·
    refine ⟨176570325468187435166358865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235427100624249913555145153 176570325468187435166358865)
    ·
      refine ⟨132427744101140576374769149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176570325468187435166358865 132427744101140576374769149)
      ·
        refine ⟨49660404037927716140538431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132427744101140576374769149 49660404037927716140538431)
        ·
          refine ⟨74490606056891574210807647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49660404037927716140538431 74490606056891574210807647)
          ·
            refine ⟨111735909085337361316211471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74490606056891574210807647 111735909085337361316211471)
            ·
              refine ⟨167603863628006041974317207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111735909085337361316211471 167603863628006041974317207)
              ·
                refine ⟨251405795442009062961475811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167603863628006041974317207 251405795442009062961475811)
                ·
                  refine ⟨377108693163013594442213717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251405795442009062961475811 377108693163013594442213717)
                  ·
                    refine ⟨1104810624501016389967423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 377108693163013594442213717 1104810624501016389967423)
                    ·
                      rfl

theorem cell23_6454833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_6454833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454833 prefixEnd_6454833 := by exact prefixLift 6454833
  have htrace : WordTrace (prefixWord ++ tailWord_6454833) baseStart_6454833 baseEnd_6454833 := by
    simpa [prefixWord, tailWord_6454833, baseEnd_6454833] using wordTrace_append hprefix tailTrace_6454833
  have hstable : (prefixWord ++ tailWord_6454833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454833).length < 2 ^ (prefixWord ++ tailWord_6454833).sum := by decide
  have hdescent : baseEnd_6454833 < baseStart_6454833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454840 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_6454840 : Nat := 118140960795 + 6454840 * 2 ^ 59
def prefixEnd_6454840 : Nat := 4983230072969 + 3 ^ 40 * 6454840 * 2
def baseEnd_6454840 : Nat := 3314435467867630642514737

theorem tailTrace_6454840 : CollatzResearch.WordTrace tailWord_6454840 prefixEnd_6454840 3314435467867630642514737 := by
  unfold tailWord_6454840
  simp only [CollatzResearch.WordTrace]
  refine ⟨117713677967612276875324987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156951570623483035833766649 117713677967612276875324987)
  ·
    refine ⟨176570516951418415312987481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117713677967612276875324987 176570516951418415312987481)
    ·
      refine ⟨132427887713563811484740611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176570516951418415312987481 132427887713563811484740611)
      ·
        refine ⟨198641831570345717227110917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132427887713563811484740611 198641831570345717227110917)
        ·
          refine ⟨37245343419439821980083297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198641831570345717227110917 37245343419439821980083297)
          ·
            refine ⟨27934007564579866485062473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37245343419439821980083297 27934007564579866485062473)
            ·
              refine ⟨20950505673434899863796855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27934007564579866485062473 20950505673434899863796855)
              ·
                refine ⟨31425758510152349795695283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20950505673434899863796855 31425758510152349795695283)
                ·
                  refine ⟨47138637765228524693542925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31425758510152349795695283 47138637765228524693542925)
                  ·
                    refine ⟨17676989161960696760078597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47138637765228524693542925 17676989161960696760078597)
                    ·
                      refine ⟨3314435467867630642514737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17676989161960696760078597 3314435467867630642514737)
                      ·
                        rfl

theorem cell23_6454840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_6454840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454840 prefixEnd_6454840 := by exact prefixLift 6454840
  have htrace : WordTrace (prefixWord ++ tailWord_6454840) baseStart_6454840 baseEnd_6454840 := by
    simpa [prefixWord, tailWord_6454840, baseEnd_6454840] using wordTrace_append hprefix tailTrace_6454840
  have hstable : (prefixWord ++ tailWord_6454840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454840).length < 2 ^ (prefixWord ++ tailWord_6454840).sum := by decide
  have hdescent : baseEnd_6454840 < baseStart_6454840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454947 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 4]
def baseStart_6454947 : Nat := 118140960795 + 6454947 * 2 ^ 59
def prefixEnd_6454947 : Nat := 4983230072969 + 3 ^ 40 * 6454947 * 2
def baseEnd_6454947 : Nat := 3314490410297661723876745

theorem tailTrace_6454947 : CollatzResearch.WordTrace tailWord_6454947 prefixEnd_6454947 3314490410297661723876745 := by
  unfold tailWord_6454947
  simp only [CollatzResearch.WordTrace]
  refine ⟨235431258545836911024795095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156954172363891274016530063 235431258545836911024795095)
  ·
    refine ⟨353146887818755366537192643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235431258545836911024795095 353146887818755366537192643)
    ·
      refine ⟨529720331728133049805788965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353146887818755366537192643 529720331728133049805788965)
      ·
        refine ⟨99322562199024946838585431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 529720331728133049805788965 99322562199024946838585431)
        ·
          refine ⟨148983843298537420257878147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99322562199024946838585431 148983843298537420257878147)
          ·
            refine ⟨223475764947806130386817221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148983843298537420257878147 223475764947806130386817221)
            ·
              refine ⟨41901705927713649447528229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223475764947806130386817221 41901705927713649447528229)
              ·
                refine ⟨7856569861446309271411543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41901705927713649447528229 7856569861446309271411543)
                ·
                  refine ⟨11784854792169463907117315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7856569861446309271411543 11784854792169463907117315)
                  ·
                    refine ⟨17677282188254195860675973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11784854792169463907117315 17677282188254195860675973)
                    ·
                      refine ⟨3314490410297661723876745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17677282188254195860675973 3314490410297661723876745)
                      ·
                        rfl

theorem cell23_6454947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_6454947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454947 prefixEnd_6454947 := by exact prefixLift 6454947
  have htrace : WordTrace (prefixWord ++ tailWord_6454947) baseStart_6454947 baseEnd_6454947 := by
    simpa [prefixWord, tailWord_6454947, baseEnd_6454947] using wordTrace_append hprefix tailTrace_6454947
  have hstable : (prefixWord ++ tailWord_6454947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454947).length < 2 ^ (prefixWord ++ tailWord_6454947).sum := by decide
  have hdescent : baseEnd_6454947 < baseStart_6454947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454957 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6454957 : Nat := 118140960795 + 6454957 * 2 ^ 59
def prefixEnd_6454957 : Nat := 4983230072969 + 3 ^ 40 * 6454957 * 2
def baseEnd_6454957 : Nat := 1104831848368068894917233

theorem tailTrace_6454957 : CollatzResearch.WordTrace tailWord_6454957 prefixEnd_6454957 1104831848368068894917233 := by
  unfold tailWord_6454957
  simp only [CollatzResearch.WordTrace]
  refine ⟨235431623275800682732659125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156954415517200455155106083 235431623275800682732659125)
  ·
    refine ⟨22071714682106314006186793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235431623275800682732659125 22071714682106314006186793)
    ·
      refine ⟨16553786011579735504640095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22071714682106314006186793 16553786011579735504640095)
      ·
        refine ⟨24830679017369603256960143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16553786011579735504640095 24830679017369603256960143)
        ·
          refine ⟨37246018526054404885440215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24830679017369603256960143 37246018526054404885440215)
          ·
            refine ⟨55869027789081607328160323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37246018526054404885440215 55869027789081607328160323)
            ·
              refine ⟨83803541683622410992240485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55869027789081607328160323 83803541683622410992240485)
              ·
                refine ⟨15713164065679202061045091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83803541683622410992240485 15713164065679202061045091)
                ·
                  refine ⟨23569746098518803091567637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15713164065679202061045091 23569746098518803091567637)
                  ·
                    refine ⟨1104831848368068894917233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23569746098518803091567637 1104831848368068894917233)
                    ·
                      rfl

theorem cell23_6454957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6454957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454957 prefixEnd_6454957 := by exact prefixLift 6454957
  have htrace : WordTrace (prefixWord ++ tailWord_6454957) baseStart_6454957 baseEnd_6454957 := by
    simpa [prefixWord, tailWord_6454957, baseEnd_6454957] using wordTrace_append hprefix tailTrace_6454957
  have hstable : (prefixWord ++ tailWord_6454957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454957).length < 2 ^ (prefixWord ++ tailWord_6454957).sum := by decide
  have hdescent : baseEnd_6454957 < baseStart_6454957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454970 : List Nat := [3, 1, 1, 1, 2, 5, 10]
def baseStart_6454970 : Nat := 118140960795 + 6454970 * 2 ^ 59
def prefixEnd_6454970 : Nat := 4983230072969 + 3 ^ 40 * 6454970 * 2
def baseEnd_6454970 : Nat := 40919780498181668319619

theorem tailTrace_6454970 : CollatzResearch.WordTrace tailWord_6454970 prefixEnd_6454970 40919780498181668319619 := by
  unfold tailWord_6454970
  simp only [CollatzResearch.WordTrace]
  refine ⟨58858024356188396488220591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156954731616502390635254909 58858024356188396488220591)
  ·
    refine ⟨88287036534282594732330887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58858024356188396488220591 88287036534282594732330887)
    ·
      refine ⟨132430554801423892098496331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88287036534282594732330887 132430554801423892098496331)
      ·
        refine ⟨198645832202135838147744497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132430554801423892098496331 198645832202135838147744497)
        ·
          refine ⟨148984374151601878610808373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198645832202135838147744497 148984374151601878610808373)
          ·
            refine ⟨13967285076712676119763285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148984374151601878610808373 13967285076712676119763285)
            ·
              refine ⟨40919780498181668319619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13967285076712676119763285 40919780498181668319619)
              ·
                rfl

theorem cell23_6454970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 10].length) (baseStart_6454970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454970 prefixEnd_6454970 := by exact prefixLift 6454970
  have htrace : WordTrace (prefixWord ++ tailWord_6454970) baseStart_6454970 baseEnd_6454970 := by
    simpa [prefixWord, tailWord_6454970, baseEnd_6454970] using wordTrace_append hprefix tailTrace_6454970
  have hstable : (prefixWord ++ tailWord_6454970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454970).length < 2 ^ (prefixWord ++ tailWord_6454970).sum := by decide
  have hdescent : baseEnd_6454970 < baseStart_6454970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454974 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_6454974 : Nat := 118140960795 + 6454974 * 2 ^ 59
def prefixEnd_6454974 : Nat := 4983230072969 + 3 ^ 40 * 6454974 * 2
def baseEnd_6454974 : Nat := 1104834758091777706079707

theorem tailTrace_6454974 : CollatzResearch.WordTrace tailWord_6454974 prefixEnd_6454974 1104834758091777706079707 := by
  unfold tailWord_6454974
  simp only [CollatzResearch.WordTrace]
  refine ⟨29429030414592386829503497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156954828877826063090685317 29429030414592386829503497)
  ·
    refine ⟨22071772810944290122127623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29429030414592386829503497 22071772810944290122127623)
    ·
      refine ⟨33107659216416435183191435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22071772810944290122127623 33107659216416435183191435)
      ·
        refine ⟨49661488824624652774787153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33107659216416435183191435 49661488824624652774787153)
        ·
          refine ⟨37246116618468489581090365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49661488824624652774787153 37246116618468489581090365)
          ·
            refine ⟨13967293731925683592908887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37246116618468489581090365 13967293731925683592908887)
            ·
              refine ⟨20950940597888525389363331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13967293731925683592908887 20950940597888525389363331)
              ·
                refine ⟨31426410896832788084044997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20950940597888525389363331 31426410896832788084044997)
                ·
                  refine ⟨5892452043156147765758437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31426410896832788084044997 5892452043156147765758437)
                  ·
                    refine ⟨1104834758091777706079707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892452043156147765758437 1104834758091777706079707)
                    ·
                      rfl

theorem cell23_6454974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_6454974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454974 prefixEnd_6454974 := by exact prefixLift 6454974
  have htrace : WordTrace (prefixWord ++ tailWord_6454974) baseStart_6454974 baseEnd_6454974 := by
    simpa [prefixWord, tailWord_6454974, baseEnd_6454974] using wordTrace_append hprefix tailTrace_6454974
  have hstable : (prefixWord ++ tailWord_6454974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454974).length < 2 ^ (prefixWord ++ tailWord_6454974).sum := by decide
  have hdescent : baseEnd_6454974 < baseStart_6454974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6454994 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_6454994 : Nat := 118140960795 + 6454994 * 2 ^ 59
def prefixEnd_6454994 : Nat := 4983230072969 + 3 ^ 40 * 6454994 * 2
def baseEnd_6454994 : Nat := 3314514543888423039989029

theorem tailTrace_6454994 : CollatzResearch.WordTrace tailWord_6454994 prefixEnd_6454994 3314514543888423039989029 := by
  unfold tailWord_6454994
  simp only [CollatzResearch.WordTrace]
  refine ⟨58858243194166659512939009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156955315184444425367837357 58858243194166659512939009)
  ·
    refine ⟨44143682395624994634704257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58858243194166659512939009 44143682395624994634704257)
    ·
      refine ⟨33107761796718745976028193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44143682395624994634704257 33107761796718745976028193)
      ·
        refine ⟨24830821347539059482021145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33107761796718745976028193 24830821347539059482021145)
        ·
          refine ⟨18623116010654294611515859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24830821347539059482021145 18623116010654294611515859)
          ·
            refine ⟨27934674015981441917273789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18623116010654294611515859 27934674015981441917273789)
            ·
              refine ⟨10475502755993040718977671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27934674015981441917273789 10475502755993040718977671)
              ·
                refine ⟨15713254133989561078466507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10475502755993040718977671 15713254133989561078466507)
                ·
                  refine ⟨23569881200984341617699761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15713254133989561078466507 23569881200984341617699761)
                  ·
                    refine ⟨17677410900738256213274821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23569881200984341617699761 17677410900738256213274821)
                    ·
                      refine ⟨3314514543888423039989029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17677410900738256213274821 3314514543888423039989029)
                      ·
                        rfl

theorem cell23_6454994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_6454994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6454994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6454994 prefixEnd_6454994 := by exact prefixLift 6454994
  have htrace : WordTrace (prefixWord ++ tailWord_6454994) baseStart_6454994 baseEnd_6454994 := by
    simpa [prefixWord, tailWord_6454994, baseEnd_6454994] using wordTrace_append hprefix tailTrace_6454994
  have hstable : (prefixWord ++ tailWord_6454994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6454994).length < 2 ^ (prefixWord ++ tailWord_6454994).sum := by decide
  have hdescent : baseEnd_6454994 < baseStart_6454994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6454994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455004 : List Nat := [2, 2, 5, 1, 2, 1, 1, 9]
def baseStart_6455004 : Nat := 118140960795 + 6455004 * 2 ^ 59
def prefixEnd_6455004 : Nat := 4983230072969 + 3 ^ 40 * 6455004 * 2
def baseEnd_6455004 : Nat := 122759988099813629661629

theorem tailTrace_6455004 : CollatzResearch.WordTrace tailWord_6455004 prefixEnd_6455004 122759988099813629661629 := by
  unfold tailWord_6455004
  simp only [CollatzResearch.WordTrace]
  refine ⟨117716668753315204879810033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156955558337753606506413377 117716668753315204879810033)
  ·
    refine ⟨88287501564986403659857525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117716668753315204879810033 88287501564986403659857525)
    ·
      refine ⟨8276953271717475343111643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88287501564986403659857525 8276953271717475343111643)
      ·
        refine ⟨12415429907576213014667465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8276953271717475343111643 12415429907576213014667465)
        ·
          refine ⟨9311572430682159761000599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12415429907576213014667465 9311572430682159761000599)
          ·
            refine ⟨13967358646023239641500899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9311572430682159761000599 13967358646023239641500899)
            ·
              refine ⟨20951037969034859462251349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13967358646023239641500899 20951037969034859462251349)
              ·
                refine ⟨122759988099813629661629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20951037969034859462251349 122759988099813629661629)
                ·
                  rfl

theorem cell23_6455004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 9].length) (baseStart_6455004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455004 prefixEnd_6455004 := by exact prefixLift 6455004
  have htrace : WordTrace (prefixWord ++ tailWord_6455004) baseStart_6455004 baseEnd_6455004 := by
    simpa [prefixWord, tailWord_6455004, baseEnd_6455004] using wordTrace_append hprefix tailTrace_6455004
  have hstable : (prefixWord ++ tailWord_6455004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455004).length < 2 ^ (prefixWord ++ tailWord_6455004).sum := by decide
  have hdescent : baseEnd_6455004 < baseStart_6455004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455058 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6455058 : Nat := 118140960795 + 6455058 * 2 ^ 59
def prefixEnd_6455058 : Nat := 4983230072969 + 3 ^ 40 * 6455058 * 2
def baseEnd_6455058 : Nat := 3314547406650310789588735

theorem tailTrace_6455058 : CollatzResearch.WordTrace tailWord_6455058 prefixEnd_6455058 3314547406650310789588735 := by
  unfold tailWord_6455058
  simp only [CollatzResearch.WordTrace]
  refine ⟨58858826762108694245521457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156956871365623184654723885 58858826762108694245521457)
  ·
    refine ⟨44144120071581520684141093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58858826762108694245521457 44144120071581520684141093)
    ·
      refine ⟨8277022513421535128276455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44144120071581520684141093 8277022513421535128276455)
      ·
        refine ⟨12415533770132302692414683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8277022513421535128276455 12415533770132302692414683)
        ·
          refine ⟨18623300655198454038622025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12415533770132302692414683 18623300655198454038622025)
          ·
            refine ⟨13967475491398840528966519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18623300655198454038622025 13967475491398840528966519)
            ·
              refine ⟨20951213237098260793449779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13967475491398840528966519 20951213237098260793449779)
              ·
                refine ⟨31426819855647391190174669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20951213237098260793449779 31426819855647391190174669)
                ·
                  refine ⟨11785057445867771696315501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31426819855647391190174669 11785057445867771696315501)
                  ·
                    refine ⟨4419396542200414386118313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11785057445867771696315501 4419396542200414386118313)
                    ·
                      refine ⟨3314547406650310789588735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419396542200414386118313 3314547406650310789588735)
                      ·
                        rfl

theorem cell23_6455058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6455058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455058 prefixEnd_6455058 := by exact prefixLift 6455058
  have htrace : WordTrace (prefixWord ++ tailWord_6455058) baseStart_6455058 baseEnd_6455058 := by
    simpa [prefixWord, tailWord_6455058, baseEnd_6455058] using wordTrace_append hprefix tailTrace_6455058
  have hstable : (prefixWord ++ tailWord_6455058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455058).length < 2 ^ (prefixWord ++ tailWord_6455058).sum := by decide
  have hdescent : baseEnd_6455058 < baseStart_6455058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455087 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 3]
def baseStart_6455087 : Nat := 118140960795 + 6455087 * 2 ^ 59
def prefixEnd_6455087 : Nat := 4983230072969 + 3 ^ 40 * 6455087 * 2
def baseEnd_6455087 : Nat := 3314562297589291176126101

theorem tailTrace_6455087 : CollatzResearch.WordTrace tailWord_6455087 prefixEnd_6455087 3314562297589291176126101 := by
  unfold tailWord_6455087
  simp only [CollatzResearch.WordTrace]
  refine ⟨235436364765329714934891515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156957576510219809956594343 235436364765329714934891515)
  ·
    refine ⟨353154547147994572402337273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235436364765329714934891515 353154547147994572402337273)
    ·
      refine ⟨264865910360995929301752955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353154547147994572402337273 264865910360995929301752955)
      ·
        refine ⟨397298865541493893952629433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264865910360995929301752955 397298865541493893952629433)
        ·
          refine ⟨297974149156120420464472075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397298865541493893952629433 297974149156120420464472075)
          ·
            refine ⟨446961223734180630696708113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297974149156120420464472075 446961223734180630696708113)
            ·
              refine ⟨335220917800635473022531085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446961223734180630696708113 335220917800635473022531085)
              ·
                refine ⟨125707844175238302383449157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335220917800635473022531085 125707844175238302383449157)
                ·
                  refine ⟨23570220782857181696896717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125707844175238302383449157 23570220782857181696896717)
                  ·
                    refine ⟨8838832793571443136336269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23570220782857181696896717 8838832793571443136336269)
                    ·
                      refine ⟨3314562297589291176126101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8838832793571443136336269 3314562297589291176126101)
                      ·
                        rfl

theorem cell23_6455087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_6455087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455087 prefixEnd_6455087 := by exact prefixLift 6455087
  have htrace : WordTrace (prefixWord ++ tailWord_6455087) baseStart_6455087 baseEnd_6455087 := by
    simpa [prefixWord, tailWord_6455087, baseEnd_6455087] using wordTrace_append hprefix tailTrace_6455087
  have hstable : (prefixWord ++ tailWord_6455087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455087).length < 2 ^ (prefixWord ++ tailWord_6455087).sum := by decide
  have hdescent : baseEnd_6455087 < baseStart_6455087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455114 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_6455114 : Nat := 118140960795 + 6455114 * 2 ^ 59
def prefixEnd_6455114 : Nat := 4983230072969 + 3 ^ 40 * 6455114 * 2
def baseEnd_6455114 : Nat := 3314576161566962570488477

theorem tailTrace_6455114 : CollatzResearch.WordTrace tailWord_6455114 prefixEnd_6455114 3314576161566962570488477 := by
  unfold tailWord_6455114
  simp only [CollatzResearch.WordTrace]
  refine ⟨58859337384057974636531099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156958233024154599030749597 58859337384057974636531099)
  ·
    refine ⟨88289006076086961954796649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58859337384057974636531099 88289006076086961954796649)
    ·
      refine ⟨66216754557065221466097487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88289006076086961954796649 66216754557065221466097487)
      ·
        refine ⟨99325131835597832199146231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66216754557065221466097487 99325131835597832199146231)
        ·
          refine ⟨148987697753396748298719347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99325131835597832199146231 148987697753396748298719347)
          ·
            refine ⟨223481546630095122448079021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148987697753396748298719347 223481546630095122448079021)
            ·
              refine ⟨83805579986285670918029633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223481546630095122448079021 83805579986285670918029633)
              ·
                refine ⟨62854184989714253188522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83805579986285670918029633 62854184989714253188522225)
                ·
                  refine ⟨47140638742285689891391669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62854184989714253188522225 47140638742285689891391669)
                  ·
                    refine ⟨4419434882089283427317969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47140638742285689891391669 4419434882089283427317969)
                    ·
                      refine ⟨3314576161566962570488477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419434882089283427317969 3314576161566962570488477)
                      ·
                        rfl

theorem cell23_6455114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_6455114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455114 prefixEnd_6455114 := by exact prefixLift 6455114
  have htrace : WordTrace (prefixWord ++ tailWord_6455114) baseStart_6455114 baseEnd_6455114 := by
    simpa [prefixWord, tailWord_6455114, baseEnd_6455114] using wordTrace_append hprefix tailTrace_6455114
  have hstable : (prefixWord ++ tailWord_6455114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455114).length < 2 ^ (prefixWord ++ tailWord_6455114).sum := by decide
  have hdescent : baseEnd_6455114 < baseStart_6455114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455124 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_6455124 : Nat := 118140960795 + 6455124 * 2 ^ 59
def prefixEnd_6455124 : Nat := 4983230072969 + 3 ^ 40 * 6455124 * 2
def baseEnd_6455124 : Nat := 1104860432124502510454477

theorem tailTrace_6455124 : CollatzResearch.WordTrace tailWord_6455124 prefixEnd_6455124 1104860432124502510454477 := by
  unfold tailWord_6455124
  simp only [CollatzResearch.WordTrace]
  refine ⟨117718857133097835126994213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156958476177463780169325617 117718857133097835126994213)
  ·
    refine ⟨22072285712455844086311415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117718857133097835126994213 22072285712455844086311415)
    ·
      refine ⟨33108428568683766129467123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22072285712455844086311415 33108428568683766129467123)
      ·
        refine ⟨49662642853025649194200685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33108428568683766129467123 49662642853025649194200685)
        ·
          refine ⟨18623491069884618447825257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49662642853025649194200685 18623491069884618447825257)
          ·
            refine ⟨13967618302413463835868943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18623491069884618447825257 13967618302413463835868943)
            ·
              refine ⟨20951427453620195753803415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13967618302413463835868943 20951427453620195753803415)
              ·
                refine ⟨31427141180430293630705123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20951427453620195753803415 31427141180430293630705123)
                ·
                  refine ⟨47140711770645440446057685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31427141180430293630705123 47140711770645440446057685)
                  ·
                    refine ⟨1104860432124502510454477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47140711770645440446057685 1104860432124502510454477)
                    ·
                      rfl

theorem cell23_6455124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_6455124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455124 prefixEnd_6455124 := by exact prefixLift 6455124
  have htrace : WordTrace (prefixWord ++ tailWord_6455124) baseStart_6455124 baseEnd_6455124 := by
    simpa [prefixWord, tailWord_6455124, baseEnd_6455124] using wordTrace_append hprefix tailTrace_6455124
  have hstable : (prefixWord ++ tailWord_6455124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455124).length < 2 ^ (prefixWord ++ tailWord_6455124).sum := by decide
  have hdescent : baseEnd_6455124 < baseStart_6455124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455144 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6455144 : Nat := 118140960795 + 6455144 * 2 ^ 59
def prefixEnd_6455144 : Nat := 4983230072969 + 3 ^ 40 * 6455144 * 2
def baseEnd_6455144 : Nat := 3314591565986597453113339

theorem tailTrace_6455144 : CollatzResearch.WordTrace tailWord_6455144 prefixEnd_6455144 3314591565986597453113339 := by
  unfold tailWord_6455144
  simp only [CollatzResearch.WordTrace]
  refine ⟨117719221863061606834858243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156958962484082142446477657 117719221863061606834858243)
  ·
    refine ⟨176578832794592410252287365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117719221863061606834858243 176578832794592410252287365)
    ·
      refine ⟨33108531148986076922303881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176578832794592410252287365 33108531148986076922303881)
      ·
        refine ⟨24831398361739557691727911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33108531148986076922303881 24831398361739557691727911)
        ·
          refine ⟨37247097542609336537591867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24831398361739557691727911 37247097542609336537591867)
          ·
            refine ⟨55870646313914004806387801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37247097542609336537591867 55870646313914004806387801)
            ·
              refine ⟨41902984735435503604790851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55870646313914004806387801 41902984735435503604790851)
              ·
                refine ⟨62854477103153255407186277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41902984735435503604790851 62854477103153255407186277)
                ·
                  refine ⟨11785214456841235388847427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62854477103153255407186277 11785214456841235388847427)
                  ·
                    refine ⟨17677821685261853083271141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11785214456841235388847427 17677821685261853083271141)
                    ·
                      refine ⟨3314591565986597453113339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17677821685261853083271141 3314591565986597453113339)
                      ·
                        rfl

theorem cell23_6455144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6455144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455144 prefixEnd_6455144 := by exact prefixLift 6455144
  have htrace : WordTrace (prefixWord ++ tailWord_6455144) baseStart_6455144 baseEnd_6455144 := by
    simpa [prefixWord, tailWord_6455144, baseEnd_6455144] using wordTrace_append hprefix tailTrace_6455144
  have hstable : (prefixWord ++ tailWord_6455144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455144).length < 2 ^ (prefixWord ++ tailWord_6455144).sum := by decide
  have hdescent : baseEnd_6455144 < baseStart_6455144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455244 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_6455244 : Nat := 118140960795 + 6455244 * 2 ^ 59
def prefixEnd_6455244 : Nat := 4983230072969 + 3 ^ 40 * 6455244 * 2
def baseEnd_6455244 : Nat := 1104880971350682353954293

theorem tailTrace_6455244 : CollatzResearch.WordTrace tailWord_6455244 prefixEnd_6455244 1104880971350682353954293 := by
  unfold tailWord_6455244
  simp only [CollatzResearch.WordTrace]
  refine ⟨117721045512880465374178393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156961394017173953832237857 117721045512880465374178393)
  ·
    refine ⟨88290784134660349030633795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117721045512880465374178393 88290784134660349030633795)
    ·
      refine ⟨132436176201990523545950693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88290784134660349030633795 132436176201990523545950693)
      ·
        refine ⟨24831783037873223164865755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132436176201990523545950693 24831783037873223164865755)
        ·
          refine ⟨37247674556809834747298633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24831783037873223164865755 37247674556809834747298633)
          ·
            refine ⟨27935755917607376060473975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37247674556809834747298633 27935755917607376060473975)
            ·
              refine ⟨41903633876411064090710963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27935755917607376060473975 41903633876411064090710963)
              ·
                refine ⟨62855450814616596136066445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41903633876411064090710963 62855450814616596136066445)
                ·
                  refine ⟨23570794055481223551024917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62855450814616596136066445 23570794055481223551024917)
                  ·
                    refine ⟨1104880971350682353954293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23570794055481223551024917 1104880971350682353954293)
                    ·
                      rfl

theorem cell23_6455244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_6455244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455244 prefixEnd_6455244 := by exact prefixLift 6455244
  have htrace : WordTrace (prefixWord ++ tailWord_6455244) baseStart_6455244 baseEnd_6455244 := by
    simpa [prefixWord, tailWord_6455244, baseEnd_6455244] using wordTrace_append hprefix tailTrace_6455244
  have hstable : (prefixWord ++ tailWord_6455244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455244).length < 2 ^ (prefixWord ++ tailWord_6455244).sum := by decide
  have hdescent : baseEnd_6455244 < baseStart_6455244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455257 : List Nat := [1, 2, 1, 2, 17]
def baseStart_6455257 : Nat := 118140960795 + 6455257 * 2 ^ 59
def prefixEnd_6455257 : Nat := 4983230072969 + 3 ^ 40 * 6455257 * 2
def baseEnd_6455257 : Nat := 4546844429767565858711

theorem tailTrace_6455257 : CollatzResearch.WordTrace tailWord_6455257 prefixEnd_6455257 4546844429767565858711 := by
  unfold tailWord_6455257
  simp only [CollatzResearch.WordTrace]
  refine ⟨235442565174713833968580025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156961710116475889312386683 235442565174713833968580025)
  ·
    refine ⟨176581923881035375476435019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235442565174713833968580025 176581923881035375476435019)
    ·
      refine ⟨264872885821553063214652529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176581923881035375476435019 264872885821553063214652529)
      ·
        refine ⟨198654664366164797410989397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264872885821553063214652529 198654664366164797410989397)
        ·
          refine ⟨4546844429767565858711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 198654664366164797410989397 4546844429767565858711)
          ·
            rfl

theorem cell23_6455257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 17].length) (baseStart_6455257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455257 prefixEnd_6455257 := by exact prefixLift 6455257
  have htrace : WordTrace (prefixWord ++ tailWord_6455257) baseStart_6455257 baseEnd_6455257 := by
    simpa [prefixWord, tailWord_6455257, baseEnd_6455257] using wordTrace_append hprefix tailTrace_6455257
  have hstable : (prefixWord ++ tailWord_6455257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455257).length < 2 ^ (prefixWord ++ tailWord_6455257).sum := by decide
  have hdescent : baseEnd_6455257 < baseStart_6455257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455268 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_6455268 : Nat := 118140960795 + 6455268 * 2 ^ 59
def prefixEnd_6455268 : Nat := 4983230072969 + 3 ^ 40 * 6455268 * 2
def baseEnd_6455268 : Nat := 3314655237587754967962769

theorem tailTrace_6455268 : CollatzResearch.WordTrace tailWord_6455268 prefixEnd_6455268 3314655237587754967962769 := by
  unfold tailWord_6455268
  simp only [CollatzResearch.WordTrace]
  refine ⟨117721483188836991423615229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156961977585115988564820305 117721483188836991423615229)
  ·
    refine ⟨44145556195813871783855711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117721483188836991423615229 44145556195813871783855711)
    ·
      refine ⟨66218334293720807675783567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44145556195813871783855711 66218334293720807675783567)
      ·
        refine ⟨99327501440581211513675351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66218334293720807675783567 99327501440581211513675351)
        ·
          refine ⟨148991252160871817270513027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99327501440581211513675351 148991252160871817270513027)
          ·
            refine ⟨223486878241307725905769541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148991252160871817270513027 223486878241307725905769541)
            ·
              refine ⟨41903789670245198607331789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223486878241307725905769541 41903789670245198607331789)
              ·
                refine ⟨15713921126341949477749421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41903789670245198607331789 15713921126341949477749421)
                ·
                  refine ⟨5892720422378231054156033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15713921126341949477749421 5892720422378231054156033)
                  ·
                    refine ⟨4419540316783673290617025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5892720422378231054156033 4419540316783673290617025)
                    ·
                      refine ⟨3314655237587754967962769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419540316783673290617025 3314655237587754967962769)
                      ·
                        rfl

theorem cell23_6455268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_6455268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455268 prefixEnd_6455268 := by exact prefixLift 6455268
  have htrace : WordTrace (prefixWord ++ tailWord_6455268) baseStart_6455268 baseEnd_6455268 := by
    simpa [prefixWord, tailWord_6455268, baseEnd_6455268] using wordTrace_append hprefix tailTrace_6455268
  have hstable : (prefixWord ++ tailWord_6455268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455268).length < 2 ^ (prefixWord ++ tailWord_6455268).sum := by decide
  have hdescent : baseEnd_6455268 < baseStart_6455268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455278 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_6455278 : Nat := 118140960795 + 6455278 * 2 ^ 59
def prefixEnd_6455278 : Nat := 4983230072969 + 3 ^ 40 * 6455278 * 2
def baseEnd_6455278 : Nat := 1104886790798099976279241

theorem tailTrace_6455278 : CollatzResearch.WordTrace tailWord_6455278 prefixEnd_6455278 1104886790798099976279241 := by
  unfold tailWord_6455278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29430416388454719319386811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156962220738425169703396325 29430416388454719319386811)
  ·
    refine ⟨44145624582682078979080217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29430416388454719319386811 44145624582682078979080217)
    ·
      refine ⟨33109218437011559234310163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44145624582682078979080217 33109218437011559234310163)
      ·
        refine ⟨49663827655517338851465245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33109218437011559234310163 49663827655517338851465245)
        ·
          refine ⟨18623935370819002069299467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49663827655517338851465245 18623935370819002069299467)
          ·
            refine ⟨27935903056228503103949201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18623935370819002069299467 27935903056228503103949201)
            ·
              refine ⟨20951927292171377327961901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27935903056228503103949201 20951927292171377327961901)
              ·
                refine ⟨7856972734564266497985713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20951927292171377327961901 7856972734564266497985713)
                ·
                  refine ⟨5892729550923199873489285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7856972734564266497985713 5892729550923199873489285)
                  ·
                    refine ⟨1104886790798099976279241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892729550923199873489285 1104886790798099976279241)
                    ·
                      rfl

theorem cell23_6455278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_6455278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455278 prefixEnd_6455278 := by exact prefixLift 6455278
  have htrace : WordTrace (prefixWord ++ tailWord_6455278) baseStart_6455278 baseEnd_6455278 := by
    simpa [prefixWord, tailWord_6455278, baseEnd_6455278] using wordTrace_append hprefix tailTrace_6455278
  have hstable : (prefixWord ++ tailWord_6455278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455278).length < 2 ^ (prefixWord ++ tailWord_6455278).sum := by decide
  have hdescent : baseEnd_6455278 < baseStart_6455278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455301 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_6455301 : Nat := 118140960795 + 6455301 * 2 ^ 59
def prefixEnd_6455301 : Nat := 4983230072969 + 3 ^ 40 * 6455301 * 2
def baseEnd_6455301 : Nat := 3314672182449353338850117

theorem tailTrace_6455301 : CollatzResearch.WordTrace tailWord_6455301 prefixEnd_6455301 3314672182449353338850117 := by
  unfold tailWord_6455301
  simp only [CollatzResearch.WordTrace]
  refine ⟨235444169986554429483181757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156962779991036286322121171 235444169986554429483181757)
  ·
    refine ⟨88291563744957911056193159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235444169986554429483181757 88291563744957911056193159)
    ·
      refine ⟨132437345617436866584289739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88291563744957911056193159 132437345617436866584289739)
      ·
        refine ⟨198656018426155299876434609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132437345617436866584289739 198656018426155299876434609)
        ·
          refine ⟨148992013819616474907325957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198656018426155299876434609 148992013819616474907325957)
          ·
            refine ⟨27936002591178089045123617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148992013819616474907325957 27936002591178089045123617)
            ·
              refine ⟨20952001943383566783842713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27936002591178089045123617 20952001943383566783842713)
              ·
                refine ⟨15714001457537675087882035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20952001943383566783842713 15714001457537675087882035)
                ·
                  refine ⟨23571002186306512631823053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15714001457537675087882035 23571002186306512631823053)
                  ·
                    refine ⟨8839125819864942236933645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23571002186306512631823053 8839125819864942236933645)
                    ·
                      refine ⟨3314672182449353338850117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8839125819864942236933645 3314672182449353338850117)
                      ·
                        rfl

theorem cell23_6455301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_6455301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455301 prefixEnd_6455301 := by exact prefixLift 6455301
  have htrace : WordTrace (prefixWord ++ tailWord_6455301) baseStart_6455301 baseEnd_6455301 := by
    simpa [prefixWord, tailWord_6455301, baseEnd_6455301] using wordTrace_append hprefix tailTrace_6455301
  have hstable : (prefixWord ++ tailWord_6455301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455301).length < 2 ^ (prefixWord ++ tailWord_6455301).sum := by decide
  have hdescent : baseEnd_6455301 < baseStart_6455301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455345 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 1, 3, 2]
def baseStart_6455345 : Nat := 118140960795 + 6455345 * 2 ^ 59
def prefixEnd_6455345 : Nat := 4983230072969 + 3 ^ 40 * 6455345 * 2
def baseEnd_6455345 : Nat := 3314694775598151166699915

theorem tailTrace_6455345 : CollatzResearch.WordTrace tailWord_6455345 prefixEnd_6455345 3314694775598151166699915 := by
  unfold tailWord_6455345
  simp only [CollatzResearch.WordTrace]
  refine ⟨235445774798395024997783489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156963849865596683331855659 235445774798395024997783489)
  ·
    refine ⟨176584331098796268748337617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235445774798395024997783489 176584331098796268748337617)
    ·
      refine ⟨132438248324097201561253213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176584331098796268748337617 132438248324097201561253213)
      ·
        refine ⟨49664343121536450585469955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132438248324097201561253213 49664343121536450585469955)
        ·
          refine ⟨74496514682304675878204933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49664343121536450585469955 74496514682304675878204933)
          ·
            refine ⟨13968096502932126727163425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74496514682304675878204933 13968096502932126727163425)
            ·
              refine ⟨10476072377199095045372569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13968096502932126727163425 10476072377199095045372569)
              ·
                refine ⟨7857054282899321284029427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10476072377199095045372569 7857054282899321284029427)
                ·
                  refine ⟨11785581424348981926044141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7857054282899321284029427 11785581424348981926044141)
                  ·
                    refine ⟨4419593034130868222266553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11785581424348981926044141 4419593034130868222266553)
                    ·
                      refine ⟨3314694775598151166699915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419593034130868222266553 3314694775598151166699915)
                      ·
                        rfl

theorem cell23_6455345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_6455345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455345 prefixEnd_6455345 := by exact prefixLift 6455345
  have htrace : WordTrace (prefixWord ++ tailWord_6455345) baseStart_6455345 baseEnd_6455345 := by
    simpa [prefixWord, tailWord_6455345, baseEnd_6455345] using wordTrace_append hprefix tailTrace_6455345
  have hstable : (prefixWord ++ tailWord_6455345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455345).length < 2 ^ (prefixWord ++ tailWord_6455345).sum := by decide
  have hdescent : baseEnd_6455345 < baseStart_6455345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455361 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6455361 : Nat := 118140960795 + 6455361 * 2 ^ 59
def prefixEnd_6455361 : Nat := 4983230072969 + 3 ^ 40 * 6455361 * 2
def baseEnd_6455361 : Nat := 3314702991288623104099841

theorem tailTrace_6455361 : CollatzResearch.WordTrace tailWord_6455361 prefixEnd_6455361 3314702991288623104099841 := by
  unfold tailWord_6455361
  simp only [CollatzResearch.WordTrace]
  refine ⟨235446358366337059730365937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156964238910891373153577291 235446358366337059730365937)
  ·
    refine ⟨176584768774752794797774453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235446358366337059730365937 176584768774752794797774453)
    ·
      refine ⟨16554822072633074512291355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176584768774752794797774453 16554822072633074512291355)
      ·
        refine ⟨24832233108949611768437033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16554822072633074512291355 24832233108949611768437033)
        ·
          refine ⟨18624174831712208826327775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24832233108949611768437033 18624174831712208826327775)
          ·
            refine ⟨27936262247568313239491663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18624174831712208826327775 27936262247568313239491663)
            ·
              refine ⟨41904393371352469859237495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27936262247568313239491663 41904393371352469859237495)
              ·
                refine ⟨62856590057028704788856243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41904393371352469859237495 62856590057028704788856243)
                ·
                  refine ⟨94284885085543057183284365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62856590057028704788856243 94284885085543057183284365)
                  ·
                    refine ⟨35356831907078646443731637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94284885085543057183284365 35356831907078646443731637)
                    ·
                      refine ⟨3314702991288623104099841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35356831907078646443731637 3314702991288623104099841)
                      ·
                        rfl

theorem cell23_6455361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6455361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455361 prefixEnd_6455361 := by exact prefixLift 6455361
  have htrace : WordTrace (prefixWord ++ tailWord_6455361) baseStart_6455361 baseEnd_6455361 := by
    simpa [prefixWord, tailWord_6455361, baseEnd_6455361] using wordTrace_append hprefix tailTrace_6455361
  have hstable : (prefixWord ++ tailWord_6455361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455361).length < 2 ^ (prefixWord ++ tailWord_6455361).sum := by decide
  have hdescent : baseEnd_6455361 < baseStart_6455361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455381 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 7]
def baseStart_6455381 : Nat := 118140960795 + 6455381 * 2 ^ 59
def prefixEnd_6455381 : Nat := 4983230072969 + 3 ^ 40 * 6455381 * 2
def baseEnd_6455381 : Nat := 368301473433523669538861

theorem tailTrace_6455381 : CollatzResearch.WordTrace tailWord_6455381 prefixEnd_6455381 368301473433523669538861 := by
  unfold tailWord_6455381
  simp only [CollatzResearch.WordTrace]
  refine ⟨235447087826264603146093997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156964725217509735430729331 235447087826264603146093997)
  ·
    refine ⟨88292657934849226179785249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235447087826264603146093997 88292657934849226179785249)
    ·
      refine ⟨66219493451136919634838937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88292657934849226179785249 66219493451136919634838937)
      ·
        refine ⟨49664620088352689726129203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66219493451136919634838937 49664620088352689726129203)
        ·
          refine ⟨74496930132529034589193805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49664620088352689726129203 74496930132529034589193805)
          ·
            refine ⟨27936348799698387970947677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74496930132529034589193805 27936348799698387970947677)
            ·
              refine ⟨10476130799886895489105379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27936348799698387970947677 10476130799886895489105379)
              ·
                refine ⟨15714196199830343233658069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10476130799886895489105379 15714196199830343233658069)
                ·
                  refine ⟨368301473433523669538861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15714196199830343233658069 368301473433523669538861)
                  ·
                    rfl

theorem cell23_6455381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_6455381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455381 prefixEnd_6455381 := by exact prefixLift 6455381
  have htrace : WordTrace (prefixWord ++ tailWord_6455381) baseStart_6455381 baseEnd_6455381 := by
    simpa [prefixWord, tailWord_6455381, baseEnd_6455381] using wordTrace_append hprefix tailTrace_6455381
  have hstable : (prefixWord ++ tailWord_6455381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455381).length < 2 ^ (prefixWord ++ tailWord_6455381).sum := by decide
  have hdescent : baseEnd_6455381 < baseStart_6455381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455392 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 2, 2, 2]
def baseStart_6455392 : Nat := 118140960795 + 6455392 * 2 ^ 59
def prefixEnd_6455392 : Nat := 4983230072969 + 3 ^ 40 * 6455392 * 2
def baseEnd_6455392 : Nat := 3314718909188912482812199

theorem tailTrace_6455392 : CollatzResearch.WordTrace tailWord_6455392 prefixEnd_6455392 3314718909188912482812199 := by
  unfold tailWord_6455392
  simp only [CollatzResearch.WordTrace]
  refine ⟨117723744514612376012372215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156964992686149834683162953 117723744514612376012372215)
  ·
    refine ⟨176585616771918564018558323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117723744514612376012372215 176585616771918564018558323)
    ·
      refine ⟨264878425157877846027837485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176585616771918564018558323 264878425157877846027837485)
      ·
        refine ⟨99329409434204192260439057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264878425157877846027837485 99329409434204192260439057)
        ·
          refine ⟨74497057075653144195329293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99329409434204192260439057 74497057075653144195329293)
          ·
            refine ⟨27936396403369929073248485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74497057075653144195329293 27936396403369929073248485)
            ·
              refine ⟨5238074325631861701234091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27936396403369929073248485 5238074325631861701234091)
              ·
                refine ⟨7857111488447792551851137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5238074325631861701234091 7857111488447792551851137)
                ·
                  refine ⟨5892833616335844413888353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7857111488447792551851137 5892833616335844413888353)
                  ·
                    refine ⟨4419625212251883310416265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5892833616335844413888353 4419625212251883310416265)
                    ·
                      refine ⟨3314718909188912482812199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419625212251883310416265 3314718909188912482812199)
                      ·
                        rfl

theorem cell23_6455392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_6455392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455392 prefixEnd_6455392 := by exact prefixLift 6455392
  have htrace : WordTrace (prefixWord ++ tailWord_6455392) baseStart_6455392 baseEnd_6455392 := by
    simpa [prefixWord, tailWord_6455392, baseEnd_6455392] using wordTrace_append hprefix tailTrace_6455392
  have hstable : (prefixWord ++ tailWord_6455392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455392).length < 2 ^ (prefixWord ++ tailWord_6455392).sum := by decide
  have hdescent : baseEnd_6455392 < baseStart_6455392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455421 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_6455421 : Nat := 118140960795 + 6455421 * 2 ^ 59
def prefixEnd_6455421 : Nat := 4983230072969 + 3 ^ 40 * 6455421 * 2
def baseEnd_6455421 : Nat := 3314733800127892869349565

theorem tailTrace_6455421 : CollatzResearch.WordTrace tailWord_6455421 prefixEnd_6455421 3314733800127892869349565 := by
  unfold tailWord_6455421
  simp only [CollatzResearch.WordTrace]
  refine ⟨235448546746119689977550117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156965697830746459985033411 235448546746119689977550117)
  ·
    refine ⟨44146602514897441870790647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235448546746119689977550117 44146602514897441870790647)
    ·
      refine ⟨66219903772346162806185971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44146602514897441870790647 66219903772346162806185971)
      ·
        refine ⟨99329855658519244209278957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66219903772346162806185971 99329855658519244209278957)
        ·
          refine ⟨37248695871944716578479609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99329855658519244209278957 37248695871944716578479609)
          ·
            refine ⟨27936521903958537433859707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37248695871944716578479609 27936521903958537433859707)
            ·
              refine ⟨41904782855937806150789561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27936521903958537433859707 41904782855937806150789561)
              ·
                refine ⟨31428587141953354613092171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41904782855937806150789561 31428587141953354613092171)
                ·
                  refine ⟨47142880712930031919638257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31428587141953354613092171 47142880712930031919638257)
                  ·
                    refine ⟨35357160534697523939728693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47142880712930031919638257 35357160534697523939728693)
                    ·
                      refine ⟨3314733800127892869349565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35357160534697523939728693 3314733800127892869349565)
                      ·
                        rfl

theorem cell23_6455421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_6455421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455421 prefixEnd_6455421 := by exact prefixLift 6455421
  have htrace : WordTrace (prefixWord ++ tailWord_6455421) baseStart_6455421 baseEnd_6455421 := by
    simpa [prefixWord, tailWord_6455421, baseEnd_6455421] using wordTrace_append hprefix tailTrace_6455421
  have hstable : (prefixWord ++ tailWord_6455421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455421).length < 2 ^ (prefixWord ++ tailWord_6455421).sum := by decide
  have hdescent : baseEnd_6455421 < baseStart_6455421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455432 : List Nat := [2, 1, 3, 4, 1, 3, 2, 2, 5]
def baseStart_6455432 : Nat := 118140960795 + 6455432 * 2 ^ 59
def prefixEnd_6455432 : Nat := 4983230072969 + 3 ^ 40 * 6455432 * 2
def baseEnd_6455432 : Nat := 368304383157232480701335

theorem tailTrace_6455432 : CollatzResearch.WordTrace tailWord_6455432 prefixEnd_6455432 368304383157232480701335 := by
  unfold tailWord_6455432
  simp only [CollatzResearch.WordTrace]
  refine ⟨117724473974539919428100275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156965965299386559237467033 117724473974539919428100275)
  ·
    refine ⟨176586710961809879142150413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117724473974539919428100275 176586710961809879142150413)
    ·
      refine ⟨66220016610678704678306405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176586710961809879142150413 66220016610678704678306405)
      ·
        refine ⟨12416253114502257127182451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66220016610678704678306405 12416253114502257127182451)
        ·
          refine ⟨18624379671753385690773677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12416253114502257127182451 18624379671753385690773677)
          ·
            refine ⟨6984142376907519634040129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18624379671753385690773677 6984142376907519634040129)
            ·
              refine ⟨5238106782680639725530097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6984142376907519634040129 5238106782680639725530097)
              ·
                refine ⟨3928580087010479794147573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238106782680639725530097 3928580087010479794147573)
                ·
                  refine ⟨368304383157232480701335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3928580087010479794147573 368304383157232480701335)
                  ·
                    rfl

theorem cell23_6455432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 5].length) (baseStart_6455432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455432 prefixEnd_6455432 := by exact prefixLift 6455432
  have htrace : WordTrace (prefixWord ++ tailWord_6455432) baseStart_6455432 baseEnd_6455432 := by
    simpa [prefixWord, tailWord_6455432, baseEnd_6455432] using wordTrace_append hprefix tailTrace_6455432
  have hstable : (prefixWord ++ tailWord_6455432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455432).length < 2 ^ (prefixWord ++ tailWord_6455432).sum := by decide
  have hdescent : baseEnd_6455432 < baseStart_6455432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455441 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 9, 4]
def baseStart_6455441 : Nat := 118140960795 + 6455441 * 2 ^ 59
def prefixEnd_6455441 : Nat := 4983230072969 + 3 ^ 40 * 6455441 * 2
def baseEnd_6455441 : Nat := 1104914689913660930366491

theorem tailTrace_6455441 : CollatzResearch.WordTrace tailWord_6455441 prefixEnd_6455441 1104914689913660930366491 := by
  unfold tailWord_6455441
  simp only [CollatzResearch.WordTrace]
  refine ⟨235449276206047233393278177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156966184137364822262185451 235449276206047233393278177)
  ·
    refine ⟨176586957154535425044958633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235449276206047233393278177 176586957154535425044958633)
    ·
      refine ⟨132440217865901568783718975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176586957154535425044958633 132440217865901568783718975)
      ·
        refine ⟨198660326798852353175578463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132440217865901568783718975 198660326798852353175578463)
        ·
          refine ⟨297990490198278529763367695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198660326798852353175578463 297990490198278529763367695)
          ·
            refine ⟨446985735297417794645051543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297990490198278529763367695 446985735297417794645051543)
            ·
              refine ⟨670478602946126691967577315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446985735297417794645051543 670478602946126691967577315)
              ·
                refine ⟨1005717904419190037951365973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670478602946126691967577315 1005717904419190037951365973)
                ·
                  refine ⟨5892878346206191628621285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1005717904419190037951365973 5892878346206191628621285)
                  ·
                    refine ⟨1104914689913660930366491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892878346206191628621285 1104914689913660930366491)
                    ·
                      rfl

theorem cell23_6455441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_6455441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455441 prefixEnd_6455441 := by exact prefixLift 6455441
  have htrace : WordTrace (prefixWord ++ tailWord_6455441) baseStart_6455441 baseEnd_6455441 := by
    simpa [prefixWord, tailWord_6455441, baseEnd_6455441] using wordTrace_append hprefix tailTrace_6455441
  have hstable : (prefixWord ++ tailWord_6455441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455441).length < 2 ^ (prefixWord ++ tailWord_6455441).sum := by decide
  have hdescent : baseEnd_6455441 < baseStart_6455441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455488 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 6]
def baseStart_6455488 : Nat := 118140960795 + 6455488 * 2 ^ 59
def prefixEnd_6455488 : Nat := 4983230072969 + 3 ^ 40 * 6455488 * 2
def baseEnd_6455488 : Nat := 368307578147971567467973

theorem tailTrace_6455488 : CollatzResearch.WordTrace tailWord_6455488 prefixEnd_6455488 368307578147971567467973 := by
  unfold tailWord_6455488
  simp only [CollatzResearch.WordTrace]
  refine ⟨117725495218438480210119559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156967326957917973613492745 117725495218438480210119559)
  ·
    refine ⟨176588242827657720315179339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117725495218438480210119559 176588242827657720315179339)
    ·
      refine ⟨264882364241486580472769009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176588242827657720315179339 264882364241486580472769009)
      ·
        refine ⟨198661773181114935354576757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264882364241486580472769009 198661773181114935354576757)
        ·
          refine ⟨18624541235729525189491571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198661773181114935354576757 18624541235729525189491571)
          ·
            refine ⟨27936811853594287784237357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18624541235729525189491571 27936811853594287784237357)
            ·
              refine ⟨10476304445097857919089009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27936811853594287784237357 10476304445097857919089009)
              ·
                refine ⟨7857228333823393439316757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10476304445097857919089009 7857228333823393439316757)
                ·
                  refine ⟨368307578147971567467973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7857228333823393439316757 368307578147971567467973)
                  ·
                    rfl

theorem cell23_6455488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 6].length) (baseStart_6455488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455488 prefixEnd_6455488 := by exact prefixLift 6455488
  have htrace : WordTrace (prefixWord ++ tailWord_6455488) baseStart_6455488 baseEnd_6455488 := by
    simpa [prefixWord, tailWord_6455488, baseEnd_6455488] using wordTrace_append hprefix tailTrace_6455488
  have hstable : (prefixWord ++ tailWord_6455488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455488).length < 2 ^ (prefixWord ++ tailWord_6455488).sum := by decide
  have hdescent : baseEnd_6455488 < baseStart_6455488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455492 : List Nat := [2, 3, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6455492 : Nat := 118140960795 + 6455492 * 2 ^ 59
def prefixEnd_6455492 : Nat := 4983230072969 + 3 ^ 40 * 6455492 * 2
def baseEnd_6455492 : Nat := 1104923419084787363853913

theorem tailTrace_6455492 : CollatzResearch.WordTrace tailWord_6455492 prefixEnd_6455492 1104923419084787363853913 := by
  unfold tailWord_6455492
  simp only [CollatzResearch.WordTrace]
  refine ⟨117725568164431234551692365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156967424219241646068923153 117725568164431234551692365)
  ·
    refine ⟨44147088061661712956884637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117725568164431234551692365 44147088061661712956884637)
    ·
      refine ⟨16555158023123142358831739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44147088061661712956884637 16555158023123142358831739)
      ·
        refine ⟨24832737034684713538247609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16555158023123142358831739 24832737034684713538247609)
        ·
          refine ⟨18624552776013535153685707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24832737034684713538247609 18624552776013535153685707)
          ·
            refine ⟨27936829164020302730528561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18624552776013535153685707 27936829164020302730528561)
            ·
              refine ⟨20952621873015227047896421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27936829164020302730528561 20952621873015227047896421)
              ·
                refine ⟨3928616601190355071480579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20952621873015227047896421 3928616601190355071480579)
                ·
                  refine ⟨5892924901785532607220869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928616601190355071480579 5892924901785532607220869)
                  ·
                    refine ⟨1104923419084787363853913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892924901785532607220869 1104923419084787363853913)
                    ·
                      rfl

theorem cell23_6455492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6455492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455492 prefixEnd_6455492 := by exact prefixLift 6455492
  have htrace : WordTrace (prefixWord ++ tailWord_6455492) baseStart_6455492 baseEnd_6455492 := by
    simpa [prefixWord, tailWord_6455492, baseEnd_6455492] using wordTrace_append hprefix tailTrace_6455492
  have hstable : (prefixWord ++ tailWord_6455492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455492).length < 2 ^ (prefixWord ++ tailWord_6455492).sum := by decide
  have hdescent : baseEnd_6455492 < baseStart_6455492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455525 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 1, 5, 2]
def baseStart_6455525 : Nat := 118140960795 + 6455525 * 2 ^ 59
def prefixEnd_6455525 : Nat := 4983230072969 + 3 ^ 40 * 6455525 * 2
def baseEnd_6455525 : Nat := 3314787202115960462449087

theorem tailTrace_6455525 : CollatzResearch.WordTrace tailWord_6455525 prefixEnd_6455525 3314787202115960462449087 := by
  unfold tailWord_6455525
  simp only [CollatzResearch.WordTrace]
  refine ⟨235452339937742915739336029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156968226625161943826224019 235452339937742915739336029)
  ·
    refine ⟨88294627476653593402251011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235452339937742915739336029 88294627476653593402251011)
    ·
      refine ⟨132441941214980390103376517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88294627476653593402251011 132441941214980390103376517)
      ·
        refine ⟨24832863977808823144383097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132441941214980390103376517 24832863977808823144383097)
        ·
          refine ⟨18624647983356617358287323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24832863977808823144383097 18624647983356617358287323)
          ·
            refine ⟨27936971975034926037430985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18624647983356617358287323 27936971975034926037430985)
            ·
              refine ⟨20952728981276194528073239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27936971975034926037430985 20952728981276194528073239)
              ·
                refine ⟨31429093471914291792109859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20952728981276194528073239 31429093471914291792109859)
                ·
                  refine ⟨47143640207871437688164789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31429093471914291792109859 47143640207871437688164789)
                  ·
                    refine ⟨4419716269487947283265449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47143640207871437688164789 4419716269487947283265449)
                    ·
                      refine ⟨3314787202115960462449087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419716269487947283265449 3314787202115960462449087)
                      ·
                        rfl

theorem cell23_6455525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_6455525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455525 prefixEnd_6455525 := by exact prefixLift 6455525
  have htrace : WordTrace (prefixWord ++ tailWord_6455525) baseStart_6455525 baseEnd_6455525 := by
    simpa [prefixWord, tailWord_6455525, baseEnd_6455525] using wordTrace_append hprefix tailTrace_6455525
  have hstable : (prefixWord ++ tailWord_6455525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455525).length < 2 ^ (prefixWord ++ tailWord_6455525).sum := by decide
  have hdescent : baseEnd_6455525 < baseStart_6455525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455531 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 3, 6]
def baseStart_6455531 : Nat := 118140960795 + 6455531 * 2 ^ 59
def prefixEnd_6455531 : Nat := 4983230072969 + 3 ^ 40 * 6455531 * 2
def baseEnd_6455531 : Nat := 1104930094333295812991353

theorem tailTrace_6455531 : CollatzResearch.WordTrace tailWord_6455531 prefixEnd_6455531 1104930094333295812991353 := by
  unfold tailWord_6455531
  simp only [CollatzResearch.WordTrace]
  refine ⟨235452558775721178764054447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156968372517147452509369631 235452558775721178764054447)
  ·
    refine ⟨353178838163581768146081671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235452558775721178764054447 353178838163581768146081671)
    ·
      refine ⟨529768257245372652219122507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353178838163581768146081671 529768257245372652219122507)
      ·
        refine ⟨794652385868058978328683761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529768257245372652219122507 794652385868058978328683761)
        ·
          refine ⟨595989289401044233746512821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794652385868058978328683761 595989289401044233746512821)
          ·
            refine ⟨55873995881347896913735577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 595989289401044233746512821 55873995881347896913735577)
            ·
              refine ⟨41905496911010922685301683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55873995881347896913735577 41905496911010922685301683)
              ·
                refine ⟨62858245366516384027952525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41905496911010922685301683 62858245366516384027952525)
                ·
                  refine ⟨23571842012443644010482197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62858245366516384027952525 23571842012443644010482197)
                  ·
                    refine ⟨1104930094333295812991353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23571842012443644010482197 1104930094333295812991353)
                    ·
                      rfl

theorem cell23_6455531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 6].length) (baseStart_6455531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455531 prefixEnd_6455531 := by exact prefixLift 6455531
  have htrace : WordTrace (prefixWord ++ tailWord_6455531) baseStart_6455531 baseEnd_6455531 := by
    simpa [prefixWord, tailWord_6455531, baseEnd_6455531] using wordTrace_append hprefix tailTrace_6455531
  have hstable : (prefixWord ++ tailWord_6455531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455531).length < 2 ^ (prefixWord ++ tailWord_6455531).sum := by decide
  have hdescent : baseEnd_6455531 < baseStart_6455531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455551 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_6455551 : Nat := 118140960795 + 6455551 * 2 ^ 59
def prefixEnd_6455551 : Nat := 4983230072969 + 3 ^ 40 * 6455551 * 2
def baseEnd_6455551 : Nat := 3314800552612977360723967

theorem tailTrace_6455551 : CollatzResearch.WordTrace tailWord_6455551 prefixEnd_6455551 3314800552612977360723967 := by
  unfold tailWord_6455551
  simp only [CollatzResearch.WordTrace]
  refine ⟨235453288235648722179782507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156968858823765814786521671 235453288235648722179782507)
  ·
    refine ⟨353179932353473083269673761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235453288235648722179782507 353179932353473083269673761)
    ·
      refine ⟨264884949265104812452255321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353179932353473083269673761 264884949265104812452255321)
      ·
        refine ⟨198663711948828609339191491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264884949265104812452255321 198663711948828609339191491)
        ·
          refine ⟨297995567923242914008787237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198663711948828609339191491 297995567923242914008787237)
          ·
            refine ⟨55874168985608046376647607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297995567923242914008787237 55874168985608046376647607)
            ·
              refine ⟨83811253478412069564971411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55874168985608046376647607 83811253478412069564971411)
              ·
                refine ⟨125716880217618104347457117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83811253478412069564971411 125716880217618104347457117)
                ·
                  refine ⟨47143830081606789130296419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125716880217618104347457117 47143830081606789130296419)
                  ·
                    refine ⟨70715745122410183695444629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47143830081606789130296419 70715745122410183695444629)
                    ·
                      refine ⟨3314800552612977360723967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70715745122410183695444629 3314800552612977360723967)
                      ·
                        rfl

theorem cell23_6455551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_6455551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455551 prefixEnd_6455551 := by exact prefixLift 6455551
  have htrace : WordTrace (prefixWord ++ tailWord_6455551) baseStart_6455551 baseEnd_6455551 := by
    simpa [prefixWord, tailWord_6455551, baseEnd_6455551] using wordTrace_append hprefix tailTrace_6455551
  have hstable : (prefixWord ++ tailWord_6455551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455551).length < 2 ^ (prefixWord ++ tailWord_6455551).sum := by decide
  have hdescent : baseEnd_6455551 < baseStart_6455551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455561 : List Nat := [1, 2, 1, 1, 3, 4, 1, 10]
def baseStart_6455561 : Nat := 118140960795 + 6455561 * 2 ^ 59
def prefixEnd_6455561 : Nat := 4983230072969 + 3 ^ 40 * 6455561 * 2
def baseEnd_6455561 : Nat := 122770581015537863762923

theorem tailTrace_6455561 : CollatzResearch.WordTrace tailWord_6455561 prefixEnd_6455561 122770581015537863762923 := by
  unfold tailWord_6455561
  simp only [CollatzResearch.WordTrace]
  refine ⟨235453652965612493887646537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156969101977074995925097691 235453652965612493887646537)
  ·
    refine ⟨176590239724209370415734903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235453652965612493887646537 176590239724209370415734903)
    ·
      refine ⟨264885359586314055623602355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176590239724209370415734903 264885359586314055623602355)
      ·
        refine ⟨397328039379471083435403533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264885359586314055623602355 397328039379471083435403533)
        ·
          refine ⟨148998014767301656288276325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397328039379471083435403533 148998014767301656288276325)
          ·
            refine ⟨27937127768869060554051811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148998014767301656288276325 27937127768869060554051811)
            ·
              refine ⟨41905691653303590831077717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27937127768869060554051811 41905691653303590831077717)
              ·
                refine ⟨122770581015537863762923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41905691653303590831077717 122770581015537863762923)
                ·
                  rfl

theorem cell23_6455561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 10].length) (baseStart_6455561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455561 prefixEnd_6455561 := by exact prefixLift 6455561
  have htrace : WordTrace (prefixWord ++ tailWord_6455561) baseStart_6455561 baseEnd_6455561 := by
    simpa [prefixWord, tailWord_6455561, baseEnd_6455561] using wordTrace_append hprefix tailTrace_6455561
  have hstable : (prefixWord ++ tailWord_6455561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455561).length < 2 ^ (prefixWord ++ tailWord_6455561).sum := by decide
  have hdescent : baseEnd_6455561 < baseStart_6455561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455575 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_6455575 : Nat := 118140960795 + 6455575 * 2 ^ 59
def prefixEnd_6455575 : Nat := 4983230072969 + 3 ^ 40 * 6455575 * 2
def baseEnd_6455575 : Nat := 3314812876148685266823857

theorem tailTrace_6455575 : CollatzResearch.WordTrace tailWord_6455575 prefixEnd_6455575 3314812876148685266823857 := by
  unfold tailWord_6455575
  simp only [CollatzResearch.WordTrace]
  refine ⟨235454163587561774278656179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156969442391707849519104119 235454163587561774278656179)
  ·
    refine ⟨353181245381342661417984269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235454163587561774278656179 353181245381342661417984269)
    ·
      refine ⟨132442967018003498031744101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353181245381342661417984269 132442967018003498031744101)
      ·
        refine ⟨24833056315875655880952019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132442967018003498031744101 24833056315875655880952019)
        ·
          refine ⟨37249584473813483821428029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24833056315875655880952019 37249584473813483821428029)
          ·
            refine ⟨13968594177680056433035511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37249584473813483821428029 13968594177680056433035511)
            ·
              refine ⟨20952891266520084649553267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13968594177680056433035511 20952891266520084649553267)
              ·
                refine ⟨31429336899780126974329901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20952891266520084649553267 31429336899780126974329901)
                ·
                  refine ⟨11786001337417547615373713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31429336899780126974329901 11786001337417547615373713)
                  ·
                    refine ⟨8839501003063160711530285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11786001337417547615373713 8839501003063160711530285)
                    ·
                      refine ⟨3314812876148685266823857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8839501003063160711530285 3314812876148685266823857)
                      ·
                        rfl

theorem cell23_6455575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_6455575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455575 prefixEnd_6455575 := by exact prefixLift 6455575
  have htrace : WordTrace (prefixWord ++ tailWord_6455575) baseStart_6455575 baseEnd_6455575 := by
    simpa [prefixWord, tailWord_6455575, baseEnd_6455575] using wordTrace_append hprefix tailTrace_6455575
  have hstable : (prefixWord ++ tailWord_6455575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455575).length < 2 ^ (prefixWord ++ tailWord_6455575).sum := by decide
  have hdescent : baseEnd_6455575 < baseStart_6455575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455582 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6455582 : Nat := 118140960795 + 6455582 * 2 ^ 59
def prefixEnd_6455582 : Nat := 4983230072969 + 3 ^ 40 * 6455582 * 2
def baseEnd_6455582 : Nat := 1104938823504422246478775

theorem tailTrace_6455582 : CollatzResearch.WordTrace tailWord_6455582 prefixEnd_6455582 1104938823504422246478775 := by
  unfold tailWord_6455582
  simp only [CollatzResearch.WordTrace]
  refine ⟨29431802362317051809270125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156969612599024276316107333 29431802362317051809270125)
  ·
    refine ⟨11036925885868894428476297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29431802362317051809270125 11036925885868894428476297)
    ·
      refine ⟨8277694414401670821357223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11036925885868894428476297 8277694414401670821357223)
      ·
        refine ⟨12416541621602506232035835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8277694414401670821357223 12416541621602506232035835)
        ·
          refine ⟨18624812432403759348053753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12416541621602506232035835 18624812432403759348053753)
          ·
            refine ⟨13968609324302819511040315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18624812432403759348053753 13968609324302819511040315)
            ·
              refine ⟨20952913986454229266560473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13968609324302819511040315 20952913986454229266560473)
              ·
                refine ⟨15714685489840671949920355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20952913986454229266560473 15714685489840671949920355)
                ·
                  refine ⟨23572028234761007924880533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15714685489840671949920355 23572028234761007924880533)
                  ·
                    refine ⟨1104938823504422246478775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23572028234761007924880533 1104938823504422246478775)
                    ·
                      rfl

theorem cell23_6455582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6455582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455582 prefixEnd_6455582 := by exact prefixLift 6455582
  have htrace : WordTrace (prefixWord ++ tailWord_6455582) baseStart_6455582 baseEnd_6455582 := by
    simpa [prefixWord, tailWord_6455582, baseEnd_6455582] using wordTrace_append hprefix tailTrace_6455582
  have hstable : (prefixWord ++ tailWord_6455582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455582).length < 2 ^ (prefixWord ++ tailWord_6455582).sum := by decide
  have hdescent : baseEnd_6455582 < baseStart_6455582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455592 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_6455592 : Nat := 118140960795 + 6455592 * 2 ^ 59
def prefixEnd_6455592 : Nat := 4983230072969 + 3 ^ 40 * 6455592 * 2
def baseEnd_6455592 : Nat := 3314821605319811700311279

theorem tailTrace_6455592 : CollatzResearch.WordTrace tailWord_6455592 prefixEnd_6455592 3314821605319811700311279 := by
  unfold tailWord_6455592
  simp only [CollatzResearch.WordTrace]
  refine ⟨117727391814250093091012515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156969855752333457454683353 117727391814250093091012515)
  ·
    refine ⟨176591087721375139636518773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117727391814250093091012515 176591087721375139636518773)
    ·
      refine ⟨16555414473878919340923635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176591087721375139636518773 16555414473878919340923635)
      ·
        refine ⟨24833121710818379011385453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16555414473878919340923635 24833121710818379011385453)
        ·
          refine ⟨9312420641556892129269545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24833121710818379011385453 9312420641556892129269545)
          ·
            refine ⟨6984315481167669096952159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9312420641556892129269545 6984315481167669096952159)
            ·
              refine ⟨10476473221751503645428239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984315481167669096952159 10476473221751503645428239)
              ·
                refine ⟨15714709832627255468142359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10476473221751503645428239 15714709832627255468142359)
                ·
                  refine ⟨23572064748940883202213539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15714709832627255468142359 23572064748940883202213539)
                  ·
                    refine ⟨35358097123411324803320309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23572064748940883202213539 35358097123411324803320309)
                    ·
                      refine ⟨3314821605319811700311279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35358097123411324803320309 3314821605319811700311279)
                      ·
                        rfl

theorem cell23_6455592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_6455592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455592 prefixEnd_6455592 := by exact prefixLift 6455592
  have htrace : WordTrace (prefixWord ++ tailWord_6455592) baseStart_6455592 baseEnd_6455592 := by
    simpa [prefixWord, tailWord_6455592, baseEnd_6455592] using wordTrace_append hprefix tailTrace_6455592
  have hstable : (prefixWord ++ tailWord_6455592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455592).length < 2 ^ (prefixWord ++ tailWord_6455592).sum := by decide
  have hdescent : baseEnd_6455592 < baseStart_6455592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455615 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 5, 3, 2]
def baseStart_6455615 : Nat := 118140960795 + 6455615 * 2 ^ 59
def prefixEnd_6455615 : Nat := 4983230072969 + 3 ^ 40 * 6455615 * 2
def baseEnd_6455615 : Nat := 3314833415374865110323673

theorem tailTrace_6455615 : CollatzResearch.WordTrace tailWord_6455615 prefixEnd_6455615 3314833415374865110323673 := by
  unfold tailWord_6455615
  simp only [CollatzResearch.WordTrace]
  refine ⟨235455622507416861110112299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156970415004944574073408199 235455622507416861110112299)
  ·
    refine ⟨353183433761125291665168449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235455622507416861110112299 353183433761125291665168449)
    ·
      refine ⟨264887575320843968748876337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353183433761125291665168449 264887575320843968748876337)
      ·
        refine ⟨198665681490632976561657253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264887575320843968748876337 198665681490632976561657253)
        ·
          refine ⟨37249815279493683105310735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198665681490632976561657253 37249815279493683105310735)
          ·
            refine ⟨55874722919240524657966103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37249815279493683105310735 55874722919240524657966103)
            ·
              refine ⟨83812084378860786986949155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55874722919240524657966103 83812084378860786986949155)
              ·
                refine ⟨125718126568291180480423733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83812084378860786986949155 125718126568291180480423733)
                ·
                  refine ⟨11786074365777298170039725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125718126568291180480423733 11786074365777298170039725)
                  ·
                    refine ⟨4419777887166486813764897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11786074365777298170039725 4419777887166486813764897)
                    ·
                      refine ⟨3314833415374865110323673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419777887166486813764897 3314833415374865110323673)
                      ·
                        rfl

theorem cell23_6455615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_6455615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455615 prefixEnd_6455615 := by exact prefixLift 6455615
  have htrace : WordTrace (prefixWord ++ tailWord_6455615) baseStart_6455615 baseEnd_6455615 := by
    simpa [prefixWord, tailWord_6455615, baseEnd_6455615] using wordTrace_append hprefix tailTrace_6455615
  have hstable : (prefixWord ++ tailWord_6455615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455615).length < 2 ^ (prefixWord ++ tailWord_6455615).sum := by decide
  have hdescent : baseEnd_6455615 < baseStart_6455615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455628 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6455628 : Nat := 118140960795 + 6455628 * 2 ^ 59
def prefixEnd_6455628 : Nat := 4983230072969 + 3 ^ 40 * 6455628 * 2
def baseEnd_6455628 : Nat := 3314840090623373559461113

theorem tailTrace_6455628 : CollatzResearch.WordTrace tailWord_6455628 prefixEnd_6455628 3314840090623373559461113 := by
  unfold tailWord_6455628
  simp only [CollatzResearch.WordTrace]
  refine ⟨117728048328184882165167769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156970731104246509553557025 117728048328184882165167769)
  ·
    refine ⟨88296036246138661623875827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117728048328184882165167769 88296036246138661623875827)
    ·
      refine ⟨132444054369207992435813741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88296036246138661623875827 132444054369207992435813741)
      ·
        refine ⟨49666520388452997163430153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132444054369207992435813741 49666520388452997163430153)
        ·
          refine ⟨37249890291339747872572615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49666520388452997163430153 37249890291339747872572615)
          ·
            refine ⟨55874835437009621808858923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37249890291339747872572615 55874835437009621808858923)
            ·
              refine ⟨83812253155514432713288385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55874835437009621808858923 83812253155514432713288385)
              ·
                refine ⟨62859189866635824534966289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83812253155514432713288385 62859189866635824534966289)
                ·
                  refine ⟨47144392399976868401224717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62859189866635824534966289 47144392399976868401224717)
                  ·
                    refine ⟨17679147149991325650459269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47144392399976868401224717 17679147149991325650459269)
                    ·
                      refine ⟨3314840090623373559461113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17679147149991325650459269 3314840090623373559461113)
                      ·
                        rfl

theorem cell23_6455628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6455628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455628 prefixEnd_6455628 := by exact prefixLift 6455628
  have htrace : WordTrace (prefixWord ++ tailWord_6455628) baseStart_6455628 baseEnd_6455628 := by
    simpa [prefixWord, tailWord_6455628, baseEnd_6455628] using wordTrace_append hprefix tailTrace_6455628
  have hstable : (prefixWord ++ tailWord_6455628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455628).length < 2 ^ (prefixWord ++ tailWord_6455628).sum := by decide
  have hdescent : baseEnd_6455628 < baseStart_6455628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455715 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 2, 5]
def baseStart_6455715 : Nat := 118140960795 + 6455715 * 2 ^ 59
def prefixEnd_6455715 : Nat := 4983230072969 + 3 ^ 40 * 6455715 * 2
def baseEnd_6455715 : Nat := 1104961587813438239691071

theorem tailTrace_6455715 : CollatzResearch.WordTrace tailWord_6455715 prefixEnd_6455715 1104961587813438239691071 := by
  unfold tailWord_6455715
  simp only [CollatzResearch.WordTrace]
  refine ⟨235459269807054578188752599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156972846538036385459168399 235459269807054578188752599)
  ·
    refine ⟨353188904710581867283128899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235459269807054578188752599 353188904710581867283128899)
    ·
      refine ⟨529783357065872800924693349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353188904710581867283128899 529783357065872800924693349)
      ·
        refine ⟨99334379449851150173380003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 529783357065872800924693349 99334379449851150173380003)
        ·
          refine ⟨149001569174776725260070005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99334379449851150173380003 149001569174776725260070005)
          ·
            refine ⟨13968897110135317993131563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149001569174776725260070005 13968897110135317993131563)
            ·
              refine ⟨20953345665202976989697345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13968897110135317993131563 20953345665202976989697345)
              ·
                refine ⟨15715009248902232742273009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20953345665202976989697345 15715009248902232742273009)
                ·
                  refine ⟨11786256936676674556704757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15715009248902232742273009 11786256936676674556704757)
                  ·
                    refine ⟨1104961587813438239691071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11786256936676674556704757 1104961587813438239691071)
                    ·
                      rfl

theorem cell23_6455715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 5].length) (baseStart_6455715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455715 prefixEnd_6455715 := by exact prefixLift 6455715
  have htrace : WordTrace (prefixWord ++ tailWord_6455715) baseStart_6455715 baseEnd_6455715 := by
    simpa [prefixWord, tailWord_6455715, baseEnd_6455715] using wordTrace_append hprefix tailTrace_6455715
  have hstable : (prefixWord ++ tailWord_6455715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455715).length < 2 ^ (prefixWord ++ tailWord_6455715).sum := by decide
  have hdescent : baseEnd_6455715 < baseStart_6455715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455719 : List Nat := [1, 1, 6, 1, 1, 3, 3, 2, 5]
def baseStart_6455719 : Nat := 118140960795 + 6455719 * 2 ^ 59
def prefixEnd_6455719 : Nat := 4983230072969 + 3 ^ 40 * 6455719 * 2
def baseEnd_6455719 : Nat := 368320757484770300380355

theorem tailTrace_6455719 : CollatzResearch.WordTrace tailWord_6455719 prefixEnd_6455719 368320757484770300380355 := by
  unfold tailWord_6455719
  simp only [CollatzResearch.WordTrace]
  refine ⟨235459415699040086871898211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156972943799360057914598807 235459415699040086871898211)
  ·
    refine ⟨353189123548560130307847317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235459415699040086871898211 353189123548560130307847317)
    ·
      refine ⟨16555740166338756108180343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 353189123548560130307847317 16555740166338756108180343)
      ·
        refine ⟨24833610249508134162270515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16555740166338756108180343 24833610249508134162270515)
        ·
          refine ⟨37250415374262201243405773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24833610249508134162270515 37250415374262201243405773)
          ·
            refine ⟨13968905765348325466277165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37250415374262201243405773 13968905765348325466277165)
            ·
              refine ⟨5238339662005622049853937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13968905765348325466277165 5238339662005622049853937)
              ·
                refine ⟨3928754746504216537390453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238339662005622049853937 3928754746504216537390453)
                ·
                  refine ⟨368320757484770300380355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3928754746504216537390453 368320757484770300380355)
                  ·
                    rfl

theorem cell23_6455719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 5].length) (baseStart_6455719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455719 prefixEnd_6455719 := by exact prefixLift 6455719
  have htrace : WordTrace (prefixWord ++ tailWord_6455719) baseStart_6455719 baseEnd_6455719 := by
    simpa [prefixWord, tailWord_6455719, baseEnd_6455719] using wordTrace_append hprefix tailTrace_6455719
  have hstable : (prefixWord ++ tailWord_6455719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455719).length < 2 ^ (prefixWord ++ tailWord_6455719).sum := by decide
  have hdescent : baseEnd_6455719 < baseStart_6455719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455738 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_6455738 : Nat := 118140960795 + 6455738 * 2 ^ 59
def prefixEnd_6455738 : Nat := 4983230072969 + 3 ^ 40 * 6455738 * 2
def baseEnd_6455738 : Nat := 3314896573495368129085607

theorem tailTrace_6455738 : CollatzResearch.WordTrace tailWord_6455738 prefixEnd_6455738 3314896573495368129085607 := by
  unfold tailWord_6455738
  simp only [CollatzResearch.WordTrace]
  refine ⟨58865027171492813279209967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156973405790647502077893245 58865027171492813279209967)
  ·
    refine ⟨88297540757239219918814951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58865027171492813279209967 88297540757239219918814951)
    ·
      refine ⟨132446311135858829878222427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88297540757239219918814951 132446311135858829878222427)
      ·
        refine ⟨198669466703788244817333641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132446311135858829878222427 198669466703788244817333641)
        ·
          refine ⟨149002100027841183613000231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198669466703788244817333641 149002100027841183613000231)
          ·
            refine ⟨223503150041761775419500347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149002100027841183613000231 223503150041761775419500347)
            ·
              refine ⟨335254725062642663129250521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223503150041761775419500347 335254725062642663129250521)
              ·
                refine ⟨251441043796981997346937891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335254725062642663129250521 251441043796981997346937891)
                ·
                  refine ⟨377161565695472996020406837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251441043796981997346937891 377161565695472996020406837)
                  ·
                    refine ⟨35358896783950593376913141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377161565695472996020406837 35358896783950593376913141)
                    ·
                      refine ⟨3314896573495368129085607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35358896783950593376913141 3314896573495368129085607)
                      ·
                        rfl

theorem cell23_6455738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_6455738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455738 prefixEnd_6455738 := by exact prefixLift 6455738
  have htrace : WordTrace (prefixWord ++ tailWord_6455738) baseStart_6455738 baseEnd_6455738 := by
    simpa [prefixWord, tailWord_6455738, baseEnd_6455738] using wordTrace_append hprefix tailTrace_6455738
  have hstable : (prefixWord ++ tailWord_6455738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455738).length < 2 ^ (prefixWord ++ tailWord_6455738).sum := by decide
  have hdescent : baseEnd_6455738 < baseStart_6455738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455752 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_6455752 : Nat := 118140960795 + 6455752 * 2 ^ 59
def prefixEnd_6455752 : Nat := 4983230072969 + 3 ^ 40 * 6455752 * 2
def baseEnd_6455752 : Nat := 3314903762224531074310543

theorem tailTrace_6455752 : CollatzResearch.WordTrace tailWord_6455752 prefixEnd_6455752 3314903762224531074310543 := by
  unfold tailWord_6455752
  simp only [CollatzResearch.WordTrace]
  refine ⟨117730309653960266753924755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156973746205280355671899673 117730309653960266753924755)
  ·
    refine ⟨176595464480940400130887133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117730309653960266753924755 176595464480940400130887133)
    ·
      refine ⟨66223299180352650049082675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176595464480940400130887133 66223299180352650049082675)
      ·
        refine ⟨99334948770528975073624013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66223299180352650049082675 99334948770528975073624013)
        ·
          refine ⟨37250605788948365652609005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99334948770528975073624013 37250605788948365652609005)
          ·
            refine ⟨13968977170855637119728377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37250605788948365652609005 13968977170855637119728377)
            ·
              refine ⟨10476732878141727839796283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13968977170855637119728377 10476732878141727839796283)
              ·
                refine ⟨15715099317212591759694425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10476732878141727839796283 15715099317212591759694425)
                ·
                  refine ⟨11786324487909443819770819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15715099317212591759694425 11786324487909443819770819)
                  ·
                    refine ⟨17679486731864165729656229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11786324487909443819770819 17679486731864165729656229)
                    ·
                      refine ⟨3314903762224531074310543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17679486731864165729656229 3314903762224531074310543)
                      ·
                        rfl

theorem cell23_6455752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_6455752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455752 prefixEnd_6455752 := by exact prefixLift 6455752
  have htrace : WordTrace (prefixWord ++ tailWord_6455752) baseStart_6455752 baseEnd_6455752 := by
    simpa [prefixWord, tailWord_6455752, baseEnd_6455752] using wordTrace_append hprefix tailTrace_6455752
  have hstable : (prefixWord ++ tailWord_6455752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455752).length < 2 ^ (prefixWord ++ tailWord_6455752).sum := by decide
  have hdescent : baseEnd_6455752 < baseStart_6455752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455775 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 6]
def baseStart_6455775 : Nat := 118140960795 + 6455775 * 2 ^ 59
def prefixEnd_6455775 : Nat := 4983230072969 + 3 ^ 40 * 6455775 * 2
def baseEnd_6455775 : Nat := 368323952475509387146993

theorem tailTrace_6455775 : CollatzResearch.WordTrace tailWord_6455775 prefixEnd_6455775 368323952475509387146993 := by
  unfold tailWord_6455775
  simp only [CollatzResearch.WordTrace]
  refine ⟨235461458186837208435936779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156974305457891472290624519 235461458186837208435936779)
  ·
    refine ⟨353192187280255812653905169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235461458186837208435936779 353192187280255812653905169)
    ·
      refine ⟨264894140460191859490428877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353192187280255812653905169 264894140460191859490428877)
      ·
        refine ⟨99335302672571947308910829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264894140460191859490428877 99335302672571947308910829)
        ·
          refine ⟨37250738502214480240841561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99335302672571947308910829 37250738502214480240841561)
          ·
            refine ⟨27938053876660860180631171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37250738502214480240841561 27938053876660860180631171)
            ·
              refine ⟨41907080814991290270946757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27938053876660860180631171 41907080814991290270946757)
              ·
                refine ⟨7857577652810866925802517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41907080814991290270946757 7857577652810866925802517)
                ·
                  refine ⟨368323952475509387146993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7857577652810866925802517 368323952475509387146993)
                  ·
                    rfl

theorem cell23_6455775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 6].length) (baseStart_6455775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455775 prefixEnd_6455775 := by exact prefixLift 6455775
  have htrace : WordTrace (prefixWord ++ tailWord_6455775) baseStart_6455775 baseEnd_6455775 := by
    simpa [prefixWord, tailWord_6455775, baseEnd_6455775] using wordTrace_append hprefix tailTrace_6455775
  have hstable : (prefixWord ++ tailWord_6455775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455775).length < 2 ^ (prefixWord ++ tailWord_6455775).sum := by decide
  have hdescent : baseEnd_6455775 < baseStart_6455775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455805 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_6455805 : Nat := 118140960795 + 6455805 * 2 ^ 59
def prefixEnd_6455805 : Nat := 4983230072969 + 3 ^ 40 * 6455805 * 2
def baseEnd_6455805 : Nat := 1104976992233073122315933

theorem tailTrace_6455805 : CollatzResearch.WordTrace tailWord_6455805 prefixEnd_6455805 1104976992233073122315933 := by
  unfold tailWord_6455805
  simp only [CollatzResearch.WordTrace]
  refine ⟨235462552376728523559528869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156975034917819015706352579 235462552376728523559528869)
  ·
    refine ⟨44149228570636598167411663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235462552376728523559528869 44149228570636598167411663)
    ·
      refine ⟨66223842855954897251117495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44149228570636598167411663 66223842855954897251117495)
      ·
        refine ⟨99335764283932345876676243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66223842855954897251117495 99335764283932345876676243)
        ·
          refine ⟨149003646425898518815014365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99335764283932345876676243 149003646425898518815014365)
          ·
            refine ⟨55876367409711944555630387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149003646425898518815014365 55876367409711944555630387)
            ·
              refine ⟨83814551114567916833445581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55876367409711944555630387 83814551114567916833445581)
              ·
                refine ⟨31430456667962968812542093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83814551114567916833445581 31430456667962968812542093)
                ·
                  refine ⟨11786421250486113304703285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31430456667962968812542093 11786421250486113304703285)
                  ·
                    refine ⟨1104976992233073122315933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11786421250486113304703285 1104976992233073122315933)
                    ·
                      rfl

theorem cell23_6455805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_6455805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455805 prefixEnd_6455805 := by exact prefixLift 6455805
  have htrace : WordTrace (prefixWord ++ tailWord_6455805) baseStart_6455805 baseEnd_6455805 := by
    simpa [prefixWord, tailWord_6455805, baseEnd_6455805] using wordTrace_append hprefix tailTrace_6455805
  have hstable : (prefixWord ++ tailWord_6455805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455805).length < 2 ^ (prefixWord ++ tailWord_6455805).sum := by decide
  have hdescent : baseEnd_6455805 < baseStart_6455805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455825 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_6455825 : Nat := 118140960795 + 6455825 * 2 ^ 59
def prefixEnd_6455825 : Nat := 4983230072969 + 3 ^ 40 * 6455825 * 2
def baseEnd_6455825 : Nat := 3314941246312309288697707

theorem tailTrace_6455825 : CollatzResearch.WordTrace tailWord_6455825 prefixEnd_6455825 3314941246312309288697707 := by
  unfold tailWord_6455825
  simp only [CollatzResearch.WordTrace]
  refine ⟨235463281836656066975256929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156975521224437377983504619 235463281836656066975256929)
  ·
    refine ⟨176597461377492050231442697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235463281836656066975256929 176597461377492050231442697)
    ·
      refine ⟨132448096033119037673582023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176597461377492050231442697 132448096033119037673582023)
      ·
        refine ⟨198672144049678556510373035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132448096033119037673582023 198672144049678556510373035)
        ·
          refine ⟨298008216074517834765559553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198672144049678556510373035 298008216074517834765559553)
          ·
            refine ⟨223506162055888376074169665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298008216074517834765559553 223506162055888376074169665)
            ·
              refine ⟨167629621541916282055627249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223506162055888376074169665 167629621541916282055627249)
              ·
                refine ⟨125722216156437211541720437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167629621541916282055627249 125722216156437211541720437)
                ·
                  refine ⟨11786457764665988582036291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125722216156437211541720437 11786457764665988582036291)
                  ·
                    refine ⟨17679686646998982873054437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11786457764665988582036291 17679686646998982873054437)
                    ·
                      refine ⟨3314941246312309288697707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17679686646998982873054437 3314941246312309288697707)
                      ·
                        rfl

theorem cell23_6455825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_6455825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455825 prefixEnd_6455825 := by exact prefixLift 6455825
  have htrace : WordTrace (prefixWord ++ tailWord_6455825) baseStart_6455825 baseEnd_6455825 := by
    simpa [prefixWord, tailWord_6455825, baseEnd_6455825] using wordTrace_append hprefix tailTrace_6455825
  have hstable : (prefixWord ++ tailWord_6455825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455825).length < 2 ^ (prefixWord ++ tailWord_6455825).sum := by decide
  have hdescent : baseEnd_6455825 < baseStart_6455825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455836 : List Nat := [2, 2, 3, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_6455836 : Nat := 118140960795 + 6455836 * 2 ^ 59
def prefixEnd_6455836 : Nat := 4983230072969 + 3 ^ 40 * 6455836 * 2
def baseEnd_6455836 : Nat := 3314946894599508745660157

theorem tailTrace_6455836 : CollatzResearch.WordTrace tailWord_6455836 prefixEnd_6455836 3314946894599508745660157 := by
  unfold tailWord_6455836
  simp only [CollatzResearch.WordTrace]
  refine ⟨117731841519808107926953681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156975788693077477235938241 117731841519808107926953681)
  ·
    refine ⟨88298881139856080945215261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117731841519808107926953681 88298881139856080945215261)
    ·
      refine ⟨33112080427446030354455723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88298881139856080945215261 33112080427446030354455723)
      ·
        refine ⟨49668120641169045531683585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33112080427446030354455723 49668120641169045531683585)
        ·
          refine ⟨37251090480876784148762689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49668120641169045531683585 37251090480876784148762689)
          ·
            refine ⟨27938317860657588111572017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37251090480876784148762689 27938317860657588111572017)
            ·
              refine ⟨20953738395493191083679013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27938317860657588111572017 20953738395493191083679013)
              ·
                refine ⟨3928825949154973328189815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20953738395493191083679013 3928825949154973328189815)
                ·
                  refine ⟨5893238923732459992284723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928825949154973328189815 5893238923732459992284723)
                  ·
                    refine ⟨8839858385598689988427085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5893238923732459992284723 8839858385598689988427085)
                    ·
                      refine ⟨3314946894599508745660157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8839858385598689988427085 3314946894599508745660157)
                      ·
                        rfl

theorem cell23_6455836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_6455836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455836 prefixEnd_6455836 := by exact prefixLift 6455836
  have htrace : WordTrace (prefixWord ++ tailWord_6455836) baseStart_6455836 baseEnd_6455836 := by
    simpa [prefixWord, tailWord_6455836, baseEnd_6455836] using wordTrace_append hprefix tailTrace_6455836
  have hstable : (prefixWord ++ tailWord_6455836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455836).length < 2 ^ (prefixWord ++ tailWord_6455836).sum := by decide
  have hdescent : baseEnd_6455836 < baseStart_6455836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455845 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_6455845 : Nat := 118140960795 + 6455845 * 2 ^ 59
def prefixEnd_6455845 : Nat := 4983230072969 + 3 ^ 40 * 6455845 * 2
def baseEnd_6455845 : Nat := 3314951515925399210447615

theorem tailTrace_6455845 : CollatzResearch.WordTrace tailWord_6455845 prefixEnd_6455845 3314951515925399210447615 := by
  unfold tailWord_6455845
  simp only [CollatzResearch.WordTrace]
  refine ⟨235464011296583610390984989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156976007531055740260656659 235464011296583610390984989)
  ·
    refine ⟨88299004236218853896619371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235464011296583610390984989 88299004236218853896619371)
    ·
      refine ⟨132448506354328280844929057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88299004236218853896619371 132448506354328280844929057)
      ·
        refine ⟨99336379765746210633696793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132448506354328280844929057 99336379765746210633696793)
        ·
          refine ⟨74502284824309657975272595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99336379765746210633696793 74502284824309657975272595)
          ·
            refine ⟨111753427236464486962908893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74502284824309657975272595 111753427236464486962908893)
            ·
              refine ⟨41907535213674182611090835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111753427236464486962908893 41907535213674182611090835)
              ·
                refine ⟨62861302820511273916636253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41907535213674182611090835 62861302820511273916636253)
                ·
                  refine ⟨23572988557691727718738595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62861302820511273916636253 23572988557691727718738595)
                  ·
                    refine ⟨35359482836537591578107893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23572988557691727718738595 35359482836537591578107893)
                    ·
                      refine ⟨3314951515925399210447615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35359482836537591578107893 3314951515925399210447615)
                      ·
                        rfl

theorem cell23_6455845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_6455845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455845 prefixEnd_6455845 := by exact prefixLift 6455845
  have htrace : WordTrace (prefixWord ++ tailWord_6455845) baseStart_6455845 baseEnd_6455845 := by
    simpa [prefixWord, tailWord_6455845, baseEnd_6455845] using wordTrace_append hprefix tailTrace_6455845
  have hstable : (prefixWord ++ tailWord_6455845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455845).length < 2 ^ (prefixWord ++ tailWord_6455845).sum := by decide
  have hdescent : baseEnd_6455845 < baseStart_6455845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455852 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_6455852 : Nat := 118140960795 + 6455852 * 2 ^ 59
def prefixEnd_6455852 : Nat := 4983230072969 + 3 ^ 40 * 6455852 * 2
def baseEnd_6455852 : Nat := 1104985036763326894353361

theorem tailTrace_6455852 : CollatzResearch.WordTrace tailWord_6455852 prefixEnd_6455852 1104985036763326894353361 := by
  unfold tailWord_6455852
  simp only [CollatzResearch.WordTrace]
  refine ⟨117732133303779125293244905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156976177738372167057659873 117732133303779125293244905)
  ·
    refine ⟨88299099977834343969933679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117732133303779125293244905 88299099977834343969933679)
    ·
      refine ⟨132448649966751515954900519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88299099977834343969933679 132448649966751515954900519)
      ·
        refine ⟨198672974950127273932350779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132448649966751515954900519 198672974950127273932350779)
        ·
          refine ⟨298009462425190910898526169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198672974950127273932350779 298009462425190910898526169)
          ·
            refine ⟨223507096818893183173894627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298009462425190910898526169 223507096818893183173894627)
            ·
              refine ⟨335260645228339774760841941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223507096818893183173894627 335260645228339774760841941)
              ·
                refine ⟨7857671372539213470957233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 335260645228339774760841941 7857671372539213470957233)
                ·
                  refine ⟨5893253529404410103217925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7857671372539213470957233 5893253529404410103217925)
                  ·
                    refine ⟨1104985036763326894353361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5893253529404410103217925 1104985036763326894353361)
                    ·
                      rfl

theorem cell23_6455852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_6455852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455852 prefixEnd_6455852 := by exact prefixLift 6455852
  have htrace : WordTrace (prefixWord ++ tailWord_6455852) baseStart_6455852 baseEnd_6455852 := by
    simpa [prefixWord, tailWord_6455852, baseEnd_6455852] using wordTrace_append hprefix tailTrace_6455852
  have hstable : (prefixWord ++ tailWord_6455852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455852).length < 2 ^ (prefixWord ++ tailWord_6455852).sum := by decide
  have hdescent : baseEnd_6455852 < baseStart_6455852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455859 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 3, 2, 2]
def baseStart_6455859 : Nat := 118140960795 + 6455859 * 2 ^ 59
def prefixEnd_6455859 : Nat := 4983230072969 + 3 ^ 40 * 6455859 * 2
def baseEnd_6455859 : Nat := 3314958704654562155672551

theorem tailTrace_6455859 : CollatzResearch.WordTrace tailWord_6455859 prefixEnd_6455859 3314958704654562155672551 := by
  unfold tailWord_6455859
  simp only [CollatzResearch.WordTrace]
  refine ⟨235464521918532890781994631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156976347945688593854663087 235464521918532890781994631)
  ·
    refine ⟨353196782877799336172991947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235464521918532890781994631 353196782877799336172991947)
    ·
      refine ⟨529795174316699004259487921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353196782877799336172991947 529795174316699004259487921)
      ·
        refine ⟨397346380737524253194615941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529795174316699004259487921 397346380737524253194615941)
        ·
          refine ⟨74502446388285797473990489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397346380737524253194615941 74502446388285797473990489)
          ·
            refine ⟨55876834791214348105492867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74502446388285797473990489 55876834791214348105492867)
            ·
              refine ⟨83815252186821522158239301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55876834791214348105492867 83815252186821522158239301)
              ·
                refine ⟨15715359785029035404669869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83815252186821522158239301 15715359785029035404669869)
                ·
                  refine ⟨5893259919385888276751201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15715359785029035404669869 5893259919385888276751201)
                  ·
                    refine ⟨4419944939539416207563401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5893259919385888276751201 4419944939539416207563401)
                    ·
                      refine ⟨3314958704654562155672551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4419944939539416207563401 3314958704654562155672551)
                      ·
                        rfl

theorem cell23_6455859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 2, 2].length) (baseStart_6455859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455859 prefixEnd_6455859 := by exact prefixLift 6455859
  have htrace : WordTrace (prefixWord ++ tailWord_6455859) baseStart_6455859 baseEnd_6455859 := by
    simpa [prefixWord, tailWord_6455859, baseEnd_6455859] using wordTrace_append hprefix tailTrace_6455859
  have hstable : (prefixWord ++ tailWord_6455859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455859).length < 2 ^ (prefixWord ++ tailWord_6455859).sum := by decide
  have hdescent : baseEnd_6455859 < baseStart_6455859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455865 : List Nat := [1, 2, 1, 5, 1, 1, 3, 9]
def baseStart_6455865 : Nat := 118140960795 + 6455865 * 2 ^ 59
def prefixEnd_6455865 : Nat := 4983230072969 + 3 ^ 40 * 6455865 * 2
def baseEnd_6455865 : Nat := 122776362427351449340649

theorem tailTrace_6455865 : CollatzResearch.WordTrace tailWord_6455865 prefixEnd_6455865 122776362427351449340649 := by
  unfold tailWord_6455865
  simp only [CollatzResearch.WordTrace]
  refine ⟨235464740756511153806713049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156976493837674102537808699 235464740756511153806713049)
  ·
    refine ⟨176598555567383365355034787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235464740756511153806713049 176598555567383365355034787)
    ·
      refine ⟨264897833351075048032552181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176598555567383365355034787 264897833351075048032552181)
      ·
        refine ⟨24834171876663285753051767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264897833351075048032552181 24834171876663285753051767)
        ·
          refine ⟨37251257814994928629577651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24834171876663285753051767 37251257814994928629577651)
          ·
            refine ⟨55876886722492392944366477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37251257814994928629577651 55876886722492392944366477)
            ·
              refine ⟨20953832520934647354137429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55876886722492392944366477 20953832520934647354137429)
              ·
                refine ⟨122776362427351449340649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20953832520934647354137429 122776362427351449340649)
                ·
                  rfl

theorem cell23_6455865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 9].length) (baseStart_6455865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455865 prefixEnd_6455865 := by exact prefixLift 6455865
  have htrace : WordTrace (prefixWord ++ tailWord_6455865) baseStart_6455865 baseEnd_6455865 := by
    simpa [prefixWord, tailWord_6455865, baseEnd_6455865] using wordTrace_append hprefix tailTrace_6455865
  have hstable : (prefixWord ++ tailWord_6455865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455865).length < 2 ^ (prefixWord ++ tailWord_6455865).sum := by decide
  have hdescent : baseEnd_6455865 < baseStart_6455865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455879 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_6455879 : Nat := 118140960795 + 6455879 * 2 ^ 59
def prefixEnd_6455879 : Nat := 4983230072969 + 3 ^ 40 * 6455879 * 2
def baseEnd_6455879 : Nat := 3314968974267652077422459

theorem tailTrace_6455879 : CollatzResearch.WordTrace tailWord_6455879 prefixEnd_6455879 3314968974267652077422459 := by
  unfold tailWord_6455879
  simp only [CollatzResearch.WordTrace]
  refine ⟨235465251378460434197722691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156976834252306956131815127 235465251378460434197722691)
  ·
    refine ⟨353197877067690651296584037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235465251378460434197722691 353197877067690651296584037)
    ·
      refine ⟨66224601950191997118109507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353197877067690651296584037 66224601950191997118109507)
      ·
        refine ⟨99336902925287995677164261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66224601950191997118109507 99336902925287995677164261)
        ·
          refine ⟨18625669298491499189468299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99336902925287995677164261 18625669298491499189468299)
          ·
            refine ⟨27938503947737248784202449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18625669298491499189468299 27938503947737248784202449)
            ·
              refine ⟨20953877960802936588151837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27938503947737248784202449 20953877960802936588151837)
              ·
                refine ⟨7857704235301101220556939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20953877960802936588151837 7857704235301101220556939)
                ·
                  refine ⟨11786556352951651830835409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7857704235301101220556939 11786556352951651830835409)
                  ·
                    refine ⟨8839917264713738873126557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11786556352951651830835409 8839917264713738873126557)
                    ·
                      refine ⟨3314968974267652077422459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8839917264713738873126557 3314968974267652077422459)
                      ·
                        rfl

theorem cell23_6455879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_6455879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455879 prefixEnd_6455879 := by exact prefixLift 6455879
  have htrace : WordTrace (prefixWord ++ tailWord_6455879) baseStart_6455879 baseEnd_6455879 := by
    simpa [prefixWord, tailWord_6455879, baseEnd_6455879] using wordTrace_append hprefix tailTrace_6455879
  have hstable : (prefixWord ++ tailWord_6455879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455879).length < 2 ^ (prefixWord ++ tailWord_6455879).sum := by decide
  have hdescent : baseEnd_6455879 < baseStart_6455879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455895 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 2, 7]
def baseStart_6455895 : Nat := 118140960795 + 6455895 * 2 ^ 59
def prefixEnd_6455895 : Nat := 4983230072969 + 3 ^ 40 * 6455895 * 2
def baseEnd_6455895 : Nat := 1104992396652708004940795

theorem tailTrace_6455895 : CollatzResearch.WordTrace tailWord_6455895 prefixEnd_6455895 1104992396652708004940795 := by
  unfold tailWord_6455895
  simp only [CollatzResearch.WordTrace]
  refine ⟨235465834946402468930305139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156977223297601645953536759 235465834946402468930305139)
  ·
    refine ⟨353198752419603703395457709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235465834946402468930305139 353198752419603703395457709)
    ·
      refine ⟨132449532157351388773296641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353198752419603703395457709 132449532157351388773296641)
      ·
        refine ⟨99337149118013541579972481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132449532157351388773296641 99337149118013541579972481)
        ·
          refine ⟨74502861838510156184979361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99337149118013541579972481 74502861838510156184979361)
          ·
            refine ⟨55877146378882617138734521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74502861838510156184979361 55877146378882617138734521)
            ·
              refine ⟨41907859784161962854050891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55877146378882617138734521 41907859784161962854050891)
              ·
                refine ⟨62861789676242944281076337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41907859784161962854050891 62861789676242944281076337)
                ·
                  refine ⟨47146342257182208210807253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62861789676242944281076337 47146342257182208210807253)
                  ·
                    refine ⟨1104992396652708004940795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47146342257182208210807253 1104992396652708004940795)
                    ·
                      rfl

theorem cell23_6455895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_6455895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455895 prefixEnd_6455895 := by exact prefixLift 6455895
  have htrace : WordTrace (prefixWord ++ tailWord_6455895) baseStart_6455895 baseEnd_6455895 := by
    simpa [prefixWord, tailWord_6455895, baseEnd_6455895] using wordTrace_append hprefix tailTrace_6455895
  have hstable : (prefixWord ++ tailWord_6455895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455895).length < 2 ^ (prefixWord ++ tailWord_6455895).sum := by decide
  have hdescent : baseEnd_6455895 < baseStart_6455895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455915 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4]
def baseStart_6455915 : Nat := 118140960795 + 6455915 * 2 ^ 59
def prefixEnd_6455915 : Nat := 4983230072969 + 3 ^ 40 * 6455915 * 2
def baseEnd_6455915 : Nat := 3314987459571213936572293

theorem tailTrace_6455915 : CollatzResearch.WordTrace tailWord_6455915 prefixEnd_6455915 3314987459571213936572293 := by
  unfold tailWord_6455915
  simp only [CollatzResearch.WordTrace]
  refine ⟨235466564406330012346033199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156977709604220008230688799 235466564406330012346033199)
  ·
    refine ⟨353199846609495018519049799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235466564406330012346033199 353199846609495018519049799)
    ·
      refine ⟨529799769914242527778574699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353199846609495018519049799 529799769914242527778574699)
      ·
        refine ⟨794699654871363791667862049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529799769914242527778574699 794699654871363791667862049)
        ·
          refine ⟨596024741153522843750896537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794699654871363791667862049 596024741153522843750896537)
          ·
            refine ⟨447018555865142132813172403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596024741153522843750896537 447018555865142132813172403)
            ·
              refine ⟨670527833797713199219758605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447018555865142132813172403 670527833797713199219758605)
              ·
                refine ⟨251447937674142449707409477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670527833797713199219758605 251447937674142449707409477)
                ·
                  refine ⟨47146488313901709320139277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251447937674142449707409477 47146488313901709320139277)
                  ·
                    refine ⟨17679933117713140995052229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47146488313901709320139277 17679933117713140995052229)
                    ·
                      refine ⟨3314987459571213936572293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17679933117713140995052229 3314987459571213936572293)
                      ·
                        rfl

theorem cell23_6455915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_6455915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455915 prefixEnd_6455915 := by exact prefixLift 6455915
  have htrace : WordTrace (prefixWord ++ tailWord_6455915) baseStart_6455915 baseEnd_6455915 := by
    simpa [prefixWord, tailWord_6455915, baseEnd_6455915] using wordTrace_append hprefix tailTrace_6455915
  have hstable : (prefixWord ++ tailWord_6455915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455915).length < 2 ^ (prefixWord ++ tailWord_6455915).sum := by decide
  have hdescent : baseEnd_6455915 < baseStart_6455915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455926 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_6455926 : Nat := 118140960795 + 6455926 * 2 ^ 59
def prefixEnd_6455926 : Nat := 4983230072969 + 3 ^ 40 * 6455926 * 2
def baseEnd_6455926 : Nat := 3314993107858413393534743

theorem tailTrace_6455926 : CollatzResearch.WordTrace tailWord_6455926 prefixEnd_6455926 3314993107858413393534743 := by
  unfold tailWord_6455926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14716685350580635076542727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156977977072860107483122421 14716685350580635076542727)
  ·
    refine ⟨22075028025870952614814091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14716685350580635076542727 22075028025870952614814091)
    ·
      refine ⟨33112542038806428922221137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22075028025870952614814091 33112542038806428922221137)
      ·
        refine ⟨24834406529104821691665853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33112542038806428922221137 24834406529104821691665853)
        ·
          refine ⟨9312902448414308134374695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24834406529104821691665853 9312902448414308134374695)
          ·
            refine ⟨13969353672621462201562043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9312902448414308134374695 13969353672621462201562043)
            ·
              refine ⟨20954030508932193302343065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13969353672621462201562043 20954030508932193302343065)
              ·
                refine ⟨15715522881699144976757299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20954030508932193302343065 15715522881699144976757299)
                ·
                  refine ⟨23573284322548717465135949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15715522881699144976757299 23573284322548717465135949)
                  ·
                    refine ⟨8839981620955769049425981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23573284322548717465135949 8839981620955769049425981)
                    ·
                      refine ⟨3314993107858413393534743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8839981620955769049425981 3314993107858413393534743)
                      ·
                        rfl

theorem cell23_6455926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_6455926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455926 prefixEnd_6455926 := by exact prefixLift 6455926
  have htrace : WordTrace (prefixWord ++ tailWord_6455926) baseStart_6455926 baseEnd_6455926 := by
    simpa [prefixWord, tailWord_6455926, baseEnd_6455926] using wordTrace_append hprefix tailTrace_6455926
  have hstable : (prefixWord ++ tailWord_6455926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455926).length < 2 ^ (prefixWord ++ tailWord_6455926).sum := by decide
  have hdescent : baseEnd_6455926 < baseStart_6455926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455935 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_6455935 : Nat := 118140960795 + 6455935 * 2 ^ 59
def prefixEnd_6455935 : Nat := 4983230072969 + 3 ^ 40 * 6455935 * 2
def baseEnd_6455935 : Nat := 3314997729184303858322201

theorem tailTrace_6455935 : CollatzResearch.WordTrace tailWord_6455935 prefixEnd_6455935 3314997729184303858322201 := by
  unfold tailWord_6455935
  simp only [CollatzResearch.WordTrace]
  refine ⟨235467293866257555761761259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156978195910838370507840839 235467293866257555761761259)
  ·
    refine ⟨353200940799386333642641889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235467293866257555761761259 353200940799386333642641889)
    ·
      refine ⟨264900705599539750231981417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353200940799386333642641889 264900705599539750231981417)
      ·
        refine ⟨198675529199654812673986063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264900705599539750231981417 198675529199654812673986063)
        ·
          refine ⟨298013293799482219010979095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198675529199654812673986063 298013293799482219010979095)
          ·
            refine ⟨447019940699223328516468643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298013293799482219010979095 447019940699223328516468643)
            ·
              refine ⟨670529911048834992774702965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447019940699223328516468643 670529911048834992774702965)
              ·
                refine ⟨62862179160828280572628403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670529911048834992774702965 62862179160828280572628403)
                ·
                  refine ⟨94293268741242420858942605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62862179160828280572628403 94293268741242420858942605)
                  ·
                    refine ⟨35359975777965907822103477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94293268741242420858942605 35359975777965907822103477)
                    ·
                      refine ⟨3314997729184303858322201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35359975777965907822103477 3314997729184303858322201)
                      ·
                        rfl

theorem cell23_6455935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_6455935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455935 prefixEnd_6455935 := by exact prefixLift 6455935
  have htrace : WordTrace (prefixWord ++ tailWord_6455935) baseStart_6455935 baseEnd_6455935 := by
    simpa [prefixWord, tailWord_6455935, baseEnd_6455935] using wordTrace_append hprefix tailTrace_6455935
  have hstable : (prefixWord ++ tailWord_6455935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455935).length < 2 ^ (prefixWord ++ tailWord_6455935).sum := by decide
  have hdescent : baseEnd_6455935 < baseStart_6455935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455945 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_6455945 : Nat := 118140960795 + 6455945 * 2 ^ 59
def prefixEnd_6455945 : Nat := 4983230072969 + 3 ^ 40 * 6455945 * 2
def baseEnd_6455945 : Nat := 3315002863990848819197155

theorem tailTrace_6455945 : CollatzResearch.WordTrace tailWord_6455945 prefixEnd_6455945 3315002863990848819197155 := by
  unfold tailWord_6455945
  simp only [CollatzResearch.WordTrace]
  refine ⟨235467658596221327469625289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156978439064147551646416859 235467658596221327469625289)
  ·
    refine ⟨176600743947165995602218967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235467658596221327469625289 176600743947165995602218967)
    ·
      refine ⟨264901115920748993403328451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176600743947165995602218967 264901115920748993403328451)
      ·
        refine ⟨397351673881123490104992677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264901115920748993403328451 397351673881123490104992677)
        ·
          refine ⟨74503438852710654394686127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397351673881123490104992677 74503438852710654394686127)
          ·
            refine ⟨111755158279065981592029191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74503438852710654394686127 111755158279065981592029191)
            ·
              refine ⟨167632737418598972388043787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111755158279065981592029191 167632737418598972388043787)
              ·
                refine ⟨251449106127898458582065681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167632737418598972388043787 251449106127898458582065681)
                ·
                  refine ⟨188586829595923843936549261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251449106127898458582065681 188586829595923843936549261)
                  ·
                    refine ⟨70720061098471441476205973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188586829595923843936549261 70720061098471441476205973)
                    ·
                      refine ⟨3315002863990848819197155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70720061098471441476205973 3315002863990848819197155)
                      ·
                        rfl

theorem cell23_6455945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_6455945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455945 prefixEnd_6455945 := by exact prefixLift 6455945
  have htrace : WordTrace (prefixWord ++ tailWord_6455945) baseStart_6455945 baseEnd_6455945 := by
    simpa [prefixWord, tailWord_6455945, baseEnd_6455945] using wordTrace_append hprefix tailTrace_6455945
  have hstable : (prefixWord ++ tailWord_6455945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455945).length < 2 ^ (prefixWord ++ tailWord_6455945).sum := by decide
  have hdescent : baseEnd_6455945 < baseStart_6455945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6455972 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 7]
def baseStart_6455972 : Nat := 118140960795 + 6455972 * 2 ^ 59
def prefixEnd_6455972 : Nat := 4983230072969 + 3 ^ 40 * 6455972 * 2
def baseEnd_6455972 : Nat := 368335191996502245951059

theorem tailTrace_6455972 : CollatzResearch.WordTrace tailWord_6455972 prefixEnd_6455972 368335191996502245951059 := by
  unfold tailWord_6455972
  simp only [CollatzResearch.WordTrace]
  refine ⟨117734321683561755540429085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156979095578082340720572113 117734321683561755540429085)
  ·
    refine ⟨44150370631335658327660907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117734321683561755540429085 44150370631335658327660907)
    ·
      refine ⟨66225555947003487491491361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44150370631335658327660907 66225555947003487491491361)
      ·
        refine ⟨49669166960252615618618521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66225555947003487491491361 49669166960252615618618521)
        ·
          refine ⟨37251875220189461713963891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49669166960252615618618521 37251875220189461713963891)
          ·
            refine ⟨55877812830284192570945837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37251875220189461713963891 55877812830284192570945837)
            ·
              refine ⟨20954179811356572214104689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55877812830284192570945837 20954179811356572214104689)
              ·
                refine ⟨15715634858517429160578517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20954179811356572214104689 15715634858517429160578517)
                ·
                  refine ⟨368335191996502245951059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15715634858517429160578517 368335191996502245951059)
                  ·
                    rfl

theorem cell23_6455972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_6455972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6455972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6455972 prefixEnd_6455972 := by exact prefixLift 6455972
  have htrace : WordTrace (prefixWord ++ tailWord_6455972) baseStart_6455972 baseEnd_6455972 := by
    simpa [prefixWord, tailWord_6455972, baseEnd_6455972] using wordTrace_append hprefix tailTrace_6455972
  have hstable : (prefixWord ++ tailWord_6455972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6455972).length < 2 ^ (prefixWord ++ tailWord_6455972).sum := by decide
  have hdescent : baseEnd_6455972 < baseStart_6455972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6455972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456042 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_6456042 : Nat := 118140960795 + 6456042 * 2 ^ 59
def prefixEnd_6456042 : Nat := 4983230072969 + 3 ^ 40 * 6456042 * 2
def baseEnd_6456042 : Nat := 3315052671614334939684209

theorem tailTrace_6456042 : CollatzResearch.WordTrace tailWord_6456042 prefixEnd_6456042 3315052671614334939684209 := by
  unfold tailWord_6456042
  simp only [CollatzResearch.WordTrace]
  refine ⟨58867799119217478258976595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156980797651246608690604253 58867799119217478258976595)
  ·
    refine ⟨88301698678826217388464893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58867799119217478258976595 88301698678826217388464893)
    ·
      refine ⟨33113137004559831520674335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88301698678826217388464893 33113137004559831520674335)
      ·
        refine ⟨49669705506839747281011503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33113137004559831520674335 49669705506839747281011503)
        ·
          refine ⟨74504558260259620921517255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49669705506839747281011503 74504558260259620921517255)
          ·
            refine ⟨111756837390389431382275883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74504558260259620921517255 111756837390389431382275883)
            ·
              refine ⟨167635256085584147073413825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111756837390389431382275883 167635256085584147073413825)
              ·
                refine ⟨125726442064188110305060369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167635256085584147073413825 125726442064188110305060369)
                ·
                  refine ⟨94294831548141082728795277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125726442064188110305060369 94294831548141082728795277)
                  ·
                    refine ⟨35360561830552906023298229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94294831548141082728795277 35360561830552906023298229)
                    ·
                      refine ⟨3315052671614334939684209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35360561830552906023298229 3315052671614334939684209)
                      ·
                        rfl

theorem cell23_6456042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_6456042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456042 prefixEnd_6456042 := by exact prefixLift 6456042
  have htrace : WordTrace (prefixWord ++ tailWord_6456042) baseStart_6456042 baseEnd_6456042 := by
    simpa [prefixWord, tailWord_6456042, baseEnd_6456042] using wordTrace_append hprefix tailTrace_6456042
  have hstable : (prefixWord ++ tailWord_6456042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456042).length < 2 ^ (prefixWord ++ tailWord_6456042).sum := by decide
  have hdescent : baseEnd_6456042 < baseStart_6456042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456146 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_6456146 : Nat := 118140960795 + 6456146 * 2 ^ 59
def prefixEnd_6456146 : Nat := 4983230072969 + 3 ^ 40 * 6456146 * 2
def baseEnd_6456146 : Nat := 3315106073602402532783731

theorem tailTrace_6456146 : CollatzResearch.WordTrace tailWord_6456146 prefixEnd_6456146 3315106073602402532783731 := by
  unfold tailWord_6456146
  simp only [CollatzResearch.WordTrace]
  refine ⟨58868747417123284699423073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156983326445662092531794861 58868747417123284699423073)
  ·
    refine ⟨44151560562842463524567305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58868747417123284699423073 44151560562842463524567305)
    ·
      refine ⟨33113670422131847643425479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44151560562842463524567305 33113670422131847643425479)
      ·
        refine ⟨49670505633197771465138219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33113670422131847643425479 49670505633197771465138219)
        ·
          refine ⟨74505758449796657197707329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49670505633197771465138219 74505758449796657197707329)
          ·
            refine ⟨55879318837347492898280497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74505758449796657197707329 55879318837347492898280497)
            ·
              refine ⟨41909489128010619673710373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55879318837347492898280497 41909489128010619673710373)
              ·
                refine ⟨7858029211501991188820695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41909489128010619673710373 7858029211501991188820695)
                ·
                  refine ⟨11787043817252986783231043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7858029211501991188820695 11787043817252986783231043)
                  ·
                    refine ⟨17680565725879480174846565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11787043817252986783231043 17680565725879480174846565)
                    ·
                      refine ⟨3315106073602402532783731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17680565725879480174846565 3315106073602402532783731)
                      ·
                        rfl

theorem cell23_6456146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_6456146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456146 prefixEnd_6456146 := by exact prefixLift 6456146
  have htrace : WordTrace (prefixWord ++ tailWord_6456146) baseStart_6456146 baseEnd_6456146 := by
    simpa [prefixWord, tailWord_6456146, baseEnd_6456146] using wordTrace_append hprefix tailTrace_6456146
  have hstable : (prefixWord ++ tailWord_6456146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456146).length < 2 ^ (prefixWord ++ tailWord_6456146).sum := by decide
  have hdescent : baseEnd_6456146 < baseStart_6456146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456152 : List Nat := [2, 1, 2, 2, 1, 1, 1, 13]
def baseStart_6456152 : Nat := 118140960795 + 6456152 * 2 ^ 59
def prefixEnd_6456152 : Nat := 4983230072969 + 3 ^ 40 * 6456152 * 2
def baseEnd_6456152 : Nat := 122781820536530722566989

theorem tailTrace_6456152 : CollatzResearch.WordTrace tailWord_6456152 prefixEnd_6456152 122781820536530722566989 := by
  unfold tailWord_6456152
  simp only [CollatzResearch.WordTrace]
  refine ⟨117737604253235700911205355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156983472337647601214940473 117737604253235700911205355)
  ·
    refine ⟨176606406379853551366808033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117737604253235700911205355 176606406379853551366808033)
    ·
      refine ⟨132454804784890163525106025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176606406379853551366808033 132454804784890163525106025)
      ·
        refine ⟨99341103588667622643829519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132454804784890163525106025 99341103588667622643829519)
        ·
          refine ⟨149011655383001433965744279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99341103588667622643829519 149011655383001433965744279)
          ·
            refine ⟨223517483074502150948616419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149011655383001433965744279 223517483074502150948616419)
            ·
              refine ⟨335276224611753226422924629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223517483074502150948616419 335276224611753226422924629)
              ·
                refine ⟨122781820536530722566989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 335276224611753226422924629 122781820536530722566989)
                ·
                  rfl

theorem cell23_6456152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 13].length) (baseStart_6456152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456152 prefixEnd_6456152 := by exact prefixLift 6456152
  have htrace : WordTrace (prefixWord ++ tailWord_6456152) baseStart_6456152 baseEnd_6456152 := by
    simpa [prefixWord, tailWord_6456152, baseEnd_6456152] using wordTrace_append hprefix tailTrace_6456152
  have hstable : (prefixWord ++ tailWord_6456152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456152).length < 2 ^ (prefixWord ++ tailWord_6456152).sum := by decide
  have hdescent : baseEnd_6456152 < baseStart_6456152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456156 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6456156 : Nat := 118140960795 + 6456156 * 2 ^ 59
def prefixEnd_6456156 : Nat := 4983230072969 + 3 ^ 40 * 6456156 * 2
def baseEnd_6456156 : Nat := 1105037069469649164552895

theorem tailTrace_6456156 : CollatzResearch.WordTrace tailWord_6456156 prefixEnd_6456156 1105037069469649164552895 := by
  unfold tailWord_6456156
  simp only [CollatzResearch.WordTrace]
  refine ⟨117737677199228455252778161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156983569598971273670370881 117737677199228455252778161)
  ·
    refine ⟨88303257899421341439583621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117737677199228455252778161 88303257899421341439583621)
    ·
      refine ⟨16556860856141501519921929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88303257899421341439583621 16556860856141501519921929)
      ·
        refine ⟨12417645642106126139941447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16556860856141501519921929 12417645642106126139941447)
        ·
          refine ⟨18626468463159189209912171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12417645642106126139941447 18626468463159189209912171)
          ·
            refine ⟨27939702694738783814868257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18626468463159189209912171 27939702694738783814868257)
            ·
              refine ⟨20954777021054087861151193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27939702694738783814868257 20954777021054087861151193)
              ·
                refine ⟨15716082765790565895863395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20954777021054087861151193 15716082765790565895863395)
                ·
                  refine ⟨23574124148685848843795093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15716082765790565895863395 23574124148685848843795093)
                  ·
                    refine ⟨1105037069469649164552895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23574124148685848843795093 1105037069469649164552895)
                    ·
                      rfl

theorem cell23_6456156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6456156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456156 prefixEnd_6456156 := by exact prefixLift 6456156
  have htrace : WordTrace (prefixWord ++ tailWord_6456156) baseStart_6456156 baseEnd_6456156 := by
    simpa [prefixWord, tailWord_6456156, baseEnd_6456156] using wordTrace_append hprefix tailTrace_6456156
  have hstable : (prefixWord ++ tailWord_6456156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456156).length < 2 ^ (prefixWord ++ tailWord_6456156).sum := by decide
  have hdescent : baseEnd_6456156 < baseStart_6456156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456159 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_6456159 : Nat := 118140960795 + 6456159 * 2 ^ 59
def prefixEnd_6456159 : Nat := 4983230072969 + 3 ^ 40 * 6456159 * 2
def baseEnd_6456159 : Nat := 3315112748850910981921171

theorem tailTrace_6456159 : CollatzResearch.WordTrace tailWord_6456159 prefixEnd_6456159 3315112748850910981921171 := by
  unfold tailWord_6456159
  simp only [CollatzResearch.WordTrace]
  refine ⟨235475463817446042017915531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156983642544964028011943687 235475463817446042017915531)
  ·
    refine ⟨353213195726169063026873297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235475463817446042017915531 353213195726169063026873297)
    ·
      refine ⟨264909896794626797270154973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353213195726169063026873297 264909896794626797270154973)
      ·
        refine ⟨99341211297985048976308115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264909896794626797270154973 99341211297985048976308115)
        ·
          refine ⟨149011816946977573464462173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99341211297985048976308115 149011816946977573464462173)
          ·
            refine ⟨55879431355116590049173315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149011816946977573464462173 55879431355116590049173315)
            ·
              refine ⟨83819147032674885073759973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55879431355116590049173315 83819147032674885073759973)
              ·
                refine ⟨15716090068626540951329995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83819147032674885073759973 15716090068626540951329995)
                ·
                  refine ⟨23574135102939811426994993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15716090068626540951329995 23574135102939811426994993)
                  ·
                    refine ⟨17680601327204858570246245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23574135102939811426994993 17680601327204858570246245)
                    ·
                      refine ⟨3315112748850910981921171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17680601327204858570246245 3315112748850910981921171)
                      ·
                        rfl

theorem cell23_6456159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_6456159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456159 prefixEnd_6456159 := by exact prefixLift 6456159
  have htrace : WordTrace (prefixWord ++ tailWord_6456159) baseStart_6456159 baseEnd_6456159 := by
    simpa [prefixWord, tailWord_6456159, baseEnd_6456159] using wordTrace_append hprefix tailTrace_6456159
  have hstable : (prefixWord ++ tailWord_6456159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456159).length < 2 ^ (prefixWord ++ tailWord_6456159).sum := by decide
  have hdescent : baseEnd_6456159 < baseStart_6456159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456163 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 1, 1, 4]
def baseStart_6456163 : Nat := 118140960795 + 6456163 * 2 ^ 59
def prefixEnd_6456163 : Nat := 4983230072969 + 3 ^ 40 * 6456163 * 2
def baseEnd_6456163 : Nat := 3315114802773528966271153

theorem tailTrace_6456163 : CollatzResearch.WordTrace tailWord_6456163 prefixEnd_6456163 3315114802773528966271153 := by
  unfold tailWord_6456163
  simp only [CollatzResearch.WordTrace]
  refine ⟨235475609709431550701061143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156983739806287700467374095 235475609709431550701061143)
  ·
    refine ⟨353213414564147326051591715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235475609709431550701061143 353213414564147326051591715)
    ·
      refine ⟨529820121846220989077387573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353213414564147326051591715 529820121846220989077387573)
      ·
        refine ⟨49670636423083217726005085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 529820121846220989077387573 49670636423083217726005085)
        ·
          refine ⟨18626488658656206647251907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49670636423083217726005085 18626488658656206647251907)
          ·
            refine ⟨27939732987984309970877861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18626488658656206647251907 27939732987984309970877861)
            ·
              refine ⟨5238699935247058119539599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27939732987984309970877861 5238699935247058119539599)
              ·
                refine ⟨7858049902870587179309399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5238699935247058119539599 7858049902870587179309399)
                ·
                  refine ⟨11787074854305880768964099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7858049902870587179309399 11787074854305880768964099)
                  ·
                    refine ⟨17680612281458821153446149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11787074854305880768964099 17680612281458821153446149)
                    ·
                      refine ⟨3315114802773528966271153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17680612281458821153446149 3315114802773528966271153)
                      ·
                        rfl

theorem cell23_6456163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_6456163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456163 prefixEnd_6456163 := by exact prefixLift 6456163
  have htrace : WordTrace (prefixWord ++ tailWord_6456163) baseStart_6456163 baseEnd_6456163 := by
    simpa [prefixWord, tailWord_6456163, baseEnd_6456163] using wordTrace_append hprefix tailTrace_6456163
  have hstable : (prefixWord ++ tailWord_6456163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456163).length < 2 ^ (prefixWord ++ tailWord_6456163).sum := by decide
  have hdescent : baseEnd_6456163 < baseStart_6456163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456179 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 3]
def baseStart_6456179 : Nat := 118140960795 + 6456179 * 2 ^ 59
def prefixEnd_6456179 : Nat := 4983230072969 + 3 ^ 40 * 6456179 * 2
def baseEnd_6456179 : Nat := 3315123018464000903671079

theorem tailTrace_6456179 : CollatzResearch.WordTrace tailWord_6456179 prefixEnd_6456179 3315123018464000903671079 := by
  unfold tailWord_6456179
  simp only [CollatzResearch.WordTrace]
  refine ⟨235476193277373585433643591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156984128851582390289095727 235476193277373585433643591)
  ·
    refine ⟨353214289916060378150465387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235476193277373585433643591 353214289916060378150465387)
    ·
      refine ⟨529821434874090567225698081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353214289916060378150465387 529821434874090567225698081)
      ·
        refine ⟨397366076155567925419273561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529821434874090567225698081 397366076155567925419273561)
        ·
          refine ⟨298024557116675944064455171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397366076155567925419273561 298024557116675944064455171)
          ·
            refine ⟨447036835675013916096682757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298024557116675944064455171 447036835675013916096682757)
            ·
              refine ⟨83819406689065109268128017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447036835675013916096682757 83819406689065109268128017)
              ·
                refine ⟨62864555016798831951096013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83819406689065109268128017 62864555016798831951096013)
                ·
                  refine ⟨23574208131299561981661005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62864555016798831951096013 23574208131299561981661005)
                  ·
                    refine ⟨8840328049237335743122877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23574208131299561981661005 8840328049237335743122877)
                    ·
                      refine ⟨3315123018464000903671079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8840328049237335743122877 3315123018464000903671079)
                      ·
                        rfl

theorem cell23_6456179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_6456179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456179 prefixEnd_6456179 := by exact prefixLift 6456179
  have htrace : WordTrace (prefixWord ++ tailWord_6456179) baseStart_6456179 baseEnd_6456179 := by
    simpa [prefixWord, tailWord_6456179, baseEnd_6456179] using wordTrace_append hprefix tailTrace_6456179
  have hstable : (prefixWord ++ tailWord_6456179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456179).length < 2 ^ (prefixWord ++ tailWord_6456179).sum := by decide
  have hdescent : baseEnd_6456179 < baseStart_6456179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456190 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6456190 : Nat := 118140960795 + 6456190 * 2 ^ 59
def prefixEnd_6456190 : Nat := 4983230072969 + 3 ^ 40 * 6456190 * 2
def baseEnd_6456190 : Nat := 1105042888917066786877843

theorem tailTrace_6456190 : CollatzResearch.WordTrace tailWord_6456190 prefixEnd_6456190 1105042888917066786877843 := by
  unfold tailWord_6456190
  simp only [CollatzResearch.WordTrace]
  refine ⟨29434574310041716789036753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156984396320222489541529349 29434574310041716789036753)
  ·
    refine ⟨22075930732531287591777565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29434574310041716789036753 22075930732531287591777565)
    ·
      refine ⟨8278474024699232846916587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22075930732531287591777565 8278474024699232846916587)
      ·
        refine ⟨12417711037048849270374881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8278474024699232846916587 12417711037048849270374881)
        ·
          refine ⟨9313283277786636952781161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12417711037048849270374881 9313283277786636952781161)
          ·
            refine ⟨6984962458339977714585871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9313283277786636952781161 6984962458339977714585871)
            ·
              refine ⟨10477443687509966571878807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6984962458339977714585871 10477443687509966571878807)
              ·
                refine ⟨15716165531264949857818211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10477443687509966571878807 15716165531264949857818211)
                ·
                  refine ⟨23574248296897424786727317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15716165531264949857818211 23574248296897424786727317)
                  ·
                    refine ⟨1105042888917066786877843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23574248296897424786727317 1105042888917066786877843)
                    ·
                      rfl

theorem cell23_6456190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6456190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456190 prefixEnd_6456190 := by exact prefixLift 6456190
  have htrace : WordTrace (prefixWord ++ tailWord_6456190) baseStart_6456190 baseEnd_6456190 := by
    simpa [prefixWord, tailWord_6456190, baseEnd_6456190] using wordTrace_append hprefix tailTrace_6456190
  have hstable : (prefixWord ++ tailWord_6456190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456190).length < 2 ^ (prefixWord ++ tailWord_6456190).sum := by decide
  have hdescent : baseEnd_6456190 < baseStart_6456190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456236 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 3, 4, 2]
def baseStart_6456236 : Nat := 118140960795 + 6456236 * 2 ^ 59
def prefixEnd_6456236 : Nat := 4983230072969 + 3 ^ 40 * 6456236 * 2
def baseEnd_6456236 : Nat := 3315152286861307180658317

theorem tailTrace_6456236 : CollatzResearch.WordTrace tailWord_6456236 prefixEnd_6456236 3315152286861307180658317 := by
  unfold tailWord_6456236
  simp only [CollatzResearch.WordTrace]
  refine ⟨117739136119083542084234281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156985514825444722778979041 117739136119083542084234281)
  ·
    refine ⟨88304352089312656563175711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117739136119083542084234281 88304352089312656563175711)
    ·
      refine ⟨132456528133968984844763567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88304352089312656563175711 132456528133968984844763567)
      ·
        refine ⟨198684792200953477267145351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132456528133968984844763567 198684792200953477267145351)
        ·
          refine ⟨298027188301430215900718027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198684792200953477267145351 298027188301430215900718027)
          ·
            refine ⟨447040782452145323851077041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298027188301430215900718027 447040782452145323851077041)
            ·
              refine ⟨335280586839108992888307781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447040782452145323851077041 335280586839108992888307781)
              ·
                refine ⟨62865110032332936166557709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335280586839108992888307781 62865110032332936166557709)
                ·
                  refine ⟨23574416262124851062459141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62865110032332936166557709 23574416262124851062459141)
                  ·
                    refine ⟨4420203049148409574211089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23574416262124851062459141 4420203049148409574211089)
                    ·
                      refine ⟨3315152286861307180658317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420203049148409574211089 3315152286861307180658317)
                      ·
                        rfl

theorem cell23_6456236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_6456236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456236 prefixEnd_6456236 := by exact prefixLift 6456236
  have htrace : WordTrace (prefixWord ++ tailWord_6456236) baseStart_6456236 baseEnd_6456236 := by
    simpa [prefixWord, tailWord_6456236, baseEnd_6456236] using wordTrace_append hprefix tailTrace_6456236
  have hstable : (prefixWord ++ tailWord_6456236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456236).length < 2 ^ (prefixWord ++ tailWord_6456236).sum := by decide
  have hdescent : baseEnd_6456236 < baseStart_6456236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456287 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 2, 2, 2]
def baseStart_6456287 : Nat := 118140960795 + 6456287 * 2 ^ 59
def prefixEnd_6456287 : Nat := 4983230072969 + 3 ^ 40 * 6456287 * 2
def baseEnd_6456287 : Nat := 3315178474374686481120583

theorem tailTrace_6456287 : CollatzResearch.WordTrace tailWord_6456287 prefixEnd_6456287 3315178474374686481120583 := by
  unfold tailWord_6456287
  simp only [CollatzResearch.WordTrace]
  refine ⟨235480132360982319878575115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156986754907321546585716743 235480132360982319878575115)
  ·
    refine ⟨353220198541473479817862673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235480132360982319878575115 353220198541473479817862673)
    ·
      refine ⟨264915148906105109863397005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353220198541473479817862673 264915148906105109863397005)
      ·
        refine ⟨99343180839789416198773877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264915148906105109863397005 99343180839789416198773877)
        ·
          refine ⟨9313423203730257768635051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99343180839789416198773877 9313423203730257768635051)
          ·
            refine ⟨13970134805595386652952577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9313423203730257768635051 13970134805595386652952577)
            ·
              refine ⟨10477601104196539989714433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13970134805595386652952577 10477601104196539989714433)
              ·
                refine ⟨7858200828147404992285825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10477601104196539989714433 7858200828147404992285825)
                ·
                  refine ⟨5893650621110553744214369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7858200828147404992285825 5893650621110553744214369)
                  ·
                    refine ⟨4420237965832915308160777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5893650621110553744214369 4420237965832915308160777)
                    ·
                      refine ⟨3315178474374686481120583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420237965832915308160777 3315178474374686481120583)
                      ·
                        rfl

theorem cell23_6456287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_6456287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456287 prefixEnd_6456287 := by exact prefixLift 6456287
  have htrace : WordTrace (prefixWord ++ tailWord_6456287) baseStart_6456287 baseEnd_6456287 := by
    simpa [prefixWord, tailWord_6456287, baseEnd_6456287] using wordTrace_append hprefix tailTrace_6456287
  have hstable : (prefixWord ++ tailWord_6456287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456287).length < 2 ^ (prefixWord ++ tailWord_6456287).sum := by decide
  have hdescent : baseEnd_6456287 < baseStart_6456287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456289 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 3, 7]
def baseStart_6456289 : Nat := 118140960795 + 6456289 * 2 ^ 59
def prefixEnd_6456289 : Nat := 4983230072969 + 3 ^ 40 * 6456289 * 2
def baseEnd_6456289 : Nat := 1105059833778665157765191

theorem tailTrace_6456289 : CollatzResearch.WordTrace tailWord_6456289 prefixEnd_6456289 1105059833778665157765191 := by
  unfold tailWord_6456289
  simp only [CollatzResearch.WordTrace]
  refine ⟨235480205306975074220147921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156986803537983382813431947 235480205306975074220147921)
  ·
    refine ⟨176610153980231305665110941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235480205306975074220147921 176610153980231305665110941)
    ·
      refine ⟨66228807742586739624416603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176610153980231305665110941 66228807742586739624416603)
      ·
        refine ⟨99343211613880109436624905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66228807742586739624416603 99343211613880109436624905)
        ·
          refine ⟨74507408710410082077468679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99343211613880109436624905 74507408710410082077468679)
          ·
            refine ⟨111761113065615123116203019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74507408710410082077468679 111761113065615123116203019)
            ·
              refine ⟨167641669598422684674304529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111761113065615123116203019 167641669598422684674304529)
              ·
                refine ⟨125731252198817013505728397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167641669598422684674304529 125731252198817013505728397)
                ·
                  refine ⟨47149219574556380064648149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125731252198817013505728397 47149219574556380064648149)
                  ·
                    refine ⟨1105059833778665157765191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47149219574556380064648149 1105059833778665157765191)
                    ·
                      rfl

theorem cell23_6456289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_6456289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456289 prefixEnd_6456289 := by exact prefixLift 6456289
  have htrace : WordTrace (prefixWord ++ tailWord_6456289) baseStart_6456289 baseEnd_6456289 := by
    simpa [prefixWord, tailWord_6456289, baseEnd_6456289] using wordTrace_append hprefix tailTrace_6456289
  have hstable : (prefixWord ++ tailWord_6456289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456289).length < 2 ^ (prefixWord ++ tailWord_6456289).sum := by decide
  have hdescent : baseEnd_6456289 < baseStart_6456289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456338 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6456338 : Nat := 118140960795 + 6456338 * 2 ^ 59
def prefixEnd_6456338 : Nat := 4983230072969 + 3 ^ 40 * 6456338 * 2
def baseEnd_6456338 : Nat := 3315204661888065781582849

theorem tailTrace_6456338 : CollatzResearch.WordTrace tailWord_6456338 prefixEnd_6456338 3315204661888065781582849 := by
  unfold tailWord_6456338
  simp only [CollatzResearch.WordTrace]
  refine ⟨58870498120949388897170417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156987994989198370392454445 58870498120949388897170417)
  ·
    refine ⟨44152873590712041672877813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58870498120949388897170417 44152873590712041672877813)
    ·
      refine ⟨4139331899129253906832295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44152873590712041672877813 4139331899129253906832295)
      ·
        refine ⟨6208997848693880860248443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139331899129253906832295 6208997848693880860248443)
        ·
          refine ⟨9313496773040821290372665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6208997848693880860248443 9313496773040821290372665)
          ·
            refine ⟨6985122579780615967779499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9313496773040821290372665 6985122579780615967779499)
            ·
              refine ⟨10477683869670923951669249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6985122579780615967779499 10477683869670923951669249)
              ·
                refine ⟨7858262902253192963751937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10477683869670923951669249 7858262902253192963751937)
                ·
                  refine ⟨5893697176689894722813953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7858262902253192963751937 5893697176689894722813953)
                  ·
                    refine ⟨4420272882517421042110465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5893697176689894722813953 4420272882517421042110465)
                    ·
                      refine ⟨3315204661888065781582849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420272882517421042110465 3315204661888065781582849)
                      ·
                        rfl

theorem cell23_6456338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6456338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456338 prefixEnd_6456338 := by exact prefixLift 6456338
  have htrace : WordTrace (prefixWord ++ tailWord_6456338) baseStart_6456338 baseEnd_6456338 := by
    simpa [prefixWord, tailWord_6456338, baseEnd_6456338] using wordTrace_append hprefix tailTrace_6456338
  have hstable : (prefixWord ++ tailWord_6456338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456338).length < 2 ^ (prefixWord ++ tailWord_6456338).sum := by decide
  have hdescent : baseEnd_6456338 < baseStart_6456338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456353 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 3, 4]
def baseStart_6456353 : Nat := 118140960795 + 6456353 * 2 ^ 59
def prefixEnd_6456353 : Nat := 4983230072969 + 3 ^ 40 * 6456353 * 2
def baseEnd_6456353 : Nat := 1105070788032627740965093

theorem tailTrace_6456353 : CollatzResearch.WordTrace tailWord_6456353 prefixEnd_6456353 1105070788032627740965093 := by
  unfold tailWord_6456353
  simp only [CollatzResearch.WordTrace]
  refine ⟨235482539578743213150477713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156988359719162142100318475 235482539578743213150477713)
  ·
    refine ⟨176611904684057409862858285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235482539578743213150477713 176611904684057409862858285)
    ·
      refine ⟨66229464256521528698571857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176611904684057409862858285 66229464256521528698571857)
      ·
        refine ⟨49672098192391146523928893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66229464256521528698571857 49672098192391146523928893)
        ·
          refine ⟨18627036822146679946473335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49672098192391146523928893 18627036822146679946473335)
          ·
            refine ⟨27940555233220019919710003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18627036822146679946473335 27940555233220019919710003)
            ·
              refine ⟨41910832849830029879565005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27940555233220019919710003 41910832849830029879565005)
              ·
                refine ⟨15716562318686261204836877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41910832849830029879565005 15716562318686261204836877)
                ·
                  refine ⟨5893710869507347951813829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15716562318686261204836877 5893710869507347951813829)
                  ·
                    refine ⟨1105070788032627740965093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5893710869507347951813829 1105070788032627740965093)
                    ·
                      rfl

theorem cell23_6456353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_6456353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456353 prefixEnd_6456353 := by exact prefixLift 6456353
  have htrace : WordTrace (prefixWord ++ tailWord_6456353) baseStart_6456353 baseEnd_6456353 := by
    simpa [prefixWord, tailWord_6456353, baseEnd_6456353] using wordTrace_append hprefix tailTrace_6456353
  have hstable : (prefixWord ++ tailWord_6456353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456353).length < 2 ^ (prefixWord ++ tailWord_6456353).sum := by decide
  have hdescent : baseEnd_6456353 < baseStart_6456353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456396 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_6456396 : Nat := 118140960795 + 6456396 * 2 ^ 59
def prefixEnd_6456396 : Nat := 4983230072969 + 3 ^ 40 * 6456396 * 2
def baseEnd_6456396 : Nat := 1105078147922008851552527

theorem tailTrace_6456396 : CollatzResearch.WordTrace tailWord_6456396 prefixEnd_6456396 1105078147922008851552527 := by
  unfold tailWord_6456396
  simp only [CollatzResearch.WordTrace]
  refine ⟨117742053958793715747146521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156989405278391620996195361 117742053958793715747146521)
  ·
    refine ⟨88306540469095286810359891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117742053958793715747146521 88306540469095286810359891)
    ·
      refine ⟨132459810703642930215539837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88306540469095286810359891 132459810703642930215539837)
      ·
        refine ⟨49672429013866098830827439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132459810703642930215539837 49672429013866098830827439)
        ·
          refine ⟨74508643520799148246241159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49672429013866098830827439 74508643520799148246241159)
          ·
            refine ⟨111762965281198722369361739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74508643520799148246241159 111762965281198722369361739)
            ·
              refine ⟨167644447921798083554042609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111762965281198722369361739 167644447921798083554042609)
              ·
                refine ⟨125733335941348562665531957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167644447921798083554042609 125733335941348562665531957)
                ·
                  refine ⟨11787500244501427749893621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125733335941348562665531957 11787500244501427749893621)
                  ·
                    refine ⟨1105078147922008851552527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11787500244501427749893621 1105078147922008851552527)
                    ·
                      rfl

theorem cell23_6456396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_6456396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456396 prefixEnd_6456396 := by exact prefixLift 6456396
  have htrace : WordTrace (prefixWord ++ tailWord_6456396) baseStart_6456396 baseEnd_6456396 := by
    simpa [prefixWord, tailWord_6456396, baseEnd_6456396] using wordTrace_append hprefix tailTrace_6456396
  have hstable : (prefixWord ++ tailWord_6456396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456396).length < 2 ^ (prefixWord ++ tailWord_6456396).sum := by decide
  have hdescent : baseEnd_6456396 < baseStart_6456396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456403 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 4, 3, 2]
def baseStart_6456403 : Nat := 118140960795 + 6456403 * 2 ^ 59
def prefixEnd_6456403 : Nat := 4983230072969 + 3 ^ 40 * 6456403 * 2
def baseEnd_6456403 : Nat := 3315238038130608027270049

theorem tailTrace_6456403 : CollatzResearch.WordTrace tailWord_6456403 prefixEnd_6456403 3315238038130608027270049 := by
  unfold tailWord_6456403
  simp only [CollatzResearch.WordTrace]
  refine ⟨235484363228562071689797863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156989575485708047793198575 235484363228562071689797863)
  ·
    refine ⟨353226544842843107534696795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235484363228562071689797863 353226544842843107534696795)
    ·
      refine ⟨529839817264264661302045193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353226544842843107534696795 529839817264264661302045193)
      ·
        refine ⟨397379862948198495976533895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529839817264264661302045193 397379862948198495976533895)
        ·
          refine ⟨596069794422297743964800843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397379862948198495976533895 596069794422297743964800843)
          ·
            refine ⟨894104691633446615947201265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596069794422297743964800843 894104691633446615947201265)
            ·
              refine ⟨670578518725084961960400949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894104691633446615947201265 670578518725084961960400949)
              ·
                refine ⟨62866736130476715183787589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670578518725084961960400949 62866736130476715183787589)
                ·
                  refine ⟨11787513024464384096960173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62866736130476715183787589 11787513024464384096960173)
                  ·
                    refine ⟨4420317384174144036360065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11787513024464384096960173 4420317384174144036360065)
                    ·
                      refine ⟨3315238038130608027270049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420317384174144036360065 3315238038130608027270049)
                      ·
                        rfl

theorem cell23_6456403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 3, 2].length) (baseStart_6456403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456403 prefixEnd_6456403 := by exact prefixLift 6456403
  have htrace : WordTrace (prefixWord ++ tailWord_6456403) baseStart_6456403 baseEnd_6456403 := by
    simpa [prefixWord, tailWord_6456403, baseEnd_6456403] using wordTrace_append hprefix tailTrace_6456403
  have hstable : (prefixWord ++ tailWord_6456403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456403).length < 2 ^ (prefixWord ++ tailWord_6456403).sum := by decide
  have hdescent : baseEnd_6456403 < baseStart_6456403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456430 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_6456430 : Nat := 118140960795 + 6456430 * 2 ^ 59
def prefixEnd_6456430 : Nat := 4983230072969 + 3 ^ 40 * 6456430 * 2
def baseEnd_6456430 : Nat := 1105083967369426473877475

theorem tailTrace_6456430 : CollatzResearch.WordTrace tailWord_6456430 prefixEnd_6456430 1105083967369426473877475 := by
  unfold tailWord_6456430
  simp only [CollatzResearch.WordTrace]
  refine ⟨29435668499933031912628843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156990231999642836867353829 29435668499933031912628843)
  ·
    refine ⟨44153502749899547868943265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29435668499933031912628843 44153502749899547868943265)
    ·
      refine ⟨33115127062424660901707449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44153502749899547868943265 33115127062424660901707449)
      ·
        refine ⟨24836345296818495676280587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33115127062424660901707449 24836345296818495676280587)
        ·
          refine ⟨37254517945227743514420881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24836345296818495676280587 37254517945227743514420881)
          ·
            refine ⟨27940888458920807635815661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37254517945227743514420881 27940888458920807635815661)
            ·
              refine ⟨10477833172095302863430873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27940888458920807635815661 10477833172095302863430873)
              ·
                refine ⟨7858374879071477147573155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10477833172095302863430873 7858374879071477147573155)
                ·
                  refine ⟨11787562318607215721359733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7858374879071477147573155 11787562318607215721359733)
                  ·
                    refine ⟨1105083967369426473877475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11787562318607215721359733 1105083967369426473877475)
                    ·
                      rfl

theorem cell23_6456430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_6456430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456430 prefixEnd_6456430 := by exact prefixLift 6456430
  have htrace : WordTrace (prefixWord ++ tailWord_6456430) baseStart_6456430 baseEnd_6456430 := by
    simpa [prefixWord, tailWord_6456430, baseEnd_6456430] using wordTrace_append hprefix tailTrace_6456430
  have hstable : (prefixWord ++ tailWord_6456430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456430).length < 2 ^ (prefixWord ++ tailWord_6456430).sum := by decide
  have hdescent : baseEnd_6456430 < baseStart_6456430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456433 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_6456433 : Nat := 118140960795 + 6456433 * 2 ^ 59
def prefixEnd_6456433 : Nat := 4983230072969 + 3 ^ 40 * 6456433 * 2
def baseEnd_6456433 : Nat := 3315253442550242909894911

theorem tailTrace_6456433 : CollatzResearch.WordTrace tailWord_6456433 prefixEnd_6456433 3315253442550242909894911 := by
  unfold tailWord_6456433
  simp only [CollatzResearch.WordTrace]
  refine ⟨235485457418453386813389953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156990304945635591208926635 235485457418453386813389953)
  ·
    refine ⟨176614093063840040110042465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235485457418453386813389953 176614093063840040110042465)
    ·
      refine ⟨132460569797880030082531849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176614093063840040110042465 132460569797880030082531849)
      ·
        refine ⟨99345427348410022561898887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132460569797880030082531849 99345427348410022561898887)
        ·
          refine ⟨149018141022615033842848331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99345427348410022561898887 149018141022615033842848331)
          ·
            refine ⟨223527211533922550764272497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149018141022615033842848331 223527211533922550764272497)
            ·
              refine ⟨167645408650441913073204373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223527211533922550764272497 167645408650441913073204373)
              ·
                refine ⟨7858378530489464675306455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167645408650441913073204373 7858378530489464675306455)
                ·
                  refine ⟨11787567795734197012959683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7858378530489464675306455 11787567795734197012959683)
                  ·
                    refine ⟨17681351693601295519439525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11787567795734197012959683 17681351693601295519439525)
                    ·
                      refine ⟨3315253442550242909894911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17681351693601295519439525 3315253442550242909894911)
                      ·
                        rfl

theorem cell23_6456433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_6456433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456433 prefixEnd_6456433 := by exact prefixLift 6456433
  have htrace : WordTrace (prefixWord ++ tailWord_6456433) baseStart_6456433 baseEnd_6456433 := by
    simpa [prefixWord, tailWord_6456433, baseEnd_6456433] using wordTrace_append hprefix tailTrace_6456433
  have hstable : (prefixWord ++ tailWord_6456433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456433).length < 2 ^ (prefixWord ++ tailWord_6456433).sum := by decide
  have hdescent : baseEnd_6456433 < baseStart_6456433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456456 : List Nat := [2, 1, 3, 4, 13]
def baseStart_6456456 : Nat := 118140960795 + 6456456 * 2 ^ 59
def prefixEnd_6456456 : Nat := 4983230072969 + 3 ^ 40 * 6456456 * 2
def baseEnd_6456456 : Nat := 4547688961049789190545

theorem tailTrace_6456456 : CollatzResearch.WordTrace tailWord_6456456 prefixEnd_6456456 4547688961049789190545 := by
  unfold tailWord_6456456
  simp only [CollatzResearch.WordTrace]
  refine ⟨117743148148685030870738611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156990864198246707827651481 117743148148685030870738611)
  ·
    refine ⟨176614722223027546306107917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117743148148685030870738611 176614722223027546306107917)
    ·
      refine ⟨66230520833635329864790469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176614722223027546306107917 66230520833635329864790469)
      ·
        refine ⟨12418222656306624349648213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66230520833635329864790469 12418222656306624349648213)
        ·
          refine ⟨4547688961049789190545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12418222656306624349648213 4547688961049789190545)
          ·
            rfl

theorem cell23_6456456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 13].length) (baseStart_6456456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456456 prefixEnd_6456456 := by exact prefixLift 6456456
  have htrace : WordTrace (prefixWord ++ tailWord_6456456) baseStart_6456456 baseEnd_6456456 := by
    simpa [prefixWord, tailWord_6456456, baseEnd_6456456] using wordTrace_append hprefix tailTrace_6456456
  have hstable : (prefixWord ++ tailWord_6456456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456456).length < 2 ^ (prefixWord ++ tailWord_6456456).sum := by decide
  have hdescent : baseEnd_6456456 < baseStart_6456456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456496 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_6456496 : Nat := 118140960795 + 6456496 * 2 ^ 59
def prefixEnd_6456496 : Nat := 4983230072969 + 3 ^ 40 * 6456496 * 2
def baseEnd_6456496 : Nat := 3315285791831476163407121

theorem tailTrace_6456496 : CollatzResearch.WordTrace tailWord_6456496 prefixEnd_6456496 3315285791831476163407121 := by
  unfold tailWord_6456496
  simp only [CollatzResearch.WordTrace]
  refine ⟨117743877608612574286466671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156991836811483432381955561 117743877608612574286466671)
  ·
    refine ⟨176615816412918861429700007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117743877608612574286466671 176615816412918861429700007)
    ·
      refine ⟨264923724619378292144550011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176615816412918861429700007 264923724619378292144550011)
      ·
        refine ⟨397385586929067438216825017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264923724619378292144550011 397385586929067438216825017)
        ·
          refine ⟨298039190196800578662618763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397385586929067438216825017 298039190196800578662618763)
          ·
            refine ⟨447058785295200867993928145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298039190196800578662618763 447058785295200867993928145)
            ·
              refine ⟨335294088971400650995446109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447058785295200867993928145 335294088971400650995446109)
              ·
                refine ⟨125735283364275244123292291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335294088971400650995446109 125735283364275244123292291)
                ·
                  refine ⟨188602925046412866184938437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125735283364275244123292291 188602925046412866184938437)
                  ·
                    refine ⟨35363048446202412409675957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188602925046412866184938437 35363048446202412409675957)
                    ·
                      refine ⟨3315285791831476163407121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35363048446202412409675957 3315285791831476163407121)
                      ·
                        rfl

theorem cell23_6456496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_6456496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456496 prefixEnd_6456496 := by exact prefixLift 6456496
  have htrace : WordTrace (prefixWord ++ tailWord_6456496) baseStart_6456496 baseEnd_6456496 := by
    simpa [prefixWord, tailWord_6456496, baseEnd_6456496] using wordTrace_append hprefix tailTrace_6456496
  have hstable : (prefixWord ++ tailWord_6456496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456496).length < 2 ^ (prefixWord ++ tailWord_6456496).sum := by decide
  have hdescent : baseEnd_6456496 < baseStart_6456496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456543 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 3]
def baseStart_6456543 : Nat := 118140960795 + 6456543 * 2 ^ 59
def prefixEnd_6456543 : Nat := 4983230072969 + 3 ^ 40 * 6456543 * 2
def baseEnd_6456543 : Nat := 3315309925422237479519405

theorem tailTrace_6456543 : CollatzResearch.WordTrace tailWord_6456543 prefixEnd_6456543 3315309925422237479519405 := by
  unfold tailWord_6456543
  simp only [CollatzResearch.WordTrace]
  refine ⟨235489469448054875599894283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156992979632036583733262855 235489469448054875599894283)
  ·
    refine ⟨353234204172082313399841425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235489469448054875599894283 353234204172082313399841425)
    ·
      refine ⟨264925653129061735049881069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353234204172082313399841425 264925653129061735049881069)
      ·
        refine ⟨99347119923398150643705401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264925653129061735049881069 99347119923398150643705401)
        ·
          refine ⟨74510339942548612982779051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99347119923398150643705401 74510339942548612982779051)
          ·
            refine ⟨111765509913822919474168577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74510339942548612982779051 111765509913822919474168577)
            ·
              refine ⟨83824132435367189605626433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111765509913822919474168577 83824132435367189605626433)
              ·
                refine ⟨62868099326525392204219825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83824132435367189605626433 62868099326525392204219825)
                ·
                  refine ⟨47151074494894044153164869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62868099326525392204219825 47151074494894044153164869)
                  ·
                    refine ⟨8840826467792633278718413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47151074494894044153164869 8840826467792633278718413)
                    ·
                      refine ⟨3315309925422237479519405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8840826467792633278718413 3315309925422237479519405)
                      ·
                        rfl

theorem cell23_6456543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_6456543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456543 prefixEnd_6456543 := by exact prefixLift 6456543
  have htrace : WordTrace (prefixWord ++ tailWord_6456543) baseStart_6456543 baseEnd_6456543 := by
    simpa [prefixWord, tailWord_6456543, baseEnd_6456543] using wordTrace_append hprefix tailTrace_6456543
  have hstable : (prefixWord ++ tailWord_6456543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456543).length < 2 ^ (prefixWord ++ tailWord_6456543).sum := by decide
  have hdescent : baseEnd_6456543 < baseStart_6456543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456574 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_6456574 : Nat := 118140960795 + 6456574 * 2 ^ 59
def prefixEnd_6456574 : Nat := 4983230072969 + 3 ^ 40 * 6456574 * 2
def baseEnd_6456574 : Nat := 3315325843322526858231763

theorem tailTrace_6456574 : CollatzResearch.WordTrace tailWord_6456574 prefixEnd_6456574 3315325843322526858231763 := by
  unfold tailWord_6456574
  simp only [CollatzResearch.WordTrace]
  refine ⟨29436325013867820986784097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156993733407295045262848517 29436325013867820986784097)
  ·
    refine ⟨22077243760400865740088073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29436325013867820986784097 22077243760400865740088073)
    ·
      refine ⟨16557932820300649305066055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22077243760400865740088073 16557932820300649305066055)
      ·
        refine ⟨24836899230450973957599083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16557932820300649305066055 24836899230450973957599083)
        ·
          refine ⟨37255348845676460936398625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24836899230450973957599083 37255348845676460936398625)
          ·
            refine ⟨27941511634257345702298969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37255348845676460936398625 27941511634257345702298969)
            ·
              refine ⟨20956133725693009276724227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27941511634257345702298969 20956133725693009276724227)
              ·
                refine ⟨31434200588539513915086341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20956133725693009276724227 31434200588539513915086341)
                ·
                  refine ⟨5893912610351158859078689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31434200588539513915086341 5893912610351158859078689)
                  ·
                    refine ⟨4420434457763369144309017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5893912610351158859078689 4420434457763369144309017)
                    ·
                      refine ⟨3315325843322526858231763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420434457763369144309017 3315325843322526858231763)
                      ·
                        rfl

theorem cell23_6456574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_6456574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456574 prefixEnd_6456574 := by exact prefixLift 6456574
  have htrace : WordTrace (prefixWord ++ tailWord_6456574) baseStart_6456574 baseEnd_6456574 := by
    simpa [prefixWord, tailWord_6456574, baseEnd_6456574] using wordTrace_append hprefix tailTrace_6456574
  have hstable : (prefixWord ++ tailWord_6456574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456574).length < 2 ^ (prefixWord ++ tailWord_6456574).sum := by decide
  have hdescent : baseEnd_6456574 < baseStart_6456574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456580 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 7]
def baseStart_6456580 : Nat := 118140960795 + 6456580 * 2 ^ 59
def prefixEnd_6456580 : Nat := 4983230072969 + 3 ^ 40 * 6456580 * 2
def baseEnd_6456580 : Nat := 368369880467383759417415

theorem tailTrace_6456580 : CollatzResearch.WordTrace tailWord_6456580 prefixEnd_6456580 368369880467383759417415 := by
  unfold tailWord_6456580
  simp only [CollatzResearch.WordTrace]
  refine ⟨117745409474460415459495597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156993879299280553945994129 117745409474460415459495597)
  ·
    refine ⟨44154528552922655797310849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117745409474460415459495597 44154528552922655797310849)
    ·
      refine ⟨33115896414691991847983137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44154528552922655797310849 33115896414691991847983137)
      ·
        refine ⟨24836922311018993885987353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33115896414691991847983137 24836922311018993885987353)
        ·
          refine ⟨18627691733264245414490515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24836922311018993885987353 18627691733264245414490515)
          ·
            refine ⟨27941537599896368121735773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18627691733264245414490515 27941537599896368121735773)
            ·
              refine ⟨10478076599961138045650915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27941537599896368121735773 10478076599961138045650915)
              ·
                refine ⟨15717114899941707068476373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10478076599961138045650915 15717114899941707068476373)
                ·
                  refine ⟨368369880467383759417415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15717114899941707068476373 368369880467383759417415)
                  ·
                    rfl

theorem cell23_6456580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_6456580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456580 prefixEnd_6456580 := by exact prefixLift 6456580
  have htrace : WordTrace (prefixWord ++ tailWord_6456580) baseStart_6456580 baseEnd_6456580 := by
    simpa [prefixWord, tailWord_6456580, baseEnd_6456580] using wordTrace_append hprefix tailTrace_6456580
  have hstable : (prefixWord ++ tailWord_6456580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456580).length < 2 ^ (prefixWord ++ tailWord_6456580).sum := by decide
  have hdescent : baseEnd_6456580 < baseStart_6456580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456593 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 4, 5]
def baseStart_6456593 : Nat := 118140960795 + 6456593 * 2 ^ 59
def prefixEnd_6456593 : Nat := 4983230072969 + 3 ^ 40 * 6456593 * 2
def baseEnd_6456593 : Nat := 1105111866484987427964725

theorem tailTrace_6456593 : CollatzResearch.WordTrace tailWord_6456593 prefixEnd_6456593 1105111866484987427964725 := by
  unfold tailWord_6456593
  simp only [CollatzResearch.WordTrace]
  refine ⟨235491293097873734139214433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156994195398582489426142955 235491293097873734139214433)
  ·
    refine ⟨176618469823405300604410825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235491293097873734139214433 176618469823405300604410825)
    ·
      refine ⟨132463852367553975453308119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176618469823405300604410825 132463852367553975453308119)
      ·
        refine ⟨198695778551330963179962179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132463852367553975453308119 198695778551330963179962179)
        ·
          refine ⟨298043667826996444769943269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198695778551330963179962179 298043667826996444769943269)
          ·
            refine ⟨55883187717561833394364363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298043667826996444769943269 55883187717561833394364363)
            ·
              refine ⟨83824781576342750091546545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55883187717561833394364363 83824781576342750091546545)
              ·
                refine ⟨62868586182257062568659909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83824781576342750091546545 62868586182257062568659909)
                ·
                  refine ⟨11787859909173199231623733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62868586182257062568659909 11787859909173199231623733)
                  ·
                    refine ⟨1105111866484987427964725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11787859909173199231623733 1105111866484987427964725)
                    ·
                      rfl

theorem cell23_6456593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_6456593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456593 prefixEnd_6456593 := by exact prefixLift 6456593
  have htrace : WordTrace (prefixWord ++ tailWord_6456593) baseStart_6456593 baseEnd_6456593 := by
    simpa [prefixWord, tailWord_6456593, baseEnd_6456593] using wordTrace_append hprefix tailTrace_6456593
  have hstable : (prefixWord ++ tailWord_6456593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456593).length < 2 ^ (prefixWord ++ tailWord_6456593).sum := by decide
  have hdescent : baseEnd_6456593 < baseStart_6456593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456640 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 3, 4]
def baseStart_6456640 : Nat := 118140960795 + 6456640 * 2 ^ 59
def prefixEnd_6456640 : Nat := 4983230072969 + 3 ^ 40 * 6456640 * 2
def baseEnd_6456640 : Nat := 1105119911015241200002153

theorem tailTrace_6456640 : CollatzResearch.WordTrace tailWord_6456640 prefixEnd_6456640 1105119911015241200002153 := by
  unfold tailWord_6456640
  simp only [CollatzResearch.WordTrace]
  refine ⟨117746503664351730583087687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156995338219135640777450249 117746503664351730583087687)
  ·
    refine ⟨176619755496527595874631531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117746503664351730583087687 176619755496527595874631531)
    ·
      refine ⟨264929633244791393811947297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176619755496527595874631531 264929633244791393811947297)
      ·
        refine ⟨198697224933593545358960473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264929633244791393811947297 198697224933593545358960473)
        ·
          refine ⟨149022918700195159019220355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198697224933593545358960473 149022918700195159019220355)
          ·
            refine ⟨223534378050292738528830533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149022918700195159019220355 223534378050292738528830533)
            ·
              refine ⟨41912695884429888474155725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223534378050292738528830533 41912695884429888474155725)
              ·
                refine ⟨15717260956661208177808397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41912695884429888474155725 15717260956661208177808397)
                ·
                  refine ⟨5893972858747953066678149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15717260956661208177808397 5893972858747953066678149)
                  ·
                    refine ⟨1105119911015241200002153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5893972858747953066678149 1105119911015241200002153)
                    ·
                      rfl

theorem cell23_6456640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_6456640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456640 prefixEnd_6456640 := by exact prefixLift 6456640
  have htrace : WordTrace (prefixWord ++ tailWord_6456640) baseStart_6456640 baseEnd_6456640 := by
    simpa [prefixWord, tailWord_6456640, baseEnd_6456640] using wordTrace_append hprefix tailTrace_6456640
  have hstable : (prefixWord ++ tailWord_6456640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456640).length < 2 ^ (prefixWord ++ tailWord_6456640).sum := by decide
  have hdescent : baseEnd_6456640 < baseStart_6456640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456643 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4]
def baseStart_6456643 : Nat := 118140960795 + 6456643 * 2 ^ 59
def prefixEnd_6456643 : Nat := 4983230072969 + 3 ^ 40 * 6456643 * 2
def baseEnd_6456643 : Nat := 3315361273487687088268945

theorem tailTrace_6456643 : CollatzResearch.WordTrace tailWord_6456643 prefixEnd_6456643 3315361273487687088268945 := by
  unfold tailWord_6456643
  simp only [CollatzResearch.WordTrace]
  refine ⟨235493116747692592678534583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156995411165128395119023055 235493116747692592678534583)
  ·
    refine ⟨353239675121538889017801875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235493116747692592678534583 353239675121538889017801875)
    ·
      refine ⟨529859512682308333526702813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353239675121538889017801875 529859512682308333526702813)
      ·
        refine ⟨198697317255865625072513555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 529859512682308333526702813 198697317255865625072513555)
        ·
          refine ⟨298045975883798437608770333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198697317255865625072513555 298045975883798437608770333)
          ·
            refine ⟨111767240956424414103288875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298045975883798437608770333 111767240956424414103288875)
            ·
              refine ⟨167650861434636621154933313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111767240956424414103288875 167650861434636621154933313)
              ·
                refine ⟨125738146075977465866199985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167650861434636621154933313 125738146075977465866199985)
                ·
                  refine ⟨94303609556983099399649989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125738146075977465866199985 94303609556983099399649989)
                  ·
                    refine ⟨17681926791934331137434373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94303609556983099399649989 17681926791934331137434373)
                    ·
                      refine ⟨3315361273487687088268945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17681926791934331137434373 3315361273487687088268945)
                      ·
                        rfl

theorem cell23_6456643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_6456643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456643 prefixEnd_6456643 := by exact prefixLift 6456643
  have htrace : WordTrace (prefixWord ++ tailWord_6456643) baseStart_6456643 baseEnd_6456643 := by
    simpa [prefixWord, tailWord_6456643, baseEnd_6456643] using wordTrace_append hprefix tailTrace_6456643
  have hstable : (prefixWord ++ tailWord_6456643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456643).length < 2 ^ (prefixWord ++ tailWord_6456643).sum := by decide
  have hdescent : baseEnd_6456643 < baseStart_6456643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456647 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_6456647 : Nat := 118140960795 + 6456647 * 2 ^ 59
def prefixEnd_6456647 : Nat := 4983230072969 + 3 ^ 40 * 6456647 * 2
def baseEnd_6456647 : Nat := 3315363327410305072618927

theorem tailTrace_6456647 : CollatzResearch.WordTrace tailWord_6456647 prefixEnd_6456647 3315363327410305072618927 := by
  unfold tailWord_6456647
  simp only [CollatzResearch.WordTrace]
  refine ⟨235493262639678101361680195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156995508426452067574453463 235493262639678101361680195)
  ·
    refine ⟨353239893959517152042520293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235493262639678101361680195 353239893959517152042520293)
    ·
      refine ⟨66232480117409466007972555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353239893959517152042520293 66232480117409466007972555)
      ·
        refine ⟨99348720176114199011958833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66232480117409466007972555 99348720176114199011958833)
        ·
          refine ⟨74511540132085649258969125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99348720176114199011958833 74511540132085649258969125)
          ·
            refine ⟨13970913774766059236056711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74511540132085649258969125 13970913774766059236056711)
            ·
              refine ⟨20956370662149088854085067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13970913774766059236056711 20956370662149088854085067)
              ·
                refine ⟨31434555993223633281127601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20956370662149088854085067 31434555993223633281127601)
                ·
                  refine ⟨23575916994917724960845701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31434555993223633281127601 23575916994917724960845701)
                  ·
                    refine ⟨4420484436547073430158569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23575916994917724960845701 4420484436547073430158569)
                    ·
                      refine ⟨3315363327410305072618927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420484436547073430158569 3315363327410305072618927)
                      ·
                        rfl

theorem cell23_6456647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_6456647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456647 prefixEnd_6456647 := by exact prefixLift 6456647
  have htrace : WordTrace (prefixWord ++ tailWord_6456647) baseStart_6456647 baseEnd_6456647 := by
    simpa [prefixWord, tailWord_6456647, baseEnd_6456647] using wordTrace_append hprefix tailTrace_6456647
  have hstable : (prefixWord ++ tailWord_6456647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456647).length < 2 ^ (prefixWord ++ tailWord_6456647).sum := by decide
  have hdescent : baseEnd_6456647 < baseStart_6456647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456650 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_6456650 : Nat := 118140960795 + 6456650 * 2 ^ 59
def prefixEnd_6456650 : Nat := 4983230072969 + 3 ^ 40 * 6456650 * 2
def baseEnd_6456650 : Nat := 3315364867852268560881413

theorem tailTrace_6456650 : CollatzResearch.WordTrace tailWord_6456650 prefixEnd_6456650 3315364867852268560881413 := by
  unfold tailWord_6456650
  simp only [CollatzResearch.WordTrace]
  refine ⟨58873343014666808218509851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156995581372444821916026269 58873343014666808218509851)
  ·
    refine ⟨88310014522000212327764777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58873343014666808218509851 88310014522000212327764777)
    ·
      refine ⟨66232510891500159245823583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88310014522000212327764777 66232510891500159245823583)
      ·
        refine ⟨99348766337250238868735375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66232510891500159245823583 99348766337250238868735375)
        ·
          refine ⟨149023149505875358303103063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99348766337250238868735375 149023149505875358303103063)
          ·
            refine ⟨223534724258813037454654595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149023149505875358303103063 223534724258813037454654595)
            ·
              refine ⟨335302086388219556181981893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223534724258813037454654595 335302086388219556181981893)
              ·
                refine ⟨62869141197791166784121605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335302086388219556181981893 62869141197791166784121605)
                ·
                  refine ⟨11787963974585843772022801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62869141197791166784121605 11787963974585843772022801)
                  ·
                    refine ⟨8840972980939382829017101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11787963974585843772022801 8840972980939382829017101)
                    ·
                      refine ⟨3315364867852268560881413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8840972980939382829017101 3315364867852268560881413)
                      ·
                        rfl

theorem cell23_6456650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_6456650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456650 prefixEnd_6456650 := by exact prefixLift 6456650
  have htrace : WordTrace (prefixWord ++ tailWord_6456650) baseStart_6456650 baseEnd_6456650 := by
    simpa [prefixWord, tailWord_6456650, baseEnd_6456650] using wordTrace_append hprefix tailTrace_6456650
  have hstable : (prefixWord ++ tailWord_6456650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456650).length < 2 ^ (prefixWord ++ tailWord_6456650).sum := by decide
  have hdescent : baseEnd_6456650 < baseStart_6456650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456673 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_6456673 : Nat := 118140960795 + 6456673 * 2 ^ 59
def prefixEnd_6456673 : Nat := 4983230072969 + 3 ^ 40 * 6456673 * 2
def baseEnd_6456673 : Nat := 3315376677907321970893807

theorem tailTrace_6456673 : CollatzResearch.WordTrace tailWord_6456673 prefixEnd_6456673 3315376677907321970893807 := by
  unfold tailWord_6456673
  simp only [CollatzResearch.WordTrace]
  refine ⟨235494210937583907802126673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156996140625055938534751115 235494210937583907802126673)
  ·
    refine ⟨176620658203187930851595005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235494210937583907802126673 176620658203187930851595005)
    ·
      refine ⟨66232746826195474069348127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176620658203187930851595005 66232746826195474069348127)
      ·
        refine ⟨99349120239293211104022191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66232746826195474069348127 99349120239293211104022191)
        ·
          refine ⟨149023680358939816656033287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99349120239293211104022191 149023680358939816656033287)
          ·
            refine ⟨223535520538409724984049931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149023680358939816656033287 223535520538409724984049931)
            ·
              refine ⟨335303280807614587476074897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223535520538409724984049931 335303280807614587476074897)
              ·
                refine ⟨251477460605710940607056173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335303280807614587476074897 251477460605710940607056173)
                ·
                  refine ⟨94304047727141602727646065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251477460605710940607056173 94304047727141602727646065)
                  ·
                    refine ⟨70728035795356202045734549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94304047727141602727646065 70728035795356202045734549)
                    ·
                      refine ⟨3315376677907321970893807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70728035795356202045734549 3315376677907321970893807)
                      ·
                        rfl

theorem cell23_6456673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_6456673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456673 prefixEnd_6456673 := by exact prefixLift 6456673
  have htrace : WordTrace (prefixWord ++ tailWord_6456673) baseStart_6456673 baseEnd_6456673 := by
    simpa [prefixWord, tailWord_6456673, baseEnd_6456673] using wordTrace_append hprefix tailTrace_6456673
  have hstable : (prefixWord ++ tailWord_6456673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456673).length < 2 ^ (prefixWord ++ tailWord_6456673).sum := by decide
  have hdescent : baseEnd_6456673 < baseStart_6456673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456697 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 3]
def baseStart_6456697 : Nat := 118140960795 + 6456697 * 2 ^ 59
def prefixEnd_6456697 : Nat := 4983230072969 + 3 ^ 40 * 6456697 * 2
def baseEnd_6456697 : Nat := 3315389001443029876993697

theorem tailTrace_6456697 : CollatzResearch.WordTrace tailWord_6456697 prefixEnd_6456697 3315389001443029876993697 := by
  unfold tailWord_6456697
  simp only [CollatzResearch.WordTrace]
  refine ⟨235495086289496959901000345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156996724192997973267333563 235495086289496959901000345)
  ·
    refine ⟨176621314717122719925750259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235495086289496959901000345 176621314717122719925750259)
    ·
      refine ⟨264931972075684079888625389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176621314717122719925750259 264931972075684079888625389)
      ·
        refine ⟨99349489528381529958234521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264931972075684079888625389 99349489528381529958234521)
        ·
          refine ⟨74512117146286147468675891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99349489528381529958234521 74512117146286147468675891)
          ·
            refine ⟨111768175719429221203013837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74512117146286147468675891 111768175719429221203013837)
            ·
              refine ⟨41913065894785957951130189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111768175719429221203013837 41913065894785957951130189)
              ·
                refine ⟨15717399710544734231673821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41913065894785957951130189 15717399710544734231673821)
                ·
                  refine ⟨5894024891454275336877683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15717399710544734231673821 5894024891454275336877683)
                  ·
                    refine ⟨8841037337181413005316525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894024891454275336877683 8841037337181413005316525)
                    ·
                      refine ⟨3315389001443029876993697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841037337181413005316525 3315389001443029876993697)
                      ·
                        rfl

theorem cell23_6456697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_6456697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456697 prefixEnd_6456697 := by exact prefixLift 6456697
  have htrace : WordTrace (prefixWord ++ tailWord_6456697) baseStart_6456697 baseEnd_6456697 := by
    simpa [prefixWord, tailWord_6456697, baseEnd_6456697] using wordTrace_append hprefix tailTrace_6456697
  have hstable : (prefixWord ++ tailWord_6456697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456697).length < 2 ^ (prefixWord ++ tailWord_6456697).sum := by decide
  have hdescent : baseEnd_6456697 < baseStart_6456697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456707 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 1, 5, 2]
def baseStart_6456707 : Nat := 118140960795 + 6456707 * 2 ^ 59
def prefixEnd_6456707 : Nat := 4983230072969 + 3 ^ 40 * 6456707 * 2
def baseEnd_6456707 : Nat := 3315394136249574837868651

theorem tailTrace_6456707 : CollatzResearch.WordTrace tailWord_6456707 prefixEnd_6456707 3315394136249574837868651 := by
  unfold tailWord_6456707
  simp only [CollatzResearch.WordTrace]
  refine ⟨235495451019460731608864375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156996967346307154405909583 235495451019460731608864375)
  ·
    refine ⟨353243176529191097413296563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235495451019460731608864375 353243176529191097413296563)
    ·
      refine ⟨529864764793786646119944845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353243176529191097413296563 529864764793786646119944845)
      ·
        refine ⟨198699286797669992294979317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 529864764793786646119944845 198699286797669992294979317)
        ·
          refine ⟨18628058137281561777654311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198699286797669992294979317 18628058137281561777654311)
          ·
            refine ⟨27942087205922342666481467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18628058137281561777654311 27942087205922342666481467)
            ·
              refine ⟨41913130808883513999722201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27942087205922342666481467 41913130808883513999722201)
              ·
                refine ⟨31434848106662635499791651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41913130808883513999722201 31434848106662635499791651)
                ·
                  refine ⟨47152272159993953249687477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31434848106662635499791651 47152272159993953249687477)
                  ·
                    refine ⟨4420525514999433117158201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47152272159993953249687477 4420525514999433117158201)
                    ·
                      refine ⟨3315394136249574837868651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420525514999433117158201 3315394136249574837868651)
                      ·
                        rfl

theorem cell23_6456707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_6456707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456707 prefixEnd_6456707 := by exact prefixLift 6456707
  have htrace : WordTrace (prefixWord ++ tailWord_6456707) baseStart_6456707 baseEnd_6456707 := by
    simpa [prefixWord, tailWord_6456707, baseEnd_6456707] using wordTrace_append hprefix tailTrace_6456707
  have hstable : (prefixWord ++ tailWord_6456707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456707).length < 2 ^ (prefixWord ++ tailWord_6456707).sum := by decide
  have hdescent : baseEnd_6456707 < baseStart_6456707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456724 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_6456724 : Nat := 118140960795 + 6456724 * 2 ^ 59
def prefixEnd_6456724 : Nat := 4983230072969 + 3 ^ 40 * 6456724 * 2
def baseEnd_6456724 : Nat := 3315402865420701271356073

theorem tailTrace_6456724 : CollatzResearch.WordTrace tailWord_6456724 prefixEnd_6456724 3315402865420701271356073 := by
  unfold tailWord_6456724
  simp only [CollatzResearch.WordTrace]
  refine ⟨117748035530199571756116613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156997380706932762341488817 117748035530199571756116613)
  ·
    refine ⟨22077756661912419704271865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117748035530199571756116613 22077756661912419704271865)
    ·
      refine ⟨16558317496434314778203899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22077756661912419704271865 16558317496434314778203899)
      ·
        refine ⟨24837476244651472167305849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16558317496434314778203899 24837476244651472167305849)
        ·
          refine ⟨18628107183488604125479387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24837476244651472167305849 18628107183488604125479387)
          ·
            refine ⟨27942160775232906188219081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18628107183488604125479387 27942160775232906188219081)
            ·
              refine ⟨20956620581424679641164311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27942160775232906188219081 20956620581424679641164311)
              ·
                refine ⟨31434930872137019461746467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20956620581424679641164311 31434930872137019461746467)
                ·
                  refine ⟨47152396308205529192619701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31434930872137019461746467 47152396308205529192619701)
                  ·
                    refine ⟨4420537153894268361808097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47152396308205529192619701 4420537153894268361808097)
                    ·
                      refine ⟨3315402865420701271356073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420537153894268361808097 3315402865420701271356073)
                      ·
                        rfl

theorem cell23_6456724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_6456724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456724 prefixEnd_6456724 := by exact prefixLift 6456724
  have htrace : WordTrace (prefixWord ++ tailWord_6456724) baseStart_6456724 baseEnd_6456724 := by
    simpa [prefixWord, tailWord_6456724, baseEnd_6456724] using wordTrace_append hprefix tailTrace_6456724
  have hstable : (prefixWord ++ tailWord_6456724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456724).length < 2 ^ (prefixWord ++ tailWord_6456724).sum := by decide
  have hdescent : baseEnd_6456724 < baseStart_6456724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456730 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_6456730 : Nat := 118140960795 + 6456730 * 2 ^ 59
def prefixEnd_6456730 : Nat := 4983230072969 + 3 ^ 40 * 6456730 * 2
def baseEnd_6456730 : Nat := 1105135315434876082627015

theorem tailTrace_6456730 : CollatzResearch.WordTrace tailWord_6456730 prefixEnd_6456730 1105135315434876082627015 := by
  unfold tailWord_6456730
  simp only [CollatzResearch.WordTrace]
  refine ⟨58874072474594351634237911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156997526598918271024634429 58874072474594351634237911)
  ·
    refine ⟨88311108711891527451356867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58874072474594351634237911 88311108711891527451356867)
    ·
      refine ⟨132466663067837291177035301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88311108711891527451356867 132466663067837291177035301)
      ·
        refine ⟨24837499325219492095694119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132466663067837291177035301 24837499325219492095694119)
        ·
          refine ⟨37256248987829238143541179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24837499325219492095694119 37256248987829238143541179)
          ·
            refine ⟨55884373481743857215311769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37256248987829238143541179 55884373481743857215311769)
            ·
              refine ⟨41913280111307892911483827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55884373481743857215311769 41913280111307892911483827)
              ·
                refine ⟨62869920166961839367225741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41913280111307892911483827 62869920166961839367225741)
                ·
                  refine ⟨23576220062610689762709653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62869920166961839367225741 23576220062610689762709653)
                  ·
                    refine ⟨1105135315434876082627015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23576220062610689762709653 1105135315434876082627015)
                    ·
                      rfl

theorem cell23_6456730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_6456730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456730 prefixEnd_6456730 := by exact prefixLift 6456730
  have htrace : WordTrace (prefixWord ++ tailWord_6456730) baseStart_6456730 baseEnd_6456730 := by
    simpa [prefixWord, tailWord_6456730, baseEnd_6456730] using wordTrace_append hprefix tailTrace_6456730
  have hstable : (prefixWord ++ tailWord_6456730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456730).length < 2 ^ (prefixWord ++ tailWord_6456730).sum := by decide
  have hdescent : baseEnd_6456730 < baseStart_6456730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456754 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_6456754 : Nat := 118140960795 + 6456754 * 2 ^ 59
def prefixEnd_6456754 : Nat := 4983230072969 + 3 ^ 40 * 6456754 * 2
def baseEnd_6456754 : Nat := 3315418269840336153980935

theorem tailTrace_6456754 : CollatzResearch.WordTrace tailWord_6456754 prefixEnd_6456754 3315418269840336153980935 := by
  unfold tailWord_6456754
  simp only [CollatzResearch.WordTrace]
  refine ⟨58874291312572614658956329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156998110166860305757216877 58874291312572614658956329)
  ·
    refine ⟨44155718484429460994217247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58874291312572614658956329 44155718484429460994217247)
    ·
      refine ⟨66233577726644191491325871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44155718484429460994217247 66233577726644191491325871)
      ·
        refine ⟨99350366589966287236988807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66233577726644191491325871 99350366589966287236988807)
        ·
          refine ⟨149025549884949430855483211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99350366589966287236988807 149025549884949430855483211)
          ·
            refine ⟨223538324827424146283224817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149025549884949430855483211 223538324827424146283224817)
            ·
              refine ⟨167653743620568109712418613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223538324827424146283224817 167653743620568109712418613)
              ·
                refine ⟨15717538464428260285539245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167653743620568109712418613 15717538464428260285539245)
                ·
                  refine ⟨5894076924160597607077217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15717538464428260285539245 5894076924160597607077217)
                  ·
                    refine ⟨4420557693120448205307913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894076924160597607077217 4420557693120448205307913)
                    ·
                      refine ⟨3315418269840336153980935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420557693120448205307913 3315418269840336153980935)
                      ·
                        rfl

theorem cell23_6456754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_6456754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456754 prefixEnd_6456754 := by exact prefixLift 6456754
  have htrace : WordTrace (prefixWord ++ tailWord_6456754) baseStart_6456754 baseEnd_6456754 := by
    simpa [prefixWord, tailWord_6456754, baseEnd_6456754] using wordTrace_append hprefix tailTrace_6456754
  have hstable : (prefixWord ++ tailWord_6456754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456754).length < 2 ^ (prefixWord ++ tailWord_6456754).sum := by decide
  have hdescent : baseEnd_6456754 < baseStart_6456754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456757 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_6456757 : Nat := 118140960795 + 6456757 * 2 ^ 59
def prefixEnd_6456757 : Nat := 4983230072969 + 3 ^ 40 * 6456757 * 2
def baseEnd_6456757 : Nat := 3315419810282299642243421

theorem tailTrace_6456757 : CollatzResearch.WordTrace tailWord_6456757 prefixEnd_6456757 3315419810282299642243421 := by
  unfold tailWord_6456757
  simp only [CollatzResearch.WordTrace]
  refine ⟨235497274669279590148184525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156998183112853060098789683 235497274669279590148184525)
  ·
    refine ⟨88311478000979846305569197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235497274669279590148184525 88311478000979846305569197)
    ·
      refine ⟨33116804250367442364588449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88311478000979846305569197 33116804250367442364588449)
      ·
        refine ⟨24837603187775581773441337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33116804250367442364588449 24837603187775581773441337)
        ·
          refine ⟨18628202390831686330081003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24837603187775581773441337 18628202390831686330081003)
          ·
            refine ⟨27942303586247529495121505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18628202390831686330081003 27942303586247529495121505)
            ·
              refine ⟨20956727689685647121341129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27942303586247529495121505 20956727689685647121341129)
              ·
                refine ⟨15717545767264235341005847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20956727689685647121341129 15717545767264235341005847)
                ·
                  refine ⟨23576318650896353011508771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15717545767264235341005847 23576318650896353011508771)
                  ·
                    refine ⟨35364477976344529517263157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23576318650896353011508771 35364477976344529517263157)
                    ·
                      refine ⟨3315419810282299642243421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35364477976344529517263157 3315419810282299642243421)
                      ·
                        rfl

theorem cell23_6456757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_6456757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456757 prefixEnd_6456757 := by exact prefixLift 6456757
  have htrace : WordTrace (prefixWord ++ tailWord_6456757) baseStart_6456757 baseEnd_6456757 := by
    simpa [prefixWord, tailWord_6456757, baseEnd_6456757] using wordTrace_append hprefix tailTrace_6456757
  have hstable : (prefixWord ++ tailWord_6456757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456757).length < 2 ^ (prefixWord ++ tailWord_6456757).sum := by decide
  have hdescent : baseEnd_6456757 < baseStart_6456757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456805 : List Nat := [1, 3, 1, 5, 1, 1, 4, 2, 1, 2, 2]
def baseStart_6456805 : Nat := 118140960795 + 6456805 * 2 ^ 59
def prefixEnd_6456805 : Nat := 4983230072969 + 3 ^ 40 * 6456805 * 2
def baseEnd_6456805 : Nat := 3315444457353715454443201

theorem tailTrace_6456805 : CollatzResearch.WordTrace tailWord_6456805 prefixEnd_6456805 3315444457353715454443201 := by
  unfold tailWord_6456805
  simp only [CollatzResearch.WordTrace]
  refine ⟨235499025373105694345931869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156999350248737129563954579 235499025373105694345931869)
  ·
    refine ⟨88312134514914635379724451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235499025373105694345931869 88312134514914635379724451)
    ·
      refine ⟨132468201772371953069586677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88312134514914635379724451 132468201772371953069586677)
      ·
        refine ⟨12418893916159870600273751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132468201772371953069586677 12418893916159870600273751)
        ·
          refine ⟨18628340874239805900410627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12418893916159870600273751 18628340874239805900410627)
          ·
            refine ⟨27942511311359708850615941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18628340874239805900410627 27942511311359708850615941)
            ·
              refine ⟨5239220870879945409490489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27942511311359708850615941 5239220870879945409490489)
              ·
                refine ⟨3929415653159959057117867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239220870879945409490489 3929415653159959057117867)
                ·
                  refine ⟨5894123479739938585676801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929415653159959057117867 5894123479739938585676801)
                  ·
                    refine ⟨4420592609804953939257601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894123479739938585676801 4420592609804953939257601)
                    ·
                      refine ⟨3315444457353715454443201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420592609804953939257601 3315444457353715454443201)
                      ·
                        rfl

theorem cell23_6456805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_6456805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456805 prefixEnd_6456805 := by exact prefixLift 6456805
  have htrace : WordTrace (prefixWord ++ tailWord_6456805) baseStart_6456805 baseEnd_6456805 := by
    simpa [prefixWord, tailWord_6456805, baseEnd_6456805] using wordTrace_append hprefix tailTrace_6456805
  have hstable : (prefixWord ++ tailWord_6456805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456805).length < 2 ^ (prefixWord ++ tailWord_6456805).sum := by decide
  have hdescent : baseEnd_6456805 < baseStart_6456805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456814 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_6456814 : Nat := 118140960795 + 6456814 * 2 ^ 59
def prefixEnd_6456814 : Nat := 4983230072969 + 3 ^ 40 * 6456814 * 2
def baseEnd_6456814 : Nat := 3315449078679605919230659

theorem tailTrace_6456814 : CollatzResearch.WordTrace tailWord_6456814 prefixEnd_6456814 3315449078679605919230659 := by
  unfold tailWord_6456814
  simp only [CollatzResearch.WordTrace]
  refine ⟨29437419203759136110376187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156999569086715392588672997 29437419203759136110376187)
  ·
    refine ⟨44156128805638704165564281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29437419203759136110376187 44156128805638704165564281)
    ·
      refine ⟨33117096604229028124173211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44156128805638704165564281 33117096604229028124173211)
      ·
        refine ⟨49675644906343542186259817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33117096604229028124173211 49675644906343542186259817)
        ·
          refine ⟨37256733679757656639694863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49675644906343542186259817 37256733679757656639694863)
          ·
            refine ⟨55885100519636484959542295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37256733679757656639694863 55885100519636484959542295)
            ·
              refine ⟨83827650779454727439313443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55885100519636484959542295 83827650779454727439313443)
              ·
                refine ⟨125741476169182091158970165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83827650779454727439313443 125741476169182091158970165)
                ·
                  refine ⟨11788263390860821046153453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125741476169182091158970165 11788263390860821046153453)
                  ·
                    refine ⟨4420598771572807892307545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11788263390860821046153453 4420598771572807892307545)
                    ·
                      refine ⟨3315449078679605919230659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420598771572807892307545 3315449078679605919230659)
                      ·
                        rfl

theorem cell23_6456814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_6456814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456814 prefixEnd_6456814 := by exact prefixLift 6456814
  have htrace : WordTrace (prefixWord ++ tailWord_6456814) baseStart_6456814 baseEnd_6456814 := by
    simpa [prefixWord, tailWord_6456814, baseEnd_6456814] using wordTrace_append hprefix tailTrace_6456814
  have hstable : (prefixWord ++ tailWord_6456814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456814).length < 2 ^ (prefixWord ++ tailWord_6456814).sum := by decide
  have hdescent : baseEnd_6456814 < baseStart_6456814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456821 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6456821 : Nat := 118140960795 + 6456821 * 2 ^ 59
def prefixEnd_6456821 : Nat := 4983230072969 + 3 ^ 40 * 6456821 * 2
def baseEnd_6456821 : Nat := 3315452673044187391843127

theorem tailTrace_6456821 : CollatzResearch.WordTrace tailWord_6456821 prefixEnd_6456821 3315452673044187391843127 := by
  unfold tailWord_6456821
  simp only [CollatzResearch.WordTrace]
  refine ⟨235499608941047729078514317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156999739294031819385676211 235499608941047729078514317)
  ·
    refine ⟨88312353352892898404442869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235499608941047729078514317 88312353352892898404442869)
    ·
      refine ⟨8279283126833709225416519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88312353352892898404442869 8279283126833709225416519)
      ·
        refine ⟨12418924690250563838124779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8279283126833709225416519 12418924690250563838124779)
        ·
          refine ⟨18628387035375845757187169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12418924690250563838124779 18628387035375845757187169)
          ·
            refine ⟨13971290276531884317890377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18628387035375845757187169 13971290276531884317890377)
            ·
              refine ⟨10478467707398913238417783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13971290276531884317890377 10478467707398913238417783)
              ·
                refine ⟨15717701561098369857626675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10478467707398913238417783 15717701561098369857626675)
                ·
                  refine ⟨23576552341647554786440013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15717701561098369857626675 23576552341647554786440013)
                  ·
                    refine ⟨8841207128117833044915005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23576552341647554786440013 8841207128117833044915005)
                    ·
                      refine ⟨3315452673044187391843127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841207128117833044915005 3315452673044187391843127)
                      ·
                        rfl

theorem cell23_6456821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6456821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456821 prefixEnd_6456821 := by exact prefixLift 6456821
  have htrace : WordTrace (prefixWord ++ tailWord_6456821) baseStart_6456821 baseEnd_6456821 := by
    simpa [prefixWord, tailWord_6456821, baseEnd_6456821] using wordTrace_append hprefix tailTrace_6456821
  have hstable : (prefixWord ++ tailWord_6456821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456821).length < 2 ^ (prefixWord ++ tailWord_6456821).sum := by decide
  have hdescent : baseEnd_6456821 < baseStart_6456821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456827 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 5, 4, 2]
def baseStart_6456827 : Nat := 118140960795 + 6456827 * 2 ^ 59
def prefixEnd_6456827 : Nat := 4983230072969 + 3 ^ 40 * 6456827 * 2
def baseEnd_6456827 : Nat := 3315455753928114368368099

theorem tailTrace_6456827 : CollatzResearch.WordTrace tailWord_6456827 prefixEnd_6456827 3315455753928114368368099 := by
  unfold tailWord_6456827
  simp only [CollatzResearch.WordTrace]
  refine ⟨235499827779025992103232735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156999885186017328068821823 235499827779025992103232735)
  ·
    refine ⟨353249741668538988154849103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235499827779025992103232735 353249741668538988154849103)
    ·
      refine ⟨529874612502808482232273655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353249741668538988154849103 529874612502808482232273655)
      ·
        refine ⟨794811918754212723348410483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529874612502808482232273655 794811918754212723348410483)
        ·
          refine ⟨1192217878131319085022615725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794811918754212723348410483 1192217878131319085022615725)
          ·
            refine ⟨447081704299244656883480897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1192217878131319085022615725 447081704299244656883480897)
            ·
              refine ⟨335311278224433492662610673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447081704299244656883480897 335311278224433492662610673)
              ·
                refine ⟨251483458668325119496958005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335311278224433492662610673 251483458668325119496958005)
                ·
                  refine ⟨23576574250155479952839813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251483458668325119496958005 23576574250155479952839813)
                  ·
                    refine ⟨4420607671904152491157465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23576574250155479952839813 4420607671904152491157465)
                    ·
                      refine ⟨3315455753928114368368099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420607671904152491157465 3315455753928114368368099)
                      ·
                        rfl

theorem cell23_6456827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 4, 2].length) (baseStart_6456827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456827 prefixEnd_6456827 := by exact prefixLift 6456827
  have htrace : WordTrace (prefixWord ++ tailWord_6456827) baseStart_6456827 baseEnd_6456827 := by
    simpa [prefixWord, tailWord_6456827, baseEnd_6456827] using wordTrace_append hprefix tailTrace_6456827
  have hstable : (prefixWord ++ tailWord_6456827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456827).length < 2 ^ (prefixWord ++ tailWord_6456827).sum := by decide
  have hdescent : baseEnd_6456827 < baseStart_6456827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456861 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_6456861 : Nat := 118140960795 + 6456861 * 2 ^ 59
def prefixEnd_6456861 : Nat := 4983230072969 + 3 ^ 40 * 6456861 * 2
def baseEnd_6456861 : Nat := 3315473212270367235342943

theorem tailTrace_6456861 : CollatzResearch.WordTrace tailWord_6456861 prefixEnd_6456861 3315473212270367235342943 := by
  unfold tailWord_6456861
  simp only [CollatzResearch.WordTrace]
  refine ⟨235501067860902815909970437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157000711907268543939980291 235501067860902815909970437)
  ·
    refine ⟨44156450223919277983119457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235501067860902815909970437 44156450223919277983119457)
    ·
      refine ⟨33117337667939458487339593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44156450223919277983119457 33117337667939458487339593)
      ·
        refine ⟨24838003250954593865504695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33117337667939458487339593 24838003250954593865504695)
        ·
          refine ⟨37257004876431890798257043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24838003250954593865504695 37257004876431890798257043)
          ·
            refine ⟨55885507314647836197385565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37257004876431890798257043 55885507314647836197385565)
            ·
              refine ⟨20957065242992938574019587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55885507314647836197385565 20957065242992938574019587)
              ·
                refine ⟨31435597864489407861029381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20957065242992938574019587 31435597864489407861029381)
                ·
                  refine ⟨5894174599591763973943009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31435597864489407861029381 5894174599591763973943009)
                  ·
                    refine ⟨4420630949693822980457257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894174599591763973943009 4420630949693822980457257)
                    ·
                      refine ⟨3315473212270367235342943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420630949693822980457257 3315473212270367235342943)
                      ·
                        rfl

theorem cell23_6456861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_6456861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456861 prefixEnd_6456861 := by exact prefixLift 6456861
  have htrace : WordTrace (prefixWord ++ tailWord_6456861) baseStart_6456861 baseEnd_6456861 := by
    simpa [prefixWord, tailWord_6456861, baseEnd_6456861] using wordTrace_append hprefix tailTrace_6456861
  have hstable : (prefixWord ++ tailWord_6456861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456861).length < 2 ^ (prefixWord ++ tailWord_6456861).sum := by decide
  have hdescent : baseEnd_6456861 < baseStart_6456861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456878 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_6456878 : Nat := 118140960795 + 6456878 * 2 ^ 59
def prefixEnd_6456878 : Nat := 4983230072969 + 3 ^ 40 * 6456878 * 2
def baseEnd_6456878 : Nat := 3315481941441493668830365

theorem tailTrace_6456878 : CollatzResearch.WordTrace tailWord_6456878 prefixEnd_6456878 3315481941441493668830365 := by
  unfold tailWord_6456878
  simp only [CollatzResearch.WordTrace]
  refine ⟨29437710987730153476667411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157001125267894151875559525 29437710987730153476667411)
  ·
    refine ⟨44156566481595230215001117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29437710987730153476667411 44156566481595230215001117)
    ·
      refine ⟨16558712430598211330625419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44156566481595230215001117 16558712430598211330625419)
      ·
        refine ⟨24838068645897316995938129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16558712430598211330625419 24838068645897316995938129)
        ·
          refine ⟨18628551484422987746953597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24838068645897316995938129 18628551484422987746953597)
          ·
            refine ⟨6985706806658620405107599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18628551484422987746953597 6985706806658620405107599)
            ·
              refine ⟨10478560209987930607661399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6985706806658620405107599 10478560209987930607661399)
              ·
                refine ⟨15717840314981895911492099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10478560209987930607661399 15717840314981895911492099)
                ·
                  refine ⟨23576760472472843867238149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15717840314981895911492099 23576760472472843867238149)
                  ·
                    refine ⟨4420642588588658225107153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23576760472472843867238149 4420642588588658225107153)
                    ·
                      refine ⟨3315481941441493668830365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420642588588658225107153 3315481941441493668830365)
                      ·
                        rfl

theorem cell23_6456878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_6456878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456878 prefixEnd_6456878 := by exact prefixLift 6456878
  have htrace : WordTrace (prefixWord ++ tailWord_6456878) baseStart_6456878 baseEnd_6456878 := by
    simpa [prefixWord, tailWord_6456878, baseEnd_6456878] using wordTrace_append hprefix tailTrace_6456878
  have hstable : (prefixWord ++ tailWord_6456878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456878).length < 2 ^ (prefixWord ++ tailWord_6456878).sum := by decide
  have hdescent : baseEnd_6456878 < baseStart_6456878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456897 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6456897 : Nat := 118140960795 + 6456897 * 2 ^ 59
def prefixEnd_6456897 : Nat := 4983230072969 + 3 ^ 40 * 6456897 * 2
def baseEnd_6456897 : Nat := 1105163899191309698164259

theorem tailTrace_6456897 : CollatzResearch.WordTrace tailWord_6456897 prefixEnd_6456897 1105163899191309698164259 := by
  unfold tailWord_6456897
  simp only [CollatzResearch.WordTrace]
  refine ⟨235502380888772394058280945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157001587259181596038853963 235502380888772394058280945)
  ·
    refine ⟨176626785666579295543710709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235502380888772394058280945 176626785666579295543710709)
    ·
      refine ⟨16558761156241808957222879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176626785666579295543710709 16558761156241808957222879)
      ·
        refine ⟨24838141734362713435834319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16558761156241808957222879 24838141734362713435834319)
        ·
          refine ⟨37257212601544070153751479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24838141734362713435834319 37257212601544070153751479)
          ·
            refine ⟨55885818902316105230627219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37257212601544070153751479 55885818902316105230627219)
            ·
              refine ⟨83828728353474157845940829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55885818902316105230627219 83828728353474157845940829)
              ·
                refine ⟨31435773132552809192227811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83828728353474157845940829 31435773132552809192227811)
                ·
                  refine ⟨47153659698829213788341717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31435773132552809192227811 47153659698829213788341717)
                  ·
                    refine ⟨1105163899191309698164259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47153659698829213788341717 1105163899191309698164259)
                    ·
                      rfl

theorem cell23_6456897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6456897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456897 prefixEnd_6456897 := by exact prefixLift 6456897
  have htrace : WordTrace (prefixWord ++ tailWord_6456897) baseStart_6456897 baseEnd_6456897 := by
    simpa [prefixWord, tailWord_6456897, baseEnd_6456897] using wordTrace_append hprefix tailTrace_6456897
  have hstable : (prefixWord ++ tailWord_6456897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456897).length < 2 ^ (prefixWord ++ tailWord_6456897).sum := by decide
  have hdescent : baseEnd_6456897 < baseStart_6456897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456914 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_6456914 : Nat := 118140960795 + 6456914 * 2 ^ 59
def prefixEnd_6456914 : Nat := 4983230072969 + 3 ^ 40 * 6456914 * 2
def baseEnd_6456914 : Nat := 1105166808915018509326733

theorem tailTrace_6456914 : CollatzResearch.WordTrace tailWord_6456914 prefixEnd_6456914 1105166808915018509326733 := by
  unfold tailWord_6456914
  simp only [CollatzResearch.WordTrace]
  refine ⟨58875750232427701490412449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157002000619807203974433197 58875750232427701490412449)
  ·
    refine ⟨44156812674320776117809337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58875750232427701490412449 44156812674320776117809337)
    ·
      refine ⟨33117609505740582088357003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44156812674320776117809337 33117609505740582088357003)
      ·
        refine ⟨49676414258610873132535505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33117609505740582088357003 49676414258610873132535505)
        ·
          refine ⟨37257310693958154849401629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49676414258610873132535505 37257310693958154849401629)
          ·
            refine ⟨13971491510234308068525611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37257310693958154849401629 13971491510234308068525611)
            ·
              refine ⟨20957237265351462102788417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13971491510234308068525611 20957237265351462102788417)
              ·
                refine ⟨15717927949013596577091313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20957237265351462102788417 15717927949013596577091313)
                ·
                  refine ⟨11788445961760197432818485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15717927949013596577091313 11788445961760197432818485)
                  ·
                    refine ⟨1105166808915018509326733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11788445961760197432818485 1105166808915018509326733)
                    ·
                      rfl

theorem cell23_6456914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_6456914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456914 prefixEnd_6456914 := by exact prefixLift 6456914
  have htrace : WordTrace (prefixWord ++ tailWord_6456914) baseStart_6456914 baseEnd_6456914 := by
    simpa [prefixWord, tailWord_6456914, baseEnd_6456914] using wordTrace_append hprefix tailTrace_6456914
  have hstable : (prefixWord ++ tailWord_6456914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456914).length < 2 ^ (prefixWord ++ tailWord_6456914).sum := by decide
  have hdescent : baseEnd_6456914 < baseStart_6456914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456924 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6456924 : Nat := 118140960795 + 6456924 * 2 ^ 59
def prefixEnd_6456924 : Nat := 4983230072969 + 3 ^ 40 * 6456924 * 2
def baseEnd_6456924 : Nat := 3315505561551600488855153

theorem tailTrace_6456924 : CollatzResearch.WordTrace tailWord_6456924 prefixEnd_6456924 3315505561551600488855153 := by
  unfold tailWord_6456924
  simp only [CollatzResearch.WordTrace]
  refine ⟨117751682829837288834756913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157002243773116385113009217 117751682829837288834756913)
  ·
    refine ⟨88313762122377966626067685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117751682829837288834756913 88313762122377966626067685)
    ·
      refine ⟨16558830397945868742387691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88313762122377966626067685 16558830397945868742387691)
      ·
        refine ⟨24838245596918803113581537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16558830397945868742387691 24838245596918803113581537)
        ·
          refine ⟨18628684197689102335186153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24838245596918803113581537 18628684197689102335186153)
          ·
            refine ⟨13971513148266826751389615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18628684197689102335186153 13971513148266826751389615)
            ·
              refine ⟨20957269722400240127084423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13971513148266826751389615 20957269722400240127084423)
              ·
                refine ⟨31435904583600360190626635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20957269722400240127084423 31435904583600360190626635)
                ·
                  refine ⟨47153856875400540285939953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31435904583600360190626635 47153856875400540285939953)
                  ·
                    refine ⟨35365392656550405214454965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47153856875400540285939953 35365392656550405214454965)
                    ·
                      refine ⟨3315505561551600488855153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35365392656550405214454965 3315505561551600488855153)
                      ·
                        rfl

theorem cell23_6456924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6456924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456924 prefixEnd_6456924 := by exact prefixLift 6456924
  have htrace : WordTrace (prefixWord ++ tailWord_6456924) baseStart_6456924 baseEnd_6456924 := by
    simpa [prefixWord, tailWord_6456924, baseEnd_6456924] using wordTrace_append hprefix tailTrace_6456924
  have hstable : (prefixWord ++ tailWord_6456924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456924).length < 2 ^ (prefixWord ++ tailWord_6456924).sum := by decide
  have hdescent : baseEnd_6456924 < baseStart_6456924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456937 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 3]
def baseStart_6456937 : Nat := 118140960795 + 6456937 * 2 ^ 59
def prefixEnd_6456937 : Nat := 4983230072969 + 3 ^ 40 * 6456937 * 2
def baseEnd_6456937 : Nat := 3315512236800108937992593

theorem tailTrace_6456937 : CollatzResearch.WordTrace tailWord_6456937 prefixEnd_6456937 3315512236800108937992593 := by
  unfold tailWord_6456937
  simp only [CollatzResearch.WordTrace]
  refine ⟨235503839808627480889737065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157002559872418320593158043 235503839808627480889737065)
  ·
    refine ⟨176627879856470610667302799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235503839808627480889737065 176627879856470610667302799)
    ·
      refine ⟨264941819784705916000954199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176627879856470610667302799 264941819784705916000954199)
      ·
        refine ⟨397412729677058874001431299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264941819784705916000954199 397412729677058874001431299)
        ·
          refine ⟨596119094515588311002146949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397412729677058874001431299 596119094515588311002146949)
          ·
            refine ⟨111772330221672808312902553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 596119094515588311002146949 111772330221672808312902553)
            ·
              refine ⟨83829247666254606234676915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111772330221672808312902553 83829247666254606234676915)
              ·
                refine ⟨125743871499381909352015373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83829247666254606234676915 125743871499381909352015373)
                ·
                  refine ⟨47153951812268216007005765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125743871499381909352015373 47153951812268216007005765)
                  ·
                    refine ⟨8841365964800290501313581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47153951812268216007005765 8841365964800290501313581)
                    ·
                      refine ⟨3315512236800108937992593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841365964800290501313581 3315512236800108937992593)
                      ·
                        rfl

theorem cell23_6456937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_6456937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456937 prefixEnd_6456937 := by exact prefixLift 6456937
  have htrace : WordTrace (prefixWord ++ tailWord_6456937) baseStart_6456937 baseEnd_6456937 := by
    simpa [prefixWord, tailWord_6456937, baseEnd_6456937] using wordTrace_append hprefix tailTrace_6456937
  have hstable : (prefixWord ++ tailWord_6456937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456937).length < 2 ^ (prefixWord ++ tailWord_6456937).sum := by decide
  have hdescent : baseEnd_6456937 < baseStart_6456937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6456974 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_6456974 : Nat := 118140960795 + 6456974 * 2 ^ 59
def prefixEnd_6456974 : Nat := 4983230072969 + 3 ^ 40 * 6456974 * 2
def baseEnd_6456974 : Nat := 368392359509369477025547

theorem tailTrace_6456974 : CollatzResearch.WordTrace tailWord_6456974 prefixEnd_6456974 368392359509369477025547 := by
  unfold tailWord_6456974
  simp only [CollatzResearch.WordTrace]
  refine ⟨29438148663686679526104247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157003459539662290805889317 29438148663686679526104247)
  ·
    refine ⟨44157222995530019289156371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29438148663686679526104247 44157222995530019289156371)
    ·
      refine ⟨66235834493295028933734557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44157222995530019289156371 66235834493295028933734557)
      ·
        refine ⟨24838437934985635850150459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66235834493295028933734557 24838437934985635850150459)
        ·
          refine ⟨37257656902478453775225689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24838437934985635850150459 37257656902478453775225689)
          ·
            refine ⟨27943242676858840331419267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37257656902478453775225689 27943242676858840331419267)
            ·
              refine ⟨41914864015288260497128901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27943242676858840331419267 41914864015288260497128901)
              ·
                refine ⟨7859037002866548843211669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41914864015288260497128901 7859037002866548843211669)
                ·
                  refine ⟨368392359509369477025547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7859037002866548843211669 368392359509369477025547)
                  ·
                    rfl

theorem cell23_6456974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_6456974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6456974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6456974 prefixEnd_6456974 := by exact prefixLift 6456974
  have htrace : WordTrace (prefixWord ++ tailWord_6456974) baseStart_6456974 baseEnd_6456974 := by
    simpa [prefixWord, tailWord_6456974, baseEnd_6456974] using wordTrace_append hprefix tailTrace_6456974
  have hstable : (prefixWord ++ tailWord_6456974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6456974).length < 2 ^ (prefixWord ++ tailWord_6456974).sum := by decide
  have hdescent : baseEnd_6456974 < baseStart_6456974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6456974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457018 : List Nat := [3, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3]
def baseStart_6457018 : Nat := 118140960795 + 6457018 * 2 ^ 59
def prefixEnd_6457018 : Nat := 4983230072969 + 3 ^ 40 * 6457018 * 2
def baseEnd_6457018 : Nat := 3315553828733123121079721

theorem tailTrace_6457018 : CollatzResearch.WordTrace tailWord_6457018 prefixEnd_6457018 3315553828733123121079721 := by
  unfold tailWord_6457018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58876698530333507930858927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157004529414222687815623805 58876698530333507930858927)
  ·
    refine ⟨88315047795500261896288391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58876698530333507930858927 88315047795500261896288391)
    ·
      refine ⟨132472571693250392844432587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88315047795500261896288391 132472571693250392844432587)
      ·
        refine ⟨198708857539875589266648881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132472571693250392844432587 198708857539875589266648881)
        ·
          refine ⟨149031643154906691949986661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198708857539875589266648881 149031643154906691949986661)
          ·
            refine ⟨27943433091545004740622499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149031643154906691949986661 27943433091545004740622499)
            ·
              refine ⟨41915149637317507110933749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27943433091545004740622499 41915149637317507110933749)
              ·
                refine ⟨3929545278498516291650039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41915149637317507110933749 3929545278498516291650039)
                ·
                  refine ⟨5894317917747774437475059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929545278498516291650039 5894317917747774437475059)
                  ·
                    refine ⟨8841476876621661656212589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894317917747774437475059 8841476876621661656212589)
                    ·
                      refine ⟨3315553828733123121079721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841476876621661656212589 3315553828733123121079721)
                      ·
                        rfl

theorem cell23_6457018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_6457018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457018 prefixEnd_6457018 := by exact prefixLift 6457018
  have htrace : WordTrace (prefixWord ++ tailWord_6457018) baseStart_6457018 baseEnd_6457018 := by
    simpa [prefixWord, tailWord_6457018, baseEnd_6457018] using wordTrace_append hprefix tailTrace_6457018
  have hstable : (prefixWord ++ tailWord_6457018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457018).length < 2 ^ (prefixWord ++ tailWord_6457018).sum := by decide
  have hdescent : baseEnd_6457018 < baseStart_6457018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457027 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5]
def baseStart_6457027 : Nat := 118140960795 + 6457027 * 2 ^ 59
def prefixEnd_6457027 : Nat := 4983230072969 + 3 ^ 40 * 6457027 * 2
def baseEnd_6457027 : Nat := 3315558450059013585867179

theorem tailTrace_6457027 : CollatzResearch.WordTrace tailWord_6457027 prefixEnd_6457027 3315558450059013585867179 := by
  unfold tailWord_6457027
  simp only [CollatzResearch.WordTrace]
  refine ⟨235507122378301426260513335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157004748252200950840342223 235507122378301426260513335)
  ·
    refine ⟨353260683567452139390770003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235507122378301426260513335 353260683567452139390770003)
    ·
      refine ⟨529891025351178209086155005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353260683567452139390770003 529891025351178209086155005)
      ·
        refine ⟨198709134506691828407308127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 529891025351178209086155005 198709134506691828407308127)
        ·
          refine ⟨298063701760037742610962191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198709134506691828407308127 298063701760037742610962191)
          ·
            refine ⟨447095552640056613916443287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298063701760037742610962191 447095552640056613916443287)
            ·
              refine ⟨670643328960084920874664931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447095552640056613916443287 670643328960084920874664931)
              ·
                refine ⟨1005964993440127381311997397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670643328960084920874664931 1005964993440127381311997397)
                ·
                  refine ⟨23577304533752985499499939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1005964993440127381311997397 23577304533752985499499939)
                  ·
                    refine ⟨35365956800629478249249909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23577304533752985499499939 35365956800629478249249909)
                    ·
                      refine ⟨3315558450059013585867179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35365956800629478249249909 3315558450059013585867179)
                      ·
                        rfl

theorem cell23_6457027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_6457027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457027 prefixEnd_6457027 := by exact prefixLift 6457027
  have htrace : WordTrace (prefixWord ++ tailWord_6457027) baseStart_6457027 baseEnd_6457027 := by
    simpa [prefixWord, tailWord_6457027, baseEnd_6457027] using wordTrace_append hprefix tailTrace_6457027
  have hstable : (prefixWord ++ tailWord_6457027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457027).length < 2 ^ (prefixWord ++ tailWord_6457027).sum := by decide
  have hdescent : baseEnd_6457027 < baseStart_6457027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457047 : List Nat := [1, 1, 3, 2, 1, 3, 2, 10]
def baseStart_6457047 : Nat := 118140960795 + 6457047 * 2 ^ 59
def prefixEnd_6457047 : Nat := 4983230072969 + 3 ^ 40 * 6457047 * 2
def baseEnd_6457047 : Nat := 122798841469337166948781

theorem tailTrace_6457047 : CollatzResearch.WordTrace tailWord_6457047 prefixEnd_6457047 122798841469337166948781 := by
  unfold tailWord_6457047
  simp only [CollatzResearch.WordTrace]
  refine ⟨235507851838228969676241395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157005234558819313117494263 235507851838228969676241395)
  ·
    refine ⟨353261777757343454514362093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235507851838228969676241395 353261777757343454514362093)
    ·
      refine ⟨132473166659003795442885785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353261777757343454514362093 132473166659003795442885785)
      ·
        refine ⟨99354874994252846582164339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132473166659003795442885785 99354874994252846582164339)
        ·
          refine ⟨149032312491379269873246509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99354874994252846582164339 149032312491379269873246509)
          ·
            refine ⟨55887117184267226202467441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149032312491379269873246509 55887117184267226202467441)
            ·
              refine ⟨41915337888200419651850581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55887117184267226202467441 41915337888200419651850581)
              ·
                refine ⟨122798841469337166948781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41915337888200419651850581 122798841469337166948781)
                ·
                  rfl

theorem cell23_6457047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 10].length) (baseStart_6457047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457047 prefixEnd_6457047 := by exact prefixLift 6457047
  have htrace : WordTrace (prefixWord ++ tailWord_6457047) baseStart_6457047 baseEnd_6457047 := by
    simpa [prefixWord, tailWord_6457047, baseEnd_6457047] using wordTrace_append hprefix tailTrace_6457047
  have hstable : (prefixWord ++ tailWord_6457047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457047).length < 2 ^ (prefixWord ++ tailWord_6457047).sum := by decide
  have hdescent : baseEnd_6457047 < baseStart_6457047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457064 : List Nat := [2, 1, 4, 1, 3, 2, 1, 9]
def baseStart_6457064 : Nat := 118140960795 + 6457064 * 2 ^ 59
def prefixEnd_6457064 : Nat := 4983230072969 + 3 ^ 40 * 6457064 * 2
def baseEnd_6457064 : Nat := 122799164771971479300167

theorem tailTrace_6457064 : CollatzResearch.WordTrace tailWord_6457064 prefixEnd_6457064 122799164771971479300167 := by
  unfold tailWord_6457064
  simp only [CollatzResearch.WordTrace]
  refine ⟨117754235939583690789805123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157005647919444921053073497 117754235939583690789805123)
  ·
    refine ⟨176631353909375536184707685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117754235939583690789805123 176631353909375536184707685)
    ·
      refine ⟨33118378858007913034632691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176631353909375536184707685 33118378858007913034632691)
      ·
        refine ⟨49677568287011869551949037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33118378858007913034632691 49677568287011869551949037)
        ·
          refine ⟨18629088107629451081980889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49677568287011869551949037 18629088107629451081980889)
          ·
            refine ⟨13971816080722088311485667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18629088107629451081980889 13971816080722088311485667)
            ·
              refine ⟨20957724121083132467228501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13971816080722088311485667 20957724121083132467228501)
              ·
                refine ⟨122799164771971479300167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20957724121083132467228501 122799164771971479300167)
                ·
                  rfl

theorem cell23_6457064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 9].length) (baseStart_6457064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457064 prefixEnd_6457064 := by exact prefixLift 6457064
  have htrace : WordTrace (prefixWord ++ tailWord_6457064) baseStart_6457064 baseEnd_6457064 := by
    simpa [prefixWord, tailWord_6457064, baseEnd_6457064] using wordTrace_append hprefix tailTrace_6457064
  have hstable : (prefixWord ++ tailWord_6457064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457064).length < 2 ^ (prefixWord ++ tailWord_6457064).sum := by decide
  have hdescent : baseEnd_6457064 < baseStart_6457064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457075 : List Nat := [1, 1, 1, 2, 2, 3, 5, 3, 1, 2, 2]
def baseStart_6457075 : Nat := 118140960795 + 6457075 * 2 ^ 59
def prefixEnd_6457075 : Nat := 4983230072969 + 3 ^ 40 * 6457075 * 2
def baseEnd_6457075 : Nat := 3315583097130429398066959

theorem tailTrace_6457075 : CollatzResearch.WordTrace tailWord_6457075 prefixEnd_6457075 3315583097130429398066959 := by
  unfold tailWord_6457075
  simp only [CollatzResearch.WordTrace]
  refine ⟨235508873082127530458260679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157005915388085020305507119 235508873082127530458260679)
  ·
    refine ⟨353263309623191295687391019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235508873082127530458260679 353263309623191295687391019)
    ·
      refine ⟨529894964434786943531086529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353263309623191295687391019 529894964434786943531086529)
      ·
        refine ⟨397421223326090207648314897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529894964434786943531086529 397421223326090207648314897)
        ·
          refine ⟨298065917494567655736236173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397421223326090207648314897 298065917494567655736236173)
          ·
            refine ⟨111774719060462870901088565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298065917494567655736236173 111774719060462870901088565)
            ·
              refine ⟨10478879911918394146977053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111774719060462870901088565 10478879911918394146977053)
              ·
                refine ⟨3929579966969397805116395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10478879911918394146977053 3929579966969397805116395)
                ·
                  refine ⟨5894369950454096707674593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929579966969397805116395 5894369950454096707674593)
                  ·
                    refine ⟨4420777462840572530755945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894369950454096707674593 4420777462840572530755945)
                    ·
                      refine ⟨3315583097130429398066959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420777462840572530755945 3315583097130429398066959)
                      ·
                        rfl

theorem cell23_6457075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 2, 2].length) (baseStart_6457075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457075 prefixEnd_6457075 := by exact prefixLift 6457075
  have htrace : WordTrace (prefixWord ++ tailWord_6457075) baseStart_6457075 baseEnd_6457075 := by
    simpa [prefixWord, tailWord_6457075, baseEnd_6457075] using wordTrace_append hprefix tailTrace_6457075
  have hstable : (prefixWord ++ tailWord_6457075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457075).length < 2 ^ (prefixWord ++ tailWord_6457075).sum := by decide
  have hdescent : baseEnd_6457075 < baseStart_6457075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457078 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_6457078 : Nat := 118140960795 + 6457078 * 2 ^ 59
def prefixEnd_6457078 : Nat := 4983230072969 + 3 ^ 40 * 6457078 * 2
def baseEnd_6457078 : Nat := 3315584637572392886329445

theorem tailTrace_6457078 : CollatzResearch.WordTrace tailWord_6457078 prefixEnd_6457078 3315584637572392886329445 := by
  unfold tailWord_6457078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719311406319791373163743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157005988334077774647079925 14719311406319791373163743)
  ·
    refine ⟨22078967109479687059745615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14719311406319791373163743 22078967109479687059745615)
    ·
      refine ⟨33118450664219530589618423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22078967109479687059745615 33118450664219530589618423)
      ·
        refine ⟨49677675996329295884427635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33118450664219530589618423 49677675996329295884427635)
        ·
          refine ⟨74516513994493943826641453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49677675996329295884427635 74516513994493943826641453)
          ·
            refine ⟨27943692747935228934990545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74516513994493943826641453 27943692747935228934990545)
            ·
              refine ⟨20957769560951421701242909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27943692747935228934990545 20957769560951421701242909)
              ·
                refine ⟨7859163585356783137966091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20957769560951421701242909 7859163585356783137966091)
                ·
                  refine ⟨11788745378035174706949137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7859163585356783137966091 11788745378035174706949137)
                  ·
                    refine ⟨8841559033526381030211853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11788745378035174706949137 8841559033526381030211853)
                    ·
                      refine ⟨3315584637572392886329445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841559033526381030211853 3315584637572392886329445)
                      ·
                        rfl

theorem cell23_6457078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_6457078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457078 prefixEnd_6457078 := by exact prefixLift 6457078
  have htrace : WordTrace (prefixWord ++ tailWord_6457078) baseStart_6457078 baseEnd_6457078 := by
    simpa [prefixWord, tailWord_6457078, baseEnd_6457078] using wordTrace_append hprefix tailTrace_6457078
  have hstable : (prefixWord ++ tailWord_6457078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457078).length < 2 ^ (prefixWord ++ tailWord_6457078).sum := by decide
  have hdescent : baseEnd_6457078 < baseStart_6457078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457091 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 3]
def baseStart_6457091 : Nat := 118140960795 + 6457091 * 2 ^ 59
def prefixEnd_6457091 : Nat := 4983230072969 + 3 ^ 40 * 6457091 * 2
def baseEnd_6457091 : Nat := 3315591312820901335466885

theorem tailTrace_6457091 : CollatzResearch.WordTrace tailWord_6457091 prefixEnd_6457091 3315591312820901335466885 := by
  unfold tailWord_6457091
  simp only [CollatzResearch.WordTrace]
  refine ⟨235509456650069565190843127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157006304433379710127228751 235509456650069565190843127)
  ·
    refine ⟨353264184975104347786264691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235509456650069565190843127 353264184975104347786264691)
    ·
      refine ⟨529896277462656521679397037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353264184975104347786264691 529896277462656521679397037)
      ·
        refine ⟨198711104048496195629773889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 529896277462656521679397037 198711104048496195629773889)
        ·
          refine ⟨149033328036372146722330417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198711104048496195629773889 149033328036372146722330417)
          ·
            refine ⟨111774996027279110041747813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149033328036372146722330417 111774996027279110041747813)
            ·
              refine ⟨20957811755114833132827715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111774996027279110041747813 20957811755114833132827715)
              ·
                refine ⟨31436717632672249699241573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20957811755114833132827715 31436717632672249699241573)
                ·
                  refine ⟨5894384556126046818607795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31436717632672249699241573 5894384556126046818607795)
                  ·
                    refine ⟨8841576834189070227911693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894384556126046818607795 8841576834189070227911693)
                    ·
                      refine ⟨3315591312820901335466885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841576834189070227911693 3315591312820901335466885)
                      ·
                        rfl

theorem cell23_6457091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_6457091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457091 prefixEnd_6457091 := by exact prefixLift 6457091
  have htrace : WordTrace (prefixWord ++ tailWord_6457091) baseStart_6457091 baseEnd_6457091 := by
    simpa [prefixWord, tailWord_6457091, baseEnd_6457091] using wordTrace_append hprefix tailTrace_6457091
  have hstable : (prefixWord ++ tailWord_6457091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457091).length < 2 ^ (prefixWord ++ tailWord_6457091).sum := by decide
  have hdescent : baseEnd_6457091 < baseStart_6457091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457142 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6457142 : Nat := 118140960795 + 6457142 * 2 ^ 59
def prefixEnd_6457142 : Nat := 4983230072969 + 3 ^ 40 * 6457142 * 2
def baseEnd_6457142 : Nat := 3315617500334280635929151

theorem tailTrace_6457142 : CollatzResearch.WordTrace tailWord_6457142 prefixEnd_6457142 3315617500334280635929151 := by
  unfold tailWord_6457142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719457298305300056309355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157007544515256533933966453 14719457298305300056309355)
  ·
    refine ⟨22079185947457950084464033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14719457298305300056309355 22079185947457950084464033)
    ·
      refine ⟨16559389460593462563348025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22079185947457950084464033 16559389460593462563348025)
      ·
        refine ⟨12419542095445096922511019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16559389460593462563348025 12419542095445096922511019)
        ·
          refine ⟨18629313143167645383766529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419542095445096922511019 18629313143167645383766529)
          ·
            refine ⟨13971984857375734037824897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18629313143167645383766529 13971984857375734037824897)
            ·
              refine ⟨10478988643031800528368673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13971984857375734037824897 10478988643031800528368673)
              ·
                refine ⟨7859241482273850396276505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10478988643031800528368673 7859241482273850396276505)
                ·
                  refine ⟨5894431111705387797207379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7859241482273850396276505 5894431111705387797207379)
                  ·
                    refine ⟨8841646667558081695811069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894431111705387797207379 8841646667558081695811069)
                    ·
                      refine ⟨3315617500334280635929151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841646667558081695811069 3315617500334280635929151)
                      ·
                        rfl

theorem cell23_6457142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6457142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457142 prefixEnd_6457142 := by exact prefixLift 6457142
  have htrace : WordTrace (prefixWord ++ tailWord_6457142) baseStart_6457142 baseEnd_6457142 := by
    simpa [prefixWord, tailWord_6457142, baseEnd_6457142] using wordTrace_append hprefix tailTrace_6457142
  have hstable : (prefixWord ++ tailWord_6457142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457142).length < 2 ^ (prefixWord ++ tailWord_6457142).sum := by decide
  have hdescent : baseEnd_6457142 < baseStart_6457142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457148 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_6457148 : Nat := 118140960795 + 6457148 * 2 ^ 59
def prefixEnd_6457148 : Nat := 4983230072969 + 3 ^ 40 * 6457148 * 2
def baseEnd_6457148 : Nat := 3315620581218207612454123

theorem tailTrace_6457148 : CollatzResearch.WordTrace tailWord_6457148 prefixEnd_6457148 3315620581218207612454123 := by
  unfold tailWord_6457148
  simp only [CollatzResearch.WordTrace]
  refine ⟨117755767805431531962834049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157007690407242042617112065 117755767805431531962834049)
  ·
    refine ⟨88316825854073648972125537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117755767805431531962834049 88316825854073648972125537)
    ·
      refine ⟨66237619390555236729094153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88316825854073648972125537 66237619390555236729094153)
      ·
        refine ⟨49678214542916427546820615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66237619390555236729094153 49678214542916427546820615)
        ·
          refine ⟨74517321814374641320230923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49678214542916427546820615 74517321814374641320230923)
          ·
            refine ⟨111775982721561961980346385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74517321814374641320230923 111775982721561961980346385)
            ·
              refine ⟨83831987041171471485259789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111775982721561961980346385 83831987041171471485259789)
              ·
                refine ⟨31436995140439301806972421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83831987041171471485259789 31436995140439301806972421)
                ·
                  refine ⟨5894436588832369088807329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31436995140439301806972421 5894436588832369088807329)
                  ·
                    refine ⟨4420827441624276816605497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894436588832369088807329 4420827441624276816605497)
                    ·
                      refine ⟨3315620581218207612454123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420827441624276816605497 3315620581218207612454123)
                      ·
                        rfl

theorem cell23_6457148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_6457148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457148 prefixEnd_6457148 := by exact prefixLift 6457148
  have htrace : WordTrace (prefixWord ++ tailWord_6457148) baseStart_6457148 baseEnd_6457148 := by
    simpa [prefixWord, tailWord_6457148, baseEnd_6457148] using wordTrace_append hprefix tailTrace_6457148
  have hstable : (prefixWord ++ tailWord_6457148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457148).length < 2 ^ (prefixWord ++ tailWord_6457148).sum := by decide
  have hdescent : baseEnd_6457148 < baseStart_6457148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457158 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_6457158 : Nat := 118140960795 + 6457158 * 2 ^ 59
def prefixEnd_6457158 : Nat := 4983230072969 + 3 ^ 40 * 6457158 * 2
def baseEnd_6457158 : Nat := 1105208572008250857776359

theorem tailTrace_6457158 : CollatzResearch.WordTrace tailWord_6457158 prefixEnd_6457158 1105208572008250857776359 := by
  unfold tailWord_6457158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7359746885650838613547879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157007933560551223755688085 7359746885650838613547879)
  ·
    refine ⟨11039620328476257920321819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7359746885650838613547879 11039620328476257920321819)
    ·
      refine ⟨16559430492714386880482729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11039620328476257920321819 16559430492714386880482729)
      ·
        refine ⟨12419572869535790160362047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16559430492714386880482729 12419572869535790160362047)
        ·
          refine ⟨18629359304303685240543071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419572869535790160362047 18629359304303685240543071)
          ·
            refine ⟨27944038956455527860814607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18629359304303685240543071 27944038956455527860814607)
            ·
              refine ⟨41916058434683291791221911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27944038956455527860814607 41916058434683291791221911)
              ·
                refine ⟨62874087652024937686832867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41916058434683291791221911 62874087652024937686832867)
                ·
                  refine ⟨94311131478037406530249301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62874087652024937686832867 94311131478037406530249301)
                  ·
                    refine ⟨1105208572008250857776359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94311131478037406530249301 1105208572008250857776359)
                    ·
                      rfl

theorem cell23_6457158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_6457158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457158 prefixEnd_6457158 := by exact prefixLift 6457158
  have htrace : WordTrace (prefixWord ++ tailWord_6457158) baseStart_6457158 baseEnd_6457158 := by
    simpa [prefixWord, tailWord_6457158, baseEnd_6457158] using wordTrace_append hprefix tailTrace_6457158
  have hstable : (prefixWord ++ tailWord_6457158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457158).length < 2 ^ (prefixWord ++ tailWord_6457158).sum := by decide
  have hdescent : baseEnd_6457158 < baseStart_6457158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457165 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6457165 : Nat := 118140960795 + 6457165 * 2 ^ 59
def prefixEnd_6457165 : Nat := 4983230072969 + 3 ^ 40 * 6457165 * 2
def baseEnd_6457165 : Nat := 3315629310389334045941545

theorem tailTrace_6457165 : CollatzResearch.WordTrace tailWord_6457165 prefixEnd_6457165 3315629310389334045941545 := by
  unfold tailWord_6457165
  simp only [CollatzResearch.WordTrace]
  refine ⟨235512155651801475829036949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157008103767867650552691299 235512155651801475829036949)
  ·
    refine ⟨11039632296178194179486107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235512155651801475829036949 11039632296178194179486107)
    ·
      refine ⟨16559448444267291269229161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11039632296178194179486107 16559448444267291269229161)
      ·
        refine ⟨12419586333200468451921871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16559448444267291269229161 12419586333200468451921871)
        ·
          refine ⟨18629379499800702677882807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419586333200468451921871 18629379499800702677882807)
          ·
            refine ⟨27944069249701054016824211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18629379499800702677882807 27944069249701054016824211)
            ·
              refine ⟨41916103874551581025236317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27944069249701054016824211 41916103874551581025236317)
              ·
                refine ⟨15718538952956842884463619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41916103874551581025236317 15718538952956842884463619)
                ·
                  refine ⟨23577808429435264326695429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15718538952956842884463619 23577808429435264326695429)
                  ·
                    refine ⟨4420839080519112061255393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23577808429435264326695429 4420839080519112061255393)
                    ·
                      refine ⟨3315629310389334045941545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420839080519112061255393 3315629310389334045941545)
                      ·
                        rfl

theorem cell23_6457165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6457165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457165 prefixEnd_6457165 := by exact prefixLift 6457165
  have htrace : WordTrace (prefixWord ++ tailWord_6457165) baseStart_6457165 baseEnd_6457165 := by
    simpa [prefixWord, tailWord_6457165, baseEnd_6457165] using wordTrace_append hprefix tailTrace_6457165
  have hstable : (prefixWord ++ tailWord_6457165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457165).length < 2 ^ (prefixWord ++ tailWord_6457165).sum := by decide
  have hdescent : baseEnd_6457165 < baseStart_6457165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457198 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_6457198 : Nat := 118140960795 + 6457198 * 2 ^ 59
def prefixEnd_6457198 : Nat := 4983230072969 + 3 ^ 40 * 6457198 * 2
def baseEnd_6457198 : Nat := 3315646255250932416828893

theorem tailTrace_6457198 : CollatzResearch.WordTrace tailWord_6457198 prefixEnd_6457198 3315646255250932416828893 := by
  unfold tailWord_6457198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29439169907585240308123531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157008906173787948309992165 29439169907585240308123531)
  ·
    refine ⟨44158754861377860462185297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29439169907585240308123531 44158754861377860462185297)
    ·
      refine ⟨33119066146033395346638973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44158754861377860462185297 33119066146033395346638973)
      ·
        refine ⟨12419649804762523254989615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33119066146033395346638973 12419649804762523254989615)
        ·
          refine ⟨18629474707143784882484423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419649804762523254989615 18629474707143784882484423)
          ·
            refine ⟨27944212060715677323726635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18629474707143784882484423 27944212060715677323726635)
            ·
              refine ⟨41916318091073515985589953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27944212060715677323726635 41916318091073515985589953)
              ·
                refine ⟨31437238568305136989192465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41916318091073515985589953 31437238568305136989192465)
                ·
                  refine ⟨23577928926228852741894349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31437238568305136989192465 23577928926228852741894349)
                  ·
                    refine ⟨8841723347335819778210381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23577928926228852741894349 8841723347335819778210381)
                    ·
                      refine ⟨3315646255250932416828893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841723347335819778210381 3315646255250932416828893)
                      ·
                        rfl

theorem cell23_6457198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_6457198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457198 prefixEnd_6457198 := by exact prefixLift 6457198
  have htrace : WordTrace (prefixWord ++ tailWord_6457198) baseStart_6457198 baseEnd_6457198 := by
    simpa [prefixWord, tailWord_6457198, baseEnd_6457198] using wordTrace_append hprefix tailTrace_6457198
  have hstable : (prefixWord ++ tailWord_6457198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457198).length < 2 ^ (prefixWord ++ tailWord_6457198).sum := by decide
  have hdescent : baseEnd_6457198 < baseStart_6457198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457241 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 3]
def baseStart_6457241 : Nat := 118140960795 + 6457241 * 2 ^ 59
def prefixEnd_6457241 : Nat := 4983230072969 + 3 ^ 40 * 6457241 * 2
def baseEnd_6457241 : Nat := 3315668334919075748591195

theorem tailTrace_6457241 : CollatzResearch.WordTrace tailWord_6457241 prefixEnd_6457241 3315668334919075748591195 := by
  unfold tailWord_6457241
  simp only [CollatzResearch.WordTrace]
  refine ⟨235514927599526140808803577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157009951733017427205869051 235514927599526140808803577)
  ·
    refine ⟨176636195699644605606602683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235514927599526140808803577 176636195699644605606602683)
    ·
      refine ⟨264954293549466908409904025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176636195699644605606602683 264954293549466908409904025)
      ·
        refine ⟨198715720162100181307428019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264954293549466908409904025 198715720162100181307428019)
        ·
          refine ⟨298073580243150271961142029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198715720162100181307428019 298073580243150271961142029)
          ·
            refine ⟨111777592591181351985428261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298073580243150271961142029 111777592591181351985428261)
            ·
              refine ⟨20958298610846503497267799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111777592591181351985428261 20958298610846503497267799)
              ·
                refine ⟨31437447916269755245901699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20958298610846503497267799 31437447916269755245901699)
                ·
                  refine ⟨47156171874404632868852549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31437447916269755245901699 47156171874404632868852549)
                  ·
                    refine ⟨8841782226450868662909853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47156171874404632868852549 8841782226450868662909853)
                    ·
                      refine ⟨3315668334919075748591195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841782226450868662909853 3315668334919075748591195)
                      ·
                        rfl

theorem cell23_6457241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_6457241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457241 prefixEnd_6457241 := by exact prefixLift 6457241
  have htrace : WordTrace (prefixWord ++ tailWord_6457241) baseStart_6457241 baseEnd_6457241 := by
    simpa [prefixWord, tailWord_6457241, baseEnd_6457241] using wordTrace_append hprefix tailTrace_6457241
  have hstable : (prefixWord ++ tailWord_6457241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457241).length < 2 ^ (prefixWord ++ tailWord_6457241).sum := by decide
  have hdescent : baseEnd_6457241 < baseStart_6457241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457262 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6457262 : Nat := 118140960795 + 6457262 * 2 ^ 59
def prefixEnd_6457262 : Nat := 4983230072969 + 3 ^ 40 * 6457262 * 2
def baseEnd_6457262 : Nat := 3315679118012820166428599

theorem tailTrace_6457262 : CollatzResearch.WordTrace tailWord_6457262 prefixEnd_6457262 3315679118012820166428599 := by
  unfold tailWord_6457262
  simp only [CollatzResearch.WordTrace]
  refine ⟨29439461691556257674414755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157010462354966707596878693 29439461691556257674414755)
  ·
    refine ⟨44159192537334386511622133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29439461691556257674414755 44159192537334386511622133)
    ·
      refine ⟨4139924300375098735464575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44159192537334386511622133 4139924300375098735464575)
      ·
        refine ⟨6209886450562648103196863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139924300375098735464575 6209886450562648103196863)
        ·
          refine ⟨9314829675843972154795295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209886450562648103196863 9314829675843972154795295)
          ·
            refine ⟨13972244513765958232192943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9314829675843972154795295 13972244513765958232192943)
            ·
              refine ⟨20958366770648937348289415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13972244513765958232192943 20958366770648937348289415)
              ·
                refine ⟨31437550155973406022434123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20958366770648937348289415 31437550155973406022434123)
                ·
                  refine ⟨47156325233960109033651185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31437550155973406022434123 47156325233960109033651185)
                  ·
                    refine ⟨35367243925470081775238389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47156325233960109033651185 35367243925470081775238389)
                    ·
                      refine ⟨3315679118012820166428599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35367243925470081775238389 3315679118012820166428599)
                      ·
                        rfl

theorem cell23_6457262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6457262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457262 prefixEnd_6457262 := by exact prefixLift 6457262
  have htrace : WordTrace (prefixWord ++ tailWord_6457262) baseStart_6457262 baseEnd_6457262 := by
    simpa [prefixWord, tailWord_6457262, baseEnd_6457262] using wordTrace_append hprefix tailTrace_6457262
  have hstable : (prefixWord ++ tailWord_6457262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457262).length < 2 ^ (prefixWord ++ tailWord_6457262).sum := by decide
  have hdescent : baseEnd_6457262 < baseStart_6457262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457265 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 3, 4]
def baseStart_6457265 : Nat := 118140960795 + 6457265 * 2 ^ 59
def prefixEnd_6457265 : Nat := 4983230072969 + 3 ^ 40 * 6457265 * 2
def baseEnd_6457265 : Nat := 1105226886151594551563695

theorem tailTrace_6457265 : CollatzResearch.WordTrace tailWord_6457265 prefixEnd_6457265 1105226886151594551563695 := by
  unfold tailWord_6457265
  simp only [CollatzResearch.WordTrace]
  refine ⟨235515802951439192907677249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157010535300959461938451499 235515802951439192907677249)
  ·
    refine ⟨176636852213579394680757937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235515802951439192907677249 176636852213579394680757937)
    ·
      refine ⟨132477639160184546010568453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176636852213579394680757937 132477639160184546010568453)
      ·
        refine ⟨24839557342534602376981585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132477639160184546010568453 24839557342534602376981585)
        ·
          refine ⟨18629668006900951782736189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24839557342534602376981585 18629668006900951782736189)
          ·
            refine ⟨6986125502587856918526071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18629668006900951782736189 6986125502587856918526071)
            ·
              refine ⟨10479188253881785377789107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986125502587856918526071 10479188253881785377789107)
              ·
                refine ⟨15718782380822678066683661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10479188253881785377789107 15718782380822678066683661)
                ·
                  refine ⟨5894543392808504275006373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15718782380822678066683661 5894543392808504275006373)
                  ·
                    refine ⟨1105226886151594551563695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5894543392808504275006373 1105226886151594551563695)
                    ·
                      rfl

theorem cell23_6457265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_6457265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457265 prefixEnd_6457265 := by exact prefixLift 6457265
  have htrace : WordTrace (prefixWord ++ tailWord_6457265) baseStart_6457265 baseEnd_6457265 := by
    simpa [prefixWord, tailWord_6457265, baseEnd_6457265] using wordTrace_append hprefix tailTrace_6457265
  have hstable : (prefixWord ++ tailWord_6457265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457265).length < 2 ^ (prefixWord ++ tailWord_6457265).sum := by decide
  have hdescent : baseEnd_6457265 < baseStart_6457265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457278 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_6457278 : Nat := 118140960795 + 6457278 * 2 ^ 59
def prefixEnd_6457278 : Nat := 4983230072969 + 3 ^ 40 * 6457278 * 2
def baseEnd_6457278 : Nat := 368409703744810233758725

theorem tailTrace_6457278 : CollatzResearch.WordTrace tailWord_6457278 prefixEnd_6457278 368409703744810233758725 := by
  unfold tailWord_6457278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29439534637549012015987561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157010851400261397418600325 29439534637549012015987561)
  ·
    refine ⟨22079650978161759011990671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29439534637549012015987561 22079650978161759011990671)
    ·
      refine ⟨33119476467242638517986007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22079650978161759011990671 33119476467242638517986007)
      ·
        refine ⟨49679214700863957776979011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33119476467242638517986007 49679214700863957776979011)
        ·
          refine ⟨74518822051295936665468517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49679214700863957776979011 74518822051295936665468517)
          ·
            refine ⟨13972279134617988124775347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74518822051295936665468517 13972279134617988124775347)
            ·
              refine ⟨20958418701926982187163021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13972279134617988124775347 20958418701926982187163021)
              ·
                refine ⟨7859407013222618320186133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20958418701926982187163021 7859407013222618320186133)
                ·
                  refine ⟨368409703744810233758725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7859407013222618320186133 368409703744810233758725)
                  ·
                    rfl

theorem cell23_6457278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_6457278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457278 prefixEnd_6457278 := by exact prefixLift 6457278
  have htrace : WordTrace (prefixWord ++ tailWord_6457278) baseStart_6457278 baseEnd_6457278 := by
    simpa [prefixWord, tailWord_6457278, baseEnd_6457278] using wordTrace_append hprefix tailTrace_6457278
  have hstable : (prefixWord ++ tailWord_6457278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457278).length < 2 ^ (prefixWord ++ tailWord_6457278).sum := by decide
  have hdescent : baseEnd_6457278 < baseStart_6457278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457291 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 3, 5]
def baseStart_6457291 : Nat := 118140960795 + 6457291 * 2 ^ 59
def prefixEnd_6457291 : Nat := 4983230072969 + 3 ^ 40 * 6457291 * 2
def baseEnd_6457291 : Nat := 1105231336317266850988655

theorem tailTrace_6457291 : CollatzResearch.WordTrace tailWord_6457291 prefixEnd_6457291 1105231336317266850988655 := by
  unfold tailWord_6457291
  simp only [CollatzResearch.WordTrace]
  refine ⟨235516751249344999348123727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157011167499563332898749151 235516751249344999348123727)
  ·
    refine ⟨353275126874017499022185591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235516751249344999348123727 353275126874017499022185591)
    ·
      refine ⟨529912690311026248533278387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353275126874017499022185591 529912690311026248533278387)
      ·
        refine ⟨794869035466539372799917581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529912690311026248533278387 794869035466539372799917581)
        ·
          refine ⟨298075888299952264799969093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794869035466539372799917581 298075888299952264799969093)
          ·
            refine ⟨55889229056241049649994205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298075888299952264799969093 55889229056241049649994205)
            ·
              refine ⟨20958460896090393618747827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55889229056241049649994205 20958460896090393618747827)
              ·
                refine ⟨31437691344135590428121741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20958460896090393618747827 31437691344135590428121741)
                ·
                  refine ⟨11789134254050846410545653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31437691344135590428121741 11789134254050846410545653)
                  ·
                    refine ⟨1105231336317266850988655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11789134254050846410545653 1105231336317266850988655)
                    ·
                      rfl

theorem cell23_6457291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 5].length) (baseStart_6457291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457291 prefixEnd_6457291 := by exact prefixLift 6457291
  have htrace : WordTrace (prefixWord ++ tailWord_6457291) baseStart_6457291 baseEnd_6457291 := by
    simpa [prefixWord, tailWord_6457291, baseEnd_6457291] using wordTrace_append hprefix tailTrace_6457291
  have hstable : (prefixWord ++ tailWord_6457291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457291).length < 2 ^ (prefixWord ++ tailWord_6457291).sum := by decide
  have hdescent : baseEnd_6457291 < baseStart_6457291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457315 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 2, 3, 2]
def baseStart_6457315 : Nat := 118140960795 + 6457315 * 2 ^ 59
def prefixEnd_6457315 : Nat := 4983230072969 + 3 ^ 40 * 6457315 * 2
def baseEnd_6457315 : Nat := 3315706332487508459065855

theorem tailTrace_6457315 : CollatzResearch.WordTrace tailWord_6457315 prefixEnd_6457315 3315706332487508459065855 := by
  unfold tailWord_6457315
  simp only [CollatzResearch.WordTrace]
  refine ⟨235517626601258051446997399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157011751067505367631331599 235517626601258051446997399)
  ·
    refine ⟨353276439901887077170496099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235517626601258051446997399 353276439901887077170496099)
    ·
      refine ⟨529914659852830615755744149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353276439901887077170496099 529914659852830615755744149)
      ·
        refine ⟨24839749680601435113550507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 529914659852830615755744149 24839749680601435113550507)
        ·
          refine ⟨37259624520902152670325761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24839749680601435113550507 37259624520902152670325761)
          ·
            refine ⟨27944718390676614502744321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37259624520902152670325761 27944718390676614502744321)
            ·
              refine ⟨20958538793007460877058241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27944718390676614502744321 20958538793007460877058241)
              ·
                refine ⟨15718904094755595657793681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20958538793007460877058241 15718904094755595657793681)
                ·
                  refine ⟨11789178071066696743345261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15718904094755595657793681 11789178071066696743345261)
                  ·
                    refine ⟨4420941776650011278754473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11789178071066696743345261 4420941776650011278754473)
                    ·
                      refine ⟨3315706332487508459065855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420941776650011278754473 3315706332487508459065855)
                      ·
                        rfl

theorem cell23_6457315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_6457315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457315 prefixEnd_6457315 := by exact prefixLift 6457315
  have htrace : WordTrace (prefixWord ++ tailWord_6457315) baseStart_6457315 baseEnd_6457315 := by
    simpa [prefixWord, tailWord_6457315, baseEnd_6457315] using wordTrace_append hprefix tailTrace_6457315
  have hstable : (prefixWord ++ tailWord_6457315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457315).length < 2 ^ (prefixWord ++ tailWord_6457315).sum := by decide
  have hdescent : baseEnd_6457315 < baseStart_6457315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457322 : List Nat := [3, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_6457322 : Nat := 118140960795 + 6457322 * 2 ^ 59
def prefixEnd_6457322 : Nat := 4983230072969 + 3 ^ 40 * 6457322 * 2
def baseEnd_6457322 : Nat := 3315709926852089931678323

theorem tailTrace_6457322 : CollatzResearch.WordTrace tailWord_6457322 prefixEnd_6457322 3315709926852089931678323 := by
  unfold tailWord_6457322
  simp only [CollatzResearch.WordTrace]
  refine ⟨58879470478058172910625555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157011921274821794428334813 58879470478058172910625555)
  ·
    refine ⟨88319205717087259365938333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58879470478058172910625555 88319205717087259365938333)
    ·
      refine ⟨33119702143907722262226875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88319205717087259365938333 33119702143907722262226875)
      ·
        refine ⟨49679553215861583393340313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33119702143907722262226875 49679553215861583393340313)
        ·
          refine ⟨37259664911896187545005235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49679553215861583393340313 37259664911896187545005235)
          ·
            refine ⟨55889497367844281317507853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37259664911896187545005235 55889497367844281317507853)
            ·
              refine ⟨20958561512941605494065445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55889497367844281317507853 20958561512941605494065445)
              ·
                refine ⟨3929730283676551030137271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20958561512941605494065445 3929730283676551030137271)
                ·
                  refine ⟨5894595425514826545205907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929730283676551030137271 5894595425514826545205907)
                  ·
                    refine ⟨8841893138272239817808861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894595425514826545205907 8841893138272239817808861)
                    ·
                      refine ⟨3315709926852089931678323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841893138272239817808861 3315709926852089931678323)
                      ·
                        rfl

theorem cell23_6457322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_6457322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457322 prefixEnd_6457322 := by exact prefixLift 6457322
  have htrace : WordTrace (prefixWord ++ tailWord_6457322) baseStart_6457322 baseEnd_6457322 := by
    simpa [prefixWord, tailWord_6457322, baseEnd_6457322] using wordTrace_append hprefix tailTrace_6457322
  have hstable : (prefixWord ++ tailWord_6457322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457322).length < 2 ^ (prefixWord ++ tailWord_6457322).sum := by decide
  have hdescent : baseEnd_6457322 < baseStart_6457322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457331 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5]
def baseStart_6457331 : Nat := 118140960795 + 6457331 * 2 ^ 59
def prefixEnd_6457331 : Nat := 4983230072969 + 3 ^ 40 * 6457331 * 2
def baseEnd_6457331 : Nat := 3315714548177980396465781

theorem tailTrace_6457331 : CollatzResearch.WordTrace tailWord_6457331 prefixEnd_6457331 3315714548177980396465781 := by
  unfold tailWord_6457331
  simp only [CollatzResearch.WordTrace]
  refine ⟨235518210169200086179579847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157012140112800057453053231 235518210169200086179579847)
  ·
    refine ⟨353277315253800129269369771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235518210169200086179579847 353277315253800129269369771)
    ·
      refine ⟨529915972880700193904054657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353277315253800129269369771 529915972880700193904054657)
      ·
        refine ⟨397436979660525145428040993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529915972880700193904054657 397436979660525145428040993)
        ·
          refine ⟨298077734745393859071030745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397436979660525145428040993 298077734745393859071030745)
          ·
            refine ⟨223558301059045394303273059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298077734745393859071030745 223558301059045394303273059)
            ·
              refine ⟨335337451588568091454909589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223558301059045394303273059 335337451588568091454909589)
              ·
                refine ⟨15718943043214129286948887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 335337451588568091454909589 15718943043214129286948887)
                ·
                  refine ⟨23578414564821193930423331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15718943043214129286948887 23578414564821193930423331)
                  ·
                    refine ⟨35367621847231790895634997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23578414564821193930423331 35367621847231790895634997)
                    ·
                      refine ⟨3315714548177980396465781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35367621847231790895634997 3315714548177980396465781)
                      ·
                        rfl

theorem cell23_6457331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_6457331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457331 prefixEnd_6457331 := by exact prefixLift 6457331
  have htrace : WordTrace (prefixWord ++ tailWord_6457331) baseStart_6457331 baseEnd_6457331 := by
    simpa [prefixWord, tailWord_6457331, baseEnd_6457331] using wordTrace_append hprefix tailTrace_6457331
  have hstable : (prefixWord ++ tailWord_6457331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457331).length < 2 ^ (prefixWord ++ tailWord_6457331).sum := by decide
  have hdescent : baseEnd_6457331 < baseStart_6457331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457341 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_6457341 : Nat := 118140960795 + 6457341 * 2 ^ 59
def prefixEnd_6457341 : Nat := 4983230072969 + 3 ^ 40 * 6457341 * 2
def baseEnd_6457341 : Nat := 3315719682984525357340735

theorem tailTrace_6457341 : CollatzResearch.WordTrace tailWord_6457341 prefixEnd_6457341 3315719682984525357340735 := by
  unfold tailWord_6457341
  simp only [CollatzResearch.WordTrace]
  refine ⟨235518574899163857887443877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157012383266109238591629251 235518574899163857887443877)
  ·
    refine ⟨44159732793593223353895727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235518574899163857887443877 44159732793593223353895727)
    ·
      refine ⟨66239599190389835030843591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44159732793593223353895727 66239599190389835030843591)
      ·
        refine ⟨99359398785584752546265387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66239599190389835030843591 99359398785584752546265387)
        ·
          refine ⟨149039098178377128819398081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99359398785584752546265387 149039098178377128819398081)
          ·
            refine ⟨111779323633782846614548561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149039098178377128819398081 111779323633782846614548561)
            ·
              refine ⟨83834492725337134960911421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111779323633782846614548561 83834492725337134960911421)
              ·
                refine ⟨31437934772001425610341783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83834492725337134960911421 31437934772001425610341783)
                ·
                  refine ⟨47156902158002138415512675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31437934772001425610341783 47156902158002138415512675)
                  ·
                    refine ⟨70735353237003207623269013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47156902158002138415512675 70735353237003207623269013)
                    ·
                      refine ⟨3315719682984525357340735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70735353237003207623269013 3315719682984525357340735)
                      ·
                        rfl

theorem cell23_6457341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_6457341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457341 prefixEnd_6457341 := by exact prefixLift 6457341
  have htrace : WordTrace (prefixWord ++ tailWord_6457341) baseStart_6457341 baseEnd_6457341 := by
    simpa [prefixWord, tailWord_6457341, baseEnd_6457341] using wordTrace_append hprefix tailTrace_6457341
  have hstable : (prefixWord ++ tailWord_6457341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457341).length < 2 ^ (prefixWord ++ tailWord_6457341).sum := by decide
  have hdescent : baseEnd_6457341 < baseStart_6457341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457358 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6457358 : Nat := 118140960795 + 6457358 * 2 ^ 59
def prefixEnd_6457358 : Nat := 4983230072969 + 3 ^ 40 * 6457358 * 2
def baseEnd_6457358 : Nat := 3315728412155651790828157

theorem tailTrace_6457358 : CollatzResearch.WordTrace tailWord_6457358 prefixEnd_6457358 3315728412155651790828157 := by
  unfold tailWord_6457358
  simp only [CollatzResearch.WordTrace]
  refine ⟨29439899367512783723851591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157012796626734846527208485 29439899367512783723851591)
  ·
    refine ⟨44159849051269175585777387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29439899367512783723851591 44159849051269175585777387)
    ·
      refine ⟨66239773576903763378666081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44159849051269175585777387 66239773576903763378666081)
      ·
        refine ⟨49679830182677822533999561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66239773576903763378666081 49679830182677822533999561)
        ·
          refine ⟨37259872637008366900499671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49679830182677822533999561 37259872637008366900499671)
          ·
            refine ⟨55889808955512550350749507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37259872637008366900499671 55889808955512550350749507)
            ·
              refine ⟨83834713433268825526124261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55889808955512550350749507 83834713433268825526124261)
              ·
                refine ⟨15719008768737904786148299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83834713433268825526124261 15719008768737904786148299)
                ·
                  refine ⟨23578513153106857179222449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15719008768737904786148299 23578513153106857179222449)
                  ·
                    refine ⟨17683884864830142884416837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23578513153106857179222449 17683884864830142884416837)
                    ·
                      refine ⟨3315728412155651790828157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17683884864830142884416837 3315728412155651790828157)
                      ·
                        rfl

theorem cell23_6457358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6457358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457358 prefixEnd_6457358 := by exact prefixLift 6457358
  have htrace : WordTrace (prefixWord ++ tailWord_6457358) baseStart_6457358 baseEnd_6457358 := by
    simpa [prefixWord, tailWord_6457358, baseEnd_6457358] using wordTrace_append hprefix tailTrace_6457358
  have hstable : (prefixWord ++ tailWord_6457358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457358).length < 2 ^ (prefixWord ++ tailWord_6457358).sum := by decide
  have hdescent : baseEnd_6457358 < baseStart_6457358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457372 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_6457372 : Nat := 118140960795 + 6457372 * 2 ^ 59
def prefixEnd_6457372 : Nat := 4983230072969 + 3 ^ 40 * 6457372 * 2
def baseEnd_6457372 : Nat := 1105245200294938245351031

theorem tailTrace_6457372 : CollatzResearch.WordTrace tailWord_6457372 prefixEnd_6457372 1105245200294938245351031 := by
  unfold tailWord_6457372
  simp only [CollatzResearch.WordTrace]
  refine ⟨117759852781025775090911185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157013137041367700121214913 117759852781025775090911185)
  ·
    refine ⟨88319889585769331318183389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117759852781025775090911185 88319889585769331318183389)
    ·
      refine ⟨33119958594663499244318771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88319889585769331318183389 33119958594663499244318771)
      ·
        refine ⟨49679937891995248866478157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33119958594663499244318771 49679937891995248866478157)
        ·
          refine ⟨18629976709498218324929309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49679937891995248866478157 18629976709498218324929309)
          ·
            refine ⟨6986241266061831871848491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18629976709498218324929309 6986241266061831871848491)
            ·
              refine ⟨10479361899092747807772737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986241266061831871848491 10479361899092747807772737)
              ·
                refine ⟨7859521424319560855829553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10479361899092747807772737 7859521424319560855829553)
                ·
                  refine ⟨5894641068239670641872165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7859521424319560855829553 5894641068239670641872165)
                  ·
                    refine ⟨1105245200294938245351031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5894641068239670641872165 1105245200294938245351031)
                    ·
                      rfl

theorem cell23_6457372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_6457372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457372 prefixEnd_6457372 := by exact prefixLift 6457372
  have htrace : WordTrace (prefixWord ++ tailWord_6457372) baseStart_6457372 baseEnd_6457372 := by
    simpa [prefixWord, tailWord_6457372, baseEnd_6457372] using wordTrace_append hprefix tailTrace_6457372
  have hstable : (prefixWord ++ tailWord_6457372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457372).length < 2 ^ (prefixWord ++ tailWord_6457372).sum := by decide
  have hdescent : baseEnd_6457372 < baseStart_6457372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457388 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 7, 2]
def baseStart_6457388 : Nat := 118140960795 + 6457388 * 2 ^ 59
def prefixEnd_6457388 : Nat := 4983230072969 + 3 ^ 40 * 6457388 * 2
def baseEnd_6457388 : Nat := 3315743816575286673453019

theorem tailTrace_6457388 : CollatzResearch.WordTrace tailWord_6457388 prefixEnd_6457388 3315743816575286673453019 := by
  unfold tailWord_6457388
  simp only [CollatzResearch.WordTrace]
  refine ⟨117760144564996792457202409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157013526086662389942936545 117760144564996792457202409)
  ·
    refine ⟨88320108423747594342901807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117760144564996792457202409 88320108423747594342901807)
    ·
      refine ⟨132480162635621391514352711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88320108423747594342901807 132480162635621391514352711)
      ·
        refine ⟨198720243953432087271529067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132480162635621391514352711 198720243953432087271529067)
        ·
          refine ⟨298080365930148130907293601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198720243953432087271529067 298080365930148130907293601)
          ·
            refine ⟨223560274447611098180470201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298080365930148130907293601 223560274447611098180470201)
            ·
              refine ⟨167670205835708323635352651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223560274447611098180470201 167670205835708323635352651)
              ·
                refine ⟨251505308753562485453028977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167670205835708323635352651 251505308753562485453028977)
                ·
                  refine ⟨188628981565171864089771733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251505308753562485453028977 188628981565171864089771733)
                  ·
                    refine ⟨4420991755433715564604025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 188628981565171864089771733 4420991755433715564604025)
                    ·
                      refine ⟨3315743816575286673453019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4420991755433715564604025 3315743816575286673453019)
                      ·
                        rfl

theorem cell23_6457388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_6457388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457388 prefixEnd_6457388 := by exact prefixLift 6457388
  have htrace : WordTrace (prefixWord ++ tailWord_6457388) baseStart_6457388 baseEnd_6457388 := by
    simpa [prefixWord, tailWord_6457388, baseEnd_6457388] using wordTrace_append hprefix tailTrace_6457388
  have hstable : (prefixWord ++ tailWord_6457388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457388).length < 2 ^ (prefixWord ++ tailWord_6457388).sum := by decide
  have hdescent : baseEnd_6457388 < baseStart_6457388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457395 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 3]
def baseStart_6457395 : Nat := 118140960795 + 6457395 * 2 ^ 59
def prefixEnd_6457395 : Nat := 4983230072969 + 3 ^ 40 * 6457395 * 2
def baseEnd_6457395 : Nat := 3315747410939868146065487

theorem tailTrace_6457395 : CollatzResearch.WordTrace tailWord_6457395 prefixEnd_6457395 3315747410939868146065487 := by
  unfold tailWord_6457395
  simp only [CollatzResearch.WordTrace]
  refine ⟨235520544440968225109909639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157013696293978816739939759 235520544440968225109909639)
  ·
    refine ⟨353280816661452337664864459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235520544440968225109909639 353280816661452337664864459)
    ·
      refine ⟨529921224992178506497296689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353280816661452337664864459 529921224992178506497296689)
      ·
        refine ⟨397440918744133879872972517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529921224992178506497296689 397440918744133879872972517)
        ·
          refine ⟨74520172264525102476182347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397440918744133879872972517 74520172264525102476182347)
          ·
            refine ⟨111780258396787653714273521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74520172264525102476182347 111780258396787653714273521)
            ·
              refine ⟨83835193797590740285705141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111780258396787653714273521 83835193797590740285705141)
              ·
                refine ⟨7859549418524131901784857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83835193797590740285705141 7859549418524131901784857)
                ·
                  refine ⟨5894662063893098926338643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7859549418524131901784857 5894662063893098926338643)
                  ·
                    refine ⟨8841993095839648389507965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894662063893098926338643 8841993095839648389507965)
                    ·
                      refine ⟨3315747410939868146065487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8841993095839648389507965 3315747410939868146065487)
                      ·
                        rfl

theorem cell23_6457395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 3].length) (baseStart_6457395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457395 prefixEnd_6457395 := by exact prefixLift 6457395
  have htrace : WordTrace (prefixWord ++ tailWord_6457395) baseStart_6457395 baseEnd_6457395 := by
    simpa [prefixWord, tailWord_6457395, baseEnd_6457395] using wordTrace_append hprefix tailTrace_6457395
  have hstable : (prefixWord ++ tailWord_6457395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457395).length < 2 ^ (prefixWord ++ tailWord_6457395).sum := by decide
  have hdescent : baseEnd_6457395 < baseStart_6457395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457411 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 4, 6]
def baseStart_6457411 : Nat := 118140960795 + 6457411 * 2 ^ 59
def prefixEnd_6457411 : Nat := 4983230072969 + 3 ^ 40 * 6457411 * 2
def baseEnd_6457411 : Nat := 1105251875543446694488471

theorem tailTrace_6457411 : CollatzResearch.WordTrace tailWord_6457411 prefixEnd_6457411 1105251875543446694488471 := by
  unfold tailWord_6457411
  simp only [CollatzResearch.WordTrace]
  refine ⟨235521128008910259842492087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157014085339273506561661391 235521128008910259842492087)
  ·
    refine ⟨353281692013365389763738131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235521128008910259842492087 353281692013365389763738131)
    ·
      refine ⟨529922538020048084645607197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353281692013365389763738131 529922538020048084645607197)
      ·
        refine ⟨198720951757518031742102699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 529922538020048084645607197 198720951757518031742102699)
        ·
          refine ⟨298081427636277047613154049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198720951757518031742102699 298081427636277047613154049)
          ·
            refine ⟨223561070727207785709865537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298081427636277047613154049 223561070727207785709865537)
            ·
              refine ⟨167670803045405839282399153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223561070727207785709865537 167670803045405839282399153)
              ·
                refine ⟨125753102284054379461799365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167670803045405839282399153 125753102284054379461799365)
                ·
                  refine ⟨23578706678260196149087381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125753102284054379461799365 23578706678260196149087381)
                  ·
                    refine ⟨1105251875543446694488471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23578706678260196149087381 1105251875543446694488471)
                    ·
                      rfl

theorem cell23_6457411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 6].length) (baseStart_6457411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457411 prefixEnd_6457411 := by exact prefixLift 6457411
  have htrace : WordTrace (prefixWord ++ tailWord_6457411) baseStart_6457411 baseEnd_6457411 := by
    simpa [prefixWord, tailWord_6457411, baseEnd_6457411] using wordTrace_append hprefix tailTrace_6457411
  have hstable : (prefixWord ++ tailWord_6457411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457411).length < 2 ^ (prefixWord ++ tailWord_6457411).sum := by decide
  have hdescent : baseEnd_6457411 < baseStart_6457411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457422 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_6457422 : Nat := 118140960795 + 6457422 * 2 ^ 59
def prefixEnd_6457422 : Nat := 4983230072969 + 3 ^ 40 * 6457422 * 2
def baseEnd_6457422 : Nat := 3315761274917539540427863

theorem tailTrace_6457422 : CollatzResearch.WordTrace tailWord_6457422 prefixEnd_6457422 3315761274917539540427863 := by
  unfold tailWord_6457422
  simp only [CollatzResearch.WordTrace]
  refine ⟨29440191151483801090142815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157014352807913605814095013 29440191151483801090142815)
  ·
    refine ⟨44160286727225701635214223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29440191151483801090142815 44160286727225701635214223)
    ·
      refine ⟨66240430090838552452821335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44160286727225701635214223 66240430090838552452821335)
      ·
        refine ⟨99360645136257828679232003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66240430090838552452821335 99360645136257828679232003)
        ·
          refine ⟨149040967704386743018848005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99360645136257828679232003 149040967704386743018848005)
          ·
            refine ⟨27945181444572514316034001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149040967704386743018848005 27945181444572514316034001)
            ·
              refine ⟨20958886083429385737025501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27945181444572514316034001 20958886083429385737025501)
              ·
                refine ⟨7859582281286019651384563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20958886083429385737025501 7859582281286019651384563)
                ·
                  refine ⟨11789373421929029477076845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7859582281286019651384563 11789373421929029477076845)
                  ·
                    refine ⟨4421015033223386053903817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11789373421929029477076845 4421015033223386053903817)
                    ·
                      refine ⟨3315761274917539540427863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421015033223386053903817 3315761274917539540427863)
                      ·
                        rfl

theorem cell23_6457422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_6457422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457422 prefixEnd_6457422 := by exact prefixLift 6457422
  have htrace : WordTrace (prefixWord ++ tailWord_6457422) baseStart_6457422 baseEnd_6457422 := by
    simpa [prefixWord, tailWord_6457422, baseEnd_6457422] using wordTrace_append hprefix tailTrace_6457422
  have hstable : (prefixWord ++ tailWord_6457422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457422).length < 2 ^ (prefixWord ++ tailWord_6457422).sum := by decide
  have hdescent : baseEnd_6457422 < baseStart_6457422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457430 : List Nat := [5, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6457430 : Nat := 118140960795 + 6457430 * 2 ^ 59
def prefixEnd_6457430 : Nat := 4983230072969 + 3 ^ 40 * 6457430 * 2
def baseEnd_6457430 : Nat := 3315765382762775509127827

theorem tailTrace_6457430 : CollatzResearch.WordTrace tailWord_6457430 prefixEnd_6457430 3315765382762775509127827 := by
  unfold tailWord_6457430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14720113812240089130464609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157014547330560950724955829 14720113812240089130464609)
  ·
    refine ⟨11040085359180066847848457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14720113812240089130464609 11040085359180066847848457)
    ·
      refine ⟨8280064019385050135886343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11040085359180066847848457 8280064019385050135886343)
      ·
        refine ⟨12420096029077575203829515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8280064019385050135886343 12420096029077575203829515)
        ·
          refine ⟨18630144043616362805744273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12420096029077575203829515 18630144043616362805744273)
          ·
            refine ⟨13972608032712272104308205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18630144043616362805744273 13972608032712272104308205)
            ·
              refine ⟨5239728012267102039115577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13972608032712272104308205 5239728012267102039115577)
              ·
                refine ⟨3929796009200326529336683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239728012267102039115577 3929796009200326529336683)
                ·
                  refine ⟨5894694013800489794005025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929796009200326529336683 5894694013800489794005025)
                  ·
                    refine ⟨4421020510350367345503769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894694013800489794005025 4421020510350367345503769)
                    ·
                      refine ⟨3315765382762775509127827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421020510350367345503769 3315765382762775509127827)
                      ·
                        rfl

theorem cell23_6457430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6457430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457430 prefixEnd_6457430 := by exact prefixLift 6457430
  have htrace : WordTrace (prefixWord ++ tailWord_6457430) baseStart_6457430 baseEnd_6457430 := by
    simpa [prefixWord, tailWord_6457430, baseEnd_6457430] using wordTrace_append hprefix tailTrace_6457430
  have hstable : (prefixWord ++ tailWord_6457430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457430).length < 2 ^ (prefixWord ++ tailWord_6457430).sum := by decide
  have hdescent : baseEnd_6457430 < baseStart_6457430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457486 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6457486 : Nat := 118140960795 + 6457486 * 2 ^ 59
def prefixEnd_6457486 : Nat := 4983230072969 + 3 ^ 40 * 6457486 * 2
def baseEnd_6457486 : Nat := 3315794137679427290027569

theorem tailTrace_6457486 : CollatzResearch.WordTrace tailWord_6457486 prefixEnd_6457486 3315794137679427290027569 := by
  unfold tailWord_6457486
  simp only [CollatzResearch.WordTrace]
  refine ⟨29440482935454818456434039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157015908989092365100981541 29440482935454818456434039)
  ·
    refine ⟨44160724403182227684651059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29440482935454818456434039 44160724403182227684651059)
    ·
      refine ⟨66241086604773341526976589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44160724403182227684651059 66241086604773341526976589)
      ·
        refine ⟨24840407476790003072616221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66241086604773341526976589 24840407476790003072616221)
        ·
          refine ⟨9315152803796251152231083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24840407476790003072616221 9315152803796251152231083)
          ·
            refine ⟨13972729205694376728346625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315152803796251152231083 13972729205694376728346625)
            ·
              refine ⟨10479546904270782546259969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13972729205694376728346625 10479546904270782546259969)
              ·
                refine ⟨7859660178203086909694977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10479546904270782546259969 7859660178203086909694977)
                ·
                  refine ⟨5894745133652315182271233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7859660178203086909694977 5894745133652315182271233)
                  ·
                    refine ⟨4421058850239236386703425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894745133652315182271233 4421058850239236386703425)
                    ·
                      refine ⟨3315794137679427290027569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421058850239236386703425 3315794137679427290027569)
                      ·
                        rfl

theorem cell23_6457486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6457486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457486 prefixEnd_6457486 := by exact prefixLift 6457486
  have htrace : WordTrace (prefixWord ++ tailWord_6457486) baseStart_6457486 baseEnd_6457486 := by
    simpa [prefixWord, tailWord_6457486, baseEnd_6457486] using wordTrace_append hprefix tailTrace_6457486
  have hstable : (prefixWord ++ tailWord_6457486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457486).length < 2 ^ (prefixWord ++ tailWord_6457486).sum := by decide
  have hdescent : baseEnd_6457486 < baseStart_6457486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457488 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 2, 5]
def baseStart_6457488 : Nat := 118140960795 + 6457488 * 2 ^ 59
def prefixEnd_6457488 : Nat := 4983230072969 + 3 ^ 40 * 6457488 * 2
def baseEnd_6457488 : Nat := 1105265054880245427400853

theorem tailTrace_6457488 : CollatzResearch.WordTrace tailWord_6457488 prefixEnd_6457488 1105265054880245427400853 := by
  unfold tailWord_6457488
  simp only [CollatzResearch.WordTrace]
  refine ⟨117761968214815650996522559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157015957619754201328696745 117761968214815650996522559)
  ·
    refine ⟨176642952322223476494783839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117761968214815650996522559 176642952322223476494783839)
    ·
      refine ⟨264964428483335214742175759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176642952322223476494783839 264964428483335214742175759)
      ·
        refine ⟨397446642725002822113263639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264964428483335214742175759 397446642725002822113263639)
        ·
          refine ⟨596169964087504233169895459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397446642725002822113263639 596169964087504233169895459)
          ·
            refine ⟨894254946131256349754843189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596169964087504233169895459 894254946131256349754843189)
            ·
              refine ⟨83836401199805282789516549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 894254946131256349754843189 83836401199805282789516549)
              ·
                refine ⟨15719325224963490523034353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83836401199805282789516549 15719325224963490523034353)
                ·
                  refine ⟨11789493918722617892275765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15719325224963490523034353 11789493918722617892275765)
                  ·
                    refine ⟨1105265054880245427400853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11789493918722617892275765 1105265054880245427400853)
                    ·
                      rfl

theorem cell23_6457488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_6457488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457488 prefixEnd_6457488 := by exact prefixLift 6457488
  have htrace : WordTrace (prefixWord ++ tailWord_6457488) baseStart_6457488 baseEnd_6457488 := by
    simpa [prefixWord, tailWord_6457488, baseEnd_6457488] using wordTrace_append hprefix tailTrace_6457488
  have hstable : (prefixWord ++ tailWord_6457488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457488).length < 2 ^ (prefixWord ++ tailWord_6457488).sum := by decide
  have hdescent : baseEnd_6457488 < baseStart_6457488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457568 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_6457568 : Nat := 118140960795 + 6457568 * 2 ^ 59
def prefixEnd_6457568 : Nat := 4983230072969 + 3 ^ 40 * 6457568 * 2
def baseEnd_6457568 : Nat := 3315836243093095969202191

theorem tailTrace_6457568 : CollatzResearch.WordTrace tailWord_6457568 prefixEnd_6457568 3315836243093095969202191 := by
  unfold tailWord_6457568
  simp only [CollatzResearch.WordTrace]
  refine ⟨117763427134670737827978679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157017902846227650437304905 117763427134670737827978679)
  ·
    refine ⟨176645140702006106741968019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117763427134670737827978679 176645140702006106741968019)
    ·
      refine ⟨264967711053009160112952029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176645140702006106741968019 264967711053009160112952029)
      ·
        refine ⟨99362891644878435042357011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264967711053009160112952029 99362891644878435042357011)
        ·
          refine ⟨149044337467317652563535517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99362891644878435042357011 149044337467317652563535517)
          ·
            refine ⟨55891626550244119711325819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149044337467317652563535517 55891626550244119711325819)
            ·
              refine ⟨83837439825366179566988729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55891626550244119711325819 83837439825366179566988729)
              ·
                refine ⟨62878079869024634675241547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83837439825366179566988729 62878079869024634675241547)
                ·
                  refine ⟨94317119803536952012862321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62878079869024634675241547 94317119803536952012862321)
                  ·
                    refine ⟨70737839852652714009646741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94317119803536952012862321 70737839852652714009646741)
                    ·
                      refine ⟨3315836243093095969202191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70737839852652714009646741 3315836243093095969202191)
                      ·
                        rfl

theorem cell23_6457568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_6457568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457568 prefixEnd_6457568 := by exact prefixLift 6457568
  have htrace : WordTrace (prefixWord ++ tailWord_6457568) baseStart_6457568 baseEnd_6457568 := by
    simpa [prefixWord, tailWord_6457568, baseEnd_6457568] using wordTrace_append hprefix tailTrace_6457568
  have hstable : (prefixWord ++ tailWord_6457568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457568).length < 2 ^ (prefixWord ++ tailWord_6457568).sum := by decide
  have hdescent : baseEnd_6457568 < baseStart_6457568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457586 : List Nat := [3, 2, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_6457586 : Nat := 118140960795 + 6457586 * 2 ^ 59
def prefixEnd_6457586 : Nat := 4983230072969 + 3 ^ 40 * 6457586 * 2
def baseEnd_6457586 : Nat := 1105281828581625632925703

theorem tailTrace_6457586 : CollatzResearch.WordTrace tailWord_6457586 prefixEnd_6457586 1105281828581625632925703 := by
  unfold tailWord_6457586
  simp only [CollatzResearch.WordTrace]
  refine ⟨58881877695819066182528153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157018340522184176486741741 58881877695819066182528153)
  ·
    refine ⟨44161408271864299636896115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58881877695819066182528153 44161408271864299636896115)
    ·
      refine ⟨66242112407796449455344173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44161408271864299636896115 66242112407796449455344173)
      ·
        refine ⟨24840792152923668545754065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66242112407796449455344173 24840792152923668545754065)
        ·
          refine ⟨18630594114692751409315549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24840792152923668545754065 18630594114692751409315549)
          ·
            refine ⟨6986472793009781778493331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18630594114692751409315549 6986472793009781778493331)
            ·
              refine ⟨10479709189514672667739997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986472793009781778493331 10479709189514672667739997)
              ·
                refine ⟨3929890946068002250402499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10479709189514672667739997 3929890946068002250402499)
                ·
                  refine ⟨5894836419102003375603749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929890946068002250402499 5894836419102003375603749)
                  ·
                    refine ⟨1105281828581625632925703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5894836419102003375603749 1105281828581625632925703)
                    ·
                      rfl

theorem cell23_6457586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_6457586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457586 prefixEnd_6457586 := by exact prefixLift 6457586
  have htrace : WordTrace (prefixWord ++ tailWord_6457586) baseStart_6457586 baseEnd_6457586 := by
    simpa [prefixWord, tailWord_6457586, baseEnd_6457586] using wordTrace_append hprefix tailTrace_6457586
  have hstable : (prefixWord ++ tailWord_6457586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457586).length < 2 ^ (prefixWord ++ tailWord_6457586).sum := by decide
  have hdescent : baseEnd_6457586 < baseStart_6457586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457609 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 3]
def baseStart_6457609 : Nat := 118140960795 + 6457609 * 2 ^ 59
def prefixEnd_6457609 : Nat := 4983230072969 + 3 ^ 40 * 6457609 * 2
def baseEnd_6457609 : Nat := 3315857295799930308789503

theorem tailTrace_6457609 : CollatzResearch.WordTrace tailWord_6457609 prefixEnd_6457609 3315857295799930308789503 := by
  unfold tailWord_6457609
  simp only [CollatzResearch.WordTrace]
  refine ⟨235528349662192939658199881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157018899774795293105466587 235528349662192939658199881)
  ·
    refine ⟨176646262246644704743649911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235528349662192939658199881 176646262246644704743649911)
    ·
      refine ⟨264969393369967057115474867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176646262246644704743649911 264969393369967057115474867)
      ·
        refine ⟨397454090054950585673212301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264969393369967057115474867 397454090054950585673212301)
        ·
          refine ⟨149045283770606469627454613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397454090054950585673212301 149045283770606469627454613)
          ·
            refine ⟨6986497676747178263786935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149045283770606469627454613 6986497676747178263786935)
            ·
              refine ⟨10479746515120767395680403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986497676747178263786935 10479746515120767395680403)
              ·
                refine ⟨15719619772681151093520605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10479746515120767395680403 15719619772681151093520605)
                ·
                  refine ⟨5894857414755431660070227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15719619772681151093520605 5894857414755431660070227)
                  ·
                    refine ⟨8842286122133147490105341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894857414755431660070227 8842286122133147490105341)
                    ·
                      refine ⟨3315857295799930308789503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8842286122133147490105341 3315857295799930308789503)
                      ·
                        rfl

theorem cell23_6457609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 3].length) (baseStart_6457609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457609 prefixEnd_6457609 := by exact prefixLift 6457609
  have htrace : WordTrace (prefixWord ++ tailWord_6457609) baseStart_6457609 baseEnd_6457609 := by
    simpa [prefixWord, tailWord_6457609, baseEnd_6457609] using wordTrace_append hprefix tailTrace_6457609
  have hstable : (prefixWord ++ tailWord_6457609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457609).length < 2 ^ (prefixWord ++ tailWord_6457609).sum := by decide
  have hdescent : baseEnd_6457609 < baseStart_6457609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457632 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6457632 : Nat := 118140960795 + 6457632 * 2 ^ 59
def prefixEnd_6457632 : Nat := 4983230072969 + 3 ^ 40 * 6457632 * 2
def baseEnd_6457632 : Nat := 3315869105854983718801897

theorem tailTrace_6457632 : CollatzResearch.WordTrace tailWord_6457632 prefixEnd_6457632 3315869105854983718801897 := by
  unfold tailWord_6457632
  simp only [CollatzResearch.WordTrace]
  refine ⟨117764594270554807293143575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157019459027406409724191433 117764594270554807293143575)
  ·
    refine ⟨176646891405832210939715363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117764594270554807293143575 176646891405832210939715363)
    ·
      refine ⟨264970337108748316409573045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176646891405832210939715363 264970337108748316409573045)
      ·
        refine ⟨24840969103945154663397473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264970337108748316409573045 24840969103945154663397473)
        ·
          refine ⟨18630726827958865997548105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24840969103945154663397473 18630726827958865997548105)
          ·
            refine ⟨13973045120969149498161079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18630726827958865997548105 13973045120969149498161079)
            ·
              refine ⟨20959567681453724247241619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13973045120969149498161079 20959567681453724247241619)
              ·
                refine ⟨31439351522180586370862429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20959567681453724247241619 31439351522180586370862429)
                ·
                  refine ⟨11789756820817719889073411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31439351522180586370862429 11789756820817719889073411)
                  ·
                    refine ⟨17684635231226579833610117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11789756820817719889073411 17684635231226579833610117)
                    ·
                      refine ⟨3315869105854983718801897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17684635231226579833610117 3315869105854983718801897)
                      ·
                        rfl

theorem cell23_6457632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6457632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457632 prefixEnd_6457632 := by exact prefixLift 6457632
  have htrace : WordTrace (prefixWord ++ tailWord_6457632) baseStart_6457632 baseEnd_6457632 := by
    simpa [prefixWord, tailWord_6457632, baseEnd_6457632] using wordTrace_append hprefix tailTrace_6457632
  have hstable : (prefixWord ++ tailWord_6457632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457632).length < 2 ^ (prefixWord ++ tailWord_6457632).sum := by decide
  have hdescent : baseEnd_6457632 < baseStart_6457632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457682 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_6457682 : Nat := 118140960795 + 6457682 * 2 ^ 59
def prefixEnd_6457682 : Nat := 4983230072969 + 3 ^ 40 * 6457682 * 2
def baseEnd_6457682 : Nat := 3315894779887708523176667

theorem tailTrace_6457682 : CollatzResearch.WordTrace tailWord_6457682 prefixEnd_6457682 3315894779887708523176667 := by
  unfold tailWord_6457682
  simp only [CollatzResearch.WordTrace]
  refine ⟨58882753047732118281401825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157020674793952315417071533 58882753047732118281401825)
  ·
    refine ⟨44162064785799088711051369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58882753047732118281401825 44162064785799088711051369)
    ·
      refine ⟨33121548589349316533288527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44162064785799088711051369 33121548589349316533288527)
      ·
        refine ⟨49682322884023974799932791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33121548589349316533288527 49682322884023974799932791)
        ·
          refine ⟨74523484326035962199899187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49682322884023974799932791 74523484326035962199899187)
          ·
            refine ⟨111785226489053943299848781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74523484326035962199899187 111785226489053943299848781)
            ·
              refine ⟨41919459933395228737443293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111785226489053943299848781 41919459933395228737443293)
              ·
                refine ⟨15719797475023210776541235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41919459933395228737443293 15719797475023210776541235)
                ·
                  refine ⟨23579696212534816164811853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15719797475023210776541235 23579696212534816164811853)
                  ·
                    refine ⟨8842386079700556061804445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23579696212534816164811853 8842386079700556061804445)
                    ·
                      refine ⟨3315894779887708523176667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8842386079700556061804445 3315894779887708523176667)
                      ·
                        rfl

theorem cell23_6457682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_6457682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457682 prefixEnd_6457682 := by exact prefixLift 6457682
  have htrace : WordTrace (prefixWord ++ tailWord_6457682) baseStart_6457682 baseEnd_6457682 := by
    simpa [prefixWord, tailWord_6457682, baseEnd_6457682] using wordTrace_append hprefix tailTrace_6457682
  have hstable : (prefixWord ++ tailWord_6457682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457682).length < 2 ^ (prefixWord ++ tailWord_6457682).sum := by decide
  have hdescent : baseEnd_6457682 < baseStart_6457682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457694 : List Nat := [4, 4, 2, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6457694 : Nat := 118140960795 + 6457694 * 2 ^ 59
def prefixEnd_6457694 : Nat := 4983230072969 + 3 ^ 40 * 6457694 * 2
def baseEnd_6457694 : Nat := 3315900941655562476226613

theorem tailTrace_6457694 : CollatzResearch.WordTrace tailWord_6457694 prefixEnd_6457694 3315900941655562476226613 := by
  unfold tailWord_6457694
  simp only [CollatzResearch.WordTrace]
  refine ⟨29441431233360624896880517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157020966577923332783362757 29441431233360624896880517)
  ·
    refine ⟨5520268356255117168165097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29441431233360624896880517 5520268356255117168165097)
    ·
      refine ⟨4140201267191337876123823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5520268356255117168165097 4140201267191337876123823)
      ·
        refine ⟨6210301900787006814185735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140201267191337876123823 6210301900787006814185735)
        ·
          refine ⟨9315452851180510221278603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210301900787006814185735 9315452851180510221278603)
          ·
            refine ⟨13973179276770765331917905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315452851180510221278603 13973179276770765331917905)
            ·
              refine ⟨10479884457578073998938429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13973179276770765331917905 10479884457578073998938429)
              ·
                refine ⟨3929956671591777749601911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10479884457578073998938429 3929956671591777749601911)
                ·
                  refine ⟨5894935007387666624402867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929956671591777749601911 5894935007387666624402867)
                  ·
                    refine ⟨8842402511081499936604301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894935007387666624402867 8842402511081499936604301)
                    ·
                      refine ⟨3315900941655562476226613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8842402511081499936604301 3315900941655562476226613)
                      ·
                        rfl

theorem cell23_6457694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6457694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457694 prefixEnd_6457694 := by exact prefixLift 6457694
  have htrace : WordTrace (prefixWord ++ tailWord_6457694) baseStart_6457694 baseEnd_6457694 := by
    simpa [prefixWord, tailWord_6457694, baseEnd_6457694] using wordTrace_append hprefix tailTrace_6457694
  have hstable : (prefixWord ++ tailWord_6457694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457694).length < 2 ^ (prefixWord ++ tailWord_6457694).sum := by decide
  have hdescent : baseEnd_6457694 < baseStart_6457694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457739 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 1, 4, 2]
def baseStart_6457739 : Nat := 118140960795 + 6457739 * 2 ^ 59
def prefixEnd_6457739 : Nat := 4983230072969 + 3 ^ 40 * 6457739 * 2
def baseEnd_6457739 : Nat := 3315924048285014800163905

theorem tailTrace_6457739 : CollatzResearch.WordTrace tailWord_6457739 prefixEnd_6457739 3315924048285014800163905 := by
  unfold tailWord_6457739
  simp only [CollatzResearch.WordTrace]
  refine ⟨235533091151721971860432271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157022060767814647906954847 235533091151721971860432271)
  ·
    refine ⟨353299636727582957790648407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235533091151721971860432271 353299636727582957790648407)
    ·
      refine ⟨529949455091374436685972611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353299636727582957790648407 529949455091374436685972611)
      ·
        refine ⟨794924182637061655028958917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529949455091374436685972611 794924182637061655028958917)
        ·
          refine ⟨149048284244449060317929797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 794924182637061655028958917 149048284244449060317929797)
          ·
            refine ⟨27946553295834198809611837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149048284244449060317929797 27946553295834198809611837)
            ·
              refine ⟨10479957485937824553604439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27946553295834198809611837 10479957485937824553604439)
              ·
                refine ⟨15719936228906736830406659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10479957485937824553604439 15719936228906736830406659)
                ·
                  refine ⟨23579904343360105245609989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15719936228906736830406659 23579904343360105245609989)
                  ·
                    refine ⟨4421232064380019733551873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23579904343360105245609989 4421232064380019733551873)
                    ·
                      refine ⟨3315924048285014800163905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421232064380019733551873 3315924048285014800163905)
                      ·
                        rfl

theorem cell23_6457739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4, 2].length) (baseStart_6457739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457739 prefixEnd_6457739 := by exact prefixLift 6457739
  have htrace : WordTrace (prefixWord ++ tailWord_6457739) baseStart_6457739 baseEnd_6457739 := by
    simpa [prefixWord, tailWord_6457739, baseEnd_6457739] using wordTrace_append hprefix tailTrace_6457739
  have hstable : (prefixWord ++ tailWord_6457739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457739).length < 2 ^ (prefixWord ++ tailWord_6457739).sum := by decide
  have hdescent : baseEnd_6457739 < baseStart_6457739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457815 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_6457815 : Nat := 118140960795 + 6457815 * 2 ^ 59
def prefixEnd_6457815 : Nat := 4983230072969 + 3 ^ 40 * 6457815 * 2
def baseEnd_6457815 : Nat := 3315963072814756502813555

theorem tailTrace_6457815 : CollatzResearch.WordTrace tailWord_6457815 prefixEnd_6457815 3315963072814756502813555 := by
  unfold tailWord_6457815
  simp only [CollatzResearch.WordTrace]
  refine ⟨235535863099446636840198899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157023908732964424560132599 235535863099446636840198899)
  ·
    refine ⟨353303794649169955260298349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235535863099446636840198899 353303794649169955260298349)
    ·
      refine ⟨132488922993438733222611881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353303794649169955260298349 132488922993438733222611881)
      ·
        refine ⟨99366692245079049916958911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132488922993438733222611881 99366692245079049916958911)
        ·
          refine ⟨149050038367618574875438367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99366692245079049916958911 149050038367618574875438367)
          ·
            refine ⟨223575057551427862313157551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149050038367618574875438367 223575057551427862313157551)
            ·
              refine ⟨335362586327141793469736327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223575057551427862313157551 335362586327141793469736327)
              ·
                refine ⟨503043879490712690204604491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335362586327141793469736327 503043879490712690204604491)
                ·
                  refine ⟨754565819236069035306906737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503043879490712690204604491 754565819236069035306906737)
                  ·
                    refine ⟨565924364427051776480180053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 754565819236069035306906737 565924364427051776480180053)
                    ·
                      refine ⟨3315963072814756502813555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 565924364427051776480180053 3315963072814756502813555)
                      ·
                        rfl

theorem cell23_6457815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_6457815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457815 prefixEnd_6457815 := by exact prefixLift 6457815
  have htrace : WordTrace (prefixWord ++ tailWord_6457815) baseStart_6457815 baseEnd_6457815 := by
    simpa [prefixWord, tailWord_6457815, baseEnd_6457815] using wordTrace_append hprefix tailTrace_6457815
  have hstable : (prefixWord ++ tailWord_6457815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457815).length < 2 ^ (prefixWord ++ tailWord_6457815).sum := by decide
  have hdescent : baseEnd_6457815 < baseStart_6457815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457846 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_6457846 : Nat := 118140960795 + 6457846 * 2 ^ 59
def prefixEnd_6457846 : Nat := 4983230072969 + 3 ^ 40 * 6457846 * 2
def baseEnd_6457846 : Nat := 3315978990715045881525913

theorem tailTrace_6457846 : CollatzResearch.WordTrace tailWord_6457846 prefixEnd_6457846 3315978990715045881525913 := by
  unfold tailWord_6457846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721062110145895570911087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157024662508222886089718261 14721062110145895570911087)
  ·
    refine ⟨22081593165218843356366631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14721062110145895570911087 22081593165218843356366631)
    ·
      refine ⟨33122389747828265034549947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22081593165218843356366631 33122389747828265034549947)
      ·
        refine ⟨49683584621742397551824921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33122389747828265034549947 49683584621742397551824921)
        ·
          refine ⟨37262688466306798163868691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49683584621742397551824921 37262688466306798163868691)
          ·
            refine ⟨55894032699460197245803037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37262688466306798163868691 55894032699460197245803037)
            ·
              refine ⟨20960262262297573967176139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55894032699460197245803037 20960262262297573967176139)
              ·
                refine ⟨31440393393446360950764209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20960262262297573967176139 31440393393446360950764209)
                ·
                  refine ⟨23580295045084770713073157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31440393393446360950764209 23580295045084770713073157)
                  ·
                    refine ⟨4421305320953394508701217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23580295045084770713073157 4421305320953394508701217)
                    ·
                      refine ⟨3315978990715045881525913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421305320953394508701217 3315978990715045881525913)
                      ·
                        rfl

theorem cell23_6457846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_6457846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457846 prefixEnd_6457846 := by exact prefixLift 6457846
  have htrace : WordTrace (prefixWord ++ tailWord_6457846) baseStart_6457846 baseEnd_6457846 := by
    simpa [prefixWord, tailWord_6457846, baseEnd_6457846] using wordTrace_append hprefix tailTrace_6457846
  have hstable : (prefixWord ++ tailWord_6457846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457846).length < 2 ^ (prefixWord ++ tailWord_6457846).sum := by decide
  have hdescent : baseEnd_6457846 < baseStart_6457846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457863 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_6457863 : Nat := 118140960795 + 6457863 * 2 ^ 59
def prefixEnd_6457863 : Nat := 4983230072969 + 3 ^ 40 * 6457863 * 2
def baseEnd_6457863 : Nat := 3315987719886172315013335

theorem tailTrace_6457863 : CollatzResearch.WordTrace tailWord_6457863 prefixEnd_6457863 3315987719886172315013335 := by
  unfold tailWord_6457863
  simp only [CollatzResearch.WordTrace]
  refine ⟨235537613803272741037946243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157025075868848494025297495 235537613803272741037946243)
  ·
    refine ⟨353306420704909111556919365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235537613803272741037946243 353306420704909111556919365)
    ·
      refine ⟨66244953882170458416922381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353306420704909111556919365 66244953882170458416922381)
      ·
        refine ⟨24841857705813921906345893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66244953882170458416922381 24841857705813921906345893)
        ·
          refine ⟨4657848319840110357439855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24841857705813921906345893 4657848319840110357439855)
          ·
            refine ⟨6986772479760165536159783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657848319840110357439855 6986772479760165536159783)
            ·
              refine ⟨10480158719640248304239675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986772479760165536159783 10480158719640248304239675)
              ·
                refine ⟨15720238079460372456359513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480158719640248304239675 15720238079460372456359513)
                ·
                  refine ⟨11790178559595279342269635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15720238079460372456359513 11790178559595279342269635)
                  ·
                    refine ⟨17685267839392919013404453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11790178559595279342269635 17685267839392919013404453)
                    ·
                      refine ⟨3315987719886172315013335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17685267839392919013404453 3315987719886172315013335)
                      ·
                        rfl

theorem cell23_6457863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_6457863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457863 prefixEnd_6457863 := by exact prefixLift 6457863
  have htrace : WordTrace (prefixWord ++ tailWord_6457863) baseStart_6457863 baseEnd_6457863 := by
    simpa [prefixWord, tailWord_6457863, baseEnd_6457863] using wordTrace_append hprefix tailTrace_6457863
  have hstable : (prefixWord ++ tailWord_6457863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457863).length < 2 ^ (prefixWord ++ tailWord_6457863).sum := by decide
  have hdescent : baseEnd_6457863 < baseStart_6457863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457916 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_6457916 : Nat := 118140960795 + 6457916 * 2 ^ 59
def prefixEnd_6457916 : Nat := 4983230072969 + 3 ^ 40 * 6457916 * 2
def baseEnd_6457916 : Nat := 1105338311453620202550197

theorem tailTrace_6457916 : CollatzResearch.WordTrace tailWord_6457916 prefixEnd_6457916 1105338311453620202550197 := by
  unfold tailWord_6457916
  simp only [CollatzResearch.WordTrace]
  refine ⟨117769773436040365544812801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157026364581387154059750401 117769773436040365544812801)
  ·
    refine ⟨88327330077030274158609601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117769773436040365544812801 88327330077030274158609601)
    ·
      refine ⟨66245497557772705618957201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88327330077030274158609601 66245497557772705618957201)
      ·
        refine ⟨49684123168329529214217901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66245497557772705618957201 49684123168329529214217901)
        ·
          refine ⟨18631546188123573455331713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49684123168329529214217901 18631546188123573455331713)
          ·
            refine ⟨13973659641092680091498785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18631546188123573455331713 13973659641092680091498785)
            ·
              refine ⟨10480244730819510068624089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13973659641092680091498785 10480244730819510068624089)
              ·
                refine ⟨7860183548114632551468067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10480244730819510068624089 7860183548114632551468067)
                ·
                  refine ⟨11790275322171948827202101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7860183548114632551468067 11790275322171948827202101)
                  ·
                    refine ⟨1105338311453620202550197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11790275322171948827202101 1105338311453620202550197)
                    ·
                      rfl

theorem cell23_6457916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_6457916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457916 prefixEnd_6457916 := by exact prefixLift 6457916
  have htrace : WordTrace (prefixWord ++ tailWord_6457916) baseStart_6457916 baseEnd_6457916 := by
    simpa [prefixWord, tailWord_6457916, baseEnd_6457916] using wordTrace_append hprefix tailTrace_6457916
  have hstable : (prefixWord ++ tailWord_6457916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457916).length < 2 ^ (prefixWord ++ tailWord_6457916).sum := by decide
  have hdescent : baseEnd_6457916 < baseStart_6457916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457919 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 2, 6, 2]
def baseStart_6457919 : Nat := 118140960795 + 6457919 * 2 ^ 59
def prefixEnd_6457919 : Nat := 4983230072969 + 3 ^ 40 * 6457919 * 2
def baseEnd_6457919 : Nat := 3316016474802824095913077

theorem tailTrace_6457919 : CollatzResearch.WordTrace tailWord_6457919 prefixEnd_6457919 3316016474802824095913077 := by
  unfold tailWord_6457919
  simp only [CollatzResearch.WordTrace]
  refine ⟨235539656291069862601984811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157026437527379908401323207 235539656291069862601984811)
  ·
    refine ⟨353309484436604793902977217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235539656291069862601984811 353309484436604793902977217)
    ·
      refine ⟨264982113327453595427232913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353309484436604793902977217 264982113327453595427232913)
      ·
        refine ⟨198736584995590196570424685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264982113327453595427232913 198736584995590196570424685)
        ·
          refine ⟨74526219373346323713909257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198736584995590196570424685 74526219373346323713909257)
          ·
            refine ⟨55894664530009742785431943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74526219373346323713909257 55894664530009742785431943)
            ·
              refine ⟨83841996795014614178147915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55894664530009742785431943 83841996795014614178147915)
              ·
                refine ⟨125762995192521921267221873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83841996795014614178147915 125762995192521921267221873)
                ·
                  refine ⟨94322246394391440950416405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125762995192521921267221873 94322246394391440950416405)
                  ·
                    refine ⟨4421355299737098794550769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94322246394391440950416405 4421355299737098794550769)
                    ·
                      refine ⟨3316016474802824095913077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421355299737098794550769 3316016474802824095913077)
                      ·
                        rfl

theorem cell23_6457919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_6457919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457919 prefixEnd_6457919 := by exact prefixLift 6457919
  have htrace : WordTrace (prefixWord ++ tailWord_6457919) baseStart_6457919 baseEnd_6457919 := by
    simpa [prefixWord, tailWord_6457919, baseEnd_6457919] using wordTrace_append hprefix tailTrace_6457919
  have hstable : (prefixWord ++ tailWord_6457919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457919).length < 2 ^ (prefixWord ++ tailWord_6457919).sum := by decide
  have hdescent : baseEnd_6457919 < baseStart_6457919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457924 : List Nat := [2, 3, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6457924 : Nat := 118140960795 + 6457924 * 2 ^ 59
def prefixEnd_6457924 : Nat := 4983230072969 + 3 ^ 40 * 6457924 * 2
def baseEnd_6457924 : Nat := 1105339680735365525450185

theorem tailTrace_6457924 : CollatzResearch.WordTrace tailWord_6457924 prefixEnd_6457924 1105339680735365525450185 := by
  unfold tailWord_6457924
  simp only [CollatzResearch.WordTrace]
  refine ⟨117769919328025874227958413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157026559104034498970611217 117769919328025874227958413)
  ·
    refine ⟨44163719748009702835484405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117769919328025874227958413 44163719748009702835484405)
    ·
      refine ⟨4140348726375909640826663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44163719748009702835484405 4140348726375909640826663)
      ·
        refine ⟨6210523089563864461239995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140348726375909640826663 6210523089563864461239995)
        ·
          refine ⟨9315784634345796691859993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210523089563864461239995 9315784634345796691859993)
          ·
            refine ⟨6986838475759347518894995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9315784634345796691859993 6986838475759347518894995)
            ·
              refine ⟨10480257713639021278342493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986838475759347518894995 10480257713639021278342493)
              ·
                refine ⟨3930096642614632979378435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10480257713639021278342493 3930096642614632979378435)
                ·
                  refine ⟨5895144963921949469067653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930096642614632979378435 5895144963921949469067653)
                  ·
                    refine ⟨1105339680735365525450185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5895144963921949469067653 1105339680735365525450185)
                    ·
                      rfl

theorem cell23_6457924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6457924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457924 prefixEnd_6457924 := by exact prefixLift 6457924
  have htrace : WordTrace (prefixWord ++ tailWord_6457924) baseStart_6457924 baseEnd_6457924 := by
    simpa [prefixWord, tailWord_6457924, baseEnd_6457924] using wordTrace_append hprefix tailTrace_6457924
  have hstable : (prefixWord ++ tailWord_6457924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457924).length < 2 ^ (prefixWord ++ tailWord_6457924).sum := by decide
  have hdescent : baseEnd_6457924 < baseStart_6457924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457930 : List Nat := [3, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_6457930 : Nat := 118140960795 + 6457930 * 2 ^ 59
def prefixEnd_6457930 : Nat := 4983230072969 + 3 ^ 40 * 6457930 * 2
def baseEnd_6457930 : Nat := 3316022123090023552875527

theorem tailTrace_6457930 : CollatzResearch.WordTrace tailWord_6457930 prefixEnd_6457930 3316022123090023552875527 := by
  unfold tailWord_6457930
  simp only [CollatzResearch.WordTrace]
  refine ⟨58885014373507502870158811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157026704996020007653756829 58885014373507502870158811)
  ·
    refine ⟨88327521560261254305238217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58885014373507502870158811 88327521560261254305238217)
    ·
      refine ⟨66245641170195940728928663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88327521560261254305238217 66245641170195940728928663)
      ·
        refine ⟨99368461755293911093392995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66245641170195940728928663 99368461755293911093392995)
        ·
          refine ⟨149052692632940866640089493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99368461755293911093392995 149052692632940866640089493)
          ·
            refine ⟨6986844967169103123754195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149052692632940866640089493 6986844967169103123754195)
            ·
              refine ⟨10480267450753654685631293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986844967169103123754195 10480267450753654685631293)
              ·
                refine ⟨3930100294032620507111735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10480267450753654685631293 3930100294032620507111735)
                ·
                  refine ⟨5895150441048930760667603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930100294032620507111735 5895150441048930760667603)
                  ·
                    refine ⟨8842725661573396141001405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5895150441048930760667603 8842725661573396141001405)
                    ·
                      refine ⟨3316022123090023552875527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8842725661573396141001405 3316022123090023552875527)
                      ·
                        rfl

theorem cell23_6457930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_6457930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457930 prefixEnd_6457930 := by exact prefixLift 6457930
  have htrace : WordTrace (prefixWord ++ tailWord_6457930) baseStart_6457930 baseEnd_6457930 := by
    simpa [prefixWord, tailWord_6457930, baseEnd_6457930] using wordTrace_append hprefix tailTrace_6457930
  have hstable : (prefixWord ++ tailWord_6457930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457930).length < 2 ^ (prefixWord ++ tailWord_6457930).sum := by decide
  have hdescent : baseEnd_6457930 < baseStart_6457930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457953 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_6457953 : Nat := 118140960795 + 6457953 * 2 ^ 59
def prefixEnd_6457953 : Nat := 4983230072969 + 3 ^ 40 * 6457953 * 2
def baseEnd_6457953 : Nat := 3316033933145076962887921

theorem tailTrace_6457953 : CollatzResearch.WordTrace tailWord_6457953 prefixEnd_6457953 3316033933145076962887921 := by
  unfold tailWord_6457953
  simp only [CollatzResearch.WordTrace]
  refine ⟨235540896372946686408722513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157027264248631124272481675 235540896372946686408722513)
  ·
    refine ⟨176655672279710014806541885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235540896372946686408722513 176655672279710014806541885)
    ·
      refine ⟨66245877104891255552453207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176655672279710014806541885 66245877104891255552453207)
      ·
        refine ⟨99368815657336883328679811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66245877104891255552453207 99368815657336883328679811)
        ·
          refine ⟨149053223486005324993019717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99368815657336883328679811 149053223486005324993019717)
          ·
            refine ⟨27947479403625998436191197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149053223486005324993019717 27947479403625998436191197)
            ·
              refine ⟨10480304776359749413571699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27947479403625998436191197 10480304776359749413571699)
              ·
                refine ⟨15720457164539624120357549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480304776359749413571699 15720457164539624120357549)
                ·
                  refine ⟨5895171436702359045134081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15720457164539624120357549 5895171436702359045134081)
                  ·
                    refine ⟨4421378577526769283850561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5895171436702359045134081 4421378577526769283850561)
                    ·
                      refine ⟨3316033933145076962887921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421378577526769283850561 3316033933145076962887921)
                      ·
                        rfl

theorem cell23_6457953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_6457953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457953 prefixEnd_6457953 := by exact prefixLift 6457953
  have htrace : WordTrace (prefixWord ++ tailWord_6457953) baseStart_6457953 baseEnd_6457953 := by
    simpa [prefixWord, tailWord_6457953, baseEnd_6457953] using wordTrace_append hprefix tailTrace_6457953
  have hstable : (prefixWord ++ tailWord_6457953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457953).length < 2 ^ (prefixWord ++ tailWord_6457953).sum := by decide
  have hdescent : baseEnd_6457953 < baseStart_6457953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457970 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_6457970 : Nat := 118140960795 + 6457970 * 2 ^ 59
def prefixEnd_6457970 : Nat := 4983230072969 + 3 ^ 40 * 6457970 * 2
def baseEnd_6457970 : Nat := 3316042662316203396375343

theorem tailTrace_6457970 : CollatzResearch.WordTrace tailWord_6457970 prefixEnd_6457970 3316042662316203396375343 := by
  unfold tailWord_6457970
  simp only [CollatzResearch.WordTrace]
  refine ⟨58885379103471274578022841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157027677609256732208060909 58885379103471274578022841)
  ·
    refine ⟨44164034327603455933517131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58885379103471274578022841 44164034327603455933517131)
    ·
      refine ⟨66246051491405183900275697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44164034327603455933517131 66246051491405183900275697)
      ·
        refine ⟨49684538618553887925206773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66246051491405183900275697 49684538618553887925206773)
        ·
          refine ⟨4657925495489426992988135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49684538618553887925206773 4657925495489426992988135)
          ·
            refine ⟨6986888243234140489482203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657925495489426992988135 6986888243234140489482203)
            ·
              refine ⟨10480332364851210734223305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986888243234140489482203 10480332364851210734223305)
              ·
                refine ⟨7860249273638408050667479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10480332364851210734223305 7860249273638408050667479)
                ·
                  refine ⟨11790373910457612076001219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7860249273638408050667479 11790373910457612076001219)
                  ·
                    refine ⟨17685560865686418114001829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11790373910457612076001219 17685560865686418114001829)
                    ·
                      refine ⟨3316042662316203396375343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17685560865686418114001829 3316042662316203396375343)
                      ·
                        rfl

theorem cell23_6457970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_6457970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457970 prefixEnd_6457970 := by exact prefixLift 6457970
  have htrace : WordTrace (prefixWord ++ tailWord_6457970) baseStart_6457970 baseEnd_6457970 := by
    simpa [prefixWord, tailWord_6457970, baseEnd_6457970] using wordTrace_append hprefix tailTrace_6457970
  have hstable : (prefixWord ++ tailWord_6457970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457970).length < 2 ^ (prefixWord ++ tailWord_6457970).sum := by decide
  have hdescent : baseEnd_6457970 < baseStart_6457970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457973 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6457973 : Nat := 118140960795 + 6457973 * 2 ^ 59
def prefixEnd_6457973 : Nat := 4983230072969 + 3 ^ 40 * 6457973 * 2
def baseEnd_6457973 : Nat := 3316044202758166884637829

theorem tailTrace_6457973 : CollatzResearch.WordTrace tailWord_6457973 prefixEnd_6457973 3316044202758166884637829 := by
  unfold tailWord_6457973
  simp only [CollatzResearch.WordTrace]
  refine ⟨235541625832874229824450573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157027750555249486549633715 235541625832874229824450573)
  ·
    refine ⟨88328109687327836184168965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235541625832874229824450573 88328109687327836184168965)
    ·
      refine ⟨16561520566373969284531681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88328109687327836184168965 16561520566373969284531681)
      ·
        refine ⟨12421140424780476963398761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16561520566373969284531681 12421140424780476963398761)
        ·
          refine ⟨9315855318585357722549071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12421140424780476963398761 9315855318585357722549071)
          ·
            refine ⟨13973782977878036583823607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315855318585357722549071 13973782977878036583823607)
            ·
              refine ⟨20960674466817054875735411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13973782977878036583823607 20960674466817054875735411)
              ·
                refine ⟨31441011700225582313603117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20960674466817054875735411 31441011700225582313603117)
                ·
                  refine ⟨11790379387584593367601169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31441011700225582313603117 11790379387584593367601169)
                  ·
                    refine ⟨8842784540688445025700877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11790379387584593367601169 8842784540688445025700877)
                    ·
                      refine ⟨3316044202758166884637829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8842784540688445025700877 3316044202758166884637829)
                      ·
                        rfl

theorem cell23_6457973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6457973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6457973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6457973 prefixEnd_6457973 := by exact prefixLift 6457973
  have htrace : WordTrace (prefixWord ++ tailWord_6457973) baseStart_6457973 baseEnd_6457973 := by
    simpa [prefixWord, tailWord_6457973, baseEnd_6457973] using wordTrace_append hprefix tailTrace_6457973
  have hstable : (prefixWord ++ tailWord_6457973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457973).length < 2 ^ (prefixWord ++ tailWord_6457973).sum := by decide
  have hdescent : baseEnd_6457973 < baseStart_6457973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458004 : List Nat := [2, 4, 2, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_6458004 : Nat := 118140960795 + 6458004 * 2 ^ 59
def prefixEnd_6458004 : Nat := 4983230072969 + 3 ^ 40 * 6458004 * 2
def baseEnd_6458004 : Nat := 3316060120658456263350187

theorem tailTrace_6458004 : CollatzResearch.WordTrace tailWord_6458004 prefixEnd_6458004 3316060120658456263350187 := by
  unfold tailWord_6458004
  simp only [CollatzResearch.WordTrace]
  refine ⟨117771378247880961059414533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157028504330507948079219377 117771378247880961059414533)
  ·
    refine ⟨22082133421477680198640225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117771378247880961059414533 22082133421477680198640225)
    ·
      refine ⟨16561600066108260148980169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22082133421477680198640225 16561600066108260148980169)
      ·
        refine ⟨12421200049581195111735127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16561600066108260148980169 12421200049581195111735127)
        ·
          refine ⟨18631800074371792667602691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12421200049581195111735127 18631800074371792667602691)
          ·
            refine ⟨27947700111557689001404037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18631800074371792667602691 27947700111557689001404037)
            ·
              refine ⟨5240193770917066687763257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27947700111557689001404037 5240193770917066687763257)
              ·
                refine ⟨3930145328187800015822443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5240193770917066687763257 3930145328187800015822443)
                ·
                  refine ⟨5895217992281700023733665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930145328187800015822443 5895217992281700023733665)
                  ·
                    refine ⟨4421413494211275017800249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5895217992281700023733665 4421413494211275017800249)
                    ·
                      refine ⟨3316060120658456263350187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421413494211275017800249 3316060120658456263350187)
                      ·
                        rfl

theorem cell23_6458004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_6458004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458004 prefixEnd_6458004 := by exact prefixLift 6458004
  have htrace : WordTrace (prefixWord ++ tailWord_6458004) baseStart_6458004 baseEnd_6458004 := by
    simpa [prefixWord, tailWord_6458004, baseEnd_6458004] using wordTrace_append hprefix tailTrace_6458004
  have hstable : (prefixWord ++ tailWord_6458004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458004).length < 2 ^ (prefixWord ++ tailWord_6458004).sum := by decide
  have hdescent : baseEnd_6458004 < baseStart_6458004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458030 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6458030 : Nat := 118140960795 + 6458030 * 2 ^ 59
def prefixEnd_6458030 : Nat := 4983230072969 + 3 ^ 40 * 6458030 * 2
def baseEnd_6458030 : Nat := 3316073471155473161625067

theorem tailTrace_6458030 : CollatzResearch.WordTrace tailWord_6458030 prefixEnd_6458030 3316073471155473161625067 := by
  unfold tailWord_6458030
  simp only [CollatzResearch.WordTrace]
  refine ⟨29442963099208466069909443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157029136529111819039517029 29442963099208466069909443)
  ·
    refine ⟨44164444648812699104864165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29442963099208466069909443 44164444648812699104864165)
    ·
      refine ⟨8280833371652381082162031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44164444648812699104864165 8280833371652381082162031)
      ·
        refine ⟨12421250057478571623243047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8280833371652381082162031 12421250057478571623243047)
        ·
          refine ⟨18631875086217857434864571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12421250057478571623243047 18631875086217857434864571)
          ·
            refine ⟨27947812629326786152296857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18631875086217857434864571 27947812629326786152296857)
            ·
              refine ⟨20960859471995089614222643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27947812629326786152296857 20960859471995089614222643)
              ·
                refine ⟨31441289207992634421333965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20960859471995089614222643 31441289207992634421333965)
                ·
                  refine ⟨11790483452997237908000237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31441289207992634421333965 11790483452997237908000237)
                  ·
                    refine ⟨4421431294873964215500089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11790483452997237908000237 4421431294873964215500089)
                    ·
                      refine ⟨3316073471155473161625067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421431294873964215500089 3316073471155473161625067)
                      ·
                        rfl

theorem cell23_6458030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6458030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458030 prefixEnd_6458030 := by exact prefixLift 6458030
  have htrace : WordTrace (prefixWord ++ tailWord_6458030) baseStart_6458030 baseEnd_6458030 := by
    simpa [prefixWord, tailWord_6458030, baseEnd_6458030] using wordTrace_append hprefix tailTrace_6458030
  have hstable : (prefixWord ++ tailWord_6458030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458030).length < 2 ^ (prefixWord ++ tailWord_6458030).sum := by decide
  have hdescent : baseEnd_6458030 < baseStart_6458030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458060 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6458060 : Nat := 118140960795 + 6458060 * 2 ^ 59
def prefixEnd_6458060 : Nat := 4983230072969 + 3 ^ 40 * 6458060 * 2
def baseEnd_6458060 : Nat := 3316088875575108044249929

theorem tailTrace_6458060 : CollatzResearch.WordTrace tailWord_6458060 prefixEnd_6458060 3316088875575108044249929 := by
  unfold tailWord_6458060
  simp only [CollatzResearch.WordTrace]
  refine ⟨117772399491779521841433817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157029865989039362455245089 117772399491779521841433817)
  ·
    refine ⟨88329299618834641381075363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117772399491779521841433817 88329299618834641381075363)
    ·
      refine ⟨132493949428251962071613045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88329299618834641381075363 132493949428251962071613045)
      ·
        refine ⟨12421307758898621444213723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132493949428251962071613045 12421307758898621444213723)
        ·
          refine ⟨18631961638347932166320585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12421307758898621444213723 18631961638347932166320585)
          ·
            refine ⟨13973971228760949124740439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18631961638347932166320585 13973971228760949124740439)
            ·
              refine ⟨20960956843141423687110659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13973971228760949124740439 20960956843141423687110659)
              ·
                refine ⟨31441435264712135530665989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20960956843141423687110659 31441435264712135530665989)
                ·
                  refine ⟨5895269112133525411999873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31441435264712135530665989 5895269112133525411999873)
                  ·
                    refine ⟨4421451834100144058999905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5895269112133525411999873 4421451834100144058999905)
                    ·
                      refine ⟨3316088875575108044249929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421451834100144058999905 3316088875575108044249929)
                      ·
                        rfl

theorem cell23_6458060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6458060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458060 prefixEnd_6458060 := by exact prefixLift 6458060
  have htrace : WordTrace (prefixWord ++ tailWord_6458060) baseStart_6458060 baseEnd_6458060 := by
    simpa [prefixWord, tailWord_6458060, baseEnd_6458060] using wordTrace_append hprefix tailTrace_6458060
  have hstable : (prefixWord ++ tailWord_6458060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458060).length < 2 ^ (prefixWord ++ tailWord_6458060).sum := by decide
  have hdescent : baseEnd_6458060 < baseStart_6458060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458079 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 1, 7]
def baseStart_6458079 : Nat := 118140960795 + 6458079 * 2 ^ 59
def prefixEnd_6458079 : Nat := 4983230072969 + 3 ^ 40 * 6458079 * 2
def baseEnd_6458079 : Nat := 1105366210569181156637447

theorem tailTrace_6458079 : CollatzResearch.WordTrace tailWord_6458079 prefixEnd_6458079 1105366210569181156637447 := by
  unfold tailWord_6458079
  simp only [CollatzResearch.WordTrace]
  refine ⟨235545491970490209927809291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157030327980326806618539527 235545491970490209927809291)
  ·
    refine ⟨353318237955735314891713937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235545491970490209927809291 353318237955735314891713937)
    ·
      refine ⟨264988678466801486168785453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353318237955735314891713937 264988678466801486168785453)
      ·
        refine ⟨99370754425050557313294545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264988678466801486168785453 99370754425050557313294545)
        ·
          refine ⟨74528065818787917984970909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99370754425050557313294545 74528065818787917984970909)
          ·
            refine ⟨27948024682045469244364091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74528065818787917984970909 27948024682045469244364091)
            ·
              refine ⟨41922037023068203866546137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27948024682045469244364091 41922037023068203866546137)
              ·
                refine ⟨31441527767301152899909603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41922037023068203866546137 31441527767301152899909603)
                ·
                  refine ⟨47162291650951729349864405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31441527767301152899909603 47162291650951729349864405)
                  ·
                    refine ⟨1105366210569181156637447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47162291650951729349864405 1105366210569181156637447)
                    ·
                      rfl

theorem cell23_6458079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_6458079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458079 prefixEnd_6458079 := by exact prefixLift 6458079
  have htrace : WordTrace (prefixWord ++ tailWord_6458079) baseStart_6458079 baseEnd_6458079 := by
    simpa [prefixWord, tailWord_6458079, baseEnd_6458079] using wordTrace_append hprefix tailTrace_6458079
  have hstable : (prefixWord ++ tailWord_6458079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458079).length < 2 ^ (prefixWord ++ tailWord_6458079).sum := by decide
  have hdescent : baseEnd_6458079 < baseStart_6458079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458129 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_6458129 : Nat := 118140960795 + 6458129 * 2 ^ 59
def prefixEnd_6458129 : Nat := 4983230072969 + 3 ^ 40 * 6458129 * 2
def baseEnd_6458129 : Nat := 3316124305740268274287111

theorem tailTrace_6458129 : CollatzResearch.WordTrace tailWord_6458129 prefixEnd_6458129 3316124305740268274287111 := by
  unfold tailWord_6458129
  simp only [CollatzResearch.WordTrace]
  refine ⟨235547315620309068467129441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157031543746872712311419627 235547315620309068467129441)
  ·
    refine ⟨176660486715231801350347081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235547315620309068467129441 176660486715231801350347081)
    ·
      refine ⟨132495365036423851012760311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176660486715231801350347081 132495365036423851012760311)
      ·
        refine ⟨198743047554635776519140467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132495365036423851012760311 198743047554635776519140467)
        ·
          refine ⟨298114571331953664778710701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198743047554635776519140467 298114571331953664778710701)
          ·
            refine ⟨111792964249482624292016513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298114571331953664778710701 111792964249482624292016513)
            ·
              refine ⟨83844723187111968219012385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111792964249482624292016513 83844723187111968219012385)
              ·
                refine ⟨62883542390333976164259289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83844723187111968219012385 62883542390333976164259289)
                ·
                  refine ⟨47162656792750482123194467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62883542390333976164259289 47162656792750482123194467)
                  ·
                    refine ⟨70743985189125723184791701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47162656792750482123194467 70743985189125723184791701)
                    ·
                      refine ⟨3316124305740268274287111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70743985189125723184791701 3316124305740268274287111)
                      ·
                        rfl

theorem cell23_6458129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_6458129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458129 prefixEnd_6458129 := by exact prefixLift 6458129
  have htrace : WordTrace (prefixWord ++ tailWord_6458129) baseStart_6458129 baseEnd_6458129 := by
    simpa [prefixWord, tailWord_6458129, baseEnd_6458129] using wordTrace_append hprefix tailTrace_6458129
  have hstable : (prefixWord ++ tailWord_6458129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458129).length < 2 ^ (prefixWord ++ tailWord_6458129).sum := by decide
  have hdescent : baseEnd_6458129 < baseStart_6458129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458136 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_6458136 : Nat := 118140960795 + 6458136 * 2 ^ 59
def prefixEnd_6458136 : Nat := 4983230072969 + 3 ^ 40 * 6458136 * 2
def baseEnd_6458136 : Nat := 3316127900104849746899579

theorem tailTrace_6458136 : CollatzResearch.WordTrace tailWord_6458136 prefixEnd_6458136 3316127900104849746899579 := by
  unfold tailWord_6458136
  simp only [CollatzResearch.WordTrace]
  refine ⟨117773785465641854331317131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157031713954189139108422841 117773785465641854331317131)
  ·
    refine ⟨176660678198462781496975697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117773785465641854331317131 176660678198462781496975697)
    ·
      refine ⟨132495508648847086122731773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176660678198462781496975697 132495508648847086122731773)
      ·
        refine ⟨49685815743317657296024415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132495508648847086122731773 49685815743317657296024415)
        ·
          refine ⟨74528723614976485944036623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49685815743317657296024415 74528723614976485944036623)
          ·
            refine ⟨111793085422464728916054935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74528723614976485944036623 111793085422464728916054935)
            ·
              refine ⟨167689628133697093374082403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111793085422464728916054935 167689628133697093374082403)
              ·
                refine ⟨251534442200545640061123605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167689628133697093374082403 251534442200545640061123605)
                ·
                  refine ⟨11790676978150576877865169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 251534442200545640061123605 11790676978150576877865169)
                  ·
                    refine ⟨8843007733612932658398877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11790676978150576877865169 8843007733612932658398877)
                    ·
                      refine ⟨3316127900104849746899579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8843007733612932658398877 3316127900104849746899579)
                      ·
                        rfl

theorem cell23_6458136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_6458136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458136 prefixEnd_6458136 := by exact prefixLift 6458136
  have htrace : WordTrace (prefixWord ++ tailWord_6458136) baseStart_6458136 baseEnd_6458136 := by
    simpa [prefixWord, tailWord_6458136, baseEnd_6458136] using wordTrace_append hprefix tailTrace_6458136
  have hstable : (prefixWord ++ tailWord_6458136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458136).length < 2 ^ (prefixWord ++ tailWord_6458136).sum := by decide
  have hdescent : baseEnd_6458136 < baseStart_6458136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458183 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_6458183 : Nat := 118140960795 + 6458183 * 2 ^ 59
def prefixEnd_6458183 : Nat := 4983230072969 + 3 ^ 40 * 6458183 * 2
def baseEnd_6458183 : Nat := 3316152033695611063011863

theorem tailTrace_6458183 : CollatzResearch.WordTrace tailWord_6458183 prefixEnd_6458183 3316152033695611063011863 := by
  unfold tailWord_6458183
  simp only [CollatzResearch.WordTrace]
  refine ⟨235549285162113435689595203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157032856774742290459730135 235549285162113435689595203)
  ·
    refine ⟨353323927743170153534392805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235549285162113435689595203 353323927743170153534392805)
    ·
      refine ⟨66248236451844403787698651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353323927743170153534392805 66248236451844403787698651)
      ·
        refine ⟨99372354677766605681547977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66248236451844403787698651 99372354677766605681547977)
        ·
          refine ⟨74529266008324954261160983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99372354677766605681547977 74529266008324954261160983)
          ·
            refine ⟨111793899012487431391741475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74529266008324954261160983 111793899012487431391741475)
            ·
              refine ⟨167690848518731147087612213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111793899012487431391741475 167690848518731147087612213)
              ·
                refine ⟨15721017048631045039463645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167690848518731147087612213 15721017048631045039463645)
                ·
                  refine ⟨5895381393236641889798867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15721017048631045039463645 5895381393236641889798867)
                  ·
                    refine ⟨8843072089854962834698301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5895381393236641889798867 8843072089854962834698301)
                    ·
                      refine ⟨3316152033695611063011863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8843072089854962834698301 3316152033695611063011863)
                      ·
                        rfl

theorem cell23_6458183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_6458183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458183 prefixEnd_6458183 := by exact prefixLift 6458183
  have htrace : WordTrace (prefixWord ++ tailWord_6458183) baseStart_6458183 baseEnd_6458183 := by
    simpa [prefixWord, tailWord_6458183, baseEnd_6458183] using wordTrace_append hprefix tailTrace_6458183
  have hstable : (prefixWord ++ tailWord_6458183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458183).length < 2 ^ (prefixWord ++ tailWord_6458183).sum := by decide
  have hdescent : baseEnd_6458183 < baseStart_6458183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458233 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 4, 4]
def baseStart_6458233 : Nat := 118140960795 + 6458233 * 2 ^ 59
def prefixEnd_6458233 : Nat := 4983230072969 + 3 ^ 40 * 6458233 * 2
def baseEnd_6458233 : Nat := 1105392569242778622462211

theorem tailTrace_6458233 : CollatzResearch.WordTrace tailWord_6458233 prefixEnd_6458233 1105392569242778622462211 := by
  unfold tailWord_6458233
  simp only [CollatzResearch.WordTrace]
  refine ⟨235551108811932294228915353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157034072541288196152610235 235551108811932294228915353)
  ·
    refine ⟨176663331608949220671686515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235551108811932294228915353 176663331608949220671686515)
    ·
      refine ⟨264994997413423831007529773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176663331608949220671686515 264994997413423831007529773)
      ·
        refine ⟨99373124030033936627823665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264994997413423831007529773 99373124030033936627823665)
        ·
          refine ⟨74529843022525452470867749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99373124030033936627823665 74529843022525452470867749)
          ·
            refine ⟨13974345566723522338287703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74529843022525452470867749 13974345566723522338287703)
            ·
              refine ⟨20961518350085283507431555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13974345566723522338287703 20961518350085283507431555)
              ·
                refine ⟨31442277525127925261147333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20961518350085283507431555 31442277525127925261147333)
                ·
                  refine ⟨5895427035961485986465125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31442277525127925261147333 5895427035961485986465125)
                  ·
                    refine ⟨1105392569242778622462211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5895427035961485986465125 1105392569242778622462211)
                    ·
                      rfl

theorem cell23_6458233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_6458233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458233 prefixEnd_6458233 := by exact prefixLift 6458233
  have htrace : WordTrace (prefixWord ++ tailWord_6458233) baseStart_6458233 baseEnd_6458233 := by
    simpa [prefixWord, tailWord_6458233, baseEnd_6458233] using wordTrace_append hprefix tailTrace_6458233
  have hstable : (prefixWord ++ tailWord_6458233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458233).length < 2 ^ (prefixWord ++ tailWord_6458233).sum := by decide
  have hdescent : baseEnd_6458233 < baseStart_6458233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458236 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_6458236 : Nat := 118140960795 + 6458236 * 2 ^ 59
def prefixEnd_6458236 : Nat := 4983230072969 + 3 ^ 40 * 6458236 * 2
def baseEnd_6458236 : Nat := 3316179248170299355649119

theorem tailTrace_6458236 : CollatzResearch.WordTrace tailWord_6458236 prefixEnd_6458236 3316179248170299355649119 := by
  unfold tailWord_6458236
  simp only [CollatzResearch.WordTrace]
  refine ⟨117775609115460712870637281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157034145487280950494183041 117775609115460712870637281)
  ·
    refine ⟨88331706836595534652977961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117775609115460712870637281 88331706836595534652977961)
    ·
      refine ⟨66248780127446650989733471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88331706836595534652977961 66248780127446650989733471)
      ·
        refine ⟨99373170191169976484600207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66248780127446650989733471 99373170191169976484600207)
        ·
          refine ⟨149059755286754964726900311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99373170191169976484600207 149059755286754964726900311)
          ·
            refine ⟨223589632930132447090350467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149059755286754964726900311 223589632930132447090350467)
            ·
              refine ⟨335384449395198670635525701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223589632930132447090350467 335384449395198670635525701)
              ·
                refine ⟨62884584261599750744161069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335384449395198670635525701 62884584261599750744161069)
                ·
                  refine ⟨23581719098099906529060401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62884584261599750744161069 23581719098099906529060401)
                  ·
                    refine ⟨17686289323574929896795301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23581719098099906529060401 17686289323574929896795301)
                    ·
                      refine ⟨3316179248170299355649119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17686289323574929896795301 3316179248170299355649119)
                      ·
                        rfl

theorem cell23_6458236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_6458236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458236 prefixEnd_6458236 := by exact prefixLift 6458236
  have htrace : WordTrace (prefixWord ++ tailWord_6458236) baseStart_6458236 baseEnd_6458236 := by
    simpa [prefixWord, tailWord_6458236, baseEnd_6458236] using wordTrace_append hprefix tailTrace_6458236
  have hstable : (prefixWord ++ tailWord_6458236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458236).length < 2 ^ (prefixWord ++ tailWord_6458236).sum := by decide
  have hdescent : baseEnd_6458236 < baseStart_6458236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458250 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_6458250 : Nat := 118140960795 + 6458250 * 2 ^ 59
def prefixEnd_6458250 : Nat := 4983230072969 + 3 ^ 40 * 6458250 * 2
def baseEnd_6458250 : Nat := 1105395478966487433624685

theorem tailTrace_6458250 : CollatzResearch.WordTrace tailWord_6458250 prefixEnd_6458250 1105395478966487433624685 := by
  unfold tailWord_6458250
  simp only [CollatzResearch.WordTrace]
  refine ⟨58887932213217676533071051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157034485901913804088189469 58887932213217676533071051)
  ·
    refine ⟨88331898319826514799606577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58887932213217676533071051 88331898319826514799606577)
    ·
      refine ⟨66248923739869886099704933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88331898319826514799606577 66248923739869886099704933)
      ·
        refine ⟨12421673201225603643694675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66248923739869886099704933 12421673201225603643694675)
        ·
          refine ⟨18632509801838405465542013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12421673201225603643694675 18632509801838405465542013)
          ·
            refine ⟨6987191175689402049578255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18632509801838405465542013 6987191175689402049578255)
            ·
              refine ⟨10480786763534103074367383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987191175689402049578255 10480786763534103074367383)
              ·
                refine ⟨15721180145301154611551075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480786763534103074367383 15721180145301154611551075)
                ·
                  refine ⟨23581770217951731917326613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15721180145301154611551075 23581770217951731917326613)
                  ·
                    refine ⟨1105395478966487433624685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23581770217951731917326613 1105395478966487433624685)
                    ·
                      rfl

theorem cell23_6458250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_6458250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458250 prefixEnd_6458250 := by exact prefixLift 6458250
  have htrace : WordTrace (prefixWord ++ tailWord_6458250) baseStart_6458250 baseEnd_6458250 := by
    simpa [prefixWord, tailWord_6458250, baseEnd_6458250] using wordTrace_append hprefix tailTrace_6458250
  have hstable : (prefixWord ++ tailWord_6458250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458250).length < 2 ^ (prefixWord ++ tailWord_6458250).sum := by decide
  have hdescent : baseEnd_6458250 < baseStart_6458250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458330 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2]
def baseStart_6458330 : Nat := 118140960795 + 6458330 * 2 ^ 59
def prefixEnd_6458330 : Nat := 4983230072969 + 3 ^ 40 * 6458330 * 2
def baseEnd_6458330 : Nat := 3316227515351821987873687

theorem tailTrace_6458330 : CollatzResearch.WordTrace tailWord_6458330 prefixEnd_6458330 3316227515351821987873687 := by
  unfold tailWord_6458330
  simp only [CollatzResearch.WordTrace]
  refine ⟨58888661673145219948799111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157036431128387253196797629 58888661673145219948799111)
  ·
    refine ⟨88332992509717829923198667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58888661673145219948799111 88332992509717829923198667)
    ·
      refine ⟨132499488764576744884798001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88332992509717829923198667 132499488764576744884798001)
      ·
        refine ⟨99374616573432558663598501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132499488764576744884798001 99374616573432558663598501)
        ·
          refine ⟨18632740607518604749424719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99374616573432558663598501 18632740607518604749424719)
          ·
            refine ⟨27949110911277907124137079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18632740607518604749424719 27949110911277907124137079)
            ·
              refine ⟨41923666366916860686205619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27949110911277907124137079 41923666366916860686205619)
              ·
                refine ⟨62885499550375291029308429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41923666366916860686205619 62885499550375291029308429)
                ·
                  refine ⟨23582062331390734135990661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62885499550375291029308429 23582062331390734135990661)
                  ·
                    refine ⟨4421636687135762650498249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23582062331390734135990661 4421636687135762650498249)
                    ·
                      refine ⟨3316227515351821987873687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421636687135762650498249 3316227515351821987873687)
                      ·
                        rfl

theorem cell23_6458330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_6458330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458330 prefixEnd_6458330 := by exact prefixLift 6458330
  have htrace : WordTrace (prefixWord ++ tailWord_6458330) baseStart_6458330 baseEnd_6458330 := by
    simpa [prefixWord, tailWord_6458330, baseEnd_6458330] using wordTrace_append hprefix tailTrace_6458330
  have hstable : (prefixWord ++ tailWord_6458330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458330).length < 2 ^ (prefixWord ++ tailWord_6458330).sum := by decide
  have hdescent : baseEnd_6458330 < baseStart_6458330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458357 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6458357 : Nat := 118140960795 + 6458357 * 2 ^ 59
def prefixEnd_6458357 : Nat := 4983230072969 + 3 ^ 40 * 6458357 * 2
def baseEnd_6458357 : Nat := 1105413793109831127412021

theorem tailTrace_6458357 : CollatzResearch.WordTrace tailWord_6458357 prefixEnd_6458357 1105413793109831127412021 := by
  unfold tailWord_6458357
  simp only [CollatzResearch.WordTrace]
  refine ⟨235555631463483063406429325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157037087642322042270952883 235555631463483063406429325)
  ·
    refine ⟨88333361798806148777410997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235555631463483063406429325 88333361798806148777410997)
    ·
      refine ⟨8281252668638076447882281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88333361798806148777410997 8281252668638076447882281)
      ·
        refine ⟨6210939501478557335911711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8281252668638076447882281 6210939501478557335911711)
        ·
          refine ⟨9316409252217836003867567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210939501478557335911711 9316409252217836003867567)
          ·
            refine ⟨13974613878326754005801351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9316409252217836003867567 13974613878326754005801351)
            ·
              refine ⟨20961920817490131008702027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13974613878326754005801351 20961920817490131008702027)
              ·
                refine ⟨31442881226235196513053041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20961920817490131008702027 31442881226235196513053041)
                ·
                  refine ⟨23582160919676397384789781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31442881226235196513053041 23582160919676397384789781)
                  ·
                    refine ⟨1105413793109831127412021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23582160919676397384789781 1105413793109831127412021)
                    ·
                      rfl

theorem cell23_6458357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6458357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458357 prefixEnd_6458357 := by exact prefixLift 6458357
  have htrace : WordTrace (prefixWord ++ tailWord_6458357) baseStart_6458357 baseEnd_6458357 := by
    simpa [prefixWord, tailWord_6458357, baseEnd_6458357] using wordTrace_append hprefix tailTrace_6458357
  have hstable : (prefixWord ++ tailWord_6458357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458357).length < 2 ^ (prefixWord ++ tailWord_6458357).sum := by decide
  have hdescent : baseEnd_6458357 < baseStart_6458357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458440 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_6458440 : Nat := 118140960795 + 6458440 * 2 ^ 59
def prefixEnd_6458440 : Nat := 4983230072969 + 3 ^ 40 * 6458440 * 2
def baseEnd_6458440 : Nat := 3316283998223816557498181

theorem tailTrace_6458440 : CollatzResearch.WordTrace tailWord_6458440 prefixEnd_6458440 3316283998223816557498181 := by
  unfold tailWord_6458440
  simp only [CollatzResearch.WordTrace]
  refine ⟨117779329361091184290850387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157039105814788245721133849 117779329361091184290850387)
  ·
    refine ⟨176668994041636776436275581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117779329361091184290850387 176668994041636776436275581)
    ·
      refine ⟨66250872765613791163603343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176668994041636776436275581 66250872765613791163603343)
      ·
        refine ⟨99376309148420686745405015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66250872765613791163603343 99376309148420686745405015)
        ·
          refine ⟨149064463722631030118107523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99376309148420686745405015 149064463722631030118107523)
          ·
            refine ⟨223596695583946545177161285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149064463722631030118107523 223596695583946545177161285)
            ·
              refine ⟨41924380421989977220717741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223596695583946545177161285 41924380421989977220717741)
              ·
                refine ⟨15721642658246241457769153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41924380421989977220717741 15721642658246241457769153)
                ·
                  refine ⟨11791231993684681093326865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15721642658246241457769153 11791231993684681093326865)
                  ·
                    refine ⟨8843423995263510819995149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11791231993684681093326865 8843423995263510819995149)
                    ·
                      refine ⟨3316283998223816557498181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8843423995263510819995149 3316283998223816557498181)
                      ·
                        rfl

theorem cell23_6458440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_6458440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458440 prefixEnd_6458440 := by exact prefixLift 6458440
  have htrace : WordTrace (prefixWord ++ tailWord_6458440) baseStart_6458440 baseEnd_6458440 := by
    simpa [prefixWord, tailWord_6458440, baseEnd_6458440] using wordTrace_append hprefix tailTrace_6458440
  have hstable : (prefixWord ++ tailWord_6458440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458440).length < 2 ^ (prefixWord ++ tailWord_6458440).sum := by decide
  have hdescent : baseEnd_6458440 < baseStart_6458440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458460 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 6]
def baseStart_6458460 : Nat := 118140960795 + 6458460 * 2 ^ 59
def prefixEnd_6458460 : Nat := 4983230072969 + 3 ^ 40 * 6458460 * 2
def baseEnd_6458460 : Nat := 368477140870767386583121

theorem tailTrace_6458460 : CollatzResearch.WordTrace tailWord_6458460 prefixEnd_6458460 368477140870767386583121 := by
  unfold tailWord_6458460
  simp only [CollatzResearch.WordTrace]
  refine ⟨117779694091054955998714417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157039592121406607998285889 117779694091054955998714417)
  ·
    refine ⟨88334770568291216999035813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117779694091054955998714417 88334770568291216999035813)
    ·
      refine ⟨16562769481554603187319215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88334770568291216999035813 16562769481554603187319215)
      ·
        refine ⟨24844154222331904780978823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16562769481554603187319215 24844154222331904780978823)
        ·
          refine ⟨37266231333497857171468235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24844154222331904780978823 37266231333497857171468235)
          ·
            refine ⟨55899347000246785757202353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37266231333497857171468235 55899347000246785757202353)
            ·
              refine ⟨41924510250185089317901765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55899347000246785757202353 41924510250185089317901765)
              ·
                refine ⟨7860845671909704247106581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41924510250185089317901765 7860845671909704247106581)
                ·
                  refine ⟨368477140870767386583121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7860845671909704247106581 368477140870767386583121)
                  ·
                    rfl

theorem cell23_6458460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_6458460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458460 prefixEnd_6458460 := by exact prefixLift 6458460
  have htrace : WordTrace (prefixWord ++ tailWord_6458460) baseStart_6458460 baseEnd_6458460 := by
    simpa [prefixWord, tailWord_6458460, baseEnd_6458460] using wordTrace_append hprefix tailTrace_6458460
  have hstable : (prefixWord ++ tailWord_6458460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458460).length < 2 ^ (prefixWord ++ tailWord_6458460).sum := by decide
  have hdescent : baseEnd_6458460 < baseStart_6458460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458464 : List Nat := [2, 1, 1, 3, 2, 2, 5, 2, 1, 4]
def baseStart_6458464 : Nat := 118140960795 + 6458464 * 2 ^ 59
def prefixEnd_6458464 : Nat := 4983230072969 + 3 ^ 40 * 6458464 * 2
def baseEnd_6458464 : Nat := 1105432107253174821199357

theorem tailTrace_6458464 : CollatzResearch.WordTrace tailWord_6458464 prefixEnd_6458464 1105432107253174821199357 := by
  unfold tailWord_6458464
  simp only [CollatzResearch.WordTrace]
  refine ⟨117779767037047710340287223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157039689382730280453716297 117779767037047710340287223)
  ·
    refine ⟨176669650555571565510430835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117779767037047710340287223 176669650555571565510430835)
    ·
      refine ⟨265004475833357348265646253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176669650555571565510430835 265004475833357348265646253)
      ·
        refine ⟨99376678437509005599617345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265004475833357348265646253 99376678437509005599617345)
        ·
          refine ⟨74532508828131754199713009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99376678437509005599617345 74532508828131754199713009)
          ·
            refine ⟨55899381621098815649784757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74532508828131754199713009 55899381621098815649784757)
            ·
              refine ⟨5240567026978013967167321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55899381621098815649784757 5240567026978013967167321)
              ·
                refine ⟨3930425270233510475375491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5240567026978013967167321 3930425270233510475375491)
                ·
                  refine ⟨5895637905350265713063237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930425270233510475375491 5895637905350265713063237)
                  ·
                    refine ⟨1105432107253174821199357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5895637905350265713063237 1105432107253174821199357)
                    ·
                      rfl

theorem cell23_6458464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 1, 4].length) (baseStart_6458464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458464 prefixEnd_6458464 := by exact prefixLift 6458464
  have htrace : WordTrace (prefixWord ++ tailWord_6458464) baseStart_6458464 baseEnd_6458464 := by
    simpa [prefixWord, tailWord_6458464, baseEnd_6458464] using wordTrace_append hprefix tailTrace_6458464
  have hstable : (prefixWord ++ tailWord_6458464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458464).length < 2 ^ (prefixWord ++ tailWord_6458464).sum := by decide
  have hdescent : baseEnd_6458464 < baseStart_6458464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458477 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 6]
def baseStart_6458477 : Nat := 118140960795 + 6458477 * 2 ^ 59
def prefixEnd_6458477 : Nat := 4983230072969 + 3 ^ 40 * 6458477 * 2
def baseEnd_6458477 : Nat := 368478110778670323637279

theorem tailTrace_6458477 : CollatzResearch.WordTrace tailWord_6458477 prefixEnd_6458477 368478110778670323637279 := by
  unfold tailWord_6458477
  simp only [CollatzResearch.WordTrace]
  refine ⟨235560008223048323900797685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157040005482032215933865123 235560008223048323900797685)
  ·
    refine ⟨22083750770910780365699783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235560008223048323900797685 22083750770910780365699783)
    ·
      refine ⟨33125626156366170548549675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22083750770910780365699783 33125626156366170548549675)
      ·
        refine ⟨49688439234549255822824513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33125626156366170548549675 49688439234549255822824513)
        ·
          refine ⟨37266329425911941867118385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49688439234549255822824513 37266329425911941867118385)
          ·
            refine ⟨27949747069433956400338789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37266329425911941867118385 27949747069433956400338789)
            ·
              refine ⟨5240577575518866825063523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27949747069433956400338789 5240577575518866825063523)
              ·
                refine ⟨7860866363278300237595285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240577575518866825063523 7860866363278300237595285)
                ·
                  refine ⟨368478110778670323637279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7860866363278300237595285 368478110778670323637279)
                  ·
                    rfl

theorem cell23_6458477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_6458477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458477 prefixEnd_6458477 := by exact prefixLift 6458477
  have htrace : WordTrace (prefixWord ++ tailWord_6458477) baseStart_6458477 baseEnd_6458477 := by
    simpa [prefixWord, tailWord_6458477, baseEnd_6458477] using wordTrace_append hprefix tailTrace_6458477
  have hstable : (prefixWord ++ tailWord_6458477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458477).length < 2 ^ (prefixWord ++ tailWord_6458477).sum := by decide
  have hdescent : baseEnd_6458477 < baseStart_6458477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458514 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_6458514 : Nat := 118140960795 + 6458514 * 2 ^ 59
def prefixEnd_6458514 : Nat := 4983230072969 + 3 ^ 40 * 6458514 * 2
def baseEnd_6458514 : Nat := 3316321995792249267972841

theorem tailTrace_6458514 : CollatzResearch.WordTrace tailWord_6458514 prefixEnd_6458514 3316321995792249267972841 := by
  unfold tailWord_6458514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58890339430978569804973649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157040905149276186146596397 58890339430978569804973649)
  ·
    refine ⟨44167754573233927353730237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58890339430978569804973649 44167754573233927353730237)
    ·
      refine ⟨16562907964962722757648839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44167754573233927353730237 16562907964962722757648839)
      ·
        refine ⟨24844361947444084136473259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16562907964962722757648839 24844361947444084136473259)
        ·
          refine ⟨37266542921166126204709889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24844361947444084136473259 37266542921166126204709889)
          ·
            refine ⟨27949907190874594653532417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37266542921166126204709889 27949907190874594653532417)
            ·
              refine ⟨20962430393155945990149313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27949907190874594653532417 20962430393155945990149313)
              ·
                refine ⟨15721822794866959492611985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20962430393155945990149313 15721822794866959492611985)
                ·
                  refine ⟨11791367096150219619458989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15721822794866959492611985 11791367096150219619458989)
                  ·
                    refine ⟨4421762661056332357297121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11791367096150219619458989 4421762661056332357297121)
                    ·
                      refine ⟨3316321995792249267972841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421762661056332357297121 3316321995792249267972841)
                      ·
                        rfl

theorem cell23_6458514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_6458514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458514 prefixEnd_6458514 := by exact prefixLift 6458514
  have htrace : WordTrace (prefixWord ++ tailWord_6458514) baseStart_6458514 baseEnd_6458514 := by
    simpa [prefixWord, tailWord_6458514, baseEnd_6458514] using wordTrace_append hprefix tailTrace_6458514
  have hstable : (prefixWord ++ tailWord_6458514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458514).length < 2 ^ (prefixWord ++ tailWord_6458514).sum := by decide
  have hdescent : baseEnd_6458514 < baseStart_6458514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458523 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4]
def baseStart_6458523 : Nat := 118140960795 + 6458523 * 2 ^ 59
def prefixEnd_6458523 : Nat := 4983230072969 + 3 ^ 40 * 6458523 * 2
def baseEnd_6458523 : Nat := 3316326617118139732760299

theorem tailTrace_6458523 : CollatzResearch.WordTrace tailWord_6458523 prefixEnd_6458523 3316326617118139732760299 := by
  unfold tailWord_6458523
  simp only [CollatzResearch.WordTrace]
  refine ⟨235561685980881673756972223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157041123987254449171314815 235561685980881673756972223)
  ·
    refine ⟨353342528971322510635458335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235561685980881673756972223 353342528971322510635458335)
    ·
      refine ⟨530013793456983765953187503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353342528971322510635458335 530013793456983765953187503)
      ·
        refine ⟨795020690185475648929781255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530013793456983765953187503 795020690185475648929781255)
        ·
          refine ⟨1192531035278213473394671883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795020690185475648929781255 1192531035278213473394671883)
          ·
            refine ⟨1788796552917320210092007825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192531035278213473394671883 1788796552917320210092007825)
            ·
              refine ⟨1341597414687990157569005869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788796552917320210092007825 1341597414687990157569005869)
              ·
                refine ⟨503099030507996309088377201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1341597414687990157569005869 503099030507996309088377201)
                ·
                  refine ⟨377324272880997231816282901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503099030507996309088377201 377324272880997231816282901)
                  ·
                    refine ⟨17687075291296745241388261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 377324272880997231816282901 17687075291296745241388261)
                    ·
                      refine ⟨3316326617118139732760299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17687075291296745241388261 3316326617118139732760299)
                      ·
                        rfl

theorem cell23_6458523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_6458523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458523 prefixEnd_6458523 := by exact prefixLift 6458523
  have htrace : WordTrace (prefixWord ++ tailWord_6458523) baseStart_6458523 baseEnd_6458523 := by
    simpa [prefixWord, tailWord_6458523, baseEnd_6458523] using wordTrace_append hprefix tailTrace_6458523
  have hstable : (prefixWord ++ tailWord_6458523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458523).length < 2 ^ (prefixWord ++ tailWord_6458523).sum := by decide
  have hdescent : baseEnd_6458523 < baseStart_6458523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458561 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6458561 : Nat := 118140960795 + 6458561 * 2 ^ 59
def prefixEnd_6458561 : Nat := 4983230072969 + 3 ^ 40 * 6458561 * 2
def baseEnd_6458561 : Nat := 3316346129383010584085125

theorem tailTrace_6458561 : CollatzResearch.WordTrace tailWord_6458561 prefixEnd_6458561 3316346129383010584085125 := by
  unfold tailWord_6458561
  simp only [CollatzResearch.WordTrace]
  refine ⟨235563071954744006246855537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157042047969829337497903691 235563071954744006246855537)
  ·
    refine ⟨176672303966058004685141653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235563071954744006246855537 176672303966058004685141653)
    ·
      refine ⟨8281514248408968969616015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176672303966058004685141653 8281514248408968969616015)
      ·
        refine ⟨12422271372613453454424023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8281514248408968969616015 12422271372613453454424023)
        ·
          refine ⟨18633407058920180181636035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12422271372613453454424023 18633407058920180181636035)
          ·
            refine ⟨27950110588380270272454053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18633407058920180181636035 27950110588380270272454053)
            ·
              refine ⟨5240645735321300676085135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27950110588380270272454053 5240645735321300676085135)
              ·
                refine ⟨7860968602981951014127703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240645735321300676085135 7860968602981951014127703)
                ·
                  refine ⟨11791452904472926521191555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7860968602981951014127703 11791452904472926521191555)
                  ·
                    refine ⟨17687179356709389781787333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11791452904472926521191555 17687179356709389781787333)
                    ·
                      refine ⟨3316346129383010584085125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17687179356709389781787333 3316346129383010584085125)
                      ·
                        rfl

theorem cell23_6458561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6458561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458561 prefixEnd_6458561 := by exact prefixLift 6458561
  have htrace : WordTrace (prefixWord ++ tailWord_6458561) baseStart_6458561 baseEnd_6458561 := by
    simpa [prefixWord, tailWord_6458561, baseEnd_6458561] using wordTrace_append hprefix tailTrace_6458561
  have hstable : (prefixWord ++ tailWord_6458561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458561).length < 2 ^ (prefixWord ++ tailWord_6458561).sum := by decide
  have hdescent : baseEnd_6458561 < baseStart_6458561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458563 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 9]
def baseStart_6458563 : Nat := 118140960795 + 6458563 * 2 ^ 59
def prefixEnd_6458563 : Nat := 4983230072969 + 3 ^ 40 * 6458563 * 2
def baseEnd_6458563 : Nat := 1105449052114773192086705

theorem tailTrace_6458563 : CollatzResearch.WordTrace tailWord_6458563 prefixEnd_6458563 1105449052114773192086705 := by
  unfold tailWord_6458563
  simp only [CollatzResearch.WordTrace]
  refine ⟨235563144900736760588428343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157042096600491173725618895 235563144900736760588428343)
  ·
    refine ⟨353344717351105140882642515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235563144900736760588428343 353344717351105140882642515)
    ·
      refine ⟨530017076026657711323963773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353344717351105140882642515 530017076026657711323963773)
      ·
        refine ⟨198756403509996641746486415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530017076026657711323963773 198756403509996641746486415)
        ·
          refine ⟨298134605264994962619729623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198756403509996641746486415 298134605264994962619729623)
          ·
            refine ⟨447201907897492443929594435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298134605264994962619729623 447201907897492443929594435)
            ·
              refine ⟨670802861846238665894391653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447201907897492443929594435 670802861846238665894391653)
              ·
                refine ⟨125775536596169749855198435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 670802861846238665894391653 125775536596169749855198435)
                ·
                  refine ⟨188663304894254624782797653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125775536596169749855198435 188663304894254624782797653)
                  ·
                    refine ⟨1105449052114773192086705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 188663304894254624782797653 1105449052114773192086705)
                    ·
                      rfl

theorem cell23_6458563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 9].length) (baseStart_6458563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458563 prefixEnd_6458563 := by exact prefixLift 6458563
  have htrace : WordTrace (prefixWord ++ tailWord_6458563) baseStart_6458563 baseEnd_6458563 := by
    simpa [prefixWord, tailWord_6458563, baseEnd_6458563] using wordTrace_append hprefix tailTrace_6458563
  have hstable : (prefixWord ++ tailWord_6458563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458563).length < 2 ^ (prefixWord ++ tailWord_6458563).sum := by decide
  have hdescent : baseEnd_6458563 < baseStart_6458563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458604 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 1, 3, 2]
def baseStart_6458604 : Nat := 118140960795 + 6458604 * 2 ^ 59
def prefixEnd_6458604 : Nat := 4983230072969 + 3 ^ 40 * 6458604 * 2
def baseEnd_6458604 : Nat := 3316368209051153915847427

theorem tailTrace_6458604 : CollatzResearch.WordTrace tailWord_6458604 prefixEnd_6458604 3316368209051153915847427 := by
  unfold tailWord_6458604
  simp only [CollatzResearch.WordTrace]
  refine ⟨117782320146794112295335433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157043093529058816393780577 117782320146794112295335433)
  ·
    refine ⟨88336740110095584221501575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117782320146794112295335433 88336740110095584221501575)
    ·
      refine ⟨132505110165143376332252363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88336740110095584221501575 132505110165143376332252363)
      ·
        refine ⟨198757665247715064498378545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132505110165143376332252363 198757665247715064498378545)
        ·
          refine ⟨149068248935786298373783909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198757665247715064498378545 149068248935786298373783909)
          ·
            refine ⟨27950296675459930945084483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149068248935786298373783909 27950296675459930945084483)
            ·
              refine ⟨41925445013189896417626725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27950296675459930945084483 41925445013189896417626725)
              ·
                refine ⟨7861020939973105578305011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41925445013189896417626725 7861020939973105578305011)
                ·
                  refine ⟨11791531409959658367457517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7861020939973105578305011 11791531409959658367457517)
                  ·
                    refine ⟨4421824278734871887796569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11791531409959658367457517 4421824278734871887796569)
                    ·
                      refine ⟨3316368209051153915847427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421824278734871887796569 3316368209051153915847427)
                      ·
                        rfl

theorem cell23_6458604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_6458604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458604 prefixEnd_6458604 := by exact prefixLift 6458604
  have htrace : WordTrace (prefixWord ++ tailWord_6458604) baseStart_6458604 baseEnd_6458604 := by
    simpa [prefixWord, tailWord_6458604, baseEnd_6458604] using wordTrace_append hprefix tailTrace_6458604
  have hstable : (prefixWord ++ tailWord_6458604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458604).length < 2 ^ (prefixWord ++ tailWord_6458604).sum := by decide
  have hdescent : baseEnd_6458604 < baseStart_6458604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458617 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 3, 4, 2]
def baseStart_6458617 : Nat := 118140960795 + 6458617 * 2 ^ 59
def prefixEnd_6458617 : Nat := 4983230072969 + 3 ^ 40 * 6458617 * 2
def baseEnd_6458617 : Nat := 3316374884299662364984867

theorem tailTrace_6458617 : CollatzResearch.WordTrace tailWord_6458617 prefixEnd_6458617 3316374884299662364984867 := by
  unfold tailWord_6458617
  simp only [CollatzResearch.WordTrace]
  refine ⟨235565114442541127810894105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157043409628360751873929403 235565114442541127810894105)
  ·
    refine ⟨176673835831905845858170579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235565114442541127810894105 176673835831905845858170579)
    ·
      refine ⟨265010753747858768787255869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176673835831905845858170579 265010753747858768787255869)
      ·
        refine ⟨99379032655447038295220951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265010753747858768787255869 99379032655447038295220951)
        ·
          refine ⟨149068548983170557442831427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99379032655447038295220951 149068548983170557442831427)
          ·
            refine ⟨223602823474755836164247141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149068548983170557442831427 223602823474755836164247141)
            ·
              refine ⟨41925529401516719280796339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223602823474755836164247141 41925529401516719280796339)
              ·
                refine ⟨62888294102275078921194509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41925529401516719280796339 62888294102275078921194509)
                ·
                  refine ⟨23583110288353154595447941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62888294102275078921194509 23583110288353154595447941)
                  ·
                    refine ⟨4421833179066216486646489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23583110288353154595447941 4421833179066216486646489)
                    ·
                      refine ⟨3316374884299662364984867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421833179066216486646489 3316374884299662364984867)
                      ·
                        rfl

theorem cell23_6458617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_6458617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458617 prefixEnd_6458617 := by exact prefixLift 6458617
  have htrace : WordTrace (prefixWord ++ tailWord_6458617) baseStart_6458617 baseEnd_6458617 := by
    simpa [prefixWord, tailWord_6458617, baseEnd_6458617] using wordTrace_append hprefix tailTrace_6458617
  have hstable : (prefixWord ++ tailWord_6458617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458617).length < 2 ^ (prefixWord ++ tailWord_6458617).sum := by decide
  have hdescent : baseEnd_6458617 < baseStart_6458617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458685 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6458685 : Nat := 118140960795 + 6458685 * 2 ^ 59
def prefixEnd_6458685 : Nat := 4983230072969 + 3 ^ 40 * 6458685 * 2
def baseEnd_6458685 : Nat := 3316409800984168098934555

theorem tailTrace_6458685 : CollatzResearch.WordTrace tailWord_6458685 prefixEnd_6458685 3316409800984168098934555 := by
  unfold tailWord_6458685
  simp only [CollatzResearch.WordTrace]
  refine ⟨235567594606294775424369509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157045063070863183616246339 235567594606294775424369509)
  ·
    refine ⟨44168923988680270392069283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235567594606294775424369509 44168923988680270392069283)
    ·
      refine ⟨66253385983020405588103925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44168923988680270392069283 66253385983020405588103925)
      ·
        refine ⟨6211254935908163023884743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66253385983020405588103925 6211254935908163023884743)
        ·
          refine ⟨9316882403862244535827115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211254935908163023884743 9316882403862244535827115)
          ·
            refine ⟨13975323605793366803740673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9316882403862244535827115 13975323605793366803740673)
            ·
              refine ⟨10481492704345025102805505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13975323605793366803740673 10481492704345025102805505)
              ·
                refine ⟨7861119528258768827104129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10481492704345025102805505 7861119528258768827104129)
                ·
                  refine ⟨5895839646194076620328097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7861119528258768827104129 5895839646194076620328097)
                  ·
                    refine ⟨4421879734645557465246073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5895839646194076620328097 4421879734645557465246073)
                    ·
                      refine ⟨3316409800984168098934555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421879734645557465246073 3316409800984168098934555)
                      ·
                        rfl

theorem cell23_6458685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6458685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458685 prefixEnd_6458685 := by exact prefixLift 6458685
  have htrace : WordTrace (prefixWord ++ tailWord_6458685) baseStart_6458685 baseEnd_6458685 := by
    simpa [prefixWord, tailWord_6458685, baseEnd_6458685] using wordTrace_append hprefix tailTrace_6458685
  have hstable : (prefixWord ++ tailWord_6458685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458685).length < 2 ^ (prefixWord ++ tailWord_6458685).sum := by decide
  have hdescent : baseEnd_6458685 < baseStart_6458685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458687 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 2, 5]
def baseStart_6458687 : Nat := 118140960795 + 6458687 * 2 ^ 59
def prefixEnd_6458687 : Nat := 4983230072969 + 3 ^ 40 * 6458687 * 2
def baseEnd_6458687 : Nat := 1105470275981825697036515

theorem tailTrace_6458687 : CollatzResearch.WordTrace tailWord_6458687 prefixEnd_6458687 1105470275981825697036515 := by
  unfold tailWord_6458687
  simp only [CollatzResearch.WordTrace]
  refine ⟨235567667552287529765942315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157045111701525019843961543 235567667552287529765942315)
  ·
    refine ⟨353351501328431294648913473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235567667552287529765942315 353351501328431294648913473)
    ·
      refine ⟨265013625996323470986685105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353351501328431294648913473 265013625996323470986685105)
      ·
        refine ⟨198760219497242603240013829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265013625996323470986685105 198760219497242603240013829)
        ·
          refine ⟨37267541155732988107502593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198760219497242603240013829 37267541155732988107502593)
          ·
            refine ⟨27950655866799741080626945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37267541155732988107502593 27950655866799741080626945)
            ·
              refine ⟨20962991900099805810470209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27950655866799741080626945 20962991900099805810470209)
              ·
                refine ⟨15722243925074854357852657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20962991900099805810470209 15722243925074854357852657)
                ·
                  refine ⟨11791682943806140768389493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15722243925074854357852657 11791682943806140768389493)
                  ·
                    refine ⟨1105470275981825697036515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11791682943806140768389493 1105470275981825697036515)
                    ·
                      rfl

theorem cell23_6458687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_6458687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458687 prefixEnd_6458687 := by exact prefixLift 6458687
  have htrace : WordTrace (prefixWord ++ tailWord_6458687) baseStart_6458687 baseEnd_6458687 := by
    simpa [prefixWord, tailWord_6458687, baseEnd_6458687] using wordTrace_append hprefix tailTrace_6458687
  have hstable : (prefixWord ++ tailWord_6458687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458687).length < 2 ^ (prefixWord ++ tailWord_6458687).sum := by decide
  have hdescent : baseEnd_6458687 < baseStart_6458687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458724 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_6458724 : Nat := 118140960795 + 6458724 * 2 ^ 59
def prefixEnd_6458724 : Nat := 4983230072969 + 3 ^ 40 * 6458724 * 2
def baseEnd_6458724 : Nat := 3316429826729693446346875

theorem tailTrace_6458724 : CollatzResearch.WordTrace tailWord_6458724 prefixEnd_6458724 3316429826729693446346875 := by
  unfold tailWord_6458724
  simp only [CollatzResearch.WordTrace]
  refine ⟨117784508526576742542519613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157046011368768990056692817 117784508526576742542519613)
  ·
    refine ⟨44169190697466278453444855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117784508526576742542519613 44169190697466278453444855)
    ·
      refine ⟨66253786046199417680167283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44169190697466278453444855 66253786046199417680167283)
      ·
        refine ⟨99380679069299126520250925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66253786046199417680167283 99380679069299126520250925)
        ·
          refine ⟨37267754650987172445094097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99380679069299126520250925 37267754650987172445094097)
          ·
            refine ⟨27950815988240379333820573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37267754650987172445094097 27950815988240379333820573)
            ·
              refine ⟨10481555995590142250182715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27950815988240379333820573 10481555995590142250182715)
              ·
                refine ⟨15722333993385213375274073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10481555995590142250182715 15722333993385213375274073)
                ·
                  refine ⟨11791750495038910031455555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15722333993385213375274073 11791750495038910031455555)
                  ·
                    refine ⟨17687625742558365047183333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11791750495038910031455555 17687625742558365047183333)
                    ·
                      refine ⟨3316429826729693446346875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17687625742558365047183333 3316429826729693446346875)
                      ·
                        rfl

theorem cell23_6458724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_6458724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458724 prefixEnd_6458724 := by exact prefixLift 6458724
  have htrace : WordTrace (prefixWord ++ tailWord_6458724) baseStart_6458724 baseEnd_6458724 := by
    simpa [prefixWord, tailWord_6458724, baseEnd_6458724] using wordTrace_append hprefix tailTrace_6458724
  have hstable : (prefixWord ++ tailWord_6458724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458724).length < 2 ^ (prefixWord ++ tailWord_6458724).sum := by decide
  have hdescent : baseEnd_6458724 < baseStart_6458724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458764 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 6]
def baseStart_6458764 : Nat := 118140960795 + 6458764 * 2 ^ 59
def prefixEnd_6458764 : Nat := 4983230072969 + 3 ^ 40 * 6458764 * 2
def baseEnd_6458764 : Nat := 368494485106208143316299

theorem tailTrace_6458764 : CollatzResearch.WordTrace tailWord_6458764 prefixEnd_6458764 368494485106208143316299 := by
  unfold tailWord_6458764
  simp only [CollatzResearch.WordTrace]
  refine ⟨117785237986504285958247673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157046983982005714610996897 117785237986504285958247673)
  ·
    refine ⟨88338928489878214468685755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117785237986504285958247673 88338928489878214468685755)
    ·
      refine ⟨132508392734817321703028633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88338928489878214468685755 132508392734817321703028633)
      ·
        refine ⟨99381294551112991277271475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132508392734817321703028633 99381294551112991277271475)
        ·
          refine ⟨149071941826669486915907213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99381294551112991277271475 149071941826669486915907213)
          ·
            refine ⟨55901978185001057593465205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149071941826669486915907213 55901978185001057593465205)
            ·
              refine ⟨5240810454843849149387363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55901978185001057593465205 5240810454843849149387363)
              ·
                refine ⟨7861215682265773724081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240810454843849149387363 7861215682265773724081045)
                ·
                  refine ⟨368494485106208143316299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7861215682265773724081045 368494485106208143316299)
                  ·
                    rfl

theorem cell23_6458764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_6458764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458764 prefixEnd_6458764 := by exact prefixLift 6458764
  have htrace : WordTrace (prefixWord ++ tailWord_6458764) baseStart_6458764 baseEnd_6458764 := by
    simpa [prefixWord, tailWord_6458764, baseEnd_6458764] using wordTrace_append hprefix tailTrace_6458764
  have hstable : (prefixWord ++ tailWord_6458764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458764).length < 2 ^ (prefixWord ++ tailWord_6458764).sum := by decide
  have hdescent : baseEnd_6458764 < baseStart_6458764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458784 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 1, 5, 2]
def baseStart_6458784 : Nat := 118140960795 + 6458784 * 2 ^ 59
def prefixEnd_6458784 : Nat := 4983230072969 + 3 ^ 40 * 6458784 * 2
def baseEnd_6458784 : Nat := 3316460635568963211596599

theorem tailTrace_6458784 : CollatzResearch.WordTrace tailWord_6458784 prefixEnd_6458784 3316460635568963211596599 := by
  unfold tailWord_6458784
  simp only [CollatzResearch.WordTrace]
  refine ⟨117785602716468057666111703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157047470288624076888148937 117785602716468057666111703)
  ·
    refine ⟨176678404074702086499167555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117785602716468057666111703 176678404074702086499167555)
    ·
      refine ⟨265017606112053129748751333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176678404074702086499167555 265017606112053129748751333)
      ·
        refine ⟨49690801146009961827890875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265017606112053129748751333 49690801146009961827890875)
        ·
          refine ⟨74536201719014942741836313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49690801146009961827890875 74536201719014942741836313)
          ·
            refine ⟨55902151289261207056377235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74536201719014942741836313 55902151289261207056377235)
            ·
              refine ⟨83853226933891810584565853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55902151289261207056377235 83853226933891810584565853)
              ·
                refine ⟨31444960100209428969212195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83853226933891810584565853 31444960100209428969212195)
                ·
                  refine ⟨47167440150314143453818293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31444960100209428969212195 47167440150314143453818293)
                  ·
                    refine ⟨4421947514091950948795465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47167440150314143453818293 4421947514091950948795465)
                    ·
                      refine ⟨3316460635568963211596599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421947514091950948795465 3316460635568963211596599)
                      ·
                        rfl

theorem cell23_6458784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_6458784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458784 prefixEnd_6458784 := by exact prefixLift 6458784
  have htrace : WordTrace (prefixWord ++ tailWord_6458784) baseStart_6458784 baseEnd_6458784 := by
    simpa [prefixWord, tailWord_6458784, baseEnd_6458784] using wordTrace_append hprefix tailTrace_6458784
  have hstable : (prefixWord ++ tailWord_6458784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458784).length < 2 ^ (prefixWord ++ tailWord_6458784).sum := by decide
  have hdescent : baseEnd_6458784 < baseStart_6458784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458801 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 2, 3, 2]
def baseStart_6458801 : Nat := 118140960795 + 6458801 * 2 ^ 59
def prefixEnd_6458801 : Nat := 4983230072969 + 3 ^ 40 * 6458801 * 2
def baseEnd_6458801 : Nat := 3316469364740089645084021

theorem tailTrace_6458801 : CollatzResearch.WordTrace tailWord_6458801 prefixEnd_6458801 3316469364740089645084021 := by
  unfold tailWord_6458801
  simp only [CollatzResearch.WordTrace]
  refine ⟨235571825473874527235592257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157047883649249684823728171 235571825473874527235592257)
  ·
    refine ⟨176678869105405895426694193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235571825473874527235592257 176678869105405895426694193)
    ·
      refine ⟨132509151829054421570020645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176678869105405895426694193 132509151829054421570020645)
      ·
        refine ⟨24845465967947704044378871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132509151829054421570020645 24845465967947704044378871)
        ·
          refine ⟨37268198951921556066568307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24845465967947704044378871 37268198951921556066568307)
          ·
            refine ⟨55902298427882334099852461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37268198951921556066568307 55902298427882334099852461)
            ·
              refine ⟨20963361910455875287444673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55902298427882334099852461 20963361910455875287444673)
              ·
                refine ⟨15722521432841906465583505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20963361910455875287444673 15722521432841906465583505)
                ·
                  refine ⟨11791891074631429849187629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15722521432841906465583505 11791891074631429849187629)
                  ·
                    refine ⟨4421959152986786193445361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11791891074631429849187629 4421959152986786193445361)
                    ·
                      refine ⟨3316469364740089645084021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421959152986786193445361 3316469364740089645084021)
                      ·
                        rfl

theorem cell23_6458801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_6458801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458801 prefixEnd_6458801 := by exact prefixLift 6458801
  have htrace : WordTrace (prefixWord ++ tailWord_6458801) baseStart_6458801 baseEnd_6458801 := by
    simpa [prefixWord, tailWord_6458801, baseEnd_6458801] using wordTrace_append hprefix tailTrace_6458801
  have hstable : (prefixWord ++ tailWord_6458801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458801).length < 2 ^ (prefixWord ++ tailWord_6458801).sum := by decide
  have hdescent : baseEnd_6458801 < baseStart_6458801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458814 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_6458814 : Nat := 118140960795 + 6458814 * 2 ^ 59
def prefixEnd_6458814 : Nat := 4983230072969 + 3 ^ 40 * 6458814 * 2
def baseEnd_6458814 : Nat := 3316476039988598094221461

theorem tailTrace_6458814 : CollatzResearch.WordTrace tailWord_6458814 prefixEnd_6458814 3316476039988598094221461 := by
  unfold tailWord_6458814
  simp only [CollatzResearch.WordTrace]
  refine ⟨29446537452853428806976937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157048199748551620303876997 29446537452853428806976937)
  ·
    refine ⟨22084903089640071605232703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29446537452853428806976937 22084903089640071605232703)
    ·
      refine ⟨33127354634460107407849055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22084903089640071605232703 33127354634460107407849055)
      ·
        refine ⟨49691031951690161111773583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33127354634460107407849055 49691031951690161111773583)
        ·
          refine ⟨74536547927535241667660375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49691031951690161111773583 74536547927535241667660375)
          ·
            refine ⟨111804821891302862501490563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74536547927535241667660375 111804821891302862501490563)
            ·
              refine ⟨167707232836954293752235845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111804821891302862501490563 167707232836954293752235845)
              ·
                refine ⟨31445106156928930078544221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167707232836954293752235845 31445106156928930078544221)
                ·
                  refine ⟨11791914808848348779454083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31445106156928930078544221 11791914808848348779454083)
                  ·
                    refine ⟨17687872213272523169181125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11791914808848348779454083 17687872213272523169181125)
                    ·
                      refine ⟨3316476039988598094221461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17687872213272523169181125 3316476039988598094221461)
                      ·
                        rfl

theorem cell23_6458814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_6458814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458814 prefixEnd_6458814 := by exact prefixLift 6458814
  have htrace : WordTrace (prefixWord ++ tailWord_6458814) baseStart_6458814 baseEnd_6458814 := by
    simpa [prefixWord, tailWord_6458814, baseEnd_6458814] using wordTrace_append hprefix tailTrace_6458814
  have hstable : (prefixWord ++ tailWord_6458814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458814).length < 2 ^ (prefixWord ++ tailWord_6458814).sum := by decide
  have hdescent : baseEnd_6458814 < baseStart_6458814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458827 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6]
def baseStart_6458827 : Nat := 118140960795 + 6458827 * 2 ^ 59
def prefixEnd_6458827 : Nat := 4983230072969 + 3 ^ 40 * 6458827 * 2
def baseEnd_6458827 : Nat := 3316482715237106543358901

theorem tailTrace_6458827 : CollatzResearch.WordTrace tailWord_6458827 prefixEnd_6458827 3316482715237106543358901 := by
  unfold tailWord_6458827
  simp only [CollatzResearch.WordTrace]
  refine ⟨235572773771780333676038735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157048515847853555784025823 235572773771780333676038735)
  ·
    refine ⟨353359160657670500514058103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235572773771780333676038735 353359160657670500514058103)
    ·
      refine ⟨530038740986505750771087155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353359160657670500514058103 530038740986505750771087155)
      ·
        refine ⟨795058111479758626156630733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530038740986505750771087155 795058111479758626156630733)
        ·
          refine ⟨298146791804909484808736525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795058111479758626156630733 298146791804909484808736525)
          ·
            refine ⟨111805046926841056803276197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298146791804909484808736525 111805046926841056803276197)
            ·
              refine ⟨20963446298782698150614287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111805046926841056803276197 20963446298782698150614287)
              ·
                refine ⟨31445169448174047225921431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20963446298782698150614287 31445169448174047225921431)
                ·
                  refine ⟨47167754172261070838882147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31445169448174047225921431 47167754172261070838882147)
                  ·
                    refine ⟨70751631258391606258323221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47167754172261070838882147 70751631258391606258323221)
                    ·
                      refine ⟨3316482715237106543358901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70751631258391606258323221 3316482715237106543358901)
                      ·
                        rfl

theorem cell23_6458827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_6458827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458827 prefixEnd_6458827 := by exact prefixLift 6458827
  have htrace : WordTrace (prefixWord ++ tailWord_6458827) baseStart_6458827 baseEnd_6458827 := by
    simpa [prefixWord, tailWord_6458827, baseEnd_6458827] using wordTrace_append hprefix tailTrace_6458827
  have hstable : (prefixWord ++ tailWord_6458827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458827).length < 2 ^ (prefixWord ++ tailWord_6458827).sum := by decide
  have hdescent : baseEnd_6458827 < baseStart_6458827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458831 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 3, 2, 2]
def baseStart_6458831 : Nat := 118140960795 + 6458831 * 2 ^ 59
def prefixEnd_6458831 : Nat := 4983230072969 + 3 ^ 40 * 6458831 * 2
def baseEnd_6458831 : Nat := 3316484769159724527708883

theorem tailTrace_6458831 : CollatzResearch.WordTrace tailWord_6458831 prefixEnd_6458831 3316484769159724527708883 := by
  unfold tailWord_6458831
  simp only [CollatzResearch.WordTrace]
  refine ⟨235572919663765842359184347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157048613109177228239456231 235572919663765842359184347)
  ·
    refine ⟨353359379495648763538776521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235572919663765842359184347 353359379495648763538776521)
    ·
      refine ⟨265019534621736572654082391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353359379495648763538776521 265019534621736572654082391)
      ·
        refine ⟨397529301932604858981123587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265019534621736572654082391 397529301932604858981123587)
        ·
          refine ⟨596293952898907288471685381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397529301932604858981123587 596293952898907288471685381)
          ·
            refine ⟨111805116168545116588441009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 596293952898907288471685381 111805116168545116588441009)
            ·
              refine ⟨83853837126408837441330757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111805116168545116588441009 83853837126408837441330757)
              ·
                refine ⟨15722594461201657020249517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83853837126408837441330757 15722594461201657020249517)
                ·
                  refine ⟨5895972922950621382593569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15722594461201657020249517 5895972922950621382593569)
                  ·
                    refine ⟨4421979692212966036945177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5895972922950621382593569 4421979692212966036945177)
                    ·
                      refine ⟨3316484769159724527708883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4421979692212966036945177 3316484769159724527708883)
                      ·
                        rfl

theorem cell23_6458831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 2, 2].length) (baseStart_6458831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458831 prefixEnd_6458831 := by exact prefixLift 6458831
  have htrace : WordTrace (prefixWord ++ tailWord_6458831) baseStart_6458831 baseEnd_6458831 := by
    simpa [prefixWord, tailWord_6458831, baseEnd_6458831] using wordTrace_append hprefix tailTrace_6458831
  have hstable : (prefixWord ++ tailWord_6458831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458831).length < 2 ^ (prefixWord ++ tailWord_6458831).sum := by decide
  have hdescent : baseEnd_6458831 < baseStart_6458831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458837 : List Nat := [1, 3, 2, 3, 1, 1, 1, 11]
def baseStart_6458837 : Nat := 118140960795 + 6458837 * 2 ^ 59
def prefixEnd_6458837 : Nat := 4983230072969 + 3 ^ 40 * 6458837 * 2
def baseEnd_6458837 : Nat := 122832883334950055712365

theorem tailTrace_6458837 : CollatzResearch.WordTrace tailWord_6458837 prefixEnd_6458837 122832883334950055712365 := by
  unfold tailWord_6458837
  simp only [CollatzResearch.WordTrace]
  refine ⟨235573138501744105383902765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157048759001162736922601843 235573138501744105383902765)
  ·
    refine ⟨88339926938154039518963537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235573138501744105383902765 88339926938154039518963537)
    ·
      refine ⟨66254945203615529639222653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88339926938154039518963537 66254945203615529639222653)
      ·
        refine ⟨24845604451355823614708495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66254945203615529639222653 24845604451355823614708495)
        ·
          refine ⟨37268406677033735422062743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24845604451355823614708495 37268406677033735422062743)
          ·
            refine ⟨55902610015550603133094115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37268406677033735422062743 55902610015550603133094115)
            ·
              refine ⟨83853915023325904699641173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55902610015550603133094115 83853915023325904699641173)
              ·
                refine ⟨122832883334950055712365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 83853915023325904699641173 122832883334950055712365)
                ·
                  rfl

theorem cell23_6458837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 11].length) (baseStart_6458837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458837 prefixEnd_6458837 := by exact prefixLift 6458837
  have htrace : WordTrace (prefixWord ++ tailWord_6458837) baseStart_6458837 baseEnd_6458837 := by
    simpa [prefixWord, tailWord_6458837, baseEnd_6458837] using wordTrace_append hprefix tailTrace_6458837
  have hstable : (prefixWord ++ tailWord_6458837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458837).length < 2 ^ (prefixWord ++ tailWord_6458837).sum := by decide
  have hdescent : baseEnd_6458837 < baseStart_6458837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458851 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 5]
def baseStart_6458851 : Nat := 118140960795 + 6458851 * 2 ^ 59
def prefixEnd_6458851 : Nat := 4983230072969 + 3 ^ 40 * 6458851 * 2
def baseEnd_6458851 : Nat := 3316495038772814449458791

theorem tailTrace_6458851 : CollatzResearch.WordTrace tailWord_6458851 prefixEnd_6458851 3316495038772814449458791 := by
  unfold tailWord_6458851
  simp only [CollatzResearch.WordTrace]
  refine ⟨235573649123693385774912407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157049099415795590516608271 235573649123693385774912407)
  ·
    refine ⟨353360473685540078662368611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235573649123693385774912407 353360473685540078662368611)
    ·
      refine ⟨530040710528310117993552917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353360473685540078662368611 530040710528310117993552917)
      ·
        refine ⟨24845658306014536780947793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 530040710528310117993552917 24845658306014536780947793)
        ·
          refine ⟨18634243729510902585710845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24845658306014536780947793 18634243729510902585710845)
          ·
            refine ⟨6987841398566588469641567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18634243729510902585710845 6987841398566588469641567)
            ·
              refine ⟨10481762097849882704462351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987841398566588469641567 10481762097849882704462351)
              ·
                refine ⟨15722643146774824056693527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10481762097849882704462351 15722643146774824056693527)
                ·
                  refine ⟨23583964720162236085040291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15722643146774824056693527 23583964720162236085040291)
                  ·
                    refine ⟨35375947080243354127560437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23583964720162236085040291 35375947080243354127560437)
                    ·
                      refine ⟨3316495038772814449458791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35375947080243354127560437 3316495038772814449458791)
                      ·
                        rfl

theorem cell23_6458851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_6458851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458851 prefixEnd_6458851 := by exact prefixLift 6458851
  have htrace : WordTrace (prefixWord ++ tailWord_6458851) baseStart_6458851 baseEnd_6458851 := by
    simpa [prefixWord, tailWord_6458851, baseEnd_6458851] using wordTrace_append hprefix tailTrace_6458851
  have hstable : (prefixWord ++ tailWord_6458851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458851).length < 2 ^ (prefixWord ++ tailWord_6458851).sum := by decide
  have hdescent : baseEnd_6458851 < baseStart_6458851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458858 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_6458858 : Nat := 118140960795 + 6458858 * 2 ^ 59
def prefixEnd_6458858 : Nat := 4983230072969 + 3 ^ 40 * 6458858 * 2
def baseEnd_6458858 : Nat := 1105499544379131974023753

theorem tailTrace_6458858 : CollatzResearch.WordTrace tailWord_6458858 prefixEnd_6458858 1105499544379131974023753 := by
  unfold tailWord_6458858
  simp only [CollatzResearch.WordTrace]
  refine ⟨58893476108667006492604307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157049269623112017313611485 58893476108667006492604307)
  ·
    refine ⟨88340214163000509738906461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58893476108667006492604307 88340214163000509738906461)
    ·
      refine ⟨33127580311125191152089923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88340214163000509738906461 33127580311125191152089923)
      ·
        refine ⟨49691370466687786728134885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33127580311125191152089923 49691370466687786728134885)
        ·
          refine ⟨9317131962503960011525291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49691370466687786728134885 9317131962503960011525291)
          ·
            refine ⟨13975697943755940017287937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9317131962503960011525291 13975697943755940017287937)
            ·
              refine ⟨10481773457816955012965953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13975697943755940017287937 10481773457816955012965953)
              ·
                refine ⟨7861330093362716259724465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10481773457816955012965953 7861330093362716259724465)
                ·
                  refine ⟨5895997570022037194793349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7861330093362716259724465 5895997570022037194793349)
                  ·
                    refine ⟨1105499544379131974023753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5895997570022037194793349 1105499544379131974023753)
                    ·
                      rfl

theorem cell23_6458858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_6458858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458858 prefixEnd_6458858 := by exact prefixLift 6458858
  have htrace : WordTrace (prefixWord ++ tailWord_6458858) baseStart_6458858 baseEnd_6458858 := by
    simpa [prefixWord, tailWord_6458858, baseEnd_6458858] using wordTrace_append hprefix tailTrace_6458858
  have hstable : (prefixWord ++ tailWord_6458858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458858).length < 2 ^ (prefixWord ++ tailWord_6458858).sum := by decide
  have hdescent : baseEnd_6458858 < baseStart_6458858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458865 : List Nat := [1, 2, 2, 2, 3, 3, 1, 4, 1, 2, 2]
def baseStart_6458865 : Nat := 118140960795 + 6458865 * 2 ^ 59
def prefixEnd_6458865 : Nat := 4983230072969 + 3 ^ 40 * 6458865 * 2
def baseEnd_6458865 : Nat := 3316502227501977394683727

theorem tailTrace_6458865 : CollatzResearch.WordTrace tailWord_6458865 prefixEnd_6458865 3316502227501977394683727 := by
  unfold tailWord_6458865
  simp only [CollatzResearch.WordTrace]
  refine ⟨235574159745642666165922049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157049439830428444110614699 235574159745642666165922049)
  ·
    refine ⟨176680619809231999624441537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235574159745642666165922049 176680619809231999624441537)
    ·
      refine ⟨132510464856923999718331153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176680619809231999624441537 132510464856923999718331153)
      ·
        refine ⟨99382848642692999788748365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132510464856923999718331153 99382848642692999788748365)
        ·
          refine ⟨37268568241009874920780637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99382848642692999788748365 37268568241009874920780637)
          ·
            refine ⟨13975713090378703095292739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37268568241009874920780637 13975713090378703095292739)
            ·
              refine ⟨20963569635568054642939109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13975713090378703095292739 20963569635568054642939109)
              ·
                refine ⟨3930669306669010245551083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20963569635568054642939109 3930669306669010245551083)
                ·
                  refine ⟨5896003960003515368326625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930669306669010245551083 5896003960003515368326625)
                  ·
                    refine ⟨4422002970002636526244969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5896003960003515368326625 4422002970002636526244969)
                    ·
                      refine ⟨3316502227501977394683727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422002970002636526244969 3316502227501977394683727)
                      ·
                        rfl

theorem cell23_6458865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_6458865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458865 prefixEnd_6458865 := by exact prefixLift 6458865
  have htrace : WordTrace (prefixWord ++ tailWord_6458865) baseStart_6458865 baseEnd_6458865 := by
    simpa [prefixWord, tailWord_6458865, baseEnd_6458865] using wordTrace_append hprefix tailTrace_6458865
  have hstable : (prefixWord ++ tailWord_6458865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458865).length < 2 ^ (prefixWord ++ tailWord_6458865).sum := by decide
  have hdescent : baseEnd_6458865 < baseStart_6458865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458886 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_6458886 : Nat := 118140960795 + 6458886 * 2 ^ 59
def prefixEnd_6458886 : Nat := 4983230072969 + 3 ^ 40 * 6458886 * 2
def baseEnd_6458886 : Nat := 3316513010595721812521131

theorem tailTrace_6458886 : CollatzResearch.WordTrace tailWord_6458886 prefixEnd_6458886 3316513010595721812521131 := by
  unfold tailWord_6458886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361716427455205836013641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157049950452377724501624341 7361716427455205836013641)
  ·
    refine ⟨5521287320591404377010231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7361716427455205836013641 5521287320591404377010231)
    ·
      refine ⟨8281930980887106565515347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5521287320591404377010231 8281930980887106565515347)
      ·
        refine ⟨12422896471330659848273021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8281930980887106565515347 12422896471330659848273021)
        ·
          refine ⟨4658586176748997443102383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12422896471330659848273021 4658586176748997443102383)
          ·
            refine ⟨6987879265123496164653575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658586176748997443102383 6987879265123496164653575)
            ·
              refine ⟨10481818897685244246980363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987879265123496164653575 10481818897685244246980363)
              ·
                refine ⟨15722728346527866370470545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10481818897685244246980363 15722728346527866370470545)
                ·
                  refine ⟨11792046259895899777852909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15722728346527866370470545 11792046259895899777852909)
                  ·
                    refine ⟨4422017347460962416694841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11792046259895899777852909 4422017347460962416694841)
                    ·
                      refine ⟨3316513010595721812521131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422017347460962416694841 3316513010595721812521131)
                      ·
                        rfl

theorem cell23_6458886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_6458886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458886 prefixEnd_6458886 := by exact prefixLift 6458886
  have htrace : WordTrace (prefixWord ++ tailWord_6458886) baseStart_6458886 baseEnd_6458886 := by
    simpa [prefixWord, tailWord_6458886, baseEnd_6458886] using wordTrace_append hprefix tailTrace_6458886
  have hstable : (prefixWord ++ tailWord_6458886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458886).length < 2 ^ (prefixWord ++ tailWord_6458886).sum := by decide
  have hdescent : baseEnd_6458886 < baseStart_6458886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458897 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 1, 8]
def baseStart_6458897 : Nat := 118140960795 + 6458897 * 2 ^ 59
def prefixEnd_6458897 : Nat := 4983230072969 + 3 ^ 40 * 6458897 * 2
def baseEnd_6458897 : Nat := 1105506219627640423161193

theorem tailTrace_6458897 : CollatzResearch.WordTrace tailWord_6458897 prefixEnd_6458897 1105506219627640423161193 := by
  unfold tailWord_6458897
  simp only [CollatzResearch.WordTrace]
  refine ⟨235575326881526735631086945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157050217921017823754057963 235575326881526735631086945)
  ·
    refine ⟨176681495161145051723315209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235575326881526735631086945 176681495161145051723315209)
    ·
      refine ⟨132511121370858788792486407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176681495161145051723315209 132511121370858788792486407)
      ·
        refine ⟨198766682056288183188729611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132511121370858788792486407 198766682056288183188729611)
        ·
          refine ⟨298150023084432274783094417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198766682056288183188729611 298150023084432274783094417)
          ·
            refine ⟨223612517313324206087320813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298150023084432274783094417 223612517313324206087320813)
            ·
              refine ⟨83854693992496577282745305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223612517313324206087320813 83854693992496577282745305)
              ·
                refine ⟨62891020494372432962058979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83854693992496577282745305 62891020494372432962058979)
                ·
                  refine ⟨94336530741558649443088469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62891020494372432962058979 94336530741558649443088469)
                  ·
                    refine ⟨1105506219627640423161193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94336530741558649443088469 1105506219627640423161193)
                    ·
                      rfl

theorem cell23_6458897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_6458897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458897 prefixEnd_6458897 := by exact prefixLift 6458897
  have htrace : WordTrace (prefixWord ++ tailWord_6458897) baseStart_6458897 baseEnd_6458897 := by
    simpa [prefixWord, tailWord_6458897, baseEnd_6458897] using wordTrace_append hprefix tailTrace_6458897
  have hstable : (prefixWord ++ tailWord_6458897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458897).length < 2 ^ (prefixWord ++ tailWord_6458897).sum := by decide
  have hdescent : baseEnd_6458897 < baseStart_6458897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458908 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_6458908 : Nat := 118140960795 + 6458908 * 2 ^ 59
def prefixEnd_6458908 : Nat := 4983230072969 + 3 ^ 40 * 6458908 * 2
def baseEnd_6458908 : Nat := 3316524307170120726446029

theorem tailTrace_6458908 : CollatzResearch.WordTrace tailWord_6458908 prefixEnd_6458908 3316524307170120726446029 := by
  unfold tailWord_6458908
  simp only [CollatzResearch.WordTrace]
  refine ⟨117787864042243442254868689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157050485389657923006491585 117787864042243442254868689)
  ·
    refine ⟨88340898031682581691151517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117787864042243442254868689 88340898031682581691151517)
    ·
      refine ⟨33127836761880968134181819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88340898031682581691151517 33127836761880968134181819)
      ·
        refine ⟨49691755142821452201272729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33127836761880968134181819 49691755142821452201272729)
        ·
          refine ⟨37268816357116089150954547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49691755142821452201272729 37268816357116089150954547)
          ·
            refine ⟨55903224535674133726431821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37268816357116089150954547 55903224535674133726431821)
            ·
              refine ⟨20963709200877800147411933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55903224535674133726431821 20963709200877800147411933)
              ·
                refine ⟨7861390950329175055279475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20963709200877800147411933 7861390950329175055279475)
                ·
                  refine ⟨11792086425493762582919213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7861390950329175055279475 11792086425493762582919213)
                  ·
                    refine ⟨4422032409560160968594705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11792086425493762582919213 4422032409560160968594705)
                    ·
                      refine ⟨3316524307170120726446029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422032409560160968594705 3316524307170120726446029)
                      ·
                        rfl

theorem cell23_6458908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_6458908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458908 prefixEnd_6458908 := by exact prefixLift 6458908
  have htrace : WordTrace (prefixWord ++ tailWord_6458908) baseStart_6458908 baseEnd_6458908 := by
    simpa [prefixWord, tailWord_6458908, baseEnd_6458908] using wordTrace_append hprefix tailTrace_6458908
  have hstable : (prefixWord ++ tailWord_6458908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458908).length < 2 ^ (prefixWord ++ tailWord_6458908).sum := by decide
  have hdescent : baseEnd_6458908 < baseStart_6458908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458914 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_6458914 : Nat := 118140960795 + 6458914 * 2 ^ 59
def prefixEnd_6458914 : Nat := 4983230072969 + 3 ^ 40 * 6458914 * 2
def baseEnd_6458914 : Nat := 1105509129351349234323667

theorem tailTrace_6458914 : CollatzResearch.WordTrace tailWord_6458914 prefixEnd_6458914 1105509129351349234323667 := by
  unfold tailWord_6458914
  simp only [CollatzResearch.WordTrace]
  refine ⟨58893986730616286883613949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157050631281643431689637197 58893986730616286883613949)
  ·
    refine ⟨22085245023981107581355231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58893986730616286883613949 22085245023981107581355231)
    ·
      refine ⟨33127867535971661372032847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22085245023981107581355231 33127867535971661372032847)
      ·
        refine ⟨49691801303957492058049271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33127867535971661372032847 49691801303957492058049271)
        ·
          refine ⟨74537701955936238087073907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49691801303957492058049271 74537701955936238087073907)
          ·
            refine ⟨111806552933904357130610861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74537701955936238087073907 111806552933904357130610861)
            ·
              refine ⟨41927457350214133923979073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111806552933904357130610861 41927457350214133923979073)
              ·
                refine ⟨31445593012660600442984305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41927457350214133923979073 31445593012660600442984305)
                ·
                  refine ⟨23584194759495450332238229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31445593012660600442984305 23584194759495450332238229)
                  ·
                    refine ⟨1105509129351349234323667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23584194759495450332238229 1105509129351349234323667)
                    ·
                      rfl

theorem cell23_6458914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_6458914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458914 prefixEnd_6458914 := by exact prefixLift 6458914
  have htrace : WordTrace (prefixWord ++ tailWord_6458914) baseStart_6458914 baseEnd_6458914 := by
    simpa [prefixWord, tailWord_6458914, baseEnd_6458914] using wordTrace_append hprefix tailTrace_6458914
  have hstable : (prefixWord ++ tailWord_6458914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458914).length < 2 ^ (prefixWord ++ tailWord_6458914).sum := by decide
  have hdescent : baseEnd_6458914 < baseStart_6458914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458915 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 3]
def baseStart_6458915 : Nat := 118140960795 + 6458915 * 2 ^ 59
def prefixEnd_6458915 : Nat := 4983230072969 + 3 ^ 40 * 6458915 * 2
def baseEnd_6458915 : Nat := 3316527901534702199058497

theorem tailTrace_6458915 : CollatzResearch.WordTrace tailWord_6458915 prefixEnd_6458915 3316527901534702199058497 := by
  unfold tailWord_6458915
  simp only [CollatzResearch.WordTrace]
  refine ⟨235575983395461524705242199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157050655596974349803494799 235575983395461524705242199)
  ·
    refine ⟨353363975093192287057863299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235575983395461524705242199 353363975093192287057863299)
    ·
      refine ⟨530045962639788430586794949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353363975093192287057863299 530045962639788430586794949)
      ·
        refine ⟨99383617994960330735024053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 530045962639788430586794949 99383617994960330735024053)
        ·
          refine ⟨9317214187027531006408505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99383617994960330735024053 9317214187027531006408505)
          ·
            refine ⟨6987910640270648254806379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9317214187027531006408505 6987910640270648254806379)
            ·
              refine ⟨10481865960405972382209569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987910640270648254806379 10481865960405972382209569)
              ·
                refine ⟨7861399470304479286657177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10481865960405972382209569 7861399470304479286657177)
                ·
                  refine ⟨5896049602728359464992883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7861399470304479286657177 5896049602728359464992883)
                  ·
                    refine ⟨8844074404092539197489325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5896049602728359464992883 8844074404092539197489325)
                    ·
                      refine ⟨3316527901534702199058497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8844074404092539197489325 3316527901534702199058497)
                      ·
                        rfl

theorem cell23_6458915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_6458915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458915 prefixEnd_6458915 := by exact prefixLift 6458915
  have htrace : WordTrace (prefixWord ++ tailWord_6458915) baseStart_6458915 baseEnd_6458915 := by
    simpa [prefixWord, tailWord_6458915, baseEnd_6458915] using wordTrace_append hprefix tailTrace_6458915
  have hstable : (prefixWord ++ tailWord_6458915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458915).length < 2 ^ (prefixWord ++ tailWord_6458915).sum := by decide
  have hdescent : baseEnd_6458915 < baseStart_6458915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6458989 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_6458989 : Nat := 118140960795 + 6458989 * 2 ^ 59
def prefixEnd_6458989 : Nat := 4983230072969 + 3 ^ 40 * 6458989 * 2
def baseEnd_6458989 : Nat := 3316565899103134909533157

theorem tailTrace_6458989 : CollatzResearch.WordTrace tailWord_6458989 prefixEnd_6458989 3316565899103134909533157 := by
  unfold tailWord_6458989
  simp only [CollatzResearch.WordTrace]
  refine ⟨235578682397193435343436021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157052454931462290228957347 235578682397193435343436021)
  ·
    refine ⟨22085501474736884563447127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235578682397193435343436021 22085501474736884563447127)
    ·
      refine ⟨33128252212105326845170691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22085501474736884563447127 33128252212105326845170691)
      ·
        refine ⟨49692378318157990267756037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33128252212105326845170691 49692378318157990267756037)
        ·
          refine ⟨9317320934654623175204257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49692378318157990267756037 9317320934654623175204257)
          ·
            refine ⟨6987990700990967381403193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9317320934654623175204257 6987990700990967381403193)
            ·
              refine ⟨5240993025743225536052395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6987990700990967381403193 5240993025743225536052395)
              ·
                refine ⟨7861489538614838304078593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240993025743225536052395 7861489538614838304078593)
                ·
                  refine ⟨5896117153961128728058945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7861489538614838304078593 5896117153961128728058945)
                  ·
                    refine ⟨4422087865470846546044209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5896117153961128728058945 4422087865470846546044209)
                    ·
                      refine ⟨3316565899103134909533157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422087865470846546044209 3316565899103134909533157)
                      ·
                        rfl

theorem cell23_6458989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_6458989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6458989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6458989 prefixEnd_6458989 := by exact prefixLift 6458989
  have htrace : WordTrace (prefixWord ++ tailWord_6458989) baseStart_6458989 baseEnd_6458989 := by
    simpa [prefixWord, tailWord_6458989, baseEnd_6458989] using wordTrace_append hprefix tailTrace_6458989
  have hstable : (prefixWord ++ tailWord_6458989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6458989).length < 2 ^ (prefixWord ++ tailWord_6458989).sum := by decide
  have hdescent : baseEnd_6458989 < baseStart_6458989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6458989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459011 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 4, 4, 2]
def baseStart_6459011 : Nat := 118140960795 + 6459011 * 2 ^ 59
def prefixEnd_6459011 : Nat := 4983230072969 + 3 ^ 40 * 6459011 * 2
def baseEnd_6459011 : Nat := 3316577195677533823458055

theorem tailTrace_6459011 : CollatzResearch.WordTrace tailWord_6459011 prefixEnd_6459011 3316577195677533823458055 := by
  unfold tailWord_6459011
  simp only [CollatzResearch.WordTrace]
  refine ⟨235579484803113733100736887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157052989868742488733824591 235579484803113733100736887)
  ·
    refine ⟨353369227204670599651105331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235579484803113733100736887 353369227204670599651105331)
    ·
      refine ⟨530053840807005899476657997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353369227204670599651105331 530053840807005899476657997)
      ·
        refine ⟨198770190302627212303746749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530053840807005899476657997 198770190302627212303746749)
        ·
          refine ⟨74538821363485204613905031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198770190302627212303746749 74538821363485204613905031)
          ·
            refine ⟨111808232045227806920857547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74538821363485204613905031 111808232045227806920857547)
            ·
              refine ⟨167712348067841710381286321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111808232045227806920857547 167712348067841710381286321)
              ·
                refine ⟨125784261050881282785964741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167712348067841710381286321 125784261050881282785964741)
                ·
                  refine ⟨23584548947040240522368389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125784261050881282785964741 23584548947040240522368389)
                  ·
                    refine ⟨4422102927570045097944073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23584548947040240522368389 4422102927570045097944073)
                    ·
                      refine ⟨3316577195677533823458055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422102927570045097944073 3316577195677533823458055)
                      ·
                        rfl

theorem cell23_6459011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_6459011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459011 prefixEnd_6459011 := by exact prefixLift 6459011
  have htrace : WordTrace (prefixWord ++ tailWord_6459011) baseStart_6459011 baseEnd_6459011 := by
    simpa [prefixWord, tailWord_6459011, baseEnd_6459011] using wordTrace_append hprefix tailTrace_6459011
  have hstable : (prefixWord ++ tailWord_6459011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459011).length < 2 ^ (prefixWord ++ tailWord_6459011).sum := by decide
  have hdescent : baseEnd_6459011 < baseStart_6459011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459062 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6459062 : Nat := 118140960795 + 6459062 * 2 ^ 59
def prefixEnd_6459062 : Nat := 4983230072969 + 3 ^ 40 * 6459062 * 2
def baseEnd_6459062 : Nat := 3316603383190913123920321

theorem tailTrace_6459062 : CollatzResearch.WordTrace tailWord_6459062 prefixEnd_6459062 3316603383190913123920321 := by
  unfold tailWord_6459062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723834057870560550677715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157054229950619312540562293 14723834057870560550677715)
  ·
    refine ⟨22085751086805840826016573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14723834057870560550677715 22085751086805840826016573)
    ·
      refine ⟨8282156657552190309756215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22085751086805840826016573 8282156657552190309756215)
      ·
        refine ⟨12423234986328285464634323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282156657552190309756215 12423234986328285464634323)
        ·
          refine ⟨18634852479492428196951485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12423234986328285464634323 18634852479492428196951485)
          ·
            refine ⟨6988069679809660573856807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18634852479492428196951485 6988069679809660573856807)
            ·
              refine ⟨10482104519714490860785211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988069679809660573856807 10482104519714490860785211)
              ·
                refine ⟨15723156779571736291177817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10482104519714490860785211 15723156779571736291177817)
                ·
                  refine ⟨11792367584678802218383363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15723156779571736291177817 11792367584678802218383363)
                  ·
                    refine ⟨17688551377018203327575045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11792367584678802218383363 17688551377018203327575045)
                    ·
                      refine ⟨3316603383190913123920321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17688551377018203327575045 3316603383190913123920321)
                      ·
                        rfl

theorem cell23_6459062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6459062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459062 prefixEnd_6459062 := by exact prefixLift 6459062
  have htrace : WordTrace (prefixWord ++ tailWord_6459062) baseStart_6459062 baseEnd_6459062 := by
    simpa [prefixWord, tailWord_6459062, baseEnd_6459062] using wordTrace_append hprefix tailTrace_6459062
  have hstable : (prefixWord ++ tailWord_6459062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459062).length < 2 ^ (prefixWord ++ tailWord_6459062).sum := by decide
  have hdescent : baseEnd_6459062 < baseStart_6459062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459085 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 6]
def baseStart_6459085 : Nat := 118140960795 + 6459085 * 2 ^ 59
def prefixEnd_6459085 : Nat := 4983230072969 + 3 ^ 40 * 6459085 * 2
def baseEnd_6459085 : Nat := 368512799249551837103635

theorem tailTrace_6459085 : CollatzResearch.WordTrace tailWord_6459085 prefixEnd_6459085 368512799249551837103635 := by
  unfold tailWord_6459085
  simp only [CollatzResearch.WordTrace]
  refine ⟨235582183804845643738930709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157054789203230429159287139 235582183804845643738930709)
  ·
    refine ⟨11042914865852139550262377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235582183804845643738930709 11042914865852139550262377)
    ·
      refine ⟨8282186149389104662696783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11042914865852139550262377 8282186149389104662696783)
      ·
        refine ⟨12423279224083656994045175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282186149389104662696783 12423279224083656994045175)
        ·
          refine ⟨18634918836125485491067763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12423279224083656994045175 18634918836125485491067763)
          ·
            refine ⟨27952378254188228236601645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18634918836125485491067763 27952378254188228236601645)
            ·
              refine ⟨10482141845320585588725617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27952378254188228236601645 10482141845320585588725617)
              ·
                refine ⟨7861606383990439191544213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10482141845320585588725617 7861606383990439191544213)
                ·
                  refine ⟨368512799249551837103635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7861606383990439191544213 368512799249551837103635)
                  ·
                    rfl

theorem cell23_6459085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_6459085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459085 prefixEnd_6459085 := by exact prefixLift 6459085
  have htrace : WordTrace (prefixWord ++ tailWord_6459085) baseStart_6459085 baseEnd_6459085 := by
    simpa [prefixWord, tailWord_6459085, baseEnd_6459085] using wordTrace_append hprefix tailTrace_6459085
  have hstable : (prefixWord ++ tailWord_6459085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459085).length < 2 ^ (prefixWord ++ tailWord_6459085).sum := by decide
  have hdescent : baseEnd_6459085 < baseStart_6459085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459095 : List Nat := [1, 1, 3, 2, 1, 3, 1, 6, 1, 1, 3]
def baseStart_6459095 : Nat := 118140960795 + 6459095 * 2 ^ 59
def prefixEnd_6459095 : Nat := 4983230072969 + 3 ^ 40 * 6459095 * 2
def baseEnd_6459095 : Nat := 3316620328052511494807669

theorem tailTrace_6459095 : CollatzResearch.WordTrace tailWord_6459095 prefixEnd_6459095 3316620328052511494807669 := by
  unfold tailWord_6459095
  simp only [CollatzResearch.WordTrace]
  refine ⟨235582548534809415446794739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157055032356539610297863159 235582548534809415446794739)
  ·
    refine ⟨353373822802214123170192109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235582548534809415446794739 353373822802214123170192109)
    ·
      refine ⟨132515183550830296188822041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353373822802214123170192109 132515183550830296188822041)
      ·
        refine ⟨99386387663122722141616531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132515183550830296188822041 99386387663122722141616531)
        ·
          refine ⟨149079581494684083212424797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99386387663122722141616531 149079581494684083212424797)
          ·
            refine ⟨55904843060506531204659299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149079581494684083212424797 55904843060506531204659299)
            ·
              refine ⟨83857264590759796806988949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55904843060506531204659299 83857264590759796806988949)
              ·
                refine ⟨3930809277691865475327607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83857264590759796806988949 3930809277691865475327607)
                ·
                  refine ⟨5896213916537798212991411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930809277691865475327607 5896213916537798212991411)
                  ·
                    refine ⟨8844320874806697319487117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5896213916537798212991411 8844320874806697319487117)
                    ·
                      refine ⟨3316620328052511494807669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8844320874806697319487117 3316620328052511494807669)
                      ·
                        rfl

theorem cell23_6459095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_6459095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459095 prefixEnd_6459095 := by exact prefixLift 6459095
  have htrace : WordTrace (prefixWord ++ tailWord_6459095) baseStart_6459095 baseEnd_6459095 := by
    simpa [prefixWord, tailWord_6459095, baseEnd_6459095] using wordTrace_append hprefix tailTrace_6459095
  have hstable : (prefixWord ++ tailWord_6459095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459095).length < 2 ^ (prefixWord ++ tailWord_6459095).sum := by decide
  have hdescent : baseEnd_6459095 < baseStart_6459095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459118 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_6459118 : Nat := 118140960795 + 6459118 * 2 ^ 59
def prefixEnd_6459118 : Nat := 4983230072969 + 3 ^ 40 * 6459118 * 2
def baseEnd_6459118 : Nat := 3316632138107564904820063

theorem tailTrace_6459118 : CollatzResearch.WordTrace tailWord_6459118 prefixEnd_6459118 3316632138107564904820063 := by
  unfold tailWord_6459118
  simp only [CollatzResearch.WordTrace]
  refine ⟨29447923426715761296860251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157055591609150726916588005 29447923426715761296860251)
  ·
    refine ⟨44171885140073641945290377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29447923426715761296860251 44171885140073641945290377)
    ·
      refine ⟨33128913855055231458967783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44171885140073641945290377 33128913855055231458967783)
      ·
        refine ⟨49693370782582847188451675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33128913855055231458967783 49693370782582847188451675)
        ·
          refine ⟨74540056173874270782677513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49693370782582847188451675 74540056173874270782677513)
          ·
            refine ⟨55905042130405703087008135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74540056173874270782677513 55905042130405703087008135)
            ·
              refine ⟨83857563195608554630512203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55905042130405703087008135 83857563195608554630512203)
              ·
                refine ⟨125786344793412831945768305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83857563195608554630512203 125786344793412831945768305)
                ·
                  refine ⟨94339758595059623959326229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125786344793412831945768305 94339758595059623959326229)
                  ·
                    refine ⟨4422176184143419873093417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94339758595059623959326229 4422176184143419873093417)
                    ·
                      refine ⟨3316632138107564904820063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422176184143419873093417 3316632138107564904820063)
                      ·
                        rfl

theorem cell23_6459118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_6459118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459118 prefixEnd_6459118 := by exact prefixLift 6459118
  have htrace : WordTrace (prefixWord ++ tailWord_6459118) baseStart_6459118 baseEnd_6459118 := by
    simpa [prefixWord, tailWord_6459118, baseEnd_6459118] using wordTrace_append hprefix tailTrace_6459118
  have hstable : (prefixWord ++ tailWord_6459118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459118).length < 2 ^ (prefixWord ++ tailWord_6459118).sum := by decide
  have hdescent : baseEnd_6459118 < baseStart_6459118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459151 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 3]
def baseStart_6459151 : Nat := 118140960795 + 6459151 * 2 ^ 59
def prefixEnd_6459151 : Nat := 4983230072969 + 3 ^ 40 * 6459151 * 2
def baseEnd_6459151 : Nat := 3316649082969163275707411

theorem tailTrace_6459151 : CollatzResearch.WordTrace tailWord_6459151 prefixEnd_6459151 3316649082969163275707411 := by
  unfold tailWord_6459151
  simp only [CollatzResearch.WordTrace]
  refine ⟨235584591022606537010833307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157056394015071024673888871 235584591022606537010833307)
  ·
    refine ⟨353376886533909805516249961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235584591022606537010833307 353376886533909805516249961)
    ·
      refine ⟨265032664900432354137187471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353376886533909805516249961 265032664900432354137187471)
      ·
        refine ⟨397548997350648531205781207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265032664900432354137187471 397548997350648531205781207)
        ·
          refine ⟨596323496025972796808671811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397548997350648531205781207 596323496025972796808671811)
          ·
            refine ⟨894485244038959195213007717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596323496025972796808671811 894485244038959195213007717)
            ·
              refine ⟨167715983257304849102438947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 894485244038959195213007717 167715983257304849102438947)
              ·
                refine ⟨251573974885957273653658421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167715983257304849102438947 251573974885957273653658421)
                ·
                  refine ⟨23585060145558494405030477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251573974885957273653658421 23585060145558494405030477)
                  ·
                    refine ⟨8844397554584435401886429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23585060145558494405030477 8844397554584435401886429)
                    ·
                      refine ⟨3316649082969163275707411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8844397554584435401886429 3316649082969163275707411)
                      ·
                        rfl

theorem cell23_6459151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_6459151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459151 prefixEnd_6459151 := by exact prefixLift 6459151
  have htrace : WordTrace (prefixWord ++ tailWord_6459151) baseStart_6459151 baseEnd_6459151 := by
    simpa [prefixWord, tailWord_6459151, baseEnd_6459151] using wordTrace_append hprefix tailTrace_6459151
  have hstable : (prefixWord ++ tailWord_6459151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459151).length < 2 ^ (prefixWord ++ tailWord_6459151).sum := by decide
  have hdescent : baseEnd_6459151 < baseStart_6459151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459162 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_6459162 : Nat := 118140960795 + 6459162 * 2 ^ 59
def prefixEnd_6459162 : Nat := 4983230072969 + 3 ^ 40 * 6459162 * 2
def baseEnd_6459162 : Nat := 1105551577085454244223287

theorem tailTrace_6459162 : CollatzResearch.WordTrace tailWord_6459162 prefixEnd_6459162 1105551577085454244223287 := by
  unfold tailWord_6459162
  simp only [CollatzResearch.WordTrace]
  refine ⟨58896248056391671472370935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157056661483711123926322493 58896248056391671472370935)
  ·
    refine ⟨88344372084587507208556403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58896248056391671472370935 88344372084587507208556403)
    ·
      refine ⟨132516558126881260812834605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88344372084587507208556403 132516558126881260812834605)
      ·
        refine ⟨49693709297580472804812977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132516558126881260812834605 49693709297580472804812977)
        ·
          refine ⟨37270281973185354603609733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49693709297580472804812977 37270281973185354603609733)
          ·
            refine ⟨6988177869972253988176825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37270281973185354603609733 6988177869972253988176825)
            ·
              refine ⟨5241133402479190491132619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988177869972253988176825 5241133402479190491132619)
              ·
                refine ⟨7861700103718785736698929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241133402479190491132619 7861700103718785736698929)
                ·
                  refine ⟨5896275077789089302524197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7861700103718785736698929 5896275077789089302524197)
                  ·
                    refine ⟨1105551577085454244223287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5896275077789089302524197 1105551577085454244223287)
                    ·
                      rfl

theorem cell23_6459162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_6459162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459162 prefixEnd_6459162 := by exact prefixLift 6459162
  have htrace : WordTrace (prefixWord ++ tailWord_6459162) baseStart_6459162 baseEnd_6459162 := by
    simpa [prefixWord, tailWord_6459162, baseEnd_6459162] using wordTrace_append hprefix tailTrace_6459162
  have hstable : (prefixWord ++ tailWord_6459162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459162).length < 2 ^ (prefixWord ++ tailWord_6459162).sum := by decide
  have hdescent : baseEnd_6459162 < baseStart_6459162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459166 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6459166 : Nat := 118140960795 + 6459166 * 2 ^ 59
def prefixEnd_6459166 : Nat := 4983230072969 + 3 ^ 40 * 6459166 * 2
def baseEnd_6459166 : Nat := 1105552261726326905673281

theorem tailTrace_6459166 : CollatzResearch.WordTrace tailWord_6459166 prefixEnd_6459166 1105552261726326905673281 := by
  unfold tailWord_6459166
  simp only [CollatzResearch.WordTrace]
  refine ⟨29448142264694024321578669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157056758745034796381752901 29448142264694024321578669)
  ·
    refine ⟨11043053349260259120592001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29448142264694024321578669 11043053349260259120592001)
    ·
      refine ⟨8282290011945194340444001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11043053349260259120592001 8282290011945194340444001)
      ·
        refine ⟨6211717508958895755333001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8282290011945194340444001 6211717508958895755333001)
        ·
          refine ⟨4658788131719171816499751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6211717508958895755333001 4658788131719171816499751)
          ·
            refine ⟨6988182197578757724749627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658788131719171816499751 6988182197578757724749627)
            ·
              refine ⟨10482273296368136587124441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988182197578757724749627 10482273296368136587124441)
              ·
                refine ⟨7861704972276102440343331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10482273296368136587124441 7861704972276102440343331)
                ·
                  refine ⟨11792557458414153660514997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7861704972276102440343331 11792557458414153660514997)
                  ·
                    refine ⟨1105552261726326905673281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11792557458414153660514997 1105552261726326905673281)
                    ·
                      rfl

theorem cell23_6459166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6459166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459166 prefixEnd_6459166 := by exact prefixLift 6459166
  have htrace : WordTrace (prefixWord ++ tailWord_6459166) baseStart_6459166 baseEnd_6459166 := by
    simpa [prefixWord, tailWord_6459166, baseEnd_6459166] using wordTrace_append hprefix tailTrace_6459166
  have hstable : (prefixWord ++ tailWord_6459166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459166).length < 2 ^ (prefixWord ++ tailWord_6459166).sum := by decide
  have hdescent : baseEnd_6459166 < baseStart_6459166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459168 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6459168 : Nat := 118140960795 + 6459168 * 2 ^ 59
def prefixEnd_6459168 : Nat := 4983230072969 + 3 ^ 40 * 6459168 * 2
def baseEnd_6459168 : Nat := 3316657812140289709194833

theorem tailTrace_6459168 : CollatzResearch.WordTrace tailWord_6459168 prefixEnd_6459168 3316657812140289709194833 := by
  unfold tailWord_6459168
  simp only [CollatzResearch.WordTrace]
  refine ⟨117792605531772474457101079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157056807375696632609468105 117792605531772474457101079)
  ·
    refine ⟨176688908297658711685651619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117792605531772474457101079 176688908297658711685651619)
    ·
      refine ⟨265033362446488067528477429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176688908297658711685651619 265033362446488067528477429)
      ·
        refine ⟨24846877729358256330794759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265033362446488067528477429 24846877729358256330794759)
        ·
          refine ⟨37270316594037384496192139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24846877729358256330794759 37270316594037384496192139)
          ·
            refine ⟨55905474891056076744288209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37270316594037384496192139 55905474891056076744288209)
            ·
              refine ⟨41929106168292057558216157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55905474891056076744288209 41929106168292057558216157)
              ·
                refine ⟨15723414813109521584331059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41929106168292057558216157 15723414813109521584331059)
                ·
                  refine ⟨23585122219664282376496589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15723414813109521584331059 23585122219664282376496589)
                  ·
                    refine ⟨8844420832374105891186221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23585122219664282376496589 8844420832374105891186221)
                    ·
                      refine ⟨3316657812140289709194833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8844420832374105891186221 3316657812140289709194833)
                      ·
                        rfl

theorem cell23_6459168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6459168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459168 prefixEnd_6459168 := by exact prefixLift 6459168
  have htrace : WordTrace (prefixWord ++ tailWord_6459168) baseStart_6459168 baseEnd_6459168 := by
    simpa [prefixWord, tailWord_6459168, baseEnd_6459168] using wordTrace_append hprefix tailTrace_6459168
  have hstable : (prefixWord ++ tailWord_6459168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459168).length < 2 ^ (prefixWord ++ tailWord_6459168).sum := by decide
  have hdescent : baseEnd_6459168 < baseStart_6459168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459172 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_6459172 : Nat := 118140960795 + 6459172 * 2 ^ 59
def prefixEnd_6459172 : Nat := 4983230072969 + 3 ^ 40 * 6459172 * 2
def baseEnd_6459172 : Nat := 3316659866062907693544815

theorem tailTrace_6459172 : CollatzResearch.WordTrace tailWord_6459172 prefixEnd_6459172 3316659866062907693544815 := by
  unfold tailWord_6459172
  simp only [CollatzResearch.WordTrace]
  refine ⟨117792678477765228798673885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157056904637020305064898513 117792678477765228798673885)
  ·
    refine ⟨44172254429161960799502707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117792678477765228798673885 44172254429161960799502707)
    ·
      refine ⟨66258381643742941199254061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44172254429161960799502707 66258381643742941199254061)
      ·
        refine ⟨24846893116403602949720273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66258381643742941199254061 24846893116403602949720273)
        ·
          refine ⟨18635169837302702212290205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24846893116403602949720273 18635169837302702212290205)
          ·
            refine ⟨6988188688988513329608827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18635169837302702212290205 6988188688988513329608827)
            ·
              refine ⟨10482283033482769994413241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988188688988513329608827 10482283033482769994413241)
              ·
                refine ⟨7861712275112077495809931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10482283033482769994413241 7861712275112077495809931)
                ·
                  refine ⟨11792568412668116243714897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7861712275112077495809931 11792568412668116243714897)
                  ·
                    refine ⟨8844426309501087182786173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11792568412668116243714897 8844426309501087182786173)
                    ·
                      refine ⟨3316659866062907693544815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8844426309501087182786173 3316659866062907693544815)
                      ·
                        rfl

theorem cell23_6459172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_6459172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459172 prefixEnd_6459172 := by exact prefixLift 6459172
  have htrace : WordTrace (prefixWord ++ tailWord_6459172) baseStart_6459172 baseEnd_6459172 := by
    simpa [prefixWord, tailWord_6459172, baseEnd_6459172] using wordTrace_append hprefix tailTrace_6459172
  have hstable : (prefixWord ++ tailWord_6459172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459172).length < 2 ^ (prefixWord ++ tailWord_6459172).sum := by decide
  have hdescent : baseEnd_6459172 < baseStart_6459172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459218 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_6459218 : Nat := 118140960795 + 6459218 * 2 ^ 59
def prefixEnd_6459218 : Nat := 4983230072969 + 3 ^ 40 * 6459218 * 2
def baseEnd_6459218 : Nat := 1105561162057671504523201

theorem tailTrace_6459218 : CollatzResearch.WordTrace tailWord_6459218 prefixEnd_6459218 1105561162057671504523201 := by
  unfold tailWord_6459218
  simp only [CollatzResearch.WordTrace]
  refine ⟨58896758678340951863380577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157058023142242538302348205 58896758678340951863380577)
  ·
    refine ⟨44172569008755713897535433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58896758678340951863380577 44172569008755713897535433)
    ·
      refine ⟨33129426756566785423151575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44172569008755713897535433 33129426756566785423151575)
      ·
        refine ⟨49694140134850178134727363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33129426756566785423151575 49694140134850178134727363)
        ·
          refine ⟨74541210202275267202091045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49694140134850178134727363 74541210202275267202091045)
          ·
            refine ⟨13976476912926612600392071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74541210202275267202091045 13976476912926612600392071)
            ·
              refine ⟨20964715369389918900588107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13976476912926612600392071 20964715369389918900588107)
              ·
                refine ⟨31447073054084878350882161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20964715369389918900588107 31447073054084878350882161)
                ·
                  refine ⟨23585304790563658763161621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31447073054084878350882161 23585304790563658763161621)
                  ·
                    refine ⟨1105561162057671504523201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23585304790563658763161621 1105561162057671504523201)
                    ·
                      rfl

theorem cell23_6459218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_6459218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459218 prefixEnd_6459218 := by exact prefixLift 6459218
  have htrace : WordTrace (prefixWord ++ tailWord_6459218) baseStart_6459218 baseEnd_6459218 := by
    simpa [prefixWord, tailWord_6459218, baseEnd_6459218] using wordTrace_append hprefix tailTrace_6459218
  have hstable : (prefixWord ++ tailWord_6459218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459218).length < 2 ^ (prefixWord ++ tailWord_6459218).sum := by decide
  have hdescent : baseEnd_6459218 < baseStart_6459218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6459225 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 1, 4, 2]
def baseStart_6459225 : Nat := 118140960795 + 6459225 * 2 ^ 59
def prefixEnd_6459225 : Nat := 4983230072969 + 3 ^ 40 * 6459225 * 2
def baseEnd_6459225 : Nat := 3316687080537595986182071

theorem tailTrace_6459225 : CollatzResearch.WordTrace tailWord_6459225 prefixEnd_6459225 3316687080537595986182071 := by
  unfold tailWord_6459225
  simp only [CollatzResearch.WordTrace]
  refine ⟨235587290024338447649027129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157058193349558965099351419 235587290024338447649027129)
  ·
    refine ⟨176690467518253835736770347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235587290024338447649027129 176690467518253835736770347)
    ·
      refine ⟨265035701277380753605155521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176690467518253835736770347 265035701277380753605155521)
      ·
        refine ⟨198776775958035565203866641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265035701277380753605155521 198776775958035565203866641)
        ·
          refine ⟨149082581968526673902899981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198776775958035565203866641 149082581968526673902899981)
          ·
            refine ⟨55905968238197502713587493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149082581968526673902899981 55905968238197502713587493)
            ·
              refine ⟨10482369044662031758797655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55905968238197502713587493 10482369044662031758797655)
              ·
                refine ⟨15723553566993047638196483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10482369044662031758797655 15723553566993047638196483)
                ·
                  refine ⟨23585330350489571457294725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15723553566993047638196483 23585330350489571457294725)
                  ·
                    refine ⟨4422249440716794648242761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23585330350489571457294725 4422249440716794648242761)
                    ·
                      refine ⟨3316687080537595986182071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4422249440716794648242761 3316687080537595986182071)
                      ·
                        rfl

theorem cell23_6459225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_6459225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6459225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6459225 prefixEnd_6459225 := by exact prefixLift 6459225
  have htrace : WordTrace (prefixWord ++ tailWord_6459225) baseStart_6459225 baseEnd_6459225 := by
    simpa [prefixWord, tailWord_6459225, baseEnd_6459225] using wordTrace_append hprefix tailTrace_6459225
  have hstable : (prefixWord ++ tailWord_6459225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6459225).length < 2 ^ (prefixWord ++ tailWord_6459225).sum := by decide
  have hdescent : baseEnd_6459225 < baseStart_6459225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6459225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
