import V185TrunkScan23Chunk1350

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8000636 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_8000636 : Nat := 118140960795 + 8000636 * 2 ^ 59
def prefixEnd_8000636 : Nat := 4983230072969 + 3 ^ 40 * 8000636 * 2
def baseEnd_8000636 : Nat := 4108171809665064708555751

theorem tailTrace_8000636 : CollatzResearch.WordTrace tailWord_8000636 prefixEnd_8000636 4108171809665064708555751 := by
  unfold tailWord_8000636
  simp only [CollatzResearch.WordTrace]
  refine ⟨145903583921534823344630881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194538111895379764459507841 145903583921534823344630881)
  ·
    refine ⟨109427687941151117508473161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145903583921534823344630881 109427687941151117508473161)
    ·
      refine ⟨82070765955863338131354871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109427687941151117508473161 82070765955863338131354871)
      ·
        refine ⟨123106148933795007197032307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82070765955863338131354871 123106148933795007197032307)
        ·
          refine ⟨184659223400692510795548461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123106148933795007197032307 184659223400692510795548461)
          ·
            refine ⟨69247208775259691548330673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184659223400692510795548461 69247208775259691548330673)
            ·
              refine ⟨51935406581444768661248005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69247208775259691548330673 51935406581444768661248005)
              ·
                refine ⟨9737888734020894123984001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51935406581444768661248005 9737888734020894123984001)
                ·
                  refine ⟨7303416550515670592988001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9737888734020894123984001 7303416550515670592988001)
                  ·
                    refine ⟨5477562412886752944741001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7303416550515670592988001 5477562412886752944741001)
                    ·
                      refine ⟨4108171809665064708555751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477562412886752944741001 4108171809665064708555751)
                      ·
                        rfl

theorem cell23_8000636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_8000636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000636 prefixEnd_8000636 := by exact prefixLift 8000636
  have htrace : WordTrace (prefixWord ++ tailWord_8000636) baseStart_8000636 baseEnd_8000636 := by
    simpa [prefixWord, tailWord_8000636, baseEnd_8000636] using wordTrace_append hprefix tailTrace_8000636
  have hstable : (prefixWord ++ tailWord_8000636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000636).length < 2 ^ (prefixWord ++ tailWord_8000636).sum := by decide
  have hdescent : baseEnd_8000636 < baseStart_8000636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000652 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_8000652 : Nat := 118140960795 + 8000652 * 2 ^ 59
def prefixEnd_8000652 : Nat := 4983230072969 + 3 ^ 40 * 8000652 * 2
def baseEnd_8000652 : Nat := 4108180025355536645955677

theorem tailTrace_8000652 : CollatzResearch.WordTrace tailWord_8000652 prefixEnd_8000652 4108180025355536645955677 := by
  unfold tailWord_8000652
  simp only [CollatzResearch.WordTrace]
  refine ⟨145903875705505840710922105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194538500940674454281229473 145903875705505840710922105)
  ·
    refine ⟨109427906779129380533191579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145903875705505840710922105 109427906779129380533191579)
    ·
      refine ⟨164141860168694070799787369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109427906779129380533191579 164141860168694070799787369)
      ·
        refine ⟨123106395126520553099840527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164141860168694070799787369 123106395126520553099840527)
        ·
          refine ⟨184659592689780829649760791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123106395126520553099840527 184659592689780829649760791)
          ·
            refine ⟨276989389034671244474641187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184659592689780829649760791 276989389034671244474641187)
            ·
              refine ⟨415484083552006866711961781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276989389034671244474641187 415484083552006866711961781)
              ·
                refine ⟨38951632833000643754246417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 415484083552006866711961781 38951632833000643754246417)
                ·
                  refine ⟨29213724624750482815684813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38951632833000643754246417 29213724624750482815684813)
                  ·
                    refine ⟨10955146734281431055881805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29213724624750482815684813 10955146734281431055881805)
                    ·
                      refine ⟨4108180025355536645955677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10955146734281431055881805 4108180025355536645955677)
                      ·
                        rfl

theorem cell23_8000652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_8000652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000652 prefixEnd_8000652 := by exact prefixLift 8000652
  have htrace : WordTrace (prefixWord ++ tailWord_8000652) baseStart_8000652 baseEnd_8000652 := by
    simpa [prefixWord, tailWord_8000652, baseEnd_8000652] using wordTrace_append hprefix tailTrace_8000652
  have hstable : (prefixWord ++ tailWord_8000652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000652).length < 2 ^ (prefixWord ++ tailWord_8000652).sum := by decide
  have hdescent : baseEnd_8000652 < baseStart_8000652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000689 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 2, 5]
def baseStart_8000689 : Nat := 118140960795 + 8000689 * 2 ^ 59
def prefixEnd_8000689 : Nat := 4983230072969 + 3 ^ 40 * 8000689 * 2
def baseEnd_8000689 : Nat := 1369399674713251000397669

theorem tailTrace_8000689 : CollatzResearch.WordTrace tailWord_8000689 prefixEnd_8000689 1369399674713251000397669 := by
  unfold tailWord_8000689
  simp only [CollatzResearch.WordTrace]
  refine ⟨291809100911877636740941121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194539400607918424493960747 291809100911877636740941121)
  ·
    refine ⟨218856825683908227555705841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291809100911877636740941121 218856825683908227555705841)
    ·
      refine ⟨164142619262931170666779381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218856825683908227555705841 164142619262931170666779381)
      ·
        refine ⟨15388370555899797250010567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164142619262931170666779381 15388370555899797250010567)
        ·
          refine ⟨23082555833849695875015851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15388370555899797250010567 23082555833849695875015851)
          ·
            refine ⟨34623833750774543812523777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23082555833849695875015851 34623833750774543812523777)
            ·
              refine ⟨25967875313080907859392833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34623833750774543812523777 25967875313080907859392833)
              ·
                refine ⟨19475906484810680894544625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25967875313080907859392833 19475906484810680894544625)
                ·
                  refine ⟨14606929863608010670908469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19475906484810680894544625 14606929863608010670908469)
                  ·
                    refine ⟨1369399674713251000397669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14606929863608010670908469 1369399674713251000397669)
                    ·
                      rfl

theorem cell23_8000689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_8000689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000689 prefixEnd_8000689 := by exact prefixLift 8000689
  have htrace : WordTrace (prefixWord ++ tailWord_8000689) baseStart_8000689 baseEnd_8000689 := by
    simpa [prefixWord, tailWord_8000689, baseEnd_8000689] using wordTrace_append hprefix tailTrace_8000689
  have hstable : (prefixWord ++ tailWord_8000689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000689).length < 2 ^ (prefixWord ++ tailWord_8000689).sum := by decide
  have hdescent : baseEnd_8000689 < baseStart_8000689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000736 : List Nat := [2, 1, 1, 3, 1, 4, 1, 5, 1, 4]
def baseStart_8000736 : Nat := 118140960795 + 8000736 * 2 ^ 59
def prefixEnd_8000736 : Nat := 4983230072969 + 3 ^ 40 * 8000736 * 2
def baseEnd_8000736 : Nat := 1369407719243504772435097

theorem tailTrace_8000736 : CollatzResearch.WordTrace tailWord_8000736 prefixEnd_8000736 1369407719243504772435097 := by
  unfold tailWord_8000736
  simp only [CollatzResearch.WordTrace]
  refine ⟨145905407571353681883951031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194540543428471575845268041 145905407571353681883951031)
  ·
    refine ⟨218858111357030522825926547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145905407571353681883951031 218858111357030522825926547)
    ·
      refine ⟨328287167035545784238889821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218858111357030522825926547 328287167035545784238889821)
      ·
        refine ⟨123107687638329669089583683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328287167035545784238889821 123107687638329669089583683)
        ·
          refine ⟨184661531457494503634375525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123107687638329669089583683 184661531457494503634375525)
          ·
            refine ⟨34624037148280219431445411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184661531457494503634375525 34624037148280219431445411)
            ·
              refine ⟨51936055722420329147168117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34624037148280219431445411 51936055722420329147168117)
              ·
                refine ⟨4869005223976905857547011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51936055722420329147168117 4869005223976905857547011)
                ·
                  refine ⟨7303507835965358786320517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869005223976905857547011 7303507835965358786320517)
                  ·
                    refine ⟨1369407719243504772435097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7303507835965358786320517 1369407719243504772435097)
                    ·
                      rfl

theorem cell23_8000736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 4].length) (baseStart_8000736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000736 prefixEnd_8000736 := by exact prefixLift 8000736
  have htrace : WordTrace (prefixWord ++ tailWord_8000736) baseStart_8000736 baseEnd_8000736 := by
    simpa [prefixWord, tailWord_8000736, baseEnd_8000736] using wordTrace_append hprefix tailTrace_8000736
  have hstable : (prefixWord ++ tailWord_8000736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000736).length < 2 ^ (prefixWord ++ tailWord_8000736).sum := by decide
  have hdescent : baseEnd_8000736 < baseStart_8000736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000749 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 8]
def baseStart_8000749 : Nat := 118140960795 + 8000749 * 2 ^ 59
def prefixEnd_8000749 : Nat := 4983230072969 + 3 ^ 40 * 8000749 * 2
def baseEnd_8000749 : Nat := 456469981442113640715859

theorem tailTrace_8000749 : CollatzResearch.WordTrace tailWord_8000749 prefixEnd_8000749 456469981442113640715859 := by
  unfold tailWord_8000749
  simp only [CollatzResearch.WordTrace]
  refine ⟨291811289291660266988125301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194540859527773511325416867 291811289291660266988125301)
  ·
    refine ⟨27357308371093150030136747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291811289291660266988125301 27357308371093150030136747)
    ·
      refine ⟨41035962556639725045205121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27357308371093150030136747 41035962556639725045205121)
      ·
        refine ⟨30776971917479793783903841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41035962556639725045205121 30776971917479793783903841)
        ·
          refine ⟨23082728938109845337927881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30776971917479793783903841 23082728938109845337927881)
          ·
            refine ⟨17312046703582384003445911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23082728938109845337927881 17312046703582384003445911)
            ·
              refine ⟨25968070055373576005168867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17312046703582384003445911 25968070055373576005168867)
              ·
                refine ⟨38952105083060364007753301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25968070055373576005168867 38952105083060364007753301)
                ·
                  refine ⟨456469981442113640715859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38952105083060364007753301 456469981442113640715859)
                  ·
                    rfl

theorem cell23_8000749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_8000749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000749 prefixEnd_8000749 := by exact prefixLift 8000749
  have htrace : WordTrace (prefixWord ++ tailWord_8000749) baseStart_8000749 baseEnd_8000749 := by
    simpa [prefixWord, tailWord_8000749, baseEnd_8000749] using wordTrace_append hprefix tailTrace_8000749
  have hstable : (prefixWord ++ tailWord_8000749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000749).length < 2 ^ (prefixWord ++ tailWord_8000749).sum := by decide
  have hdescent : baseEnd_8000749 < baseStart_8000749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000759 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_8000759 : Nat := 118140960795 + 8000759 * 2 ^ 59
def prefixEnd_8000759 : Nat := 4983230072969 + 3 ^ 40 * 8000759 * 2
def baseEnd_8000759 : Nat := 4108234967785567727317685

theorem tailTrace_8000759 : CollatzResearch.WordTrace tailWord_8000759 prefixEnd_8000759 4108234967785567727317685 := by
  unfold tailWord_8000759
  simp only [CollatzResearch.WordTrace]
  refine ⟨291811654021624038695989331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194541102681082692463992887 291811654021624038695989331)
  ·
    refine ⟨437717481032436058043983997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291811654021624038695989331 437717481032436058043983997)
    ·
      refine ⟨164144055387163521766493999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437717481032436058043983997 164144055387163521766493999)
      ·
        refine ⟨246216083080745282649740999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164144055387163521766493999 246216083080745282649740999)
        ·
          refine ⟨369324124621117923974611499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246216083080745282649740999 369324124621117923974611499)
          ·
            refine ⟨553986186931676885961917249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369324124621117923974611499 553986186931676885961917249)
            ·
              refine ⟨415489640198757664471437937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553986186931676885961917249 415489640198757664471437937)
              ·
                refine ⟨311617230149068248353578453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415489640198757664471437937 311617230149068248353578453)
                ·
                  refine ⟨7303528831618787070786995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 311617230149068248353578453 7303528831618787070786995)
                  ·
                    refine ⟨10955293247428180606180493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303528831618787070786995 10955293247428180606180493)
                    ·
                      refine ⟨4108234967785567727317685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10955293247428180606180493 4108234967785567727317685)
                      ·
                        rfl

theorem cell23_8000759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_8000759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000759 prefixEnd_8000759 := by exact prefixLift 8000759
  have htrace : WordTrace (prefixWord ++ tailWord_8000759) baseStart_8000759 baseEnd_8000759 := by
    simpa [prefixWord, tailWord_8000759, baseEnd_8000759] using wordTrace_append hprefix tailTrace_8000759
  have hstable : (prefixWord ++ tailWord_8000759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000759).length < 2 ^ (prefixWord ++ tailWord_8000759).sum := by decide
  have hdescent : baseEnd_8000759 < baseStart_8000759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000779 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 1, 5]
def baseStart_8000779 : Nat := 118140960795 + 8000779 * 2 ^ 59
def prefixEnd_8000779 : Nat := 4983230072969 + 3 ^ 40 * 8000779 * 2
def baseEnd_8000779 : Nat := 1369415079132885883022531

theorem tailTrace_8000779 : CollatzResearch.WordTrace tailWord_8000779 prefixEnd_8000779 1369415079132885883022531 := by
  unfold tailWord_8000779
  simp only [CollatzResearch.WordTrace]
  refine ⟨291812383481551582111717391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194541588987701054741144927 291812383481551582111717391)
  ·
    refine ⟨437718575222327373167576087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291812383481551582111717391 437718575222327373167576087)
    ·
      refine ⟨656577862833491059751364131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437718575222327373167576087 656577862833491059751364131)
      ·
        refine ⟨984866794250236589627046197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656577862833491059751364131 984866794250236589627046197)
        ·
          refine ⟨92331261960959680277535581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 984866794250236589627046197 92331261960959680277535581)
          ·
            refine ⟨34624223235359880104075843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92331261960959680277535581 34624223235359880104075843)
            ·
              refine ⟨51936334853039820156113765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34624223235359880104075843 51936334853039820156113765)
              ·
                refine ⟨9738062784944966279271331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51936334853039820156113765 9738062784944966279271331)
                ·
                  refine ⟨14607094177417449418906997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9738062784944966279271331 14607094177417449418906997)
                  ·
                    refine ⟨1369415079132885883022531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14607094177417449418906997 1369415079132885883022531)
                    ·
                      rfl

theorem cell23_8000779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 5].length) (baseStart_8000779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000779 prefixEnd_8000779 := by exact prefixLift 8000779
  have htrace : WordTrace (prefixWord ++ tailWord_8000779) baseStart_8000779 baseEnd_8000779 := by
    simpa [prefixWord, tailWord_8000779, baseEnd_8000779] using wordTrace_append hprefix tailTrace_8000779
  have hstable : (prefixWord ++ tailWord_8000779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000779).length < 2 ^ (prefixWord ++ tailWord_8000779).sum := by decide
  have hdescent : baseEnd_8000779 < baseStart_8000779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000810 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_8000810 : Nat := 118140960795 + 8000810 * 2 ^ 59
def prefixEnd_8000810 : Nat := 4983230072969 + 3 ^ 40 * 8000810 * 2
def baseEnd_8000810 : Nat := 4108261155298947027779951

theorem tailTrace_8000810 : CollatzResearch.WordTrace tailWord_8000810 prefixEnd_8000810 4108261155298947027779951 := by
  unfold tailWord_8000810
  simp only [CollatzResearch.WordTrace]
  refine ⟨72953378536109818601523971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194542342762959516270730589 72953378536109818601523971)
  ·
    refine ⟨109430067804164727902285957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72953378536109818601523971 109430067804164727902285957)
    ·
      refine ⟨20518137713280886481678617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109430067804164727902285957 20518137713280886481678617)
      ·
        refine ⟨15388603284960664861258963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20518137713280886481678617 15388603284960664861258963)
        ·
          refine ⟨23082904927440997291888445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15388603284960664861258963 23082904927440997291888445)
          ·
            refine ⟨8656089347790373984458167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23082904927440997291888445 8656089347790373984458167)
            ·
              refine ⟨12984134021685560976687251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656089347790373984458167 12984134021685560976687251)
              ·
                refine ⟨19476201032528341465030877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12984134021685560976687251 19476201032528341465030877)
                ·
                  refine ⟨7303575387198128049386579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19476201032528341465030877 7303575387198128049386579)
                  ·
                    refine ⟨10955363080797192074079869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303575387198128049386579 10955363080797192074079869)
                    ·
                      refine ⟨4108261155298947027779951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10955363080797192074079869 4108261155298947027779951)
                      ·
                        rfl

theorem cell23_8000810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_8000810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000810 prefixEnd_8000810 := by exact prefixLift 8000810
  have htrace : WordTrace (prefixWord ++ tailWord_8000810) baseStart_8000810 baseEnd_8000810 := by
    simpa [prefixWord, tailWord_8000810, baseEnd_8000810] using wordTrace_append hprefix tailTrace_8000810
  have hstable : (prefixWord ++ tailWord_8000810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000810).length < 2 ^ (prefixWord ++ tailWord_8000810).sum := by decide
  have hdescent : baseEnd_8000810 < baseStart_8000810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000819 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5]
def baseStart_8000819 : Nat := 118140960795 + 8000819 * 2 ^ 59
def prefixEnd_8000819 : Nat := 4983230072969 + 3 ^ 40 * 8000819 * 2
def baseEnd_8000819 : Nat := 4108265776624837492567409

theorem tailTrace_8000819 : CollatzResearch.WordTrace tailWord_8000819 prefixEnd_8000819 4108265776624837492567409 := by
  unfold tailWord_8000819
  simp only [CollatzResearch.WordTrace]
  refine ⟨291813842401406668943173511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194542561600937779295449007 291813842401406668943173511)
  ·
    refine ⟨437720763602110003414760267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291813842401406668943173511 437720763602110003414760267)
    ·
      refine ⟨656581145403165005122140401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437720763602110003414760267 656581145403165005122140401)
      ·
        refine ⟨492435859052373753841605301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656581145403165005122140401 492435859052373753841605301)
        ·
          refine ⟨46165861786160039422650497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492435859052373753841605301 46165861786160039422650497)
          ·
            refine ⟨34624396339620029566987873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46165861786160039422650497 34624396339620029566987873)
            ·
              refine ⟨25968297254715022175240905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34624396339620029566987873 25968297254715022175240905)
              ·
                refine ⟨19476222941036266631430679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25968297254715022175240905 19476222941036266631430679)
                ·
                  refine ⟨29214334411554399947146019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19476222941036266631430679 29214334411554399947146019)
                  ·
                    refine ⟨43821501617331599920719029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29214334411554399947146019 43821501617331599920719029)
                    ·
                      refine ⟨4108265776624837492567409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43821501617331599920719029 4108265776624837492567409)
                      ·
                        rfl

theorem cell23_8000819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_8000819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000819 prefixEnd_8000819 := by exact prefixLift 8000819
  have htrace : WordTrace (prefixWord ++ tailWord_8000819) baseStart_8000819 baseEnd_8000819 := by
    simpa [prefixWord, tailWord_8000819, baseEnd_8000819] using wordTrace_append hprefix tailTrace_8000819
  have hstable : (prefixWord ++ tailWord_8000819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000819).length < 2 ^ (prefixWord ++ tailWord_8000819).sum := by decide
  have hdescent : baseEnd_8000819 < baseStart_8000819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000826 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_8000826 : Nat := 118140960795 + 8000826 * 2 ^ 59
def prefixEnd_8000826 : Nat := 4983230072969 + 3 ^ 40 * 8000826 * 2
def baseEnd_8000826 : Nat := 1369423123663139655059959

theorem tailTrace_8000826 : CollatzResearch.WordTrace tailWord_8000826 prefixEnd_8000826 1369423123663139655059959 := by
  unfold tailWord_8000826
  simp only [CollatzResearch.WordTrace]
  refine ⟨72953524428095327284669583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194542731808254206092452221 72953524428095327284669583)
  ·
    refine ⟨109430286642142990927004375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72953524428095327284669583 109430286642142990927004375)
    ·
      refine ⟨164145429963214486390506563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109430286642142990927004375 164145429963214486390506563)
      ·
        refine ⟨246218144944821729585759845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164145429963214486390506563 246218144944821729585759845)
        ·
          refine ⟨46165902177154074297329971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246218144944821729585759845 46165902177154074297329971)
          ·
            refine ⟨69248853265731111445994957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46165902177154074297329971 69248853265731111445994957)
            ·
              refine ⟨25968319974649166792248109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69248853265731111445994957 25968319974649166792248109)
              ·
                refine ⟨9738119990493437547093041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25968319974649166792248109 9738119990493437547093041)
                ·
                  refine ⟨7303589992870078160319781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9738119990493437547093041 7303589992870078160319781)
                  ·
                    refine ⟨1369423123663139655059959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7303589992870078160319781 1369423123663139655059959)
                    ·
                      rfl

theorem cell23_8000826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_8000826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000826 prefixEnd_8000826 := by exact prefixLift 8000826
  have htrace : WordTrace (prefixWord ++ tailWord_8000826) baseStart_8000826 baseEnd_8000826 := by
    simpa [prefixWord, tailWord_8000826, baseEnd_8000826] using wordTrace_append hprefix tailTrace_8000826
  have hstable : (prefixWord ++ tailWord_8000826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000826).length < 2 ^ (prefixWord ++ tailWord_8000826).sum := by decide
  have hdescent : baseEnd_8000826 < baseStart_8000826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000833 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_8000833 : Nat := 118140960795 + 8000833 * 2 ^ 59
def prefixEnd_8000833 : Nat := 4983230072969 + 3 ^ 40 * 8000833 * 2
def baseEnd_8000833 : Nat := 4108272965354000437792345

theorem tailTrace_8000833 : CollatzResearch.WordTrace tailWord_8000833 prefixEnd_8000833 4108272965354000437792345 := by
  unfold tailWord_8000833
  simp only [CollatzResearch.WordTrace]
  refine ⟨291814353023355949334183153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194542902015570632889455435 291814353023355949334183153)
  ·
    refine ⟨218860764767516962000637365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291814353023355949334183153 218860764767516962000637365)
    ·
      refine ⟨20518196696954715187559753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218860764767516962000637365 20518196696954715187559753)
      ·
        refine ⟨15388647522716036390669815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20518196696954715187559753 15388647522716036390669815)
        ·
          refine ⟨23082971284074054586004723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15388647522716036390669815 23082971284074054586004723)
          ·
            refine ⟨34624456926111081879007085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23082971284074054586004723 34624456926111081879007085)
            ·
              refine ⟨12984171347291655704627657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34624456926111081879007085 12984171347291655704627657)
              ·
                refine ⟨9738128510468741778470743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12984171347291655704627657 9738128510468741778470743)
                ·
                  refine ⟨14607192765703112667706115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9738128510468741778470743 14607192765703112667706115)
                  ·
                    refine ⟨21910789148554669001559173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14607192765703112667706115 21910789148554669001559173)
                    ·
                      refine ⟨4108272965354000437792345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21910789148554669001559173 4108272965354000437792345)
                      ·
                        rfl

theorem cell23_8000833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_8000833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000833 prefixEnd_8000833 := by exact prefixLift 8000833
  have htrace : WordTrace (prefixWord ++ tailWord_8000833) baseStart_8000833 baseEnd_8000833 := by
    simpa [prefixWord, tailWord_8000833, baseEnd_8000833] using wordTrace_append hprefix tailTrace_8000833
  have hstable : (prefixWord ++ tailWord_8000833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000833).length < 2 ^ (prefixWord ++ tailWord_8000833).sum := by decide
  have hdescent : baseEnd_8000833 < baseStart_8000833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000850 : List Nat := [3, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_8000850 : Nat := 118140960795 + 8000850 * 2 ^ 59
def prefixEnd_8000850 : Nat := 4983230072969 + 3 ^ 40 * 8000850 * 2
def baseEnd_8000850 : Nat := 4108281694525126871279767

theorem tailTrace_8000850 : CollatzResearch.WordTrace tailWord_8000850 prefixEnd_8000850 4108281694525126871279767 := by
  unfold tailWord_8000850
  simp only [CollatzResearch.WordTrace]
  refine ⟨72953743266073590309388001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194543315376196240825034669 72953743266073590309388001)
  ·
    refine ⟨54715307449555192732041001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72953743266073590309388001 54715307449555192732041001)
    ·
      refine ⟨41036480587166394549030751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54715307449555192732041001 41036480587166394549030751)
      ·
        refine ⟨61554720880749591823546127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41036480587166394549030751 61554720880749591823546127)
        ·
          refine ⟨92332081321124387735319191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61554720880749591823546127 92332081321124387735319191)
          ·
            refine ⟨138498121981686581602978787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92332081321124387735319191 138498121981686581602978787)
            ·
              refine ⟨207747182972529872404468181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138498121981686581602978787 207747182972529872404468181)
              ·
                refine ⟨4869074600918668884479723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207747182972529872404468181 4869074600918668884479723)
                ·
                  refine ⟨7303611901378003326719585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869074600918668884479723 7303611901378003326719585)
                  ·
                    refine ⟨5477708926033502495039689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7303611901378003326719585 5477708926033502495039689)
                    ·
                      refine ⟨4108281694525126871279767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477708926033502495039689 4108281694525126871279767)
                      ·
                        rfl

theorem cell23_8000850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_8000850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000850 prefixEnd_8000850 := by exact prefixLift 8000850
  have htrace : WordTrace (prefixWord ++ tailWord_8000850) baseStart_8000850 baseEnd_8000850 := by
    simpa [prefixWord, tailWord_8000850, baseEnd_8000850] using wordTrace_append hprefix tailTrace_8000850
  have hstable : (prefixWord ++ tailWord_8000850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000850).length < 2 ^ (prefixWord ++ tailWord_8000850).sum := by decide
  have hdescent : baseEnd_8000850 < baseStart_8000850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000866 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_8000866 : Nat := 118140960795 + 8000866 * 2 ^ 59
def prefixEnd_8000866 : Nat := 4983230072969 + 3 ^ 40 * 8000866 * 2
def baseEnd_8000866 : Nat := 4108289910215598808679693

theorem tailTrace_8000866 : CollatzResearch.WordTrace tailWord_8000866 prefixEnd_8000866 4108289910215598808679693 := by
  unfold tailWord_8000866
  simp only [CollatzResearch.WordTrace]
  refine ⟨72953889158059098992533613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194543704421490930646756301 72953889158059098992533613)
  ·
    refine ⟨27357708434272162122200105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72953889158059098992533613 27357708434272162122200105)
    ·
      refine ⟨20518281325704121591650079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27357708434272162122200105 20518281325704121591650079)
      ·
        refine ⟨30777421988556182387475119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20518281325704121591650079 30777421988556182387475119)
        ·
          refine ⟨46166132982834273581212679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30777421988556182387475119 46166132982834273581212679)
          ·
            refine ⟨69249199474251410371819019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46166132982834273581212679 69249199474251410371819019)
            ·
              refine ⟨103873799211377115557728529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69249199474251410371819019 103873799211377115557728529)
              ·
                refine ⟨77905349408532836668296397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103873799211377115557728529 77905349408532836668296397)
                ·
                  refine ⟨29214506028199813750611149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77905349408532836668296397 29214506028199813750611149)
                  ·
                    refine ⟨10955439760574930156479181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29214506028199813750611149 10955439760574930156479181)
                    ·
                      refine ⟨4108289910215598808679693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10955439760574930156479181 4108289910215598808679693)
                      ·
                        rfl

theorem cell23_8000866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_8000866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000866 prefixEnd_8000866 := by exact prefixLift 8000866
  have htrace : WordTrace (prefixWord ++ tailWord_8000866) baseStart_8000866 baseEnd_8000866 := by
    simpa [prefixWord, tailWord_8000866, baseEnd_8000866] using wordTrace_append hprefix tailTrace_8000866
  have hstable : (prefixWord ++ tailWord_8000866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000866).length < 2 ^ (prefixWord ++ tailWord_8000866).sum := by decide
  have hdescent : baseEnd_8000866 < baseStart_8000866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000867 : List Nat := [1, 1, 1, 5, 2, 2, 4, 2, 1, 2, 2]
def baseStart_8000867 : Nat := 118140960795 + 8000867 * 2 ^ 59
def prefixEnd_8000867 : Nat := 4983230072969 + 3 ^ 40 * 8000867 * 2
def baseEnd_8000867 : Nat := 4108290423696253304767189

theorem tailTrace_8000867 : CollatzResearch.WordTrace tailWord_8000867 prefixEnd_8000867 4108290423696253304767189 := by
  unfold tailWord_8000867
  simp only [CollatzResearch.WordTrace]
  refine ⟨291815593105232773140920855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194543728736821848760613903 291815593105232773140920855)
  ·
    refine ⟨437723389657849159711381283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291815593105232773140920855 437723389657849159711381283)
    ·
      refine ⟨656585084486773739567071925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437723389657849159711381283 656585084486773739567071925)
      ·
        refine ⟨61554851670635038084412993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656585084486773739567071925 61554851670635038084412993)
        ·
          refine ⟨46166138752976278563309745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61554851670635038084412993 46166138752976278563309745)
          ·
            refine ⟨34624604064732208922482309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46166138752976278563309745 34624604064732208922482309)
            ·
              refine ⟨6492113262137289172965433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34624604064732208922482309 6492113262137289172965433)
              ·
                refine ⟨4869084946602966879724075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492113262137289172965433 4869084946602966879724075)
                ·
                  refine ⟨7303627419904450319586113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869084946602966879724075 7303627419904450319586113)
                  ·
                    refine ⟨5477720564928337739689585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7303627419904450319586113 5477720564928337739689585)
                    ·
                      refine ⟨4108290423696253304767189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477720564928337739689585 4108290423696253304767189)
                      ·
                        rfl

theorem cell23_8000867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_8000867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000867 prefixEnd_8000867 := by exact prefixLift 8000867
  have htrace : WordTrace (prefixWord ++ tailWord_8000867) baseStart_8000867 baseEnd_8000867 := by
    simpa [prefixWord, tailWord_8000867, baseEnd_8000867] using wordTrace_append hprefix tailTrace_8000867
  have hstable : (prefixWord ++ tailWord_8000867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000867).length < 2 ^ (prefixWord ++ tailWord_8000867).sum := by decide
  have hdescent : baseEnd_8000867 < baseStart_8000867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000893 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_8000893 : Nat := 118140960795 + 8000893 * 2 ^ 59
def prefixEnd_8000893 : Nat := 4983230072969 + 3 ^ 40 * 8000893 * 2
def baseEnd_8000893 : Nat := 4108303774193270203042069

theorem tailTrace_8000893 : CollatzResearch.WordTrace tailWord_8000893 prefixEnd_8000893 4108303774193270203042069 := by
  unfold tailWord_8000893
  simp only [CollatzResearch.WordTrace]
  refine ⟨291816541403138579581367333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194544360935425719720911555 291816541403138579581367333)
  ·
    refine ⟨54715601513088483671506375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291816541403138579581367333 54715601513088483671506375)
    ·
      refine ⟨82073402269632725507259563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54715601513088483671506375 82073402269632725507259563)
      ·
        refine ⟨123110103404449088260889345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82073402269632725507259563 123110103404449088260889345)
        ·
          refine ⟨92332577553336816195667009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123110103404449088260889345 92332577553336816195667009)
          ·
            refine ⟨69249433165002612146750257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92332577553336816195667009 69249433165002612146750257)
            ·
              refine ⟨51937074873751959110062693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69249433165002612146750257 51937074873751959110062693)
              ·
                refine ⟨9738201538828492333136755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51937074873751959110062693 9738201538828492333136755)
                ·
                  refine ⟨14607302308242738499705133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9738201538828492333136755 14607302308242738499705133)
                  ·
                    refine ⟨5477738365591026937389425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14607302308242738499705133 5477738365591026937389425)
                    ·
                      refine ⟨4108303774193270203042069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477738365591026937389425 4108303774193270203042069)
                      ·
                        rfl

theorem cell23_8000893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_8000893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000893 prefixEnd_8000893 := by exact prefixLift 8000893
  have htrace : WordTrace (prefixWord ++ tailWord_8000893) baseStart_8000893 baseEnd_8000893 := by
    simpa [prefixWord, tailWord_8000893, baseEnd_8000893] using wordTrace_append hprefix tailTrace_8000893
  have hstable : (prefixWord ++ tailWord_8000893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000893).length < 2 ^ (prefixWord ++ tailWord_8000893).sum := by decide
  have hdescent : baseEnd_8000893 < baseStart_8000893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000916 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_8000916 : Nat := 118140960795 + 8000916 * 2 ^ 59
def prefixEnd_8000916 : Nat := 4983230072969 + 3 ^ 40 * 8000916 * 2
def baseEnd_8000916 : Nat := 1369438528082774537684821

theorem tailTrace_8000916 : CollatzResearch.WordTrace tailWord_8000916 prefixEnd_8000916 1369438528082774537684821 := by
  unfold tailWord_8000916
  simp only [CollatzResearch.WordTrace]
  refine ⟨145908690141027627254727301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194544920188036836339636401 145908690141027627254727301)
  ·
    refine ⟨27357879401442680110261369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145908690141027627254727301 27357879401442680110261369)
    ·
      refine ⟨20518409551082010082696027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27357879401442680110261369 20518409551082010082696027)
      ·
        refine ⟨30777614326623015124044041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20518409551082010082696027 30777614326623015124044041)
        ·
          refine ⟨23083210744967261343033031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30777614326623015124044041 23083210744967261343033031)
          ·
            refine ⟨34624816117450892014549547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23083210744967261343033031 34624816117450892014549547)
            ·
              refine ⟨51937224176176338021824321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34624816117450892014549547 51937224176176338021824321)
              ·
                refine ⟨38952918132132253516368241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51937224176176338021824321 38952918132132253516368241)
                ·
                  refine ⟨29214688599099190137276181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38952918132132253516368241 29214688599099190137276181)
                  ·
                    refine ⟨1369438528082774537684821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29214688599099190137276181 1369438528082774537684821)
                    ·
                      rfl

theorem cell23_8000916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_8000916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000916 prefixEnd_8000916 := by exact prefixLift 8000916
  have htrace : WordTrace (prefixWord ++ tailWord_8000916) baseStart_8000916 baseEnd_8000916 := by
    simpa [prefixWord, tailWord_8000916, baseEnd_8000916] using wordTrace_append hprefix tailTrace_8000916
  have hstable : (prefixWord ++ tailWord_8000916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000916).length < 2 ^ (prefixWord ++ tailWord_8000916).sum := by decide
  have hdescent : baseEnd_8000916 < baseStart_8000916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000939 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 3]
def baseStart_8000939 : Nat := 118140960795 + 8000939 * 2 ^ 59
def prefixEnd_8000939 : Nat := 4983230072969 + 3 ^ 40 * 8000939 * 2
def baseEnd_8000939 : Nat := 4108327394303377023066857

theorem tailTrace_8000939 : CollatzResearch.WordTrace tailWord_8000939 prefixEnd_8000939 4108327394303377023066857 := by
  unfold tailWord_8000939
  simp only [CollatzResearch.WordTrace]
  refine ⟨291818219160971929437541871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194545479440647952958361247 291818219160971929437541871)
  ·
    refine ⟨437727328741457894156312807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291818219160971929437541871 437727328741457894156312807)
    ·
      refine ⟨656590993112186841234469211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437727328741457894156312807 656590993112186841234469211)
      ·
        refine ⟨984886489668280261851703817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656590993112186841234469211 984886489668280261851703817)
        ·
          refine ⟨738664867251210196388777863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984886489668280261851703817 738664867251210196388777863)
          ·
            refine ⟨1107997300876815294583166795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738664867251210196388777863 1107997300876815294583166795)
            ·
              refine ⟨1661995951315222941874750193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107997300876815294583166795 1661995951315222941874750193)
              ·
                refine ⟨1246496963486417206406062645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661995951315222941874750193 1246496963486417206406062645)
                ·
                  refine ⟨116859090326851613100568373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1246496963486417206406062645 116859090326851613100568373)
                  ·
                    refine ⟨10955539718142338728178285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116859090326851613100568373 10955539718142338728178285)
                    ·
                      refine ⟨4108327394303377023066857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10955539718142338728178285 4108327394303377023066857)
                      ·
                        rfl

theorem cell23_8000939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 3].length) (baseStart_8000939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000939 prefixEnd_8000939 := by exact prefixLift 8000939
  have htrace : WordTrace (prefixWord ++ tailWord_8000939) baseStart_8000939 baseEnd_8000939 := by
    simpa [prefixWord, tailWord_8000939, baseEnd_8000939] using wordTrace_append hprefix tailTrace_8000939
  have hstable : (prefixWord ++ tailWord_8000939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000939).length < 2 ^ (prefixWord ++ tailWord_8000939).sum := by decide
  have hdescent : baseEnd_8000939 < baseStart_8000939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000959 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 6, 5]
def baseStart_8000959 : Nat := 118140960795 + 8000959 * 2 ^ 59
def prefixEnd_8000959 : Nat := 4983230072969 + 3 ^ 40 * 8000959 * 2
def baseEnd_8000959 : Nat := 1369445887972155648272255

theorem tailTrace_8000959 : CollatzResearch.WordTrace tailWord_8000959 prefixEnd_8000959 1369445887972155648272255 := by
  unfold tailWord_8000959
  simp only [CollatzResearch.WordTrace]
  refine ⟨291818948620899472853269931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194545965747266315235513287 291818948620899472853269931)
  ·
    refine ⟨437728422931349209279904897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291818948620899472853269931 437728422931349209279904897)
    ·
      refine ⟨328296317198511906959928673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437728422931349209279904897 328296317198511906959928673)
      ·
        refine ⟨246222237898883930219946505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328296317198511906959928673 246222237898883930219946505)
        ·
          refine ⟨184666678424162947664959879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246222237898883930219946505 184666678424162947664959879)
          ·
            refine ⟨277000017636244421497439819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184666678424162947664959879 277000017636244421497439819)
            ·
              refine ⟨415500026454366632246159729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277000017636244421497439819 415500026454366632246159729)
              ·
                refine ⟨311625019840774974184619797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415500026454366632246159729 311625019840774974184619797)
                ·
                  refine ⟨14607422805036326914904053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311625019840774974184619797 14607422805036326914904053)
                  ·
                    refine ⟨1369445887972155648272255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14607422805036326914904053 1369445887972155648272255)
                    ·
                      rfl

theorem cell23_8000959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_8000959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000959 prefixEnd_8000959 := by exact prefixLift 8000959
  have htrace : WordTrace (prefixWord ++ tailWord_8000959) baseStart_8000959 baseEnd_8000959 := by
    simpa [prefixWord, tailWord_8000959, baseEnd_8000959] using wordTrace_append hprefix tailTrace_8000959
  have hstable : (prefixWord ++ tailWord_8000959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000959).length < 2 ^ (prefixWord ++ tailWord_8000959).sum := by decide
  have hdescent : baseEnd_8000959 < baseStart_8000959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000969 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_8000969 : Nat := 118140960795 + 8000969 * 2 ^ 59
def prefixEnd_8000969 : Nat := 4983230072969 + 3 ^ 40 * 8000969 * 2
def baseEnd_8000969 : Nat := 4108342798723011905691719

theorem tailTrace_8000969 : CollatzResearch.WordTrace tailWord_8000969 prefixEnd_8000969 4108342798723011905691719 := by
  unfold tailWord_8000969
  simp only [CollatzResearch.WordTrace]
  refine ⟨291819313350863244561133961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194546208900575496374089307 291819313350863244561133961)
  ·
    refine ⟨218864485013147433420850471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291819313350863244561133961 218864485013147433420850471)
    ·
      refine ⟨328296727519721150131275707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218864485013147433420850471 328296727519721150131275707)
      ·
        refine ⟨492445091279581725196913561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328296727519721150131275707 492445091279581725196913561)
        ·
          refine ⟨369333818459686293897685171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492445091279581725196913561 369333818459686293897685171)
          ·
            refine ⟨554000727689529440846527757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369333818459686293897685171 554000727689529440846527757)
            ·
              refine ⟨207750272883573540317447909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554000727689529440846527757 207750272883573540317447909)
              ·
                refine ⟨38953176165670038809521483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207750272883573540317447909 38953176165670038809521483)
                ·
                  refine ⟨58429764248505058214282225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38953176165670038809521483 58429764248505058214282225)
                  ·
                    refine ⟨43822323186378793660711669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58429764248505058214282225 43822323186378793660711669)
                    ·
                      refine ⟨4108342798723011905691719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43822323186378793660711669 4108342798723011905691719)
                      ·
                        rfl

theorem cell23_8000969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_8000969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000969 prefixEnd_8000969 := by exact prefixLift 8000969
  have htrace : WordTrace (prefixWord ++ tailWord_8000969) baseStart_8000969 baseEnd_8000969 := by
    simpa [prefixWord, tailWord_8000969, baseEnd_8000969] using wordTrace_append hprefix tailTrace_8000969
  have hstable : (prefixWord ++ tailWord_8000969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000969).length < 2 ^ (prefixWord ++ tailWord_8000969).sum := by decide
  have hdescent : baseEnd_8000969 < baseStart_8000969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000980 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 7]
def baseStart_8000980 : Nat := 118140960795 + 8000980 * 2 ^ 59
def prefixEnd_8000980 : Nat := 4983230072969 + 3 ^ 40 * 8000980 * 2
def baseEnd_8000980 : Nat := 456483160778912373628241

theorem tailTrace_8000980 : CollatzResearch.WordTrace tailWord_8000980 prefixEnd_8000980 456483160778912373628241 := by
  unfold tailWord_8000980
  simp only [CollatzResearch.WordTrace]
  refine ⟨145909857276911696719892197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194546476369215595626522929 145909857276911696719892197)
  ·
    refine ⟨27358098239420943134979787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145909857276911696719892197 27358098239420943134979787)
    ·
      refine ⟨41037147359131414702469681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27358098239420943134979787 41037147359131414702469681)
      ·
        refine ⟨30777860519348561026852261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41037147359131414702469681 30777860519348561026852261)
        ·
          refine ⟨5770848847377855192534799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30777860519348561026852261 5770848847377855192534799)
          ·
            refine ⟨8656273271066782788802199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5770848847377855192534799 8656273271066782788802199)
            ·
              refine ⟨12984409906600174183203299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656273271066782788802199 12984409906600174183203299)
              ·
                refine ⟨19476614859900261274804949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12984409906600174183203299 19476614859900261274804949)
                ·
                  refine ⟨456483160778912373628241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19476614859900261274804949 456483160778912373628241)
                  ·
                    rfl

theorem cell23_8000980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_8000980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000980 prefixEnd_8000980 := by exact prefixLift 8000980
  have htrace : WordTrace (prefixWord ++ tailWord_8000980) baseStart_8000980 baseEnd_8000980 := by
    simpa [prefixWord, tailWord_8000980, baseEnd_8000980] using wordTrace_append hprefix tailTrace_8000980
  have hstable : (prefixWord ++ tailWord_8000980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000980).length < 2 ^ (prefixWord ++ tailWord_8000980).sum := by decide
  have hdescent : baseEnd_8000980 < baseStart_8000980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8000986 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_8000986 : Nat := 118140960795 + 8000986 * 2 ^ 59
def prefixEnd_8000986 : Nat := 4983230072969 + 3 ^ 40 * 8000986 * 2
def baseEnd_8000986 : Nat := 4108351527894138339179141

theorem tailTrace_8000986 : CollatzResearch.WordTrace tailWord_8000986 prefixEnd_8000986 4108351527894138339179141 := by
  unfold tailWord_8000986
  simp only [CollatzResearch.WordTrace]
  refine ⟨72954983347950414116125703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194546622261201104309668541 72954983347950414116125703)
  ·
    refine ⟨109432475021925621174188555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72954983347950414116125703 109432475021925621174188555)
    ·
      refine ⟨164148712532888431761282833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109432475021925621174188555 164148712532888431761282833)
      ·
        refine ⟨123111534399666323820962125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164148712532888431761282833 123111534399666323820962125)
        ·
          refine ⟨46166825399874871432860797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123111534399666323820962125 46166825399874871432860797)
          ·
            refine ⟨17312559524953076787322799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46166825399874871432860797 17312559524953076787322799)
            ·
              refine ⟨25968839287429615180984199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17312559524953076787322799 25968839287429615180984199)
              ·
                refine ⟨38953258931144422771476299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25968839287429615180984199 38953258931144422771476299)
                ·
                  refine ⟨58429888396716634157214449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38953258931144422771476299 58429888396716634157214449)
                  ·
                    refine ⟨43822416297537475617910837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58429888396716634157214449 43822416297537475617910837)
                    ·
                      refine ⟨4108351527894138339179141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43822416297537475617910837 4108351527894138339179141)
                      ·
                        rfl

theorem cell23_8000986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_8000986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8000986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8000986 prefixEnd_8000986 := by exact prefixLift 8000986
  have htrace : WordTrace (prefixWord ++ tailWord_8000986) baseStart_8000986 baseEnd_8000986 := by
    simpa [prefixWord, tailWord_8000986, baseEnd_8000986] using wordTrace_append hprefix tailTrace_8000986
  have hstable : (prefixWord ++ tailWord_8000986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8000986).length < 2 ^ (prefixWord ++ tailWord_8000986).sum := by decide
  have hdescent : baseEnd_8000986 < baseStart_8000986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8000986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001049 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 11]
def baseStart_8001049 : Nat := 118140960795 + 8001049 * 2 ^ 59
def prefixEnd_8001049 : Nat := 4983230072969 + 3 ^ 40 * 8001049 * 2
def baseEnd_8001049 : Nat := 1369461292391790530897117

theorem tailTrace_8001049 : CollatzResearch.WordTrace tailWord_8001049 prefixEnd_8001049 1369461292391790530897117 := by
  unfold tailWord_8001049
  simp only [CollatzResearch.WordTrace]
  refine ⟨291822231190573418224046201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194548154127048945482697467 291822231190573418224046201)
  ·
    refine ⟨218866673392930063668034651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291822231190573418224046201 218866673392930063668034651)
    ·
      refine ⟨328300010089395095502051977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218866673392930063668034651 328300010089395095502051977)
      ·
        refine ⟨246225007567046321626538983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328300010089395095502051977 246225007567046321626538983)
        ·
          refine ⟨369337511350569482439808475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246225007567046321626538983 369337511350569482439808475)
          ·
            refine ⟨554006267025854223659712713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369337511350569482439808475 554006267025854223659712713)
            ·
              refine ⟨415504700269390667744784535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554006267025854223659712713 415504700269390667744784535)
              ·
                refine ⟨623257050404086001617176803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415504700269390667744784535 623257050404086001617176803)
                ·
                  refine ⟨934885575606129002425765205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623257050404086001617176803 934885575606129002425765205)
                  ·
                    refine ⟨1369461292391790530897117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 934885575606129002425765205 1369461292391790530897117)
                    ·
                      rfl

theorem cell23_8001049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_8001049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001049 prefixEnd_8001049 := by exact prefixLift 8001049
  have htrace : WordTrace (prefixWord ++ tailWord_8001049) baseStart_8001049 baseEnd_8001049 := by
    simpa [prefixWord, tailWord_8001049, baseEnd_8001049] using wordTrace_append hprefix tailTrace_8001049
  have hstable : (prefixWord ++ tailWord_8001049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001049).length < 2 ^ (prefixWord ++ tailWord_8001049).sum := by decide
  have hdescent : baseEnd_8001049 < baseStart_8001049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001113 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 2, 4]
def baseStart_8001113 : Nat := 118140960795 + 8001113 * 2 ^ 59
def prefixEnd_8001113 : Nat := 4983230072969 + 3 ^ 40 * 8001113 * 2
def baseEnd_8001113 : Nat := 1369472246645753114097019

theorem tailTrace_8001113 : CollatzResearch.WordTrace tailWord_8001113 prefixEnd_8001113 1369472246645753114097019 := by
  unfold tailWord_8001113
  simp only [CollatzResearch.WordTrace]
  refine ⟨291824565462341557154375993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194549710308227704769583995 291824565462341557154375993)
  ·
    refine ⟨218868424096756167865781995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291824565462341557154375993 218868424096756167865781995)
    ·
      refine ⟨328302636145134251798672993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218868424096756167865781995 328302636145134251798672993)
      ·
        refine ⟨246226977108850688849004745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328302636145134251798672993 246226977108850688849004745)
        ·
          refine ⟨184670232831638016636753559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246226977108850688849004745 184670232831638016636753559)
          ·
            refine ⟨277005349247457024955130339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184670232831638016636753559 277005349247457024955130339)
            ·
              refine ⟨415508023871185537432695509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277005349247457024955130339 415508023871185537432695509)
              ·
                refine ⟨9738469309480911033578801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 415508023871185537432695509 9738469309480911033578801)
                ·
                  refine ⟨7303851982110683275184101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9738469309480911033578801 7303851982110683275184101)
                  ·
                    refine ⟨1369472246645753114097019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7303851982110683275184101 1369472246645753114097019)
                    ·
                      rfl

theorem cell23_8001113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_8001113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001113 prefixEnd_8001113 := by exact prefixLift 8001113
  have htrace : WordTrace (prefixWord ++ tailWord_8001113) baseStart_8001113 baseEnd_8001113 := by
    simpa [prefixWord, tailWord_8001113, baseEnd_8001113] using wordTrace_append hprefix tailTrace_8001113
  have hstable : (prefixWord ++ tailWord_8001113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001113).length < 2 ^ (prefixWord ++ tailWord_8001113).sum := by decide
  have hdescent : baseEnd_8001113 < baseStart_8001113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001160 : List Nat := [2, 1, 3, 5, 1, 1, 2, 8]
def baseStart_8001160 : Nat := 118140960795 + 8001160 * 2 ^ 59
def prefixEnd_8001160 : Nat := 4983230072969 + 3 ^ 40 * 8001160 * 2
def baseEnd_8001160 : Nat := 152164476797334098459383

theorem tailTrace_8001160 : CollatzResearch.WordTrace tailWord_8001160 prefixEnd_8001160 152164476797334098459383 := by
  unfold tailWord_8001160
  simp only [CollatzResearch.WordTrace]
  refine ⟨145913139846585642090668467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194550853128780856120891289 145913139846585642090668467)
  ·
    refine ⟨218869709769878463136002701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145913139846585642090668467 218869709769878463136002701)
    ·
      refine ⟨82076141163704423676001013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218869709769878463136002701 82076141163704423676001013)
      ·
        refine ⟨7694638234097289719625095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82076141163704423676001013 7694638234097289719625095)
        ·
          refine ⟨11541957351145934579437643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7694638234097289719625095 11541957351145934579437643)
          ·
            refine ⟨17312936026718901869156465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11541957351145934579437643 17312936026718901869156465)
            ·
              refine ⟨12984702020039176401867349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17312936026718901869156465 12984702020039176401867349)
              ·
                refine ⟨152164476797334098459383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12984702020039176401867349 152164476797334098459383)
                ·
                  rfl

theorem cell23_8001160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 8].length) (baseStart_8001160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001160 prefixEnd_8001160 := by exact prefixLift 8001160
  have htrace : WordTrace (prefixWord ++ tailWord_8001160) baseStart_8001160 baseEnd_8001160 := by
    simpa [prefixWord, tailWord_8001160, baseEnd_8001160] using wordTrace_append hprefix tailTrace_8001160
  have hstable : (prefixWord ++ tailWord_8001160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001160).length < 2 ^ (prefixWord ++ tailWord_8001160).sum := by decide
  have hdescent : baseEnd_8001160 < baseStart_8001160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001193 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 8, 2]
def baseStart_8001193 : Nat := 118140960795 + 8001193 * 2 ^ 59
def prefixEnd_8001193 : Nat := 4983230072969 + 3 ^ 40 * 8001193 * 2
def baseEnd_8001193 : Nat := 4108457818389619029290689

theorem tailTrace_8001193 : CollatzResearch.WordTrace tailWord_8001193 prefixEnd_8001193 4108457818389619029290689 := by
  unfold tailWord_8001193
  simp only [CollatzResearch.WordTrace]
  refine ⟨291827483302051730817288233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194551655534701153878192155 291827483302051730817288233)
  ·
    refine ⟨218870612476538798112966175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291827483302051730817288233 218870612476538798112966175)
    ·
      refine ⟨328305918714808197169449263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218870612476538798112966175 328305918714808197169449263)
      ·
        refine ⟨492458878072212295754173895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328305918714808197169449263 492458878072212295754173895)
        ·
          refine ⟨738688317108318443631260843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492458878072212295754173895 738688317108318443631260843)
          ·
            refine ⟨1108032475662477665446891265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738688317108318443631260843 1108032475662477665446891265)
            ·
              refine ⟨831024356746858249085168449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1108032475662477665446891265 831024356746858249085168449)
              ·
                refine ⟨623268267560143686813876337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831024356746858249085168449 623268267560143686813876337)
                ·
                  refine ⟨467451200670107765110407253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623268267560143686813876337 467451200670107765110407253)
                  ·
                    refine ⟨5477943757852825372387585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 467451200670107765110407253 5477943757852825372387585)
                    ·
                      refine ⟨4108457818389619029290689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477943757852825372387585 4108457818389619029290689)
                      ·
                        rfl

theorem cell23_8001193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 8, 2].length) (baseStart_8001193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001193 prefixEnd_8001193 := by exact prefixLift 8001193
  have htrace : WordTrace (prefixWord ++ tailWord_8001193) baseStart_8001193 baseEnd_8001193 := by
    simpa [prefixWord, tailWord_8001193, baseEnd_8001193] using wordTrace_append hprefix tailTrace_8001193
  have hstable : (prefixWord ++ tailWord_8001193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001193).length < 2 ^ (prefixWord ++ tailWord_8001193).sum := by decide
  have hdescent : baseEnd_8001193 < baseStart_8001193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001205 : List Nat := [1, 3, 3, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_8001205 : Nat := 118140960795 + 8001205 * 2 ^ 59
def prefixEnd_8001205 : Nat := 4983230072969 + 3 ^ 40 * 8001205 * 2
def baseEnd_8001205 : Nat := 4108463980157472982340635

theorem tailTrace_8001205 : CollatzResearch.WordTrace tailWord_8001205 prefixEnd_8001205 4108463980157472982340635 := by
  unfold tailWord_8001205
  simp only [CollatzResearch.WordTrace]
  refine ⟨291827920978008256866725069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194551947318672171244483379 291827920978008256866725069)
  ·
    refine ⟨109435470366753096325021901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291827920978008256866725069 109435470366753096325021901)
    ·
      refine ⟨41038301387532411121883213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109435470366753096325021901 41038301387532411121883213)
      ·
        refine ⟨15389363020324654170706205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41038301387532411121883213 15389363020324654170706205)
        ·
          refine ⟨5771011132621745314014827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15389363020324654170706205 5771011132621745314014827)
          ·
            refine ⟨8656516698932617971022241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771011132621745314014827 8656516698932617971022241)
            ·
              refine ⟨6492387524199463478266681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8656516698932617971022241 6492387524199463478266681)
              ·
                refine ⟨4869290643149597608700011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492387524199463478266681 4869290643149597608700011)
                ·
                  refine ⟨7303935964724396413050017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869290643149597608700011 7303935964724396413050017)
                  ·
                    refine ⟨5477951973543297309787513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7303935964724396413050017 5477951973543297309787513)
                    ·
                      refine ⟨4108463980157472982340635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477951973543297309787513 4108463980157472982340635)
                      ·
                        rfl

theorem cell23_8001205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_8001205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001205 prefixEnd_8001205 := by exact prefixLift 8001205
  have htrace : WordTrace (prefixWord ++ tailWord_8001205) baseStart_8001205 baseEnd_8001205 := by
    simpa [prefixWord, tailWord_8001205, baseEnd_8001205] using wordTrace_append hprefix tailTrace_8001205
  have hstable : (prefixWord ++ tailWord_8001205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001205).length < 2 ^ (prefixWord ++ tailWord_8001205).sum := by decide
  have hdescent : baseEnd_8001205 < baseStart_8001205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001213 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_8001213 : Nat := 118140960795 + 8001213 * 2 ^ 59
def prefixEnd_8001213 : Nat := 4983230072969 + 3 ^ 40 * 8001213 * 2
def baseEnd_8001213 : Nat := 4108468088002708951040597

theorem tailTrace_8001213 : CollatzResearch.WordTrace tailWord_8001213 prefixEnd_8001213 4108468088002708951040597 := by
  unfold tailWord_8001213
  simp only [CollatzResearch.WordTrace]
  refine ⟨291828212761979274233016293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194552141841319516155344195 291828212761979274233016293)
  ·
    refine ⟨54717789892871113918690555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291828212761979274233016293 54717789892871113918690555)
    ·
      refine ⟨82076684839306670878035833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54717789892871113918690555 82076684839306670878035833)
      ·
        refine ⟨61557513629480003158526875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82076684839306670878035833 61557513629480003158526875)
        ·
          refine ⟨92336270444220004737790313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61557513629480003158526875 92336270444220004737790313)
          ·
            refine ⟨69252202833165003553342735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92336270444220004737790313 69252202833165003553342735)
            ·
              refine ⟨103878304249747505330014103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69252202833165003553342735 103878304249747505330014103)
              ·
                refine ⟨155817456374621257995021155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103878304249747505330014103 155817456374621257995021155)
                ·
                  refine ⟨233726184561931886992531733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155817456374621257995021155 233726184561931886992531733)
                  ·
                    refine ⟨10955914901340557202774925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 233726184561931886992531733 10955914901340557202774925)
                    ·
                      refine ⟨4108468088002708951040597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10955914901340557202774925 4108468088002708951040597)
                      ·
                        rfl

theorem cell23_8001213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_8001213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001213 prefixEnd_8001213 := by exact prefixLift 8001213
  have htrace : WordTrace (prefixWord ++ tailWord_8001213) baseStart_8001213 baseEnd_8001213 := by
    simpa [prefixWord, tailWord_8001213, baseEnd_8001213] using wordTrace_append hprefix tailTrace_8001213
  have hstable : (prefixWord ++ tailWord_8001213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001213).length < 2 ^ (prefixWord ++ tailWord_8001213).sum := by decide
  have hdescent : baseEnd_8001213 < baseStart_8001213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001223 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_8001223 : Nat := 118140960795 + 8001223 * 2 ^ 59
def prefixEnd_8001223 : Nat := 4983230072969 + 3 ^ 40 * 8001223 * 2
def baseEnd_8001223 : Nat := 4108473222809253911915551

theorem tailTrace_8001223 : CollatzResearch.WordTrace tailWord_8001223 prefixEnd_8001223 4108473222809253911915551 := by
  unfold tailWord_8001223
  simp only [CollatzResearch.WordTrace]
  refine ⟨291828577491943045940880323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194552384994628697293920215 291828577491943045940880323)
  ·
    refine ⟨437742866237914568911320485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291828577491943045940880323 437742866237914568911320485)
    ·
      refine ⟨82076787419608981670872591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437742866237914568911320485 82076787419608981670872591)
      ·
        refine ⟨123115181129413472506308887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82076787419608981670872591 123115181129413472506308887)
        ·
          refine ⟨184672771694120208759463331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123115181129413472506308887 184672771694120208759463331)
          ·
            refine ⟨277009157541180313139194997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184672771694120208759463331 277009157541180313139194997)
            ·
              refine ⟨25969608519485654356799531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277009157541180313139194997 25969608519485654356799531)
              ·
                refine ⟨38954412779228481535199297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25969608519485654356799531 38954412779228481535199297)
                ·
                  refine ⟨29215809584421361151399473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38954412779228481535199297 29215809584421361151399473)
                  ·
                    refine ⟨21911857188316020863549605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29215809584421361151399473 21911857188316020863549605)
                    ·
                      refine ⟨4108473222809253911915551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21911857188316020863549605 4108473222809253911915551)
                      ·
                        rfl

theorem cell23_8001223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_8001223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001223 prefixEnd_8001223 := by exact prefixLift 8001223
  have htrace : WordTrace (prefixWord ++ tailWord_8001223) baseStart_8001223 baseEnd_8001223 := by
    simpa [prefixWord, tailWord_8001223, baseEnd_8001223] using wordTrace_append hprefix tailTrace_8001223
  have hstable : (prefixWord ++ tailWord_8001223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001223).length < 2 ^ (prefixWord ++ tailWord_8001223).sum := by decide
  have hdescent : baseEnd_8001223 < baseStart_8001223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001233 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 7]
def baseStart_8001233 : Nat := 118140960795 + 8001233 * 2 ^ 59
def prefixEnd_8001233 : Nat := 4983230072969 + 3 ^ 40 * 8001233 * 2
def baseEnd_8001233 : Nat := 456497595290644319198945

theorem tailTrace_8001233 : CollatzResearch.WordTrace tailWord_8001233 prefixEnd_8001233 456497595290644319198945 := by
  unfold tailWord_8001233
  simp only [CollatzResearch.WordTrace]
  refine ⟨291828942221906817648744353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194552628147937878432496235 291828942221906817648744353)
  ·
    refine ⟨218871706666430113236558265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291828942221906817648744353 218871706666430113236558265)
    ·
      refine ⟨164153779999822584927418699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218871706666430113236558265 164153779999822584927418699)
      ·
        refine ⟨246230669999733877391128049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164153779999822584927418699 246230669999733877391128049)
        ·
          refine ⟨184673002499800408043346037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246230669999733877391128049 184673002499800408043346037)
          ·
            refine ⟨17313093984356288254063691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184673002499800408043346037 17313093984356288254063691)
            ·
              refine ⟨25969640976534432381095537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17313093984356288254063691 25969640976534432381095537)
              ·
                refine ⟨19477230732400824285821653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25969640976534432381095537 19477230732400824285821653)
                ·
                  refine ⟨456497595290644319198945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19477230732400824285821653 456497595290644319198945)
                  ·
                    rfl

theorem cell23_8001233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 7].length) (baseStart_8001233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001233 prefixEnd_8001233 := by exact prefixLift 8001233
  have htrace : WordTrace (prefixWord ++ tailWord_8001233) baseStart_8001233 baseEnd_8001233 := by
    simpa [prefixWord, tailWord_8001233, baseEnd_8001233] using wordTrace_append hprefix tailTrace_8001233
  have hstable : (prefixWord ++ tailWord_8001233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001233).length < 2 ^ (prefixWord ++ tailWord_8001233).sum := by decide
  have hdescent : baseEnd_8001233 < baseStart_8001233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001261 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_8001261 : Nat := 118140960795 + 8001261 * 2 ^ 59
def prefixEnd_8001261 : Nat := 4983230072969 + 3 ^ 40 * 8001261 * 2
def baseEnd_8001261 : Nat := 4108492735074124763240377

theorem tailTrace_8001261 : CollatzResearch.WordTrace tailWord_8001261 prefixEnd_8001261 4108492735074124763240377 := by
  unfold tailWord_8001261
  simp only [CollatzResearch.WordTrace]
  refine ⟨291829963465805378430763637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194553308977203585620509091 291829963465805378430763637)
  ·
    refine ⟨27359059074919254227884091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291829963465805378430763637 27359059074919254227884091)
    ·
      refine ⟨41038588612378881341826137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27359059074919254227884091 41038588612378881341826137)
      ·
        refine ⟨30778941459284161006369603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41038588612378881341826137 30778941459284161006369603)
        ·
          refine ⟨46168412188926241509554405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30778941459284161006369603 46168412188926241509554405)
          ·
            refine ⟨8656577285423670283041451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46168412188926241509554405 8656577285423670283041451)
            ·
              refine ⟨12984865928135505424562177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656577285423670283041451 12984865928135505424562177)
              ·
                refine ⟨9738649446101629068421633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12984865928135505424562177 9738649446101629068421633)
                ·
                  refine ⟨7303987084576221801316225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9738649446101629068421633 7303987084576221801316225)
                  ·
                    refine ⟨5477990313432166350987169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7303987084576221801316225 5477990313432166350987169)
                    ·
                      refine ⟨4108492735074124763240377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5477990313432166350987169 4108492735074124763240377)
                      ·
                        rfl

theorem cell23_8001261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_8001261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001261 prefixEnd_8001261 := by exact prefixLift 8001261
  have htrace : WordTrace (prefixWord ++ tailWord_8001261) baseStart_8001261 baseEnd_8001261 := by
    simpa [prefixWord, tailWord_8001261, baseEnd_8001261] using wordTrace_append hprefix tailTrace_8001261
  have hstable : (prefixWord ++ tailWord_8001261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001261).length < 2 ^ (prefixWord ++ tailWord_8001261).sum := by decide
  have hdescent : baseEnd_8001261 < baseStart_8001261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001263 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 4, 5]
def baseStart_8001263 : Nat := 118140960795 + 8001263 * 2 ^ 59
def prefixEnd_8001263 : Nat := 4983230072969 + 3 ^ 40 * 8001263 * 2
def baseEnd_8001263 : Nat := 1369497920678477918471789

theorem tailTrace_8001263 : CollatzResearch.WordTrace tailWord_8001263 prefixEnd_8001263 1369497920678477918471789 := by
  unfold tailWord_8001263
  simp only [CollatzResearch.WordTrace]
  refine ⟨291830036411798132772336443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194553357607865421848224295 291830036411798132772336443)
  ·
    refine ⟨437745054617697199158504665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291830036411798132772336443 437745054617697199158504665)
    ·
      refine ⟨328308790963272899368878499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437745054617697199158504665 328308790963272899368878499)
      ·
        refine ⟨492463186444909349053317749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328308790963272899368878499 492463186444909349053317749)
        ·
          refine ⟨46168423729210251473748539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492463186444909349053317749 46168423729210251473748539)
          ·
            refine ⟨69252635593815377210622809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46168423729210251473748539 69252635593815377210622809)
            ·
              refine ⟨51939476695361532907967107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69252635593815377210622809 51939476695361532907967107)
              ·
                refine ⟨77909215043042299361950661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51939476695361532907967107 77909215043042299361950661)
                ·
                  refine ⟨14607977820570431130365749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77909215043042299361950661 14607977820570431130365749)
                  ·
                    refine ⟨1369497920678477918471789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14607977820570431130365749 1369497920678477918471789)
                    ·
                      rfl

theorem cell23_8001263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_8001263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001263 prefixEnd_8001263 := by exact prefixLift 8001263
  have htrace : WordTrace (prefixWord ++ tailWord_8001263) baseStart_8001263 baseEnd_8001263 := by
    simpa [prefixWord, tailWord_8001263, baseEnd_8001263] using wordTrace_append hprefix tailTrace_8001263
  have hstable : (prefixWord ++ tailWord_8001263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001263).length < 2 ^ (prefixWord ++ tailWord_8001263).sum := by decide
  have hdescent : baseEnd_8001263 < baseStart_8001263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001278 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_8001278 : Nat := 118140960795 + 8001278 * 2 ^ 59
def prefixEnd_8001278 : Nat := 4983230072969 + 3 ^ 40 * 8001278 * 2
def baseEnd_8001278 : Nat := 4108501464245251196727799

theorem tailTrace_8001278 : CollatzResearch.WordTrace tailWord_8001278 prefixEnd_8001278 4108501464245251196727799 := by
  unfold tailWord_8001278
  simp only [CollatzResearch.WordTrace]
  refine ⟨36478822938342973791766561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194553722337829193556088325 36478822938342973791766561)
  ·
    refine ⟨27359117203757230343824921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36478822938342973791766561 27359117203757230343824921)
    ·
      refine ⟨20519337902817922757868691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27359117203757230343824921 20519337902817922757868691)
      ·
        refine ⟨30779006854226884136803037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20519337902817922757868691 30779006854226884136803037)
        ·
          refine ⟨11542127570335081551301139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30779006854226884136803037 11542127570335081551301139)
          ·
            refine ⟨17313191355502622326951709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11542127570335081551301139 17313191355502622326951709)
            ·
              refine ⟨6492446758313483372606891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17313191355502622326951709 6492446758313483372606891)
              ·
                refine ⟨9738670137470225058910337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492446758313483372606891 9738670137470225058910337)
                ·
                  refine ⟨7304002603102668794182753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9738670137470225058910337 7304002603102668794182753)
                  ·
                    refine ⟨5478001952327001595637065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7304002603102668794182753 5478001952327001595637065)
                    ·
                      refine ⟨4108501464245251196727799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478001952327001595637065 4108501464245251196727799)
                      ·
                        rfl

theorem cell23_8001278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_8001278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001278 prefixEnd_8001278 := by exact prefixLift 8001278
  have htrace : WordTrace (prefixWord ++ tailWord_8001278) baseStart_8001278 baseEnd_8001278 := by
    simpa [prefixWord, tailWord_8001278, baseEnd_8001278] using wordTrace_append hprefix tailTrace_8001278
  have hstable : (prefixWord ++ tailWord_8001278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001278).length < 2 ^ (prefixWord ++ tailWord_8001278).sum := by decide
  have hdescent : baseEnd_8001278 < baseStart_8001278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001283 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4]
def baseStart_8001283 : Nat := 118140960795 + 8001283 * 2 ^ 59
def prefixEnd_8001283 : Nat := 4983230072969 + 3 ^ 40 * 8001283 * 2
def baseEnd_8001283 : Nat := 4108504031648523677165275

theorem tailTrace_8001283 : CollatzResearch.WordTrace tailWord_8001283 prefixEnd_8001283 4108504031648523677165275 := by
  unfold tailWord_8001283
  simp only [CollatzResearch.WordTrace]
  refine ⟨291830765871725676188064503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194553843914483784125376335 291830765871725676188064503)
  ·
    refine ⟨437746148807588514282096755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291830765871725676188064503 437746148807588514282096755)
    ·
      refine ⟨656619223211382771423145133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437746148807588514282096755 656619223211382771423145133)
      ·
        refine ⟨246232208704268539283679425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 656619223211382771423145133 246232208704268539283679425)
        ·
          refine ⟨184674156528201404462759569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246232208704268539283679425 184674156528201404462759569)
          ·
            refine ⟨138505617396151053347069677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184674156528201404462759569 138505617396151053347069677)
            ·
              refine ⟨51939606523556645005151129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138505617396151053347069677 51939606523556645005151129)
              ·
                refine ⟨38954704892667483753863347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51939606523556645005151129 38954704892667483753863347)
                ·
                  refine ⟨58432057339001225630795021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38954704892667483753863347 58432057339001225630795021)
                  ·
                    refine ⟨21912021502125459611548133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58432057339001225630795021 21912021502125459611548133)
                    ·
                      refine ⟨4108504031648523677165275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21912021502125459611548133 4108504031648523677165275)
                      ·
                        rfl

theorem cell23_8001283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_8001283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001283 prefixEnd_8001283 := by exact prefixLift 8001283
  have htrace : WordTrace (prefixWord ++ tailWord_8001283) baseStart_8001283 baseEnd_8001283 := by
    simpa [prefixWord, tailWord_8001283, baseEnd_8001283] using wordTrace_append hprefix tailTrace_8001283
  have hstable : (prefixWord ++ tailWord_8001283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001283).length < 2 ^ (prefixWord ++ tailWord_8001283).sum := by decide
  have hdescent : baseEnd_8001283 < baseStart_8001283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001377 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_8001377 : Nat := 118140960795 + 8001377 * 2 ^ 59
def prefixEnd_8001377 : Nat := 4983230072969 + 3 ^ 40 * 8001377 * 2
def baseEnd_8001377 : Nat := 4108552298830046309389843

theorem tailTrace_8001377 : CollatzResearch.WordTrace tailWord_8001377 prefixEnd_8001377 4108552298830046309389843 := by
  unfold tailWord_8001377
  simp only [CollatzResearch.WordTrace]
  refine ⟨291834194333385130241986385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194556129555590086827990923 291834194333385130241986385)
  ·
    refine ⟨218875645750038847681489789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291834194333385130241986385 218875645750038847681489789)
    ·
      refine ⟨82078367156264567880558671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218875645750038847681489789 82078367156264567880558671)
      ·
        refine ⟨123117550734396851820838007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82078367156264567880558671 123117550734396851820838007)
        ·
          refine ⟨184676326101595277731257011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123117550734396851820838007 184676326101595277731257011)
          ·
            refine ⟨277014489152392916596885517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184676326101595277731257011 277014489152392916596885517)
            ·
              refine ⟨103880433432147343723832069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277014489152392916596885517 103880433432147343723832069)
              ·
                refine ⟨19477581268527626948218513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103880433432147343723832069 19477581268527626948218513)
                ·
                  refine ⟨14608185951395720211163885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19477581268527626948218513 14608185951395720211163885)
                  ·
                    refine ⟨5478069731773395079186457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14608185951395720211163885 5478069731773395079186457)
                    ·
                      refine ⟨4108552298830046309389843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478069731773395079186457 4108552298830046309389843)
                      ·
                        rfl

theorem cell23_8001377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_8001377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001377 prefixEnd_8001377 := by exact prefixLift 8001377
  have htrace : WordTrace (prefixWord ++ tailWord_8001377) baseStart_8001377 baseEnd_8001377 := by
    simpa [prefixWord, tailWord_8001377, baseEnd_8001377] using wordTrace_append hprefix tailTrace_8001377
  have hstable : (prefixWord ++ tailWord_8001377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001377).length < 2 ^ (prefixWord ++ tailWord_8001377).sum := by decide
  have hdescent : baseEnd_8001377 < baseStart_8001377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001378 : List Nat := [3, 3, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_8001378 : Nat := 118140960795 + 8001378 * 2 ^ 59
def prefixEnd_8001378 : Nat := 4983230072969 + 3 ^ 40 * 8001378 * 2
def baseEnd_8001378 : Nat := 1369517604103566935159113

theorem tailTrace_8001378 : CollatzResearch.WordTrace tailWord_8001378 prefixEnd_8001378 1369517604103566935159113 := by
  unfold tailWord_8001378
  simp only [CollatzResearch.WordTrace]
  refine ⟨72958557701595376853193197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194556153870921004941848525 72958557701595376853193197)
  ·
    refine ⟨27359459138098266319947449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72958557701595376853193197 27359459138098266319947449)
    ·
      refine ⟨20519594353573699739960587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27359459138098266319947449 20519594353573699739960587)
      ·
        refine ⟨30779391530360549609940881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20519594353573699739960587 30779391530360549609940881)
        ·
          refine ⟨23084543647770412207455661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30779391530360549609940881 23084543647770412207455661)
          ·
            refine ⟨8656703867913904577795873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23084543647770412207455661 8656703867913904577795873)
            ·
              refine ⟨6492527900935428433346905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8656703867913904577795873 6492527900935428433346905)
              ·
                refine ⟨4869395925701571325010179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492527900935428433346905 4869395925701571325010179)
                ·
                  refine ⟨7304093888552356987515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869395925701571325010179 7304093888552356987515269)
                  ·
                    refine ⟨1369517604103566935159113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304093888552356987515269 1369517604103566935159113)
                    ·
                      rfl

theorem cell23_8001378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_8001378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001378 prefixEnd_8001378 := by exact prefixLift 8001378
  have htrace : WordTrace (prefixWord ++ tailWord_8001378) baseStart_8001378 baseEnd_8001378 := by
    simpa [prefixWord, tailWord_8001378, baseEnd_8001378] using wordTrace_append hprefix tailTrace_8001378
  have hstable : (prefixWord ++ tailWord_8001378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001378).length < 2 ^ (prefixWord ++ tailWord_8001378).sum := by decide
  have hdescent : baseEnd_8001378 < baseStart_8001378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001418 : List Nat := [3, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_8001418 : Nat := 118140960795 + 8001418 * 2 ^ 59
def prefixEnd_8001418 : Nat := 4983230072969 + 3 ^ 40 * 8001418 * 2
def baseEnd_8001418 : Nat := 4108573351536880648977155

theorem tailTrace_8001418 : CollatzResearch.WordTrace tailWord_8001418 prefixEnd_8001418 4108573351536880648977155 := by
  unfold tailWord_8001418
  simp only [CollatzResearch.WordTrace]
  refine ⟨72958922431559148561057227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194557126484157729496152605 72958922431559148561057227)
  ·
    refine ⟨109438383647338722841585841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72958922431559148561057227 109438383647338722841585841)
    ·
      refine ⟨82078787735504042131189381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109438383647338722841585841 82078787735504042131189381)
      ·
        refine ⟨15389772700407007899598009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82078787735504042131189381 15389772700407007899598009)
        ·
          refine ⟨11542329525305255924698507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15389772700407007899598009 11542329525305255924698507)
          ·
            refine ⟨17313494287957883887047761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11542329525305255924698507 17313494287957883887047761)
            ·
              refine ⟨12985120715968412915285821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17313494287957883887047761 12985120715968412915285821)
              ·
                refine ⟨4869420268488154843232183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12985120715968412915285821 4869420268488154843232183)
                ·
                  refine ⟨7304130402732232264848275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869420268488154843232183 7304130402732232264848275)
                  ·
                    refine ⟨10956195604098348397272413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304130402732232264848275 10956195604098348397272413)
                    ·
                      refine ⟨4108573351536880648977155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10956195604098348397272413 4108573351536880648977155)
                      ·
                        rfl

theorem cell23_8001418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_8001418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001418 prefixEnd_8001418 := by exact prefixLift 8001418
  have htrace : WordTrace (prefixWord ++ tailWord_8001418) baseStart_8001418 baseEnd_8001418 := by
    simpa [prefixWord, tailWord_8001418, baseEnd_8001418] using wordTrace_append hprefix tailTrace_8001418
  have hstable : (prefixWord ++ tailWord_8001418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001418).length < 2 ^ (prefixWord ++ tailWord_8001418).sum := by decide
  have hdescent : baseEnd_8001418 < baseStart_8001418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001423 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_8001423 : Nat := 118140960795 + 8001423 * 2 ^ 59
def prefixEnd_8001423 : Nat := 4983230072969 + 3 ^ 40 * 8001423 * 2
def baseEnd_8001423 : Nat := 4108575918940153129414631

theorem tailTrace_8001423 : CollatzResearch.WordTrace tailWord_8001423 prefixEnd_8001423 4108575918940153129414631 := by
  unfold tailWord_8001423
  simp only [CollatzResearch.WordTrace]
  refine ⟨291835872091218480098160923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194557248060812320065440615 291835872091218480098160923)
  ·
    refine ⟨437753808136827720147241385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291835872091218480098160923 437753808136827720147241385)
    ·
      refine ⟨328315356102620790110431039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437753808136827720147241385 328315356102620790110431039)
      ·
        refine ⟨492473034153931185165646559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328315356102620790110431039 492473034153931185165646559)
        ·
          refine ⟨738709551230896777748469839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492473034153931185165646559 738709551230896777748469839)
          ·
            refine ⟨1108064326846345166622704759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738709551230896777748469839 1108064326846345166622704759)
            ·
              refine ⟨1662096490269517749934057139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108064326846345166622704759 1662096490269517749934057139)
              ·
                refine ⟨2493144735404276624901085709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662096490269517749934057139 2493144735404276624901085709)
                ·
                  refine ⟨934929275776603734337907141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2493144735404276624901085709 934929275776603734337907141)
                  ·
                    refine ⟨175299239208113200188357589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 934929275776603734337907141 175299239208113200188357589)
                    ·
                      refine ⟨4108575918940153129414631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175299239208113200188357589 4108575918940153129414631)
                      ·
                        rfl

theorem cell23_8001423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_8001423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001423 prefixEnd_8001423 := by exact prefixLift 8001423
  have htrace : WordTrace (prefixWord ++ tailWord_8001423) baseStart_8001423 baseEnd_8001423 := by
    simpa [prefixWord, tailWord_8001423, baseEnd_8001423] using wordTrace_append hprefix tailTrace_8001423
  have hstable : (prefixWord ++ tailWord_8001423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001423).length < 2 ^ (prefixWord ++ tailWord_8001423).sum := by decide
  have hdescent : baseEnd_8001423 < baseStart_8001423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001434 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_8001434 : Nat := 118140960795 + 8001434 * 2 ^ 59
def prefixEnd_8001434 : Nat := 4983230072969 + 3 ^ 40 * 8001434 * 2
def baseEnd_8001434 : Nat := 1369527189075784195459027

theorem tailTrace_8001434 : CollatzResearch.WordTrace tailWord_8001434 prefixEnd_8001434 1369527189075784195459027 := by
  unfold tailWord_8001434
  simp only [CollatzResearch.WordTrace]
  refine ⟨72959068323544657244202839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194557515529452419317874237 72959068323544657244202839)
  ·
    refine ⟨109438602485316985866304259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72959068323544657244202839 109438602485316985866304259)
    ·
      refine ⟨164157903727975478799456389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109438602485316985866304259 164157903727975478799456389)
      ·
        refine ⟨30779606948995402274898073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164157903727975478799456389 30779606948995402274898073)
        ·
          refine ⟨23084705211746551706173555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30779606948995402274898073 23084705211746551706173555)
          ·
            refine ⟨34627057817619827559260333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23084705211746551706173555 34627057817619827559260333)
            ·
              refine ⟨12985146681607435334722625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34627057817619827559260333 12985146681607435334722625)
              ·
                refine ⟨9738860011205576501041969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12985146681607435334722625 9738860011205576501041969)
                ·
                  refine ⟨7304145008404182375781477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9738860011205576501041969 7304145008404182375781477)
                  ·
                    refine ⟨1369527189075784195459027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304145008404182375781477 1369527189075784195459027)
                    ·
                      rfl

theorem cell23_8001434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_8001434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001434 prefixEnd_8001434 := by exact prefixLift 8001434
  have htrace : WordTrace (prefixWord ++ tailWord_8001434) baseStart_8001434 baseEnd_8001434 := by
    simpa [prefixWord, tailWord_8001434, baseEnd_8001434] using wordTrace_append hprefix tailTrace_8001434
  have hstable : (prefixWord ++ tailWord_8001434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001434).length < 2 ^ (prefixWord ++ tailWord_8001434).sum := by decide
  have hdescent : baseEnd_8001434 < baseStart_8001434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001514 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_8001514 : Nat := 118140960795 + 8001514 * 2 ^ 59
def prefixEnd_8001514 : Nat := 4983230072969 + 3 ^ 40 * 8001514 * 2
def baseEnd_8001514 : Nat := 4108622645679712273376713

theorem tailTrace_8001514 : CollatzResearch.WordTrace tailWord_8001514 prefixEnd_8001514 4108622645679712273376713 := by
  unfold tailWord_8001514
  simp only [CollatzResearch.WordTrace]
  refine ⟨72959797783472200659930899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194559460755925868426482397 72959797783472200659930899)
  ·
    refine ⟨109439696675208300989896349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72959797783472200659930899 109439696675208300989896349)
    ·
      refine ⟨41039886253203112871211131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109439696675208300989896349 41039886253203112871211131)
      ·
        refine ⟨61559829379804669306816697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41039886253203112871211131 61559829379804669306816697)
        ·
          refine ⟨46169872034853501980112523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61559829379804669306816697 46169872034853501980112523)
          ·
            refine ⟨69254808052280252970168785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46169872034853501980112523 69254808052280252970168785)
            ·
              refine ⟨51941106039210189727626589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69254808052280252970168785 51941106039210189727626589)
              ·
                refine ⟨19477914764703821147859971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51941106039210189727626589 19477914764703821147859971)
                ·
                  refine ⟨29216872147055731721789957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19477914764703821147859971 29216872147055731721789957)
                  ·
                    refine ⟨5478163527572949697835617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29216872147055731721789957 5478163527572949697835617)
                    ·
                      refine ⟨4108622645679712273376713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478163527572949697835617 4108622645679712273376713)
                      ·
                        rfl

theorem cell23_8001514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_8001514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001514 prefixEnd_8001514 := by exact prefixLift 8001514
  have htrace : WordTrace (prefixWord ++ tailWord_8001514) baseStart_8001514 baseEnd_8001514 := by
    simpa [prefixWord, tailWord_8001514, baseEnd_8001514] using wordTrace_append hprefix tailTrace_8001514
  have hstable : (prefixWord ++ tailWord_8001514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001514).length < 2 ^ (prefixWord ++ tailWord_8001514).sum := by decide
  have hdescent : baseEnd_8001514 < baseStart_8001514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001518 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_8001518 : Nat := 118140960795 + 8001518 * 2 ^ 59
def prefixEnd_8001518 : Nat := 4983230072969 + 3 ^ 40 * 8001518 * 2
def baseEnd_8001518 : Nat := 4108624699602330257726695

theorem tailTrace_8001518 : CollatzResearch.WordTrace tailWord_8001518 prefixEnd_8001518 4108624699602330257726695 := by
  unfold tailWord_8001518
  simp only [CollatzResearch.WordTrace]
  refine ⟨36479917128234288915358651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194559558017249540881912805 36479917128234288915358651)
  ·
    refine ⟨54719875692351433373037977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36479917128234288915358651 54719875692351433373037977)
    ·
      refine ⟨41039906769263575029778483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54719875692351433373037977 41039906769263575029778483)
      ·
        refine ⟨61559860153895362544667725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41039906769263575029778483 61559860153895362544667725)
        ·
          refine ⟨23084947557710760954250397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61559860153895362544667725 23084947557710760954250397)
          ·
            refine ⟨8656855334141535357843899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23084947557710760954250397 8656855334141535357843899)
            ·
              refine ⟨12985283001212303036765849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656855334141535357843899 12985283001212303036765849)
              ·
                refine ⟨9738962250909227277574387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12985283001212303036765849 9738962250909227277574387)
                ·
                  refine ⟨14608443376363840916361581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9738962250909227277574387 14608443376363840916361581)
                  ·
                    refine ⟨5478166266136440343635593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14608443376363840916361581 5478166266136440343635593)
                    ·
                      refine ⟨4108624699602330257726695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478166266136440343635593 4108624699602330257726695)
                      ·
                        rfl

theorem cell23_8001518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_8001518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001518 prefixEnd_8001518 := by exact prefixLift 8001518
  have htrace : WordTrace (prefixWord ++ tailWord_8001518) baseStart_8001518 baseEnd_8001518 := by
    simpa [prefixWord, tailWord_8001518, baseEnd_8001518] using wordTrace_append hprefix tailTrace_8001518
  have hstable : (prefixWord ++ tailWord_8001518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001518).length < 2 ^ (prefixWord ++ tailWord_8001518).sum := by decide
  have hdescent : baseEnd_8001518 < baseStart_8001518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001520 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 7]
def baseStart_8001520 : Nat := 118140960795 + 8001520 * 2 ^ 59
def prefixEnd_8001520 : Nat := 4983230072969 + 3 ^ 40 * 8001520 * 2
def baseEnd_8001520 : Nat := 456513969618182138877965

theorem tailTrace_8001520 : CollatzResearch.WordTrace tailWord_8001520 prefixEnd_8001520 456513969618182138877965 := by
  unfold tailWord_8001520
  simp only [CollatzResearch.WordTrace]
  refine ⟨145919704985933532832221007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194559606647911377109628009 145919704985933532832221007)
  ·
    refine ⟨218879557478900299248331511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145919704985933532832221007 218879557478900299248331511)
    ·
      refine ⟨328319336218350448872497267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218879557478900299248331511 328319336218350448872497267)
      ·
        refine ⟨492479004327525673308745901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328319336218350448872497267 492479004327525673308745901)
        ·
          refine ⟨184679626622822127490779713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492479004327525673308745901 184679626622822127490779713)
          ·
            refine ⟨138509719967116595618084785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184679626622822127490779713 138509719967116595618084785)
            ·
              refine ⟨103882289975337446713563589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138509719967116595618084785 103882289975337446713563589)
              ·
                refine ⟨19477929370375771258793173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103882289975337446713563589 19477929370375771258793173)
                ·
                  refine ⟨456513969618182138877965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19477929370375771258793173 456513969618182138877965)
                  ·
                    rfl

theorem cell23_8001520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_8001520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001520 prefixEnd_8001520 := by exact prefixLift 8001520
  have htrace : WordTrace (prefixWord ++ tailWord_8001520) baseStart_8001520 baseEnd_8001520 := by
    simpa [prefixWord, tailWord_8001520, baseEnd_8001520] using wordTrace_append hprefix tailTrace_8001520
  have hstable : (prefixWord ++ tailWord_8001520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001520).length < 2 ^ (prefixWord ++ tailWord_8001520).sum := by decide
  have hdescent : baseEnd_8001520 < baseStart_8001520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001534 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_8001534 : Nat := 118140960795 + 8001534 * 2 ^ 59
def prefixEnd_8001534 : Nat := 4983230072969 + 3 ^ 40 * 8001534 * 2
def baseEnd_8001534 : Nat := 4108632915292802195126621

theorem tailTrace_8001534 : CollatzResearch.WordTrace tailWord_8001534 prefixEnd_8001534 4108632915292802195126621 := by
  unfold tailWord_8001534
  simp only [CollatzResearch.WordTrace]
  refine ⟨36479990074227043256931457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194559947062544230703634437 36479990074227043256931457)
  ·
    refine ⟨27359992555670282442698593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36479990074227043256931457 27359992555670282442698593)
    ·
      refine ⟨20519994416752711832023945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27359992555670282442698593 20519994416752711832023945)
      ·
        refine ⟨15389995812564533874017959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20519994416752711832023945 15389995812564533874017959)
        ·
          refine ⟨23084993718846800811026939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15389995812564533874017959 23084993718846800811026939)
          ·
            refine ⟨34627490578270201216540409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23084993718846800811026939 34627490578270201216540409)
            ·
              refine ⟨25970617933702650912405307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34627490578270201216540409 25970617933702650912405307)
              ·
                refine ⟨38955926900553976368607961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25970617933702650912405307 38955926900553976368607961)
                ·
                  refine ⟨29216945175415482276455971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38955926900553976368607961 29216945175415482276455971)
                  ·
                    refine ⟨43825417763123223414683957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29216945175415482276455971 43825417763123223414683957)
                    ·
                      refine ⟨4108632915292802195126621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43825417763123223414683957 4108632915292802195126621)
                      ·
                        rfl

theorem cell23_8001534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_8001534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001534 prefixEnd_8001534 := by exact prefixLift 8001534
  have htrace : WordTrace (prefixWord ++ tailWord_8001534) baseStart_8001534 baseEnd_8001534 := by
    simpa [prefixWord, tailWord_8001534, baseEnd_8001534] using wordTrace_append hprefix tailTrace_8001534
  have hstable : (prefixWord ++ tailWord_8001534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001534).length < 2 ^ (prefixWord ++ tailWord_8001534).sum := by decide
  have hdescent : baseEnd_8001534 < baseStart_8001534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001547 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 3]
def baseStart_8001547 : Nat := 118140960795 + 8001547 * 2 ^ 59
def prefixEnd_8001547 : Nat := 4983230072969 + 3 ^ 40 * 8001547 * 2
def baseEnd_8001547 : Nat := 4108639590541310644264061

theorem tailTrace_8001547 : CollatzResearch.WordTrace tailWord_8001547 prefixEnd_8001547 4108639590541310644264061 := by
  unfold tailWord_8001547
  simp only [CollatzResearch.WordTrace]
  refine ⟨291840394742769249275674895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194560263161846166183783263 291840394742769249275674895)
  ·
    refine ⟨437760592114153873913512343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291840394742769249275674895 437760592114153873913512343)
    ·
      refine ⟨656640888171230810870268515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437760592114153873913512343 656640888171230810870268515)
      ·
        refine ⟨984961332256846216305402773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656640888171230810870268515 984961332256846216305402773)
        ·
          refine ⟨46170062449539666389315755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 984961332256846216305402773 46170062449539666389315755)
          ·
            refine ⟨69255093674309499583973633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46170062449539666389315755 69255093674309499583973633)
            ·
              refine ⟨51941320255732124687980225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69255093674309499583973633 51941320255732124687980225)
              ·
                refine ⟨38955990191799093515985169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51941320255732124687980225 38955990191799093515985169)
                ·
                  refine ⟨29216992643849320136988877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38955990191799093515985169 29216992643849320136988877)
                  ·
                    refine ⟨10956372241443495051370829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29216992643849320136988877 10956372241443495051370829)
                    ·
                      refine ⟨4108639590541310644264061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10956372241443495051370829 4108639590541310644264061)
                      ·
                        rfl

theorem cell23_8001547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 3].length) (baseStart_8001547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001547 prefixEnd_8001547 := by exact prefixLift 8001547
  have htrace : WordTrace (prefixWord ++ tailWord_8001547) baseStart_8001547 baseEnd_8001547 := by
    simpa [prefixWord, tailWord_8001547, baseEnd_8001547] using wordTrace_append hprefix tailTrace_8001547
  have hstable : (prefixWord ++ tailWord_8001547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001547).length < 2 ^ (prefixWord ++ tailWord_8001547).sum := by decide
  have hdescent : baseEnd_8001547 < baseStart_8001547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001564 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_8001564 : Nat := 118140960795 + 8001564 * 2 ^ 59
def prefixEnd_8001564 : Nat := 4983230072969 + 3 ^ 40 * 8001564 * 2
def baseEnd_8001564 : Nat := 4108648319712437077751483

theorem tailTrace_8001564 : CollatzResearch.WordTrace tailWord_8001564 prefixEnd_8001564 4108648319712437077751483 := by
  unfold tailWord_8001564
  simp only [CollatzResearch.WordTrace]
  refine ⟨145920507391853830589521873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194560676522471774119362497 145920507391853830589521873)
  ·
    refine ⟨109440380543890372942141405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145920507391853830589521873 109440380543890372942141405)
    ·
      refine ⟨41040142703958889853303027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109440380543890372942141405 41040142703958889853303027)
      ·
        refine ⟨61560214055938334779954541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41040142703958889853303027 61560214055938334779954541)
        ·
          refine ⟨23085080270976875542482953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61560214055938334779954541 23085080270976875542482953)
          ·
            refine ⟨17313810203232656656862215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23085080270976875542482953 17313810203232656656862215)
            ·
              refine ⟨25970715304848984985293323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17313810203232656656862215 25970715304848984985293323)
              ·
                refine ⟨38956072957273477477939985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25970715304848984985293323 38956072957273477477939985)
                ·
                  refine ⟨29217054717955108108454989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38956072957273477477939985 29217054717955108108454989)
                  ·
                    refine ⟨10956395519233165540670621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29217054717955108108454989 10956395519233165540670621)
                    ·
                      refine ⟨4108648319712437077751483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10956395519233165540670621 4108648319712437077751483)
                      ·
                        rfl

theorem cell23_8001564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_8001564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001564 prefixEnd_8001564 := by exact prefixLift 8001564
  have htrace : WordTrace (prefixWord ++ tailWord_8001564) baseStart_8001564 baseEnd_8001564 := by
    simpa [prefixWord, tailWord_8001564, baseEnd_8001564] using wordTrace_append hprefix tailTrace_8001564
  have hstable : (prefixWord ++ tailWord_8001564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001564).length < 2 ^ (prefixWord ++ tailWord_8001564).sum := by decide
  have hdescent : baseEnd_8001564 < baseStart_8001564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001580 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_8001580 : Nat := 118140960795 + 8001580 * 2 ^ 59
def prefixEnd_8001580 : Nat := 4983230072969 + 3 ^ 40 * 8001580 * 2
def baseEnd_8001580 : Nat := 1369552178467636338383803

theorem tailTrace_8001580 : CollatzResearch.WordTrace tailWord_8001580 prefixEnd_8001580 1369552178467636338383803 := by
  unfold tailWord_8001580
  simp only [CollatzResearch.WordTrace]
  refine ⟨145920799175824847955813097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194561065567766463941084129 145920799175824847955813097)
  ·
    refine ⟨109440599381868635966859823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145920799175824847955813097 109440599381868635966859823)
    ·
      refine ⟨164160899072802953950289735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109440599381868635966859823 164160899072802953950289735)
      ·
        refine ⟨246241348609204430925434603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164160899072802953950289735 246241348609204430925434603)
        ·
          refine ⟨369362022913806646388151905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246241348609204430925434603 369362022913806646388151905)
          ·
            refine ⟨277021517185354984791113929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369362022913806646388151905 277021517185354984791113929)
            ·
              refine ⟨207766137889016238593335447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277021517185354984791113929 207766137889016238593335447)
              ·
                refine ⟨311649206833524357890003171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207766137889016238593335447 311649206833524357890003171)
                ·
                  refine ⟨467473810250286536835004757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311649206833524357890003171 467473810250286536835004757)
                  ·
                    refine ⟨1369552178467636338383803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 467473810250286536835004757 1369552178467636338383803)
                    ·
                      rfl

theorem cell23_8001580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_8001580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001580 prefixEnd_8001580 := by exact prefixLift 8001580
  have htrace : WordTrace (prefixWord ++ tailWord_8001580) baseStart_8001580 baseEnd_8001580 := by
    simpa [prefixWord, tailWord_8001580, baseEnd_8001580] using wordTrace_append hprefix tailTrace_8001580
  have hstable : (prefixWord ++ tailWord_8001580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001580).length < 2 ^ (prefixWord ++ tailWord_8001580).sum := by decide
  have hdescent : baseEnd_8001580 < baseStart_8001580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001584 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 2, 5]
def baseStart_8001584 : Nat := 118140960795 + 8001584 * 2 ^ 59
def prefixEnd_8001584 : Nat := 4983230072969 + 3 ^ 40 * 8001584 * 2
def baseEnd_8001584 : Nat := 1369552863108508999833797

theorem tailTrace_8001584 : CollatzResearch.WordTrace tailWord_8001584 prefixEnd_8001584 1369552863108508999833797 := by
  unfold tailWord_8001584
  simp only [CollatzResearch.WordTrace]
  refine ⟨145920872121817602297385903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194561162829090136396514537 145920872121817602297385903)
  ·
    refine ⟨218881308182726403446078855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145920872121817602297385903 218881308182726403446078855)
    ·
      refine ⟨328321962274089605169118283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218881308182726403446078855 328321962274089605169118283)
      ·
        refine ⟨492482943411134407753677425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328321962274089605169118283 492482943411134407753677425)
        ·
          refine ⟨369362207558350805815258069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492482943411134407753677425 369362207558350805815258069)
          ·
            refine ⟨8656926739648847011295111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 369362207558350805815258069 8656926739648847011295111)
            ·
              refine ⟨12985390109473270516942667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656926739648847011295111 12985390109473270516942667)
              ·
                refine ⟨19478085164209905775414001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12985390109473270516942667 19478085164209905775414001)
                ·
                  refine ⟨14608563873157429331560501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19478085164209905775414001 14608563873157429331560501)
                  ·
                    refine ⟨1369552863108508999833797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14608563873157429331560501 1369552863108508999833797)
                    ·
                      rfl

theorem cell23_8001584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_8001584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001584 prefixEnd_8001584 := by exact prefixLift 8001584
  have htrace : WordTrace (prefixWord ++ tailWord_8001584) baseStart_8001584 baseEnd_8001584 := by
    simpa [prefixWord, tailWord_8001584, baseEnd_8001584] using wordTrace_append hprefix tailTrace_8001584
  have hstable : (prefixWord ++ tailWord_8001584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001584).length < 2 ^ (prefixWord ++ tailWord_8001584).sum := by decide
  have hdescent : baseEnd_8001584 < baseStart_8001584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001588 : List Nat := [2, 5, 1, 2, 2, 1, 2, 3, 5]
def baseStart_8001588 : Nat := 118140960795 + 8001588 * 2 ^ 59
def prefixEnd_8001588 : Nat := 4983230072969 + 3 ^ 40 * 8001588 * 2
def baseEnd_8001588 : Nat := 456517849249793887094597

theorem tailTrace_8001588 : CollatzResearch.WordTrace tailWord_8001588 prefixEnd_8001588 456517849249793887094597 := by
  unfold tailWord_8001588
  simp only [CollatzResearch.WordTrace]
  refine ⟨145920945067810356638958709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194561260090413808851944945 145920945067810356638958709)
  ·
    refine ⟨13680088600107220934902379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145920945067810356638958709 13680088600107220934902379)
    ·
      refine ⟨20520132900160831402353569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13680088600107220934902379 20520132900160831402353569)
      ·
        refine ⟨15390099675120623551765177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20520132900160831402353569 15390099675120623551765177)
        ·
          refine ⟨11542574756340467663823883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15390099675120623551765177 11542574756340467663823883)
          ·
            refine ⟨17313862134510701495735825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11542574756340467663823883 17313862134510701495735825)
            ·
              refine ⟨12985396600883026121801869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17313862134510701495735825 12985396600883026121801869)
              ·
                refine ⟨4869523725331134795675701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12985396600883026121801869 4869523725331134795675701)
                ·
                  refine ⟨456517849249793887094597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4869523725331134795675701 456517849249793887094597)
                  ·
                    rfl

theorem cell23_8001588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_8001588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001588 prefixEnd_8001588 := by exact prefixLift 8001588
  have htrace : WordTrace (prefixWord ++ tailWord_8001588) baseStart_8001588 baseEnd_8001588 := by
    simpa [prefixWord, tailWord_8001588, baseEnd_8001588] using wordTrace_append hprefix tailTrace_8001588
  have hstable : (prefixWord ++ tailWord_8001588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001588).length < 2 ^ (prefixWord ++ tailWord_8001588).sum := by decide
  have hdescent : baseEnd_8001588 < baseStart_8001588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001614 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_8001614 : Nat := 118140960795 + 8001614 * 2 ^ 59
def prefixEnd_8001614 : Nat := 4983230072969 + 3 ^ 40 * 8001614 * 2
def baseEnd_8001614 : Nat := 1369557997915053960708751

theorem tailTrace_8001614 : CollatzResearch.WordTrace tailWord_8001614 prefixEnd_8001614 1369557997915053960708751 := by
  unfold tailWord_8001614
  simp only [CollatzResearch.WordTrace]
  refine ⟨36480354804190814964795487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194561892289017679812242597 36480354804190814964795487)
  ·
    refine ⟨54720532206286222447193231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36480354804190814964795487 54720532206286222447193231)
    ·
      refine ⟨82080798309429333670789847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54720532206286222447193231 82080798309429333670789847)
      ·
        refine ⟨123121197464144000506184771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82080798309429333670789847 123121197464144000506184771)
        ·
          refine ⟨184681796196216000759277157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123121197464144000506184771 184681796196216000759277157)
          ·
            refine ⟨34627836786790500142364467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184681796196216000759277157 34627836786790500142364467)
            ·
              refine ⟨51941755180185750213546701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34627836786790500142364467 51941755180185750213546701)
              ·
                refine ⟨19478158192569656330080013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51941755180185750213546701 19478158192569656330080013)
                ·
                  refine ⟨7304309322213621123780005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19478158192569656330080013 7304309322213621123780005)
                  ·
                    refine ⟨1369557997915053960708751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304309322213621123780005 1369557997915053960708751)
                    ·
                      rfl

theorem cell23_8001614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_8001614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001614 prefixEnd_8001614 := by exact prefixLift 8001614
  have htrace : WordTrace (prefixWord ++ tailWord_8001614) baseStart_8001614 baseEnd_8001614 := by
    simpa [prefixWord, tailWord_8001614, baseEnd_8001614] using wordTrace_append hprefix tailTrace_8001614
  have hstable : (prefixWord ++ tailWord_8001614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001614).length < 2 ^ (prefixWord ++ tailWord_8001614).sum := by decide
  have hdescent : baseEnd_8001614 < baseStart_8001614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001648 : List Nat := [2, 1, 1, 1, 5, 4, 1, 3, 1, 4]
def baseStart_8001648 : Nat := 118140960795 + 8001648 * 2 ^ 59
def prefixEnd_8001648 : Nat := 4983230072969 + 3 ^ 40 * 8001648 * 2
def baseEnd_8001648 : Nat := 1369563817362471583033699

theorem tailTrace_8001648 : CollatzResearch.WordTrace tailWord_8001648 prefixEnd_8001648 1369563817362471583033699 := by
  unfold tailWord_8001648
  simp only [CollatzResearch.WordTrace]
  refine ⟨145922039257701671762550799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194562719010268895683401065 145922039257701671762550799)
  ·
    refine ⟨218883058886552507643826199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145922039257701671762550799 218883058886552507643826199)
    ·
      refine ⟨328324588329828761465739299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218883058886552507643826199 328324588329828761465739299)
      ·
        refine ⟨492486882494743142198608949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328324588329828761465739299 492486882494743142198608949)
        ·
          refine ⟨46170645233882169581119589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 492486882494743142198608949 46170645233882169581119589)
          ·
            refine ⟨8656995981352906796459923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46170645233882169581119589 8656995981352906796459923)
            ·
              refine ⟨12985493972029360194689885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656995981352906796459923 12985493972029360194689885)
              ·
                refine ⟨4869560239511010073008707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12985493972029360194689885 4869560239511010073008707)
                ·
                  refine ⟨7304340359266515109513061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869560239511010073008707 7304340359266515109513061)
                  ·
                    refine ⟨1369563817362471583033699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304340359266515109513061 1369563817362471583033699)
                    ·
                      rfl

theorem cell23_8001648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 1, 4].length) (baseStart_8001648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001648 prefixEnd_8001648 := by exact prefixLift 8001648
  have htrace : WordTrace (prefixWord ++ tailWord_8001648) baseStart_8001648 baseEnd_8001648 := by
    simpa [prefixWord, tailWord_8001648, baseEnd_8001648] using wordTrace_append hprefix tailTrace_8001648
  have hstable : (prefixWord ++ tailWord_8001648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001648).length < 2 ^ (prefixWord ++ tailWord_8001648).sum := by decide
  have hdescent : baseEnd_8001648 < baseStart_8001648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001665 : List Nat := [1, 2, 4, 2, 3, 1, 3, 2, 1, 4]
def baseStart_8001665 : Nat := 118140960795 + 8001665 * 2 ^ 59
def prefixEnd_8001665 : Nat := 4983230072969 + 3 ^ 40 * 8001665 * 2
def baseEnd_8001665 : Nat := 1369566727086180394196173

theorem tailTrace_8001665 : CollatzResearch.WordTrace tailWord_8001665 prefixEnd_8001665 1369566727086180394196173 := by
  unfold tailWord_8001665
  simp only [CollatzResearch.WordTrace]
  refine ⟨291844698556341755428470449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194563132370894503618980299 291844698556341755428470449)
  ·
    refine ⟨218883523917256316571352837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291844698556341755428470449 218883523917256316571352837)
    ·
      refine ⟨41040660734485559357128657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218883523917256316571352837 41040660734485559357128657)
      ·
        refine ⟨30780495550864169517846493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41040660734485559357128657 30780495550864169517846493)
        ·
          refine ⟨11542685831574063569192435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30780495550864169517846493 11542685831574063569192435)
          ·
            refine ⟨17314028747361095353788653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11542685831574063569192435 17314028747361095353788653)
            ·
              refine ⟨6492760780260410757670745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17314028747361095353788653 6492760780260410757670745)
              ·
                refine ⟨4869570585195308068253059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492760780260410757670745 4869570585195308068253059)
                ·
                  refine ⟨7304355877792962102379589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869570585195308068253059 7304355877792962102379589)
                  ·
                    refine ⟨1369566727086180394196173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304355877792962102379589 1369566727086180394196173)
                    ·
                      rfl

theorem cell23_8001665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_8001665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001665 prefixEnd_8001665 := by exact prefixLift 8001665
  have htrace : WordTrace (prefixWord ++ tailWord_8001665) baseStart_8001665 baseEnd_8001665 := by
    simpa [prefixWord, tailWord_8001665, baseEnd_8001665] using wordTrace_append hprefix tailTrace_8001665
  have hstable : (prefixWord ++ tailWord_8001665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001665).length < 2 ^ (prefixWord ++ tailWord_8001665).sum := by decide
  have hdescent : baseEnd_8001665 < baseStart_8001665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001671 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_8001671 : Nat := 118140960795 + 8001671 * 2 ^ 59
def prefixEnd_8001671 : Nat := 4983230072969 + 3 ^ 40 * 8001671 * 2
def baseEnd_8001671 : Nat := 4108703262142468159113491

theorem tailTrace_8001671 : CollatzResearch.WordTrace tailWord_8001671 prefixEnd_8001671 4108703262142468159113491 := by
  unfold tailWord_8001671
  simp only [CollatzResearch.WordTrace]
  refine ⟨291844917394320018453188867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194563278262880012302125911 291844917394320018453188867)
  ·
    refine ⟨437767376091480027679783301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291844917394320018453188867 437767376091480027679783301)
    ·
      refine ⟨82081383017152505189959369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437767376091480027679783301 82081383017152505189959369)
      ·
        refine ⟨61561037262864378892469527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82081383017152505189959369 61561037262864378892469527)
        ·
          refine ⟨92341555894296568338704291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61561037262864378892469527 92341555894296568338704291)
          ·
            refine ⟨138512333841444852508056437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92341555894296568338704291 138512333841444852508056437)
            ·
              refine ⟨12985531297635454922630291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138512333841444852508056437 12985531297635454922630291)
              ·
                refine ⟨19478296946453182383945437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12985531297635454922630291 19478296946453182383945437)
                ·
                  refine ⟨7304361354919943393979539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19478296946453182383945437 7304361354919943393979539)
                  ·
                    refine ⟨10956542032379915090969309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304361354919943393979539 10956542032379915090969309)
                    ·
                      refine ⟨4108703262142468159113491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10956542032379915090969309 4108703262142468159113491)
                      ·
                        rfl

theorem cell23_8001671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_8001671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001671 prefixEnd_8001671 := by exact prefixLift 8001671
  have htrace : WordTrace (prefixWord ++ tailWord_8001671) baseStart_8001671 baseEnd_8001671 := by
    simpa [prefixWord, tailWord_8001671, baseEnd_8001671] using wordTrace_append hprefix tailTrace_8001671
  have hstable : (prefixWord ++ tailWord_8001671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001671).length < 2 ^ (prefixWord ++ tailWord_8001671).sum := by decide
  have hdescent : baseEnd_8001671 < baseStart_8001671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001678 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_8001678 : Nat := 118140960795 + 8001678 * 2 ^ 59
def prefixEnd_8001678 : Nat := 4983230072969 + 3 ^ 40 * 8001678 * 2
def baseEnd_8001678 : Nat := 456522984056338847969551

theorem tailTrace_8001678 : CollatzResearch.WordTrace tailWord_8001678 prefixEnd_8001678 456522984056338847969551 := by
  unfold tailWord_8001678
  simp only [CollatzResearch.WordTrace]
  refine ⟨36480646588161832331086711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194563448470196439099129125 36480646588161832331086711)
  ·
    refine ⟨54720969882242748496630067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36480646588161832331086711 54720969882242748496630067)
    ·
      refine ⟨82081454823364122744945101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54720969882242748496630067 82081454823364122744945101)
      ·
        refine ⟨30780545558761546029354413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82081454823364122744945101 30780545558761546029354413)
        ·
          refine ⟨11542704584535579761007905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30780545558761546029354413 11542704584535579761007905)
          ·
            refine ⟨8657028438401684820755929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11542704584535579761007905 8657028438401684820755929)
            ·
              refine ⟨6492771328801263615566947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657028438401684820755929 6492771328801263615566947)
              ·
                refine ⟨9739156993201895423350421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492771328801263615566947 9739156993201895423350421)
                ·
                  refine ⟨456522984056338847969551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9739156993201895423350421 456522984056338847969551)
                  ·
                    rfl

theorem cell23_8001678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_8001678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001678 prefixEnd_8001678 := by exact prefixLift 8001678
  have htrace : WordTrace (prefixWord ++ tailWord_8001678) baseStart_8001678 baseEnd_8001678 := by
    simpa [prefixWord, tailWord_8001678, baseEnd_8001678] using wordTrace_append hprefix tailTrace_8001678
  have hstable : (prefixWord ++ tailWord_8001678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001678).length < 2 ^ (prefixWord ++ tailWord_8001678).sum := by decide
  have hdescent : baseEnd_8001678 < baseStart_8001678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001698 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_8001698 : Nat := 118140960795 + 8001698 * 2 ^ 59
def prefixEnd_8001698 : Nat := 4983230072969 + 3 ^ 40 * 8001698 * 2
def baseEnd_8001698 : Nat := 4108717126120139553475867

theorem tailTrace_8001698 : CollatzResearch.WordTrace tailWord_8001698 prefixEnd_8001698 4108717126120139553475867 := by
  unfold tailWord_8001698
  simp only [CollatzResearch.WordTrace]
  refine ⟨72961475541305550516105437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194563934776814801376281165 72961475541305550516105437)
  ·
    refine ⟨27360553327989581443539539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72961475541305550516105437 27360553327989581443539539)
    ·
      refine ⟨41040829991984372165309309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27360553327989581443539539 41040829991984372165309309)
      ·
        refine ⟨15390311246994139561990991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41040829991984372165309309 15390311246994139561990991)
        ·
          refine ⟨23085466870491209342986487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390311246994139561990991 23085466870491209342986487)
          ·
            refine ⟨34628200305736814014479731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23085466870491209342986487 34628200305736814014479731)
            ·
              refine ⟨51942300458605221021719597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34628200305736814014479731 51942300458605221021719597)
              ·
                refine ⟨19478362671976957883144849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51942300458605221021719597 19478362671976957883144849)
                ·
                  refine ⟨14608772003982718412358637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19478362671976957883144849 14608772003982718412358637)
                  ·
                    refine ⟨5478289501493519404634489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14608772003982718412358637 5478289501493519404634489)
                    ·
                      refine ⟨4108717126120139553475867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478289501493519404634489 4108717126120139553475867)
                      ·
                        rfl

theorem cell23_8001698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_8001698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001698 prefixEnd_8001698 := by exact prefixLift 8001698
  have htrace : WordTrace (prefixWord ++ tailWord_8001698) baseStart_8001698 baseEnd_8001698 := by
    simpa [prefixWord, tailWord_8001698, baseEnd_8001698] using wordTrace_append hprefix tailTrace_8001698
  have hstable : (prefixWord ++ tailWord_8001698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001698).length < 2 ^ (prefixWord ++ tailWord_8001698).sum := by decide
  have hdescent : baseEnd_8001698 < baseStart_8001698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001716 : List Nat := [2, 5, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_8001716 : Nat := 118140960795 + 8001716 * 2 ^ 59
def prefixEnd_8001716 : Nat := 4983230072969 + 3 ^ 40 * 8001716 * 2
def baseEnd_8001716 : Nat := 1369575456257306827683595

theorem tailTrace_8001716 : CollatzResearch.WordTrace tailWord_8001716 prefixEnd_8001716 1369575456257306827683595 := by
  unfold tailWord_8001716
  simp only [CollatzResearch.WordTrace]
  refine ⟨145923279339578495569288501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194564372452771327425718001 145923279339578495569288501)
  ·
    refine ⟨13680307438085483959620797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145923279339578495569288501 13680307438085483959620797)
    ·
      refine ⟨5130115289282056484857799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13680307438085483959620797 5130115289282056484857799)
      ·
        refine ⟨7695172933923084727286699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130115289282056484857799 7695172933923084727286699)
        ·
          refine ⟨11542759400884627090930049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695172933923084727286699 11542759400884627090930049)
          ·
            refine ⟨8657069550663470318197537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11542759400884627090930049 8657069550663470318197537)
            ·
              refine ⟨6492802162997602738648153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657069550663470318197537 6492802162997602738648153)
              ·
                refine ⟨4869601622248202053986115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492802162997602738648153 4869601622248202053986115)
                ·
                  refine ⟨7304402433372303080979173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869601622248202053986115 7304402433372303080979173)
                  ·
                    refine ⟨1369575456257306827683595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304402433372303080979173 1369575456257306827683595)
                    ·
                      rfl

theorem cell23_8001716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_8001716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001716 prefixEnd_8001716 := by exact prefixLift 8001716
  have htrace : WordTrace (prefixWord ++ tailWord_8001716) baseStart_8001716 baseEnd_8001716 := by
    simpa [prefixWord, tailWord_8001716, baseEnd_8001716] using wordTrace_append hprefix tailTrace_8001716
  have hstable : (prefixWord ++ tailWord_8001716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001716).length < 2 ^ (prefixWord ++ tailWord_8001716).sum := by decide
  have hdescent : baseEnd_8001716 < baseStart_8001716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001721 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 2, 4]
def baseStart_8001721 : Nat := 118140960795 + 8001721 * 2 ^ 59
def prefixEnd_8001721 : Nat := 4983230072969 + 3 ^ 40 * 8001721 * 2
def baseEnd_8001721 : Nat := 1369576312058397654496087

theorem tailTrace_8001721 : CollatzResearch.WordTrace tailWord_8001721 prefixEnd_8001721 1369576312058397654496087 := by
  unfold tailWord_8001721
  simp only [CollatzResearch.WordTrace]
  refine ⟨291846741044138876992509017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194564494029425917995006011 291846741044138876992509017)
  ·
    refine ⟨218885055783104157744381763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291846741044138876992509017 218885055783104157744381763)
    ·
      refine ⟨328327583674656236616572645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218885055783104157744381763 328327583674656236616572645)
      ·
        refine ⟨61561421938998044365607371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328327583674656236616572645 61561421938998044365607371)
        ·
          refine ⟨92342132908497066548411057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61561421938998044365607371 92342132908497066548411057)
          ·
            refine ⟨69256599681372799911308293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92342132908497066548411057 69256599681372799911308293)
            ·
              refine ⟨12985612440257399983370305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69256599681372799911308293 12985612440257399983370305)
              ·
                refine ⟨9739209330193049987527729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12985612440257399983370305 9739209330193049987527729)
                ·
                  refine ⟨7304406997644787490645797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9739209330193049987527729 7304406997644787490645797)
                  ·
                    refine ⟨1369576312058397654496087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304406997644787490645797 1369576312058397654496087)
                    ·
                      rfl

theorem cell23_8001721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_8001721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001721 prefixEnd_8001721 := by exact prefixLift 8001721
  have htrace : WordTrace (prefixWord ++ tailWord_8001721) baseStart_8001721 baseEnd_8001721 := by
    simpa [prefixWord, tailWord_8001721, baseEnd_8001721] using wordTrace_append hprefix tailTrace_8001721
  have hstable : (prefixWord ++ tailWord_8001721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001721).length < 2 ^ (prefixWord ++ tailWord_8001721).sum := by decide
  have hdescent : baseEnd_8001721 < baseStart_8001721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001761 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_8001761 : Nat := 118140960795 + 8001761 * 2 ^ 59
def prefixEnd_8001761 : Nat := 4983230072969 + 3 ^ 40 * 8001761 * 2
def baseEnd_8001761 : Nat := 4108749475401372806988077

theorem tailTrace_8001761 : CollatzResearch.WordTrace tailWord_8001761 prefixEnd_8001761 4108749475401372806988077 := by
  unfold tailWord_8001761
  simp only [CollatzResearch.WordTrace]
  refine ⟨291848199963993963823965137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194565466642662642549310091 291848199963993963823965137)
  ·
    refine ⟨218886149972995472867973853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291848199963993963823965137 218886149972995472867973853)
    ·
      refine ⟨82082306239873302325490195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218886149972995472867973853 82082306239873302325490195)
      ·
        refine ⟨123123459359809953488235293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82082306239873302325490195 123123459359809953488235293)
        ·
          refine ⟨46171297259928732558088235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123123459359809953488235293 46171297259928732558088235)
          ·
            refine ⟨69256945889893098837132353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46171297259928732558088235 69256945889893098837132353)
            ·
              refine ⟨51942709417419824127849265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69256945889893098837132353 51942709417419824127849265)
              ·
                refine ⟨38957032063064868095886949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51942709417419824127849265 38957032063064868095886949)
                ·
                  refine ⟨7304443511824662767978803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38957032063064868095886949 7304443511824662767978803)
                  ·
                    refine ⟨10956665267736994151968205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304443511824662767978803 10956665267736994151968205)
                    ·
                      refine ⟨4108749475401372806988077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10956665267736994151968205 4108749475401372806988077)
                      ·
                        rfl

theorem cell23_8001761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_8001761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001761 prefixEnd_8001761 := by exact prefixLift 8001761
  have htrace : WordTrace (prefixWord ++ tailWord_8001761) baseStart_8001761 baseEnd_8001761 := by
    simpa [prefixWord, tailWord_8001761, baseEnd_8001761] using wordTrace_append hprefix tailTrace_8001761
  have hstable : (prefixWord ++ tailWord_8001761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001761).length < 2 ^ (prefixWord ++ tailWord_8001761).sum := by decide
  have hdescent : baseEnd_8001761 < baseStart_8001761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001762 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_8001762 : Nat := 118140960795 + 8001762 * 2 ^ 59
def prefixEnd_8001762 : Nat := 4983230072969 + 3 ^ 40 * 8001762 * 2
def baseEnd_8001762 : Nat := 4108749988882027303075573

theorem tailTrace_8001762 : CollatzResearch.WordTrace tailWord_8001762 prefixEnd_8001762 4108749988882027303075573 := by
  unfold tailWord_8001762
  simp only [CollatzResearch.WordTrace]
  refine ⟨72962059109247585248687885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194565490957993560663167693 72962059109247585248687885)
  ·
    refine ⟨27360772165967844468257957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72962059109247585248687885 27360772165967844468257957)
    ·
      refine ⟨5130144781118970837798367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27360772165967844468257957 5130144781118970837798367)
      ·
        refine ⟨7695217171678456256697551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130144781118970837798367 7695217171678456256697551)
        ·
          refine ⟨11542825757517684385046327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695217171678456256697551 11542825757517684385046327)
          ·
            refine ⟨17314238636276526577569491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11542825757517684385046327 17314238636276526577569491)
            ·
              refine ⟨25971357954414789866354237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17314238636276526577569491 25971357954414789866354237)
              ·
                refine ⟨9739259232905546199882839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25971357954414789866354237 9739259232905546199882839)
                ·
                  refine ⟨14608888849358319299824259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9739259232905546199882839 14608888849358319299824259)
                  ·
                    refine ⟨21913333274037478949736389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14608888849358319299824259 21913333274037478949736389)
                    ·
                      refine ⟨4108749988882027303075573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21913333274037478949736389 4108749988882027303075573)
                      ·
                        rfl

theorem cell23_8001762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_8001762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001762 prefixEnd_8001762 := by exact prefixLift 8001762
  have htrace : WordTrace (prefixWord ++ tailWord_8001762) baseStart_8001762 baseEnd_8001762 := by
    simpa [prefixWord, tailWord_8001762, baseEnd_8001762] using wordTrace_append hprefix tailTrace_8001762
  have hstable : (prefixWord ++ tailWord_8001762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001762).length < 2 ^ (prefixWord ++ tailWord_8001762).sum := by decide
  have hdescent : baseEnd_8001762 < baseStart_8001762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001765 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 1, 2, 3]
def baseStart_8001765 : Nat := 118140960795 + 8001765 * 2 ^ 59
def prefixEnd_8001765 : Nat := 4983230072969 + 3 ^ 40 * 8001765 * 2
def baseEnd_8001765 : Nat := 4108751529323990791338059

theorem tailTrace_8001765 : CollatzResearch.WordTrace tailWord_8001765 prefixEnd_8001765 4108751529323990791338059 := by
  unfold tailWord_8001765
  simp only [CollatzResearch.WordTrace]
  refine ⟨291848345855979472507110749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194565563903986315004740499 291848345855979472507110749)
  ·
    refine ⟨109443129695992302190166531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291848345855979472507110749 109443129695992302190166531)
    ·
      refine ⟨164164694543988453285249797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109443129695992302190166531 164164694543988453285249797)
      ·
        refine ⟨30780880226997834990984337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164164694543988453285249797 30780880226997834990984337)
        ·
          refine ⟨23085660170248376243238253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30780880226997834990984337 23085660170248376243238253)
          ·
            refine ⟨8657122563843141091214345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23085660170248376243238253 8657122563843141091214345)
            ·
              refine ⟨6492841922882355818410759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657122563843141091214345 6492841922882355818410759)
              ·
                refine ⟨9739262884323533727616139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492841922882355818410759 9739262884323533727616139)
                ·
                  refine ⟨14608894326485300591424209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9739262884323533727616139 14608894326485300591424209)
                  ·
                    refine ⟨10956670744863975443568157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14608894326485300591424209 10956670744863975443568157)
                    ·
                      refine ⟨4108751529323990791338059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10956670744863975443568157 4108751529323990791338059)
                      ·
                        rfl

theorem cell23_8001765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_8001765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001765 prefixEnd_8001765 := by exact prefixLift 8001765
  have htrace : WordTrace (prefixWord ++ tailWord_8001765) baseStart_8001765 baseEnd_8001765 := by
    simpa [prefixWord, tailWord_8001765, baseEnd_8001765] using wordTrace_append hprefix tailTrace_8001765
  have hstable : (prefixWord ++ tailWord_8001765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001765).length < 2 ^ (prefixWord ++ tailWord_8001765).sum := by decide
  have hdescent : baseEnd_8001765 < baseStart_8001765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001778 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_8001778 : Nat := 118140960795 + 8001778 * 2 ^ 59
def prefixEnd_8001778 : Nat := 4983230072969 + 3 ^ 40 * 8001778 * 2
def baseEnd_8001778 : Nat := 4108758204572499240475499

theorem tailTrace_8001778 : CollatzResearch.WordTrace tailWord_8001778 prefixEnd_8001778 4108758204572499240475499 := by
  unfold tailWord_8001778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72962205001233093931833497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194565880003288250484889325 72962205001233093931833497)
  ·
    refine ⟨54721653750924820448875123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72962205001233093931833497 54721653750924820448875123)
    ·
      refine ⟨82082480626387230673312685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54721653750924820448875123 82082480626387230673312685)
      ·
        refine ⟨30780930234895211502492257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82082480626387230673312685 30780930234895211502492257)
        ·
          refine ⟨23085697676171408626869193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30780930234895211502492257 23085697676171408626869193)
          ·
            refine ⟨17314273257128556470151895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23085697676171408626869193 17314273257128556470151895)
            ·
              refine ⟨25971409885692834705227843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17314273257128556470151895 25971409885692834705227843)
              ·
                refine ⟨38957114828539252057841765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25971409885692834705227843 38957114828539252057841765)
                ·
                  refine ⟨7304459030351109760845331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38957114828539252057841765 7304459030351109760845331)
                  ·
                    refine ⟨10956688545526664641267997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304459030351109760845331 10956688545526664641267997)
                    ·
                      refine ⟨4108758204572499240475499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10956688545526664641267997 4108758204572499240475499)
                      ·
                        rfl

theorem cell23_8001778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_8001778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001778 prefixEnd_8001778 := by exact prefixLift 8001778
  have htrace : WordTrace (prefixWord ++ tailWord_8001778) baseStart_8001778 baseEnd_8001778 := by
    simpa [prefixWord, tailWord_8001778, baseEnd_8001778] using wordTrace_append hprefix tailTrace_8001778
  have hstable : (prefixWord ++ tailWord_8001778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001778).length < 2 ^ (prefixWord ++ tailWord_8001778).sum := by decide
  have hdescent : baseEnd_8001778 < baseStart_8001778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001804 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_8001804 : Nat := 118140960795 + 8001804 * 2 ^ 59
def prefixEnd_8001804 : Nat := 4983230072969 + 3 ^ 40 * 8001804 * 2
def baseEnd_8001804 : Nat := 4108771555069516138750379

theorem tailTrace_8001804 : CollatzResearch.WordTrace tailWord_8001804 prefixEnd_8001804 4108771555069516138750379 := by
  unfold tailWord_8001804
  simp only [CollatzResearch.WordTrace]
  refine ⟨145924884151419091083890233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194566512201892121445186977 145924884151419091083890233)
  ·
    refine ⟨109443663113564318312917675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145924884151419091083890233 109443663113564318312917675)
    ·
      refine ⟨164165494670346477469376513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109443663113564318312917675 164165494670346477469376513)
      ·
        refine ⟨123124121002759858102032385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164165494670346477469376513 123124121002759858102032385)
        ·
          refine ⟨92343090752069893576524289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123124121002759858102032385 92343090752069893576524289)
          ·
            refine ⟨69257318064052420182393217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92343090752069893576524289 69257318064052420182393217)
            ·
              refine ⟨51942988548039315136794913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69257318064052420182393217 51942988548039315136794913)
              ·
                refine ⟨38957241411029486352596185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51942988548039315136794913 38957241411029486352596185)
                ·
                  refine ⟨29217931058272114764447139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38957241411029486352596185 29217931058272114764447139)
                  ·
                    refine ⟨43826896587408172146670709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29217931058272114764447139 43826896587408172146670709)
                    ·
                      refine ⟨4108771555069516138750379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43826896587408172146670709 4108771555069516138750379)
                      ·
                        rfl

theorem cell23_8001804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_8001804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001804 prefixEnd_8001804 := by exact prefixLift 8001804
  have htrace : WordTrace (prefixWord ++ tailWord_8001804) baseStart_8001804 baseEnd_8001804 := by
    simpa [prefixWord, tailWord_8001804, baseEnd_8001804] using wordTrace_append hprefix tailTrace_8001804
  have hstable : (prefixWord ++ tailWord_8001804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001804).length < 2 ^ (prefixWord ++ tailWord_8001804).sum := by decide
  have hdescent : baseEnd_8001804 < baseStart_8001804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001822 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_8001822 : Nat := 118140960795 + 8001822 * 2 ^ 59
def prefixEnd_8001822 : Nat := 4983230072969 + 3 ^ 40 * 8001822 * 2
def baseEnd_8001822 : Nat := 4108780797721297068325297

theorem tailTrace_8001822 : CollatzResearch.WordTrace tailWord_8001822 prefixEnd_8001822 4108780797721297068325297 := by
  unfold tailWord_8001822
  simp only [CollatzResearch.WordTrace]
  refine ⟨36481303102096621405241965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194566949877848647494623813 36481303102096621405241965)
  ·
    refine ⟨13680488663286233026965737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36481303102096621405241965 13680488663286233026965737)
    ·
      refine ⟨10260366497464674770224303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13680488663286233026965737 10260366497464674770224303)
      ·
        refine ⟨15390549746197012155336455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260366497464674770224303 15390549746197012155336455)
        ·
          refine ⟨23085824619295518233004683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15390549746197012155336455 23085824619295518233004683)
          ·
            refine ⟨34628736928943277349507025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23085824619295518233004683 34628736928943277349507025)
            ·
              refine ⟨25971552696707458012130269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34628736928943277349507025 25971552696707458012130269)
              ·
                refine ⟨9739332261265296754548851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25971552696707458012130269 9739332261265296754548851)
                ·
                  refine ⟨14608998391897945131823277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9739332261265296754548851 14608998391897945131823277)
                  ·
                    refine ⟨5478374396961729424433729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14608998391897945131823277 5478374396961729424433729)
                    ·
                      refine ⟨4108780797721297068325297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478374396961729424433729 4108780797721297068325297)
                      ·
                        rfl

theorem cell23_8001822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_8001822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001822 prefixEnd_8001822 := by exact prefixLift 8001822
  have htrace : WordTrace (prefixWord ++ tailWord_8001822) baseStart_8001822 baseEnd_8001822 := by
    simpa [prefixWord, tailWord_8001822, baseEnd_8001822] using wordTrace_append hprefix tailTrace_8001822
  have hstable : (prefixWord ++ tailWord_8001822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001822).length < 2 ^ (prefixWord ++ tailWord_8001822).sum := by decide
  have hdescent : baseEnd_8001822 < baseStart_8001822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001891 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 4]
def baseStart_8001891 : Nat := 118140960795 + 8001891 * 2 ^ 59
def prefixEnd_8001891 : Nat := 4983230072969 + 3 ^ 40 * 8001891 * 2
def baseEnd_8001891 : Nat := 4108816227886457298362479

theorem tailTrace_8001891 : CollatzResearch.WordTrace tailWord_8001891 prefixEnd_8001891 4108816227886457298362479 := by
  unfold tailWord_8001891
  simp only [CollatzResearch.WordTrace]
  refine ⟨291852941453522996026197527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194568627635681997350798351 291852941453522996026197527)
  ·
    refine ⟨437779412180284494039296291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291852941453522996026197527 437779412180284494039296291)
    ·
      refine ⟨656669118270426741058944437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437779412180284494039296291 656669118270426741058944437)
      ·
        refine ⟨61562729837852506974276041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656669118270426741058944437 61562729837852506974276041)
        ·
          refine ⟨46172047378389380230707031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61562729837852506974276041 46172047378389380230707031)
          ·
            refine ⟨69258071067584070346060547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46172047378389380230707031 69258071067584070346060547)
            ·
              refine ⟨103887106601376105519090821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69258071067584070346060547 103887106601376105519090821)
              ·
                refine ⟨19478832487758019784829529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103887106601376105519090821 19478832487758019784829529)
                ·
                  refine ⟨14609124365818514838622147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19478832487758019784829529 14609124365818514838622147)
                  ·
                    refine ⟨21913686548727772257933221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14609124365818514838622147 21913686548727772257933221)
                    ·
                      refine ⟨4108816227886457298362479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21913686548727772257933221 4108816227886457298362479)
                      ·
                        rfl

theorem cell23_8001891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_8001891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001891 prefixEnd_8001891 := by exact prefixLift 8001891
  have htrace : WordTrace (prefixWord ++ tailWord_8001891) baseStart_8001891 baseEnd_8001891 := by
    simpa [prefixWord, tailWord_8001891, baseEnd_8001891] using wordTrace_append hprefix tailTrace_8001891
  have hstable : (prefixWord ++ tailWord_8001891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001891).length < 2 ^ (prefixWord ++ tailWord_8001891).sum := by decide
  have hdescent : baseEnd_8001891 < baseStart_8001891 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001922 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_8001922 : Nat := 118140960795 + 8001922 * 2 ^ 59
def prefixEnd_8001922 : Nat := 4983230072969 + 3 ^ 40 * 8001922 * 2
def baseEnd_8001922 : Nat := 1369610715262248892358279

theorem tailTrace_8001922 : CollatzResearch.WordTrace tailWord_8001922 prefixEnd_8001922 1369610715262248892358279 := by
  unfold tailWord_8001922
  simp only [CollatzResearch.WordTrace]
  refine ⟨72963518029102672080144005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194569381410940458880384013 72963518029102672080144005)
  ·
    refine ⟨13680659630456751015027001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72963518029102672080144005 13680659630456751015027001)
    ·
      refine ⟨10260494722842563261270251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13680659630456751015027001 10260494722842563261270251)
      ·
        refine ⟨15390742084263844891905377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260494722842563261270251 15390742084263844891905377)
        ·
          refine ⟨11543056563197883668929033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15390742084263844891905377 11543056563197883668929033)
          ·
            refine ⟨8657292422398412751696775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11543056563197883668929033 8657292422398412751696775)
            ·
              refine ⟨12985938633597619127545163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657292422398412751696775 12985938633597619127545163)
              ·
                refine ⟨19478907950396428691317745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12985938633597619127545163 19478907950396428691317745)
                ·
                  refine ⟨14609180962797321518488309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19478907950396428691317745 14609180962797321518488309)
                  ·
                    refine ⟨1369610715262248892358279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14609180962797321518488309 1369610715262248892358279)
                    ·
                      rfl

theorem cell23_8001922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_8001922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001922 prefixEnd_8001922 := by exact prefixLift 8001922
  have htrace : WordTrace (prefixWord ++ tailWord_8001922) baseStart_8001922 baseEnd_8001922 := by
    simpa [prefixWord, tailWord_8001922, baseEnd_8001922] using wordTrace_append hprefix tailTrace_8001922
  have hstable : (prefixWord ++ tailWord_8001922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001922).length < 2 ^ (prefixWord ++ tailWord_8001922).sum := by decide
  have hdescent : baseEnd_8001922 < baseStart_8001922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8001992 : List Nat := [2, 1, 3, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_8001992 : Nat := 118140960795 + 8001992 * 2 ^ 59
def prefixEnd_8001992 : Nat := 4983230072969 + 3 ^ 40 * 8001992 * 2
def baseEnd_8001992 : Nat := 4108868089432561403199515

theorem tailTrace_8001992 : CollatzResearch.WordTrace tailWord_8001992 prefixEnd_8001992 4108868089432561403199515 := by
  unfold tailWord_8001992
  simp only [CollatzResearch.WordTrace]
  refine ⟨145928312613078545137812115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194571083484104726850416153 145928312613078545137812115)
  ·
    refine ⟨218892468919617817706718173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145928312613078545137812115 218892468919617817706718173)
    ·
      refine ⟨82084675844856681640019315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218892468919617817706718173 82084675844856681640019315)
      ·
        refine ⟨123127013767285022460028973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82084675844856681640019315 123127013767285022460028973)
        ·
          refine ⟨46172630162731883422510865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123127013767285022460028973 46172630162731883422510865)
          ·
            refine ⟨34629472622048912566883149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46172630162731883422510865 34629472622048912566883149)
            ·
              refine ⟨12986052233268342212581181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34629472622048912566883149 12986052233268342212581181)
              ·
                refine ⟨4869769587475628329717943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12986052233268342212581181 4869769587475628329717943)
                ·
                  refine ⟨7304654381213442494576915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869769587475628329717943 7304654381213442494576915)
                  ·
                    refine ⟨10956981571820163741865373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304654381213442494576915 10956981571820163741865373)
                    ·
                      refine ⟨4108868089432561403199515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10956981571820163741865373 4108868089432561403199515)
                      ·
                        rfl

theorem cell23_8001992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_8001992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8001992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8001992 prefixEnd_8001992 := by exact prefixLift 8001992
  have htrace : WordTrace (prefixWord ++ tailWord_8001992) baseStart_8001992 baseEnd_8001992 := by
    simpa [prefixWord, tailWord_8001992, baseEnd_8001992] using wordTrace_append hprefix tailTrace_8001992
  have hstable : (prefixWord ++ tailWord_8001992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8001992).length < 2 ^ (prefixWord ++ tailWord_8001992).sum := by decide
  have hdescent : baseEnd_8001992 < baseStart_8001992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8001992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002008 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 2, 4]
def baseStart_8002008 : Nat := 118140960795 + 8002008 * 2 ^ 59
def prefixEnd_8002008 : Nat := 4983230072969 + 3 ^ 40 * 8002008 * 2
def baseEnd_8002008 : Nat := 1369625435041011113533147

theorem tailTrace_8002008 : CollatzResearch.WordTrace tailWord_8002008 prefixEnd_8002008 1369625435041011113533147 := by
  unfold tailWord_8002008
  simp only [CollatzResearch.WordTrace]
  refine ⟨145928604397049562504103339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194571472529399416672137785 145928604397049562504103339)
  ·
    refine ⟨218892906595574343756155009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145928604397049562504103339 218892906595574343756155009)
    ·
      refine ⟨164169679946680757817116257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218892906595574343756155009 164169679946680757817116257)
      ·
        refine ⟨123127259960010568362837193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164169679946680757817116257 123127259960010568362837193)
        ·
          refine ⟨92345444970007926272127895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123127259960010568362837193 92345444970007926272127895)
          ·
            refine ⟨138518167455011889408191843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92345444970007926272127895 138518167455011889408191843)
            ·
              refine ⟨207777251182517834112287765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138518167455011889408191843 207777251182517834112287765)
              ·
                refine ⟨9739558649180523474013489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207777251182517834112287765 9739558649180523474013489)
                ·
                  refine ⟨7304668986885392605510117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9739558649180523474013489 7304668986885392605510117)
                  ·
                    refine ⟨1369625435041011113533147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304668986885392605510117 1369625435041011113533147)
                    ·
                      rfl

theorem cell23_8002008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_8002008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002008 prefixEnd_8002008 := by exact prefixLift 8002008
  have htrace : WordTrace (prefixWord ++ tailWord_8002008) baseStart_8002008 baseEnd_8002008 := by
    simpa [prefixWord, tailWord_8002008, baseEnd_8002008] using wordTrace_append hprefix tailTrace_8002008
  have hstable : (prefixWord ++ tailWord_8002008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002008).length < 2 ^ (prefixWord ++ tailWord_8002008).sum := by decide
  have hdescent : baseEnd_8002008 < baseStart_8002008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002091 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5]
def baseStart_8002091 : Nat := 118140960795 + 8002091 * 2 ^ 59
def prefixEnd_8002091 : Nat := 4983230072969 + 3 ^ 40 * 8002091 * 2
def baseEnd_8002091 : Nat := 4108918924017356515861559

theorem tailTrace_8002091 : CollatzResearch.WordTrace tailWord_8002091 prefixEnd_8002091 4108918924017356515861559 := by
  unfold tailWord_8002091
  simp only [CollatzResearch.WordTrace]
  refine ⟨291860236052798430183478127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194573490701865620122318751 291860236052798430183478127)
  ·
    refine ⟨437790354079197645275217191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291860236052798430183478127 437790354079197645275217191)
    ·
      refine ⟨656685531118796467912825787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437790354079197645275217191 656685531118796467912825787)
      ·
        refine ⟨985028296678194701869238681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656685531118796467912825787 985028296678194701869238681)
        ·
          refine ⟨738771222508646026401929011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985028296678194701869238681 738771222508646026401929011)
          ·
            refine ⟨1108156833762969039602893517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738771222508646026401929011 1108156833762969039602893517)
            ·
              refine ⟨415558812661113389851085069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1108156833762969039602893517 415558812661113389851085069)
              ·
                refine ⟨155834554747917521194156901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415558812661113389851085069 155834554747917521194156901)
                ·
                  refine ⟨29218979015234535223904419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155834554747917521194156901 29218979015234535223904419)
                  ·
                    refine ⟨43828468522851802835856629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29218979015234535223904419 43828468522851802835856629)
                    ·
                      refine ⟨4108918924017356515861559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43828468522851802835856629 4108918924017356515861559)
                      ·
                        rfl

theorem cell23_8002091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_8002091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002091 prefixEnd_8002091 := by exact prefixLift 8002091
  have htrace : WordTrace (prefixWord ++ tailWord_8002091) baseStart_8002091 baseEnd_8002091 := by
    simpa [prefixWord, tailWord_8002091, baseEnd_8002091] using wordTrace_append hprefix tailTrace_8002091
  have hstable : (prefixWord ++ tailWord_8002091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002091).length < 2 ^ (prefixWord ++ tailWord_8002091).sum := by decide
  have hdescent : baseEnd_8002091 < baseStart_8002091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002105 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 1, 4, 2]
def baseStart_8002105 : Nat := 118140960795 + 8002105 * 2 ^ 59
def prefixEnd_8002105 : Nat := 4983230072969 + 3 ^ 40 * 8002105 * 2
def baseEnd_8002105 : Nat := 4108926112746519461086495

theorem tailTrace_8002105 : CollatzResearch.WordTrace tailWord_8002105 prefixEnd_8002105 4108926112746519461086495 := by
  unfold tailWord_8002105
  simp only [CollatzResearch.WordTrace]
  refine ⟨291860746674747710574487769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194573831116498473716325179 291860746674747710574487769)
  ·
    refine ⟨218895560006060782930865827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291860746674747710574487769 218895560006060782930865827)
    ·
      refine ⟨328343340009091174396298741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218895560006060782930865827 328343340009091174396298741)
      ·
        refine ⟨30782188125852297599653007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328343340009091174396298741 30782188125852297599653007)
        ·
          refine ⟨46173282188778446399479511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30782188125852297599653007 46173282188778446399479511)
          ·
            refine ⟨69259923283167669599219267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46173282188778446399479511 69259923283167669599219267)
            ·
              refine ⟨103889884924751504398828901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69259923283167669599219267 103889884924751504398828901)
              ·
                refine ⟨19479353423390907074780419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103889884924751504398828901 19479353423390907074780419)
                ·
                  refine ⟨29219030135086360612170629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19479353423390907074780419 29219030135086360612170629)
                  ·
                    refine ⟨5478568150328692614781993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29219030135086360612170629 5478568150328692614781993)
                    ·
                      refine ⟨4108926112746519461086495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478568150328692614781993 4108926112746519461086495)
                      ·
                        rfl

theorem cell23_8002105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_8002105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002105 prefixEnd_8002105 := by exact prefixLift 8002105
  have htrace : WordTrace (prefixWord ++ tailWord_8002105) baseStart_8002105 baseEnd_8002105 := by
    simpa [prefixWord, tailWord_8002105, baseEnd_8002105] using wordTrace_append hprefix tailTrace_8002105
  have hstable : (prefixWord ++ tailWord_8002105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002105).length < 2 ^ (prefixWord ++ tailWord_8002105).sum := by decide
  have hdescent : baseEnd_8002105 < baseStart_8002105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002109 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_8002109 : Nat := 118140960795 + 8002109 * 2 ^ 59
def prefixEnd_8002109 : Nat := 4983230072969 + 3 ^ 40 * 8002109 * 2
def baseEnd_8002109 : Nat := 4108928166669137445436477

theorem tailTrace_8002109 : CollatzResearch.WordTrace tailWord_8002109 prefixEnd_8002109 4108928166669137445436477 := by
  unfold tailWord_8002109
  simp only [CollatzResearch.WordTrace]
  refine ⟨291860892566733219257633381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194573928377822146171755587 291860892566733219257633381)
  ·
    refine ⟨54723917356262478610806259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291860892566733219257633381 54723917356262478610806259)
    ·
      refine ⟨82085876034393717916209389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54723917356262478610806259 82085876034393717916209389)
      ·
        refine ⟨30782203512897644218578521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82085876034393717916209389 30782203512897644218578521)
        ·
          refine ⟨23086652634673233163933891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30782203512897644218578521 23086652634673233163933891)
          ·
            refine ⟨34629978952009849745900837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23086652634673233163933891 34629978952009849745900837)
            ·
              refine ⟨6493121053501846827356407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34629978952009849745900837 6493121053501846827356407)
              ·
                refine ⟨9739681580252770241034611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493121053501846827356407 9739681580252770241034611)
                ·
                  refine ⟨14609522370379155361551917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9739681580252770241034611 14609522370379155361551917)
                  ·
                    refine ⟨5478570888892183260581969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14609522370379155361551917 5478570888892183260581969)
                    ·
                      refine ⟨4108928166669137445436477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478570888892183260581969 4108928166669137445436477)
                      ·
                        rfl

theorem cell23_8002109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_8002109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002109 prefixEnd_8002109 := by exact prefixLift 8002109
  have htrace : WordTrace (prefixWord ++ tailWord_8002109) baseStart_8002109 baseEnd_8002109 := by
    simpa [prefixWord, tailWord_8002109, baseEnd_8002109] using wordTrace_append hprefix tailTrace_8002109
  have hstable : (prefixWord ++ tailWord_8002109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002109).length < 2 ^ (prefixWord ++ tailWord_8002109).sum := by decide
  have hdescent : baseEnd_8002109 < baseStart_8002109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002111 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 9]
def baseStart_8002111 : Nat := 118140960795 + 8002111 * 2 ^ 59
def prefixEnd_8002111 : Nat := 4983230072969 + 3 ^ 40 * 8002111 * 2
def baseEnd_8002111 : Nat := 456547688181160715290163

theorem tailTrace_8002111 : CollatzResearch.WordTrace tailWord_8002111 prefixEnd_8002111 456547688181160715290163 := by
  unfold tailWord_8002111
  simp only [CollatzResearch.WordTrace]
  refine ⟨291860965512725973599206187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194573977008483982399470791 291860965512725973599206187)
  ·
    refine ⟨437791448269088960398809281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291860965512725973599206187 437791448269088960398809281)
    ·
      refine ⟨328343586201816720299106961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437791448269088960398809281 328343586201816720299106961)
      ·
        refine ⟨246257689651362540224330221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328343586201816720299106961 246257689651362540224330221)
        ·
          refine ⟨92346633619260952584123833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246257689651362540224330221 92346633619260952584123833)
          ·
            refine ⟨69259975214445714438092875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92346633619260952584123833 69259975214445714438092875)
            ·
              refine ⟨103889962821668571657139313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69259975214445714438092875 103889962821668571657139313)
              ·
                refine ⟨77917472116251428742854485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103889962821668571657139313 77917472116251428742854485)
                ·
                  refine ⟨456547688181160715290163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77917472116251428742854485 456547688181160715290163)
                  ·
                    rfl

theorem cell23_8002111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 9].length) (baseStart_8002111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002111 prefixEnd_8002111 := by exact prefixLift 8002111
  have htrace : WordTrace (prefixWord ++ tailWord_8002111) baseStart_8002111 baseEnd_8002111 := by
    simpa [prefixWord, tailWord_8002111, baseEnd_8002111] using wordTrace_append hprefix tailTrace_8002111
  have hstable : (prefixWord ++ tailWord_8002111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002111).length < 2 ^ (prefixWord ++ tailWord_8002111).sum := by decide
  have hdescent : baseEnd_8002111 < baseStart_8002111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002116 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_8002116 : Nat := 118140960795 + 8002116 * 2 ^ 59
def prefixEnd_8002116 : Nat := 4983230072969 + 3 ^ 40 * 8002116 * 2
def baseEnd_8002116 : Nat := 4108931761033718918048945

theorem tailTrace_8002116 : CollatzResearch.WordTrace tailWord_8002116 prefixEnd_8002116 4108931761033718918048945 := by
  unfold tailWord_8002116
  simp only [CollatzResearch.WordTrace]
  refine ⟨145930573938853929726569101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194574098585138572968758801 145930573938853929726569101)
  ·
    refine ⟨54723965227070223647463413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145930573938853929726569101 54723965227070223647463413)
    ·
      refine ⟨5130371740037833466949695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54723965227070223647463413 5130371740037833466949695)
      ·
        refine ⟨7695557610056750200424543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5130371740037833466949695 7695557610056750200424543)
        ·
          refine ⟨11543336415085125300636815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695557610056750200424543 11543336415085125300636815)
          ·
            refine ⟨17315004622627687950955223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543336415085125300636815 17315004622627687950955223)
            ·
              refine ⟨25972506933941531926432835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17315004622627687950955223 25972506933941531926432835)
              ·
                refine ⟨38958760400912297889649253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25972506933941531926432835 38958760400912297889649253)
                ·
                  refine ⟨7304767575171055854309235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38958760400912297889649253 7304767575171055854309235)
                  ·
                    refine ⟨10957151362756583781463853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304767575171055854309235 10957151362756583781463853)
                    ·
                      refine ⟨4108931761033718918048945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10957151362756583781463853 4108931761033718918048945)
                      ·
                        rfl

theorem cell23_8002116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_8002116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002116 prefixEnd_8002116 := by exact prefixLift 8002116
  have htrace : WordTrace (prefixWord ++ tailWord_8002116) baseStart_8002116 baseEnd_8002116 := by
    simpa [prefixWord, tailWord_8002116, baseEnd_8002116] using wordTrace_append hprefix tailTrace_8002116
  have hstable : (prefixWord ++ tailWord_8002116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002116).length < 2 ^ (prefixWord ++ tailWord_8002116).sum := by decide
  have hdescent : baseEnd_8002116 < baseStart_8002116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002122 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_8002122 : Nat := 118140960795 + 8002122 * 2 ^ 59
def prefixEnd_8002122 : Nat := 4983230072969 + 3 ^ 40 * 8002122 * 2
def baseEnd_8002122 : Nat := 4108934841917645894573917

theorem tailTrace_8002122 : CollatzResearch.WordTrace tailWord_8002122 prefixEnd_8002122 4108934841917645894573917 := by
  unfold tailWord_8002122
  simp only [CollatzResearch.WordTrace]
  refine ⟨72965341678921530619464155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194574244477124081651904413 72965341678921530619464155)
  ·
    refine ⟨109448012518382295929196233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72965341678921530619464155 109448012518382295929196233)
    ·
      refine ⟨82086009388786721946897175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109448012518382295929196233 82086009388786721946897175)
      ·
        refine ⟨123129014083180082920345763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82086009388786721946897175 123129014083180082920345763)
        ·
          refine ⟨184693521124770124380518645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123129014083180082920345763 184693521124770124380518645)
          ·
            refine ⟨17315017605447199160673623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184693521124770124380518645 17315017605447199160673623)
            ·
              refine ⟨25972526408170798741010435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17315017605447199160673623 25972526408170798741010435)
              ·
                refine ⟨38958789612256198111515653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25972526408170798741010435 38958789612256198111515653)
                ·
                  refine ⟨7304773052298037145909185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38958789612256198111515653 7304773052298037145909185)
                  ·
                    refine ⟨5478579789223527859431889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7304773052298037145909185 5478579789223527859431889)
                    ·
                      refine ⟨4108934841917645894573917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478579789223527859431889 4108934841917645894573917)
                      ·
                        rfl

theorem cell23_8002122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_8002122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002122 prefixEnd_8002122 := by exact prefixLift 8002122
  have htrace : WordTrace (prefixWord ++ tailWord_8002122) baseStart_8002122 baseEnd_8002122 := by
    simpa [prefixWord, tailWord_8002122, baseEnd_8002122] using wordTrace_append hprefix tailTrace_8002122
  have hstable : (prefixWord ++ tailWord_8002122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002122).length < 2 ^ (prefixWord ++ tailWord_8002122).sum := by decide
  have hdescent : baseEnd_8002122 < baseStart_8002122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002205 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_8002205 : Nat := 118140960795 + 8002205 * 2 ^ 59
def prefixEnd_8002205 : Nat := 4983230072969 + 3 ^ 40 * 8002205 * 2
def baseEnd_8002205 : Nat := 1369659153603989689945345

theorem tailTrace_8002205 : CollatzResearch.WordTrace tailWord_8002205 prefixEnd_8002205 1369659153603989689945345 := by
  unfold tailWord_8002205
  simp only [CollatzResearch.WordTrace]
  refine ⟨291864393974385427653128069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194576262649590285102085379 291864393974385427653128069)
  ·
    refine ⟨54724573870197267684961513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291864393974385427653128069 54724573870197267684961513)
    ·
      refine ⟨41043430402647950763721135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54724573870197267684961513 41043430402647950763721135)
      ·
        refine ⟨61565145603971926145581703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41043430402647950763721135 61565145603971926145581703)
        ·
          refine ⟨92347718405957889218372555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61565145603971926145581703 92347718405957889218372555)
          ·
            refine ⟨138521577608936833827558833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92347718405957889218372555 138521577608936833827558833)
            ·
              refine ⟨103891183206702625370669125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138521577608936833827558833 103891183206702625370669125)
              ·
                refine ⟨19479596851256742257000461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103891183206702625370669125 19479596851256742257000461)
                ·
                  refine ⟨7304848819221278346375173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19479596851256742257000461 7304848819221278346375173)
                  ·
                    refine ⟨1369659153603989689945345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304848819221278346375173 1369659153603989689945345)
                    ·
                      rfl

theorem cell23_8002205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_8002205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002205 prefixEnd_8002205 := by exact prefixLift 8002205
  have htrace : WordTrace (prefixWord ++ tailWord_8002205) baseStart_8002205 baseEnd_8002205 := by
    simpa [prefixWord, tailWord_8002205, baseEnd_8002205] using wordTrace_append hprefix tailTrace_8002205
  have hstable : (prefixWord ++ tailWord_8002205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002205).length < 2 ^ (prefixWord ++ tailWord_8002205).sum := by decide
  have hdescent : baseEnd_8002205 < baseStart_8002205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002239 : List Nat := [1, 1, 2, 2, 2, 4, 4, 2, 1, 4]
def baseStart_8002239 : Nat := 118140960795 + 8002239 * 2 ^ 59
def prefixEnd_8002239 : Nat := 4983230072969 + 3 ^ 40 * 8002239 * 2
def baseEnd_8002239 : Nat := 1369664973051407312270293

theorem tailTrace_8002239 : CollatzResearch.WordTrace tailWord_8002239 prefixEnd_8002239 1369664973051407312270293 := by
  unfold tailWord_8002239
  simp only [CollatzResearch.WordTrace]
  refine ⟨291865634056262251459865771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194577089370841500973243847 291865634056262251459865771)
  ·
    refine ⟨437798451084393377189798657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291865634056262251459865771 437798451084393377189798657)
    ·
      refine ⟨328348838313295032892348993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437798451084393377189798657 328348838313295032892348993)
      ·
        refine ⟨246261628734971274669261745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328348838313295032892348993 246261628734971274669261745)
        ·
          refine ⟨184696221551228456001946309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246261628734971274669261745 184696221551228456001946309)
          ·
            refine ⟨34630541540855335500364933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184696221551228456001946309 34630541540855335500364933)
            ·
              refine ⟨6493226538910375406318425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34630541540855335500364933 6493226538910375406318425)
              ·
                refine ⟨4869919904182781554738819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6493226538910375406318425 4869919904182781554738819)
                ·
                  refine ⟨7304879856274172332108229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869919904182781554738819 7304879856274172332108229)
                  ·
                    refine ⟨1369664973051407312270293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304879856274172332108229 1369664973051407312270293)
                    ·
                      rfl

theorem cell23_8002239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 4].length) (baseStart_8002239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002239 prefixEnd_8002239 := by exact prefixLift 8002239
  have htrace : WordTrace (prefixWord ++ tailWord_8002239) baseStart_8002239 baseEnd_8002239 := by
    simpa [prefixWord, tailWord_8002239, baseEnd_8002239] using wordTrace_append hprefix tailTrace_8002239
  have hstable : (prefixWord ++ tailWord_8002239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002239).length < 2 ^ (prefixWord ++ tailWord_8002239).sum := by decide
  have hdescent : baseEnd_8002239 < baseStart_8002239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002265 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 1, 5]
def baseStart_8002265 : Nat := 118140960795 + 8002265 * 2 ^ 59
def prefixEnd_8002265 : Nat := 4983230072969 + 3 ^ 40 * 8002265 * 2
def baseEnd_8002265 : Nat := 1369669423217079611695253

theorem tailTrace_8002265 : CollatzResearch.WordTrace tailWord_8002265 prefixEnd_8002265 1369669423217079611695253 := by
  unfold tailWord_8002265
  simp only [CollatzResearch.WordTrace]
  refine ⟨291866582354168057900312249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194577721569445371933541499 291866582354168057900312249)
  ·
    refine ⟨218899936765626043425234187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291866582354168057900312249 218899936765626043425234187)
    ·
      refine ⟨328349905148439065137851281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218899936765626043425234187 328349905148439065137851281)
      ·
        refine ⟨246262428861329298853388461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328349905148439065137851281 246262428861329298853388461)
        ·
          refine ⟨92348410822998487070020673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246262428861329298853388461 92348410822998487070020673)
          ·
            refine ⟨69261308117248865302515505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92348410822998487070020673 69261308117248865302515505)
            ·
              refine ⟨51945981087936648976886629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69261308117248865302515505 51945981087936648976886629)
              ·
                refine ⟨9739871453988121683166243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51945981087936648976886629 9739871453988121683166243)
                ·
                  refine ⟨14609807180982182524749365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9739871453988121683166243 14609807180982182524749365)
                  ·
                    refine ⟨1369669423217079611695253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14609807180982182524749365 1369669423217079611695253)
                    ·
                      rfl

theorem cell23_8002265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_8002265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002265 prefixEnd_8002265 := by exact prefixLift 8002265
  have htrace : WordTrace (prefixWord ++ tailWord_8002265) baseStart_8002265 baseEnd_8002265 := by
    simpa [prefixWord, tailWord_8002265, baseEnd_8002265] using wordTrace_append hprefix tailTrace_8002265
  have hstable : (prefixWord ++ tailWord_8002265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002265).length < 2 ^ (prefixWord ++ tailWord_8002265).sum := by decide
  have hdescent : baseEnd_8002265 < baseStart_8002265 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002312 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 1, 6]
def baseStart_8002312 : Nat := 118140960795 + 8002312 * 2 ^ 59
def prefixEnd_8002312 : Nat := 4983230072969 + 3 ^ 40 * 8002312 * 2
def baseEnd_8002312 : Nat := 1369677467747333383732681

theorem tailTrace_8002312 : CollatzResearch.WordTrace tailWord_8002312 prefixEnd_8002312 1369677467747333383732681 := by
  unfold tailWord_8002312
  simp only [CollatzResearch.WordTrace]
  refine ⟨145934148292498892463636595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194578864389998523284848793 145934148292498892463636595)
  ·
    refine ⟨218901222438748338695454893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145934148292498892463636595 218901222438748338695454893)
    ·
      refine ⟨82087958414530627010795585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218901222438748338695454893 82087958414530627010795585)
      ·
        refine ⟨61565968810897970258096689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82087958414530627010795585 61565968810897970258096689)
        ·
          refine ⟨46174476608173477693572517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61565968810897970258096689 46174476608173477693572517)
          ·
            refine ⟨8657714364032527067544847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46174476608173477693572517 8657714364032527067544847)
            ·
              refine ⟨12986571546048790601317271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657714364032527067544847 12986571546048790601317271)
              ·
                refine ⟨19479857319073185901975907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12986571546048790601317271 19479857319073185901975907)
                ·
                  refine ⟨29219785978609778852963861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19479857319073185901975907 29219785978609778852963861)
                  ·
                    refine ⟨1369677467747333383732681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29219785978609778852963861 1369677467747333383732681)
                    ·
                      rfl

theorem cell23_8002312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_8002312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002312 prefixEnd_8002312 := by exact prefixLift 8002312
  have htrace : WordTrace (prefixWord ++ tailWord_8002312) baseStart_8002312 baseEnd_8002312 := by
    simpa [prefixWord, tailWord_8002312, baseEnd_8002312] using wordTrace_append hprefix tailTrace_8002312
  have hstable : (prefixWord ++ tailWord_8002312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002312).length < 2 ^ (prefixWord ++ tailWord_8002312).sum := by decide
  have hdescent : baseEnd_8002312 < baseStart_8002312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002353 : List Nat := [1, 2, 2, 3, 2, 1, 5, 2, 1, 2, 2]
def baseStart_8002353 : Nat := 118140960795 + 8002353 * 2 ^ 59
def prefixEnd_8002353 : Nat := 4983230072969 + 3 ^ 40 * 8002353 * 2
def baseEnd_8002353 : Nat := 4109053455948834490785355

theorem tailTrace_8002353 : CollatzResearch.WordTrace tailWord_8002353 prefixEnd_8002353 4109053455948834490785355 := by
  unfold tailWord_8002353
  simp only [CollatzResearch.WordTrace]
  refine ⟨291869791977849248929515713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194579861318566165953010475 291869791977849248929515713)
  ·
    refine ⟨218902343983386936697136785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291869791977849248929515713 218902343983386936697136785)
    ·
      refine ⟨164176757987540202522852589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218902343983386936697136785 164176757987540202522852589)
      ·
        refine ⟨61566284245327575946069721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164176757987540202522852589 61566284245327575946069721)
        ·
          refine ⟨46174713183995681959552291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61566284245327575946069721 46174713183995681959552291)
          ·
            refine ⟨69262069775993522939328437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46174713183995681959552291 69262069775993522939328437)
            ·
              refine ⟨6493319041499392775562041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69262069775993522939328437 6493319041499392775562041)
              ·
                refine ⟨4869989281124544581671531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6493319041499392775562041 4869989281124544581671531)
                ·
                  refine ⟨7304983921686816872507297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869989281124544581671531 7304983921686816872507297)
                  ·
                    refine ⟨5478737941265112654380473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7304983921686816872507297 5478737941265112654380473)
                    ·
                      refine ⟨4109053455948834490785355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478737941265112654380473 4109053455948834490785355)
                      ·
                        rfl

theorem cell23_8002353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_8002353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002353 prefixEnd_8002353 := by exact prefixLift 8002353
  have htrace : WordTrace (prefixWord ++ tailWord_8002353) baseStart_8002353 baseEnd_8002353 := by
    simpa [prefixWord, tailWord_8002353, baseEnd_8002353] using wordTrace_append hprefix tailTrace_8002353
  have hstable : (prefixWord ++ tailWord_8002353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002353).length < 2 ^ (prefixWord ++ tailWord_8002353).sum := by decide
  have hdescent : baseEnd_8002353 < baseStart_8002353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002460 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_8002460 : Nat := 118140960795 + 8002460 * 2 ^ 59
def prefixEnd_8002460 : Nat := 4983230072969 + 3 ^ 40 * 8002460 * 2
def baseEnd_8002460 : Nat := 4109108398378865572147363

theorem tailTrace_8002460 : CollatzResearch.WordTrace tailWord_8002460 prefixEnd_8002460 4109108398378865572147363 := by
  unfold tailWord_8002460
  simp only [CollatzResearch.WordTrace]
  refine ⟨145936847294230803101830417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194582463058974404135773889 145936847294230803101830417)
  ·
    refine ⟨109452635470673102326372813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145936847294230803101830417 109452635470673102326372813)
    ·
      refine ⟨41044738301502413372389805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109452635470673102326372813 41044738301502413372389805)
      ·
        refine ⟨15391776863063405014646177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41044738301502413372389805 15391776863063405014646177)
        ·
          refine ⟨11543832647297553760984633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15391776863063405014646177 11543832647297553760984633)
          ·
            refine ⟨8657874485473165320738475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11543832647297553760984633 8657874485473165320738475)
            ·
              refine ⟨12986811728209747981107713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657874485473165320738475 12986811728209747981107713)
              ·
                refine ⟨9740108796157310985830785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12986811728209747981107713 9740108796157310985830785)
                ·
                  refine ⟨7305081597117983239373089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9740108796157310985830785 7305081597117983239373089)
                  ·
                    refine ⟨5478811197838487429529817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7305081597117983239373089 5478811197838487429529817)
                    ·
                      refine ⟨4109108398378865572147363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478811197838487429529817 4109108398378865572147363)
                      ·
                        rfl

theorem cell23_8002460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_8002460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002460 prefixEnd_8002460 := by exact prefixLift 8002460
  have htrace : WordTrace (prefixWord ++ tailWord_8002460) baseStart_8002460 baseEnd_8002460 := by
    simpa [prefixWord, tailWord_8002460, baseEnd_8002460] using wordTrace_append hprefix tailTrace_8002460
  have hstable : (prefixWord ++ tailWord_8002460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002460).length < 2 ^ (prefixWord ++ tailWord_8002460).sum := by decide
  have hdescent : baseEnd_8002460 < baseStart_8002460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002477 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_8002477 : Nat := 118140960795 + 8002477 * 2 ^ 59
def prefixEnd_8002477 : Nat := 4983230072969 + 3 ^ 40 * 8002477 * 2
def baseEnd_8002477 : Nat := 4109117127549992005634785

theorem tailTrace_8002477 : CollatzResearch.WordTrace tailWord_8002477 prefixEnd_8002477 4109117127549992005634785 := by
  unfold tailWord_8002477
  simp only [CollatzResearch.WordTrace]
  refine ⟨291874314629400018107029685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194582876419600012071353123 291874314629400018107029685)
  ·
    refine ⟨27363216996506251697534033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291874314629400018107029685 27363216996506251697534033)
    ·
      refine ⟨20522412747379688773150525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27363216996506251697534033 20522412747379688773150525)
      ·
        refine ⟨7695904780267383289931447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20522412747379688773150525 7695904780267383289931447)
        ·
          refine ⟨11543857170401074934897171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695904780267383289931447 11543857170401074934897171)
          ·
            refine ⟨17315785755601612402345757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543857170401074934897171 17315785755601612402345757)
            ·
              refine ⟨6493419658350604650879659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17315785755601612402345757 6493419658350604650879659)
              ·
                refine ⟨9740129487525906976319489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493419658350604650879659 9740129487525906976319489)
                ·
                  refine ⟨7305097115644430232239617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9740129487525906976319489 7305097115644430232239617)
                  ·
                    refine ⟨5478822836733322674179713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7305097115644430232239617 5478822836733322674179713)
                    ·
                      refine ⟨4109117127549992005634785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478822836733322674179713 4109117127549992005634785)
                      ·
                        rfl

theorem cell23_8002477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_8002477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002477 prefixEnd_8002477 := by exact prefixLift 8002477
  have htrace : WordTrace (prefixWord ++ tailWord_8002477) baseStart_8002477 baseEnd_8002477 := by
    simpa [prefixWord, tailWord_8002477, baseEnd_8002477] using wordTrace_append hprefix tailTrace_8002477
  have hstable : (prefixWord ++ tailWord_8002477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002477).length < 2 ^ (prefixWord ++ tailWord_8002477).sum := by decide
  have hdescent : baseEnd_8002477 < baseStart_8002477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002495 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_8002495 : Nat := 118140960795 + 8002495 * 2 ^ 59
def prefixEnd_8002495 : Nat := 4983230072969 + 3 ^ 40 * 8002495 * 2
def baseEnd_8002495 : Nat := 4109126370201772935209701

theorem tailTrace_8002495 : CollatzResearch.WordTrace tailWord_8002495 prefixEnd_8002495 4109126370201772935209701 := by
  unfold tailWord_8002495
  simp only [CollatzResearch.WordTrace]
  refine ⟨291874971143334807181184939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194583314095556538120789959 291874971143334807181184939)
  ·
    refine ⟨437812456715002210771777409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291874971143334807181184939 437812456715002210771777409)
    ·
      refine ⟨328359342536251658078833057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437812456715002210771777409 328359342536251658078833057)
      ·
        refine ⟨246269506902188743559124793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328359342536251658078833057 246269506902188743559124793)
        ·
          refine ⟨184702130176641557669343595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246269506902188743559124793 184702130176641557669343595)
          ·
            refine ⟨277053195264962336504015393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184702130176641557669343595 277053195264962336504015393)
            ·
              refine ⟨207789896448721752378011545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277053195264962336504015393 207789896448721752378011545)
              ·
                refine ⟨155842422336541314283508659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207789896448721752378011545 155842422336541314283508659)
                ·
                  refine ⟨233763633504811971425262989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155842422336541314283508659 233763633504811971425262989)
                  ·
                    refine ⟨87661362564304489284473621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233763633504811971425262989 87661362564304489284473621)
                    ·
                      refine ⟨4109126370201772935209701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87661362564304489284473621 4109126370201772935209701)
                      ·
                        rfl

theorem cell23_8002495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_8002495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002495 prefixEnd_8002495 := by exact prefixLift 8002495
  have htrace : WordTrace (prefixWord ++ tailWord_8002495) baseStart_8002495 baseEnd_8002495 := by
    simpa [prefixWord, tailWord_8002495, baseEnd_8002495] using wordTrace_append hprefix tailTrace_8002495
  have hstable : (prefixWord ++ tailWord_8002495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002495).length < 2 ^ (prefixWord ++ tailWord_8002495).sum := by decide
  have hdescent : baseEnd_8002495 < baseStart_8002495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002500 : List Nat := [2, 3, 3, 3, 2, 1, 1, 3, 5]
def baseStart_8002500 : Nat := 118140960795 + 8002500 * 2 ^ 59
def prefixEnd_8002500 : Nat := 4983230072969 + 3 ^ 40 * 8002500 * 2
def baseEnd_8002500 : Nat := 456569881956116157294131

theorem tailTrace_8002500 : CollatzResearch.WordTrace tailWord_8002500 prefixEnd_8002500 456569881956116157294131 := by
  unfold tailWord_8002500
  simp only [CollatzResearch.WordTrace]
  refine ⟨145937576754158346517558477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194583435672211128690077969 145937576754158346517558477)
  ·
    refine ⟨54726591282809379944084429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145937576754158346517558477 54726591282809379944084429)
    ·
      refine ⟨20522471731053517479031661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54726591282809379944084429 20522471731053517479031661)
      ·
        refine ⟨7695926899145069054636873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20522471731053517479031661 7695926899145069054636873)
        ·
          refine ⟨5771945174358801790977655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7695926899145069054636873 5771945174358801790977655)
          ·
            refine ⟨8657917761538202686466483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771945174358801790977655 8657917761538202686466483)
            ·
              refine ⟨12986876642307304029699725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657917761538202686466483 12986876642307304029699725)
              ·
                refine ⟨4870078740865239011137397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12986876642307304029699725 4870078740865239011137397)
                ·
                  refine ⟨456569881956116157294131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4870078740865239011137397 456569881956116157294131)
                  ·
                    rfl

theorem cell23_8002500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_8002500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002500 prefixEnd_8002500 := by exact prefixLift 8002500
  have htrace : WordTrace (prefixWord ++ tailWord_8002500) baseStart_8002500 baseEnd_8002500 := by
    simpa [prefixWord, tailWord_8002500, baseEnd_8002500] using wordTrace_append hprefix tailTrace_8002500
  have hstable : (prefixWord ++ tailWord_8002500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002500).length < 2 ^ (prefixWord ++ tailWord_8002500).sum := by decide
  have hdescent : baseEnd_8002500 < baseStart_8002500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002522 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 8]
def baseStart_8002522 : Nat := 118140960795 + 8002522 * 2 ^ 59
def prefixEnd_8002522 : Nat := 4983230072969 + 3 ^ 40 * 8002522 * 2
def baseEnd_8002522 : Nat := 456571137131049369952453

theorem tailTrace_8002522 : CollatzResearch.WordTrace tailWord_8002522 prefixEnd_8002522 456571137131049369952453 := by
  unfold tailWord_8002522
  simp only [CollatzResearch.WordTrace]
  refine ⟨72968988978559247698104455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194583970609491327194945213 72968988978559247698104455)
  ·
    refine ⟨109453483467838871547156683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72968988978559247698104455 109453483467838871547156683)
    ·
      refine ⟨164180225201758307320735025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109453483467838871547156683 164180225201758307320735025)
      ·
        refine ⟨123135168901318730490551269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164180225201758307320735025 123135168901318730490551269)
        ·
          refine ⟨23087844168997261966978363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123135168901318730490551269 23087844168997261966978363)
          ·
            refine ⟨34631766253495892950467545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23087844168997261966978363 34631766253495892950467545)
            ·
              refine ⟨25973824690121919712850659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34631766253495892950467545 25973824690121919712850659)
              ·
                refine ⟨38960737035182879569275989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25973824690121919712850659 38960737035182879569275989)
                ·
                  refine ⟨456571137131049369952453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38960737035182879569275989 456571137131049369952453)
                  ·
                    rfl

theorem cell23_8002522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_8002522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002522 prefixEnd_8002522 := by exact prefixLift 8002522
  have htrace : WordTrace (prefixWord ++ tailWord_8002522) baseStart_8002522 baseEnd_8002522 := by
    simpa [prefixWord, tailWord_8002522, baseEnd_8002522] using wordTrace_append hprefix tailTrace_8002522
  have hstable : (prefixWord ++ tailWord_8002522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002522).length < 2 ^ (prefixWord ++ tailWord_8002522).sum := by decide
  have hdescent : baseEnd_8002522 < baseStart_8002522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002532 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_8002532 : Nat := 118140960795 + 8002532 * 2 ^ 59
def prefixEnd_8002532 : Nat := 4983230072969 + 3 ^ 40 * 8002532 * 2
def baseEnd_8002532 : Nat := 4109145368985989290447031

theorem tailTrace_8002532 : CollatzResearch.WordTrace tailWord_8002532 prefixEnd_8002532 4109145368985989290447031 := by
  unfold tailWord_8002532
  simp only [CollatzResearch.WordTrace]
  refine ⟨145938160322100381250140925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194584213762800508333521233 145938160322100381250140925)
  ·
    refine ⟨54726810120787642968802847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145938160322100381250140925 54726810120787642968802847)
    ·
      refine ⟨82090215181181464453204271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54726810120787642968802847 82090215181181464453204271)
      ·
        refine ⟨123135322771772196679806407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82090215181181464453204271 123135322771772196679806407)
        ·
          refine ⟨184702984157658295019709611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123135322771772196679806407 184702984157658295019709611)
          ·
            refine ⟨277054476236487442529564417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184702984157658295019709611 277054476236487442529564417)
            ·
              refine ⟨207790857177365581897173313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277054476236487442529564417 207790857177365581897173313)
              ·
                refine ⟨155843142883024186422879985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207790857177365581897173313 155843142883024186422879985)
                ·
                  refine ⟨116882357162268139817159989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155843142883024186422879985 116882357162268139817159989)
                  ·
                    refine ⟨10957720983962638107858749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116882357162268139817159989 10957720983962638107858749)
                    ·
                      refine ⟨4109145368985989290447031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10957720983962638107858749 4109145368985989290447031)
                      ·
                        rfl

theorem cell23_8002532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_8002532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002532 prefixEnd_8002532 := by exact prefixLift 8002532
  have htrace : WordTrace (prefixWord ++ tailWord_8002532) baseStart_8002532 baseEnd_8002532 := by
    simpa [prefixWord, tailWord_8002532, baseEnd_8002532] using wordTrace_append hprefix tailTrace_8002532
  have hstable : (prefixWord ++ tailWord_8002532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002532).length < 2 ^ (prefixWord ++ tailWord_8002532).sum := by decide
  have hdescent : baseEnd_8002532 < baseStart_8002532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002606 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_8002606 : Nat := 118140960795 + 8002606 * 2 ^ 59
def prefixEnd_8002606 : Nat := 4983230072969 + 3 ^ 40 * 8002606 * 2
def baseEnd_8002606 : Nat := 4109183366554422000921691

theorem tailTrace_8002606 : CollatzResearch.WordTrace tailWord_8002606 prefixEnd_8002606 4109183366554422000921691 := by
  unfold tailWord_8002606
  simp only [CollatzResearch.WordTrace]
  refine ⟨36484877455741584142309459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194586013097288448758983781 36484877455741584142309459)
  ·
    refine ⟨54727316183612376213464189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36484877455741584142309459 54727316183612376213464189)
    ·
      refine ⟨20522743568854641080049071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54727316183612376213464189 20522743568854641080049071)
      ·
        refine ⟨30784115353281961620073607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20522743568854641080049071 30784115353281961620073607)
        ·
          refine ⟨46176173029922942430110411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30784115353281961620073607 46176173029922942430110411)
          ·
            refine ⟨69264259544884413645165617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46176173029922942430110411 69264259544884413645165617)
            ·
              refine ⟨51948194658663310233874213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69264259544884413645165617 51948194658663310233874213)
              ·
                refine ⟨9740286498499370668851415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51948194658663310233874213 9740286498499370668851415)
                ·
                  refine ⟨14610429747749056003277123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740286498499370668851415 14610429747749056003277123)
                  ·
                    refine ⟨21915644621623584004915685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14610429747749056003277123 21915644621623584004915685)
                    ·
                      refine ⟨4109183366554422000921691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21915644621623584004915685 4109183366554422000921691)
                      ·
                        rfl

theorem cell23_8002606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_8002606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002606 prefixEnd_8002606 := by exact prefixLift 8002606
  have htrace : WordTrace (prefixWord ++ tailWord_8002606) baseStart_8002606 baseEnd_8002606 := by
    simpa [prefixWord, tailWord_8002606, baseEnd_8002606] using wordTrace_append hprefix tailTrace_8002606
  have hstable : (prefixWord ++ tailWord_8002606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002606).length < 2 ^ (prefixWord ++ tailWord_8002606).sum := by decide
  have hdescent : baseEnd_8002606 < baseStart_8002606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002609 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_8002609 : Nat := 118140960795 + 8002609 * 2 ^ 59
def prefixEnd_8002609 : Nat := 4983230072969 + 3 ^ 40 * 8002609 * 2
def baseEnd_8002609 : Nat := 4109184906996385489184177

theorem tailTrace_8002609 : CollatzResearch.WordTrace tailWord_8002609 prefixEnd_8002609 4109184906996385489184177 := by
  unfold tailWord_8002609
  simp only [CollatzResearch.WordTrace]
  refine ⟨291879129064921804650834881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194586086043281203100556587 291879129064921804650834881)
  ·
    refine ⟨218909346798691353488126161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291879129064921804650834881 218909346798691353488126161)
    ·
      refine ⟨164182010099018515116094621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218909346798691353488126161 164182010099018515116094621)
      ·
        refine ⟨61568253787131943168535483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164182010099018515116094621 61568253787131943168535483)
        ·
          refine ⟨92352380680697914752803225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61568253787131943168535483 92352380680697914752803225)
          ·
            refine ⟨69264285510523436064602419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92352380680697914752803225 69264285510523436064602419)
            ·
              refine ⟨103896428265785154096903629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69264285510523436064602419 103896428265785154096903629)
              ·
                refine ⟨38961160599669432786338861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103896428265785154096903629 38961160599669432786338861)
                ·
                  refine ⟨14610435224876037294877073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38961160599669432786338861 14610435224876037294877073)
                  ·
                    refine ⟨10957826418657027971157805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14610435224876037294877073 10957826418657027971157805)
                    ·
                      refine ⟨4109184906996385489184177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10957826418657027971157805 4109184906996385489184177)
                      ·
                        rfl

theorem cell23_8002609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_8002609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002609 prefixEnd_8002609 := by exact prefixLift 8002609
  have htrace : WordTrace (prefixWord ++ tailWord_8002609) baseStart_8002609 baseEnd_8002609 := by
    simpa [prefixWord, tailWord_8002609, baseEnd_8002609] using wordTrace_append hprefix tailTrace_8002609
  have hstable : (prefixWord ++ tailWord_8002609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002609).length < 2 ^ (prefixWord ++ tailWord_8002609).sum := by decide
  have hdescent : baseEnd_8002609 < baseStart_8002609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002649 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 7, 2]
def baseStart_8002649 : Nat := 118140960795 + 8002649 * 2 ^ 59
def prefixEnd_8002649 : Nat := 4983230072969 + 3 ^ 40 * 8002649 * 2
def baseEnd_8002649 : Nat := 4109205446222565332683993

theorem tailTrace_8002649 : CollatzResearch.WordTrace tailWord_8002649 prefixEnd_8002649 4109205446222565332683993 := by
  unfold tailWord_8002649
  simp only [CollatzResearch.WordTrace]
  refine ⟨291880587984776891482291001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194587058656517927654860667 291880587984776891482291001)
  ·
    refine ⟨218910440988582668611718251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291880587984776891482291001 218910440988582668611718251)
    ·
      refine ⟨328365661482874002917577377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218910440988582668611718251 328365661482874002917577377)
      ·
        refine ⟨246274246112155502188183033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328365661482874002917577377 246274246112155502188183033)
        ·
          refine ⟨184705684584116626641137275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246274246112155502188183033 184705684584116626641137275)
          ·
            refine ⟨277058526876174939961705913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184705684584116626641137275 277058526876174939961705913)
            ·
              refine ⟨207793895157131204971279435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277058526876174939961705913 207793895157131204971279435)
              ·
                refine ⟨311690842735696807456919153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207793895157131204971279435 311690842735696807456919153)
                ·
                  refine ⟨233768132051772605592689365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311690842735696807456919153 233768132051772605592689365)
                  ·
                    refine ⟨5478940594963420443578657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 233768132051772605592689365 5478940594963420443578657)
                    ·
                      refine ⟨4109205446222565332683993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478940594963420443578657 4109205446222565332683993)
                      ·
                        rfl

theorem cell23_8002649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_8002649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002649 prefixEnd_8002649 := by exact prefixLift 8002649
  have htrace : WordTrace (prefixWord ++ tailWord_8002649) baseStart_8002649 baseEnd_8002649 := by
    simpa [prefixWord, tailWord_8002649, baseEnd_8002649] using wordTrace_append hprefix tailTrace_8002649
  have hstable : (prefixWord ++ tailWord_8002649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002649).length < 2 ^ (prefixWord ++ tailWord_8002649).sum := by decide
  have hdescent : baseEnd_8002649 < baseStart_8002649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002669 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_8002669 : Nat := 118140960795 + 8002669 * 2 ^ 59
def prefixEnd_8002669 : Nat := 4983230072969 + 3 ^ 40 * 8002669 * 2
def baseEnd_8002669 : Nat := 4109215715835655254433901

theorem tailTrace_8002669 : CollatzResearch.WordTrace tailWord_8002669 prefixEnd_8002669 4109215715835655254433901 := by
  unfold tailWord_8002669
  simp only [CollatzResearch.WordTrace]
  refine ⟨291881317444704434898019061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194587544963136289932012707 291881317444704434898019061)
  ·
    refine ⟨27363873510441040771689287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291881317444704434898019061 27363873510441040771689287)
    ·
      refine ⟨41045810265661561157533931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27363873510441040771689287 41045810265661561157533931)
      ·
        refine ⟨61568715398492341736300897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41045810265661561157533931 61568715398492341736300897)
        ·
          refine ⟨46176536548869256302225673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61568715398492341736300897 46176536548869256302225673)
          ·
            refine ⟨34632402411651942226669255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46176536548869256302225673 34632402411651942226669255)
            ·
              refine ⟨51948603617477913340003883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34632402411651942226669255 51948603617477913340003883)
              ·
                refine ⟨77922905426216870010005825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51948603617477913340003883 77922905426216870010005825)
                ·
                  refine ⟨58442179069662652507504369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77922905426216870010005825 58442179069662652507504369)
                  ·
                    refine ⟨43831634302246989380628277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58442179069662652507504369 43831634302246989380628277)
                    ·
                      refine ⟨4109215715835655254433901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43831634302246989380628277 4109215715835655254433901)
                      ·
                        rfl

theorem cell23_8002669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_8002669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002669 prefixEnd_8002669 := by exact prefixLift 8002669
  have htrace : WordTrace (prefixWord ++ tailWord_8002669) baseStart_8002669 baseEnd_8002669 := by
    simpa [prefixWord, tailWord_8002669, baseEnd_8002669] using wordTrace_append hprefix tailTrace_8002669
  have hstable : (prefixWord ++ tailWord_8002669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002669).length < 2 ^ (prefixWord ++ tailWord_8002669).sum := by decide
  have hdescent : baseEnd_8002669 < baseStart_8002669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002730 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_8002730 : Nat := 118140960795 + 8002730 * 2 ^ 59
def prefixEnd_8002730 : Nat := 4983230072969 + 3 ^ 40 * 8002730 * 2
def baseEnd_8002730 : Nat := 4109247038155579515771121

theorem tailTrace_8002730 : CollatzResearch.WordTrace tailWord_8002730 prefixEnd_8002730 4109247038155579515771121 := by
  unfold tailWord_8002730
  simp only [CollatzResearch.WordTrace]
  refine ⟨72970885574370860578997411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194589028198322294877326429 72970885574370860578997411)
  ·
    refine ⟨109456328361556290868496117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72970885574370860578997411 109456328361556290868496117)
    ·
      refine ⟨10261530783895902268921511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109456328361556290868496117 10261530783895902268921511)
      ·
        refine ⟨15392296175843853403382267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10261530783895902268921511 15392296175843853403382267)
        ·
          refine ⟨23088444263765780105073401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15392296175843853403382267 23088444263765780105073401)
          ·
            refine ⟨17316333197824335078805051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23088444263765780105073401 17316333197824335078805051)
            ·
              refine ⟨25974499796736502618207577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17316333197824335078805051 25974499796736502618207577)
              ·
                refine ⟨19480874847552376963655683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25974499796736502618207577 19480874847552376963655683)
                ·
                  refine ⟨29221312271328565445483525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19480874847552376963655683 29221312271328565445483525)
                  ·
                    refine ⟨5478996050874106021028161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29221312271328565445483525 5478996050874106021028161)
                    ·
                      refine ⟨4109247038155579515771121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5478996050874106021028161 4109247038155579515771121)
                      ·
                        rfl

theorem cell23_8002730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_8002730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002730 prefixEnd_8002730 := by exact prefixLift 8002730
  have htrace : WordTrace (prefixWord ++ tailWord_8002730) baseStart_8002730 baseEnd_8002730 := by
    simpa [prefixWord, tailWord_8002730, baseEnd_8002730] using wordTrace_append hprefix tailTrace_8002730
  have hstable : (prefixWord ++ tailWord_8002730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002730).length < 2 ^ (prefixWord ++ tailWord_8002730).sum := by decide
  have hdescent : baseEnd_8002730 < baseStart_8002730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002769 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_8002769 : Nat := 118140960795 + 8002769 * 2 ^ 59
def prefixEnd_8002769 : Nat := 4983230072969 + 3 ^ 40 * 8002769 * 2
def baseEnd_8002769 : Nat := 4109267063901104863183441

theorem tailTrace_8002769 : CollatzResearch.WordTrace tailWord_8002769 prefixEnd_8002769 4109267063901104863183441 := by
  unfold tailWord_8002769
  simp only [CollatzResearch.WordTrace]
  refine ⟨291884964744342151976659361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194589976496228101317772907 291884964744342151976659361)
  ·
    refine ⟨218913723558256613982494521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291884964744342151976659361 218913723558256613982494521)
    ·
      refine ⟨164185292668692460486870891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218913723558256613982494521 164185292668692460486870891)
      ·
        refine ⟨246277939003038690730306337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164185292668692460486870891 246277939003038690730306337)
        ·
          refine ⟨184708454252279018047729753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246277939003038690730306337 184708454252279018047729753)
          ·
            refine ⟨138531340689209263535797315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184708454252279018047729753 138531340689209263535797315)
            ·
              refine ⟨207797011033813895303695973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138531340689209263535797315 207797011033813895303695973)
              ·
                refine ⟨38961939568840105369442995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207797011033813895303695973 38961939568840105369442995)
                ·
                  refine ⟨58442909353260158054164493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38961939568840105369442995 58442909353260158054164493)
                  ·
                    refine ⟨21916091007472559270311685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58442909353260158054164493 21916091007472559270311685)
                    ·
                      refine ⟨4109267063901104863183441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21916091007472559270311685 4109267063901104863183441)
                      ·
                        rfl

theorem cell23_8002769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_8002769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002769 prefixEnd_8002769 := by exact prefixLift 8002769
  have htrace : WordTrace (prefixWord ++ tailWord_8002769) baseStart_8002769 baseEnd_8002769 := by
    simpa [prefixWord, tailWord_8002769, baseEnd_8002769] using wordTrace_append hprefix tailTrace_8002769
  have hstable : (prefixWord ++ tailWord_8002769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002769).length < 2 ^ (prefixWord ++ tailWord_8002769).sum := by decide
  have hdescent : baseEnd_8002769 < baseStart_8002769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002809 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 8]
def baseStart_8002809 : Nat := 118140960795 + 8002809 * 2 ^ 59
def prefixEnd_8002809 : Nat := 4983230072969 + 3 ^ 40 * 8002809 * 2
def baseEnd_8002809 : Nat := 456587511458587189631473

theorem tailTrace_8002809 : CollatzResearch.WordTrace tailWord_8002809 prefixEnd_8002809 456587511458587189631473 := by
  unfold tailWord_8002809
  simp only [CollatzResearch.WordTrace]
  refine ⟨291886423664197238808115481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194590949109464825872076987 291886423664197238808115481)
  ·
    refine ⟨218914817748147929106086611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291886423664197238808115481 218914817748147929106086611)
    ·
      refine ⟨328372226622221893659129917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218914817748147929106086611 328372226622221893659129917)
      ·
        refine ⟨123139584983333210122173719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328372226622221893659129917 123139584983333210122173719)
        ·
          refine ⟨184709377474999815183260579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123139584983333210122173719 184709377474999815183260579)
          ·
            refine ⟨277064066212499722774890869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184709377474999815183260579 277064066212499722774890869)
            ·
              refine ⟨25974756207421849010146019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277064066212499722774890869 25974756207421849010146019)
              ·
                refine ⟨38962134311132773515219029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25974756207421849010146019 38962134311132773515219029)
                ·
                  refine ⟨456587511458587189631473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38962134311132773515219029 456587511458587189631473)
                  ·
                    rfl

theorem cell23_8002809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_8002809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002809 prefixEnd_8002809 := by exact prefixLift 8002809
  have htrace : WordTrace (prefixWord ++ tailWord_8002809) baseStart_8002809 baseEnd_8002809 := by
    simpa [prefixWord, tailWord_8002809, baseEnd_8002809] using wordTrace_append hprefix tailTrace_8002809
  have hstable : (prefixWord ++ tailWord_8002809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002809).length < 2 ^ (prefixWord ++ tailWord_8002809).sum := by decide
  have hdescent : baseEnd_8002809 < baseStart_8002809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002847 : List Nat := [1, 1, 2, 4, 4, 2, 1, 3, 1, 4]
def baseStart_8002847 : Nat := 118140960795 + 8002847 * 2 ^ 59
def prefixEnd_8002847 : Nat := 4983230072969 + 3 ^ 40 * 8002847 * 2
def baseEnd_8002847 : Nat := 1369769038464051852669361

theorem tailTrace_8002847 : CollatzResearch.WordTrace tailWord_8002847 prefixEnd_8002847 1369769038464051852669361 := by
  unfold tailWord_8002847
  simp only [CollatzResearch.WordTrace]
  refine ⟨291887809638059571297998795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194591873092039714198665863 291887809638059571297998795)
  ·
    refine ⟨437831714457089356946998193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291887809638059571297998795 437831714457089356946998193)
    ·
      refine ⟨328373785842817017710248645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437831714457089356946998193 328373785842817017710248645)
      ·
        refine ⟨61570084845528190820671621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328373785842817017710248645 61570084845528190820671621)
        ·
          refine ⟨11544390908536535778875929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61570084845528190820671621 11544390908536535778875929)
          ·
            refine ⟨8658293181402401834156947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11544390908536535778875929 8658293181402401834156947)
            ·
              refine ⟨12987439772103602751235421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658293181402401834156947 12987439772103602751235421)
              ·
                refine ⟨4870289914538851031713283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12987439772103602751235421 4870289914538851031713283)
                ·
                  refine ⟨7305434871808276547569925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4870289914538851031713283 7305434871808276547569925)
                  ·
                    refine ⟨1369769038464051852669361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305434871808276547569925 1369769038464051852669361)
                    ·
                      rfl

theorem cell23_8002847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 4].length) (baseStart_8002847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002847 prefixEnd_8002847 := by exact prefixLift 8002847
  have htrace : WordTrace (prefixWord ++ tailWord_8002847) baseStart_8002847 baseEnd_8002847 := by
    simpa [prefixWord, tailWord_8002847, baseEnd_8002847] using wordTrace_append hprefix tailTrace_8002847
  have hstable : (prefixWord ++ tailWord_8002847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002847).length < 2 ^ (prefixWord ++ tailWord_8002847).sum := by decide
  have hdescent : baseEnd_8002847 < baseStart_8002847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002877 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 6]
def baseStart_8002877 : Nat := 118140960795 + 8002877 * 2 ^ 59
def prefixEnd_8002877 : Nat := 4983230072969 + 3 ^ 40 * 8002877 * 2
def baseEnd_8002877 : Nat := 456591391090198937848105

theorem tailTrace_8002877 : CollatzResearch.WordTrace tailWord_8002877 prefixEnd_8002877 456591391090198937848105 := by
  unfold tailWord_8002877
  simp only [CollatzResearch.WordTrace]
  refine ⟨291888903827950886421590885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194592602551967257614393923 291888903827950886421590885)
  ·
    refine ⟨54729169467740791204048291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291888903827950886421590885 54729169467740791204048291)
    ·
      refine ⟨82093754201611186806072437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54729169467740791204048291 82093754201611186806072437)
      ·
        refine ⟨7696289456401048763069291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82093754201611186806072437 7696289456401048763069291)
        ·
          refine ⟨11544434184601573144603937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7696289456401048763069291 11544434184601573144603937)
          ·
            refine ⟨8658325638451179858452953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11544434184601573144603937 8658325638451179858452953)
            ·
              refine ⟨6493744228838384893839715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8658325638451179858452953 6493744228838384893839715)
              ·
                refine ⟨9740616343257577340759573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493744228838384893839715 9740616343257577340759573)
                ·
                  refine ⟨456591391090198937848105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9740616343257577340759573 456591391090198937848105)
                  ·
                    rfl

theorem cell23_8002877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_8002877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002877 prefixEnd_8002877 := by exact prefixLift 8002877
  have htrace : WordTrace (prefixWord ++ tailWord_8002877) baseStart_8002877 baseEnd_8002877 := by
    simpa [prefixWord, tailWord_8002877, baseEnd_8002877] using wordTrace_append hprefix tailTrace_8002877
  have hstable : (prefixWord ++ tailWord_8002877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002877).length < 2 ^ (prefixWord ++ tailWord_8002877).sum := by decide
  have hdescent : baseEnd_8002877 < baseStart_8002877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002899 : List Nat := [1, 1, 1, 2, 1, 1, 5, 11]
def baseStart_8002899 : Nat := 118140960795 + 8002899 * 2 ^ 59
def prefixEnd_8002899 : Nat := 4983230072969 + 3 ^ 40 * 8002899 * 2
def baseEnd_8002899 : Nat := 152197548755044050168809

theorem tailTrace_8002899 : CollatzResearch.WordTrace tailWord_8002899 prefixEnd_8002899 152197548755044050168809 := by
  unfold tailWord_8002899
  simp only [CollatzResearch.WordTrace]
  refine ⟨291889706233871184178891751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194593137489247456119261167 291889706233871184178891751)
  ·
    refine ⟨437834559350806776268337627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291889706233871184178891751 437834559350806776268337627)
    ·
      refine ⟨656751839026210164402506441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437834559350806776268337627 656751839026210164402506441)
      ·
        refine ⟨492563879269657623301879831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656751839026210164402506441 492563879269657623301879831)
        ·
          refine ⟨738845818904486434952819747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492563879269657623301879831 738845818904486434952819747)
          ·
            refine ⟨1108268728356729652429229621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738845818904486434952819747 1108268728356729652429229621)
            ·
              refine ⟨103900193283443404915240277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1108268728356729652429229621 103900193283443404915240277)
              ·
                refine ⟨152197548755044050168809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103900193283443404915240277 152197548755044050168809)
                ·
                  rfl

theorem cell23_8002899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 11].length) (baseStart_8002899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002899 prefixEnd_8002899 := by exact prefixLift 8002899
  have htrace : WordTrace (prefixWord ++ tailWord_8002899) baseStart_8002899 baseEnd_8002899 := by
    simpa [prefixWord, tailWord_8002899, baseEnd_8002899] using wordTrace_append hprefix tailTrace_8002899
  have hstable : (prefixWord ++ tailWord_8002899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002899).length < 2 ^ (prefixWord ++ tailWord_8002899).sum := by decide
  have hdescent : baseEnd_8002899 < baseStart_8002899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002906 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_8002906 : Nat := 118140960795 + 8002906 * 2 ^ 59
def prefixEnd_8002906 : Nat := 4983230072969 + 3 ^ 40 * 8002906 * 2
def baseEnd_8002906 : Nat := 4109337410750770827170311

theorem tailTrace_8002906 : CollatzResearch.WordTrace tailWord_8002906 prefixEnd_8002906 4109337410750770827170311 := by
  unfold tailWord_8002906
  simp only [CollatzResearch.WordTrace]
  refine ⟨72972490386211456093599143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194593307696563882916264381 72972490386211456093599143)
  ·
    refine ⟨109458735579317184140398715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72972490386211456093599143 109458735579317184140398715)
    ·
      refine ⟨164188103368975776210598073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109458735579317184140398715 164188103368975776210598073)
      ·
        refine ⟨123141077526731832157948555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164188103368975776210598073 123141077526731832157948555)
        ·
          refine ⟨184711616290097748236922833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123141077526731832157948555 184711616290097748236922833)
          ·
            refine ⟨138533712217573311177692125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184711616290097748236922833 138533712217573311177692125)
            ·
              refine ⟨51950142081589991691634547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138533712217573311177692125 51950142081589991691634547)
              ·
                refine ⟨77925213122384987537451821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51950142081589991691634547 77925213122384987537451821)
                ·
                  refine ⟨29221954920894370326544433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77925213122384987537451821 29221954920894370326544433)
                  ·
                    refine ⟨21916466190670777744908325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29221954920894370326544433 21916466190670777744908325)
                    ·
                      refine ⟨4109337410750770827170311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21916466190670777744908325 4109337410750770827170311)
                      ·
                        rfl

theorem cell23_8002906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_8002906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002906 prefixEnd_8002906 := by exact prefixLift 8002906
  have htrace : WordTrace (prefixWord ++ tailWord_8002906) baseStart_8002906 baseEnd_8002906 := by
    simpa [prefixWord, tailWord_8002906, baseEnd_8002906] using wordTrace_append hprefix tailTrace_8002906
  have hstable : (prefixWord ++ tailWord_8002906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002906).length < 2 ^ (prefixWord ++ tailWord_8002906).sum := by decide
  have hdescent : baseEnd_8002906 < baseStart_8002906 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002913 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_8002913 : Nat := 118140960795 + 8002913 * 2 ^ 59
def prefixEnd_8002913 : Nat := 4983230072969 + 3 ^ 40 * 8002913 * 2
def baseEnd_8002913 : Nat := 4109341005115352299782779

theorem tailTrace_8002913 : CollatzResearch.WordTrace tailWord_8002913 prefixEnd_8002913 4109341005115352299782779 := by
  unfold tailWord_8002913
  simp only [CollatzResearch.WordTrace]
  refine ⟨291890216855820464569901393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194593477903880309713267595 291890216855820464569901393)
  ·
    refine ⟨218917662641865348427426045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291890216855820464569901393 218917662641865348427426045)
    ·
      refine ⟨82094123490699505660284767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218917662641865348427426045 82094123490699505660284767)
      ·
        refine ⟨123141185236049258490427151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82094123490699505660284767 123141185236049258490427151)
        ·
          refine ⟨184711777854073887735640727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123141185236049258490427151 184711777854073887735640727)
          ·
            refine ⟨277067666781110831603461091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184711777854073887735640727 277067666781110831603461091)
            ·
              refine ⟨415601500171666247405191637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277067666781110831603461091 415601500171666247405191637)
              ·
                refine ⟨9740660160273427673559179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 415601500171666247405191637 9740660160273427673559179)
                ·
                  refine ⟨14610990240410141510338769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740660160273427673559179 14610990240410141510338769)
                  ·
                    refine ⟨10958242680307606132754077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14610990240410141510338769 10958242680307606132754077)
                    ·
                      refine ⟨4109341005115352299782779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10958242680307606132754077 4109341005115352299782779)
                      ·
                        rfl

theorem cell23_8002913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_8002913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002913 prefixEnd_8002913 := by exact prefixLift 8002913
  have htrace : WordTrace (prefixWord ++ tailWord_8002913) baseStart_8002913 baseEnd_8002913 := by
    simpa [prefixWord, tailWord_8002913, baseEnd_8002913] using wordTrace_append hprefix tailTrace_8002913
  have hstable : (prefixWord ++ tailWord_8002913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002913).length < 2 ^ (prefixWord ++ tailWord_8002913).sum := by decide
  have hdescent : baseEnd_8002913 < baseStart_8002913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002927 : List Nat := [1, 1, 2, 1, 3, 1, 5, 4, 1, 2, 2]
def baseStart_8002927 : Nat := 118140960795 + 8002927 * 2 ^ 59
def prefixEnd_8002927 : Nat := 4983230072969 + 3 ^ 40 * 8002927 * 2
def baseEnd_8002927 : Nat := 4109348193844515245007715

theorem tailTrace_8002927 : CollatzResearch.WordTrace tailWord_8002927 prefixEnd_8002927 4109348193844515245007715 := by
  unfold tailWord_8002927
  simp only [CollatzResearch.WordTrace]
  refine ⟨291890727477769744960911035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194593818318513163307274023 291890727477769744960911035)
  ·
    refine ⟨437836091216654617441366553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291890727477769744960911035 437836091216654617441366553)
    ·
      refine ⟨328377068412490963081024915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437836091216654617441366553 328377068412490963081024915)
      ·
        refine ⟨492565602618736444621537373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328377068412490963081024915 492565602618736444621537373)
        ·
          refine ⟨184712100982026166733076515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492565602618736444621537373 184712100982026166733076515)
          ·
            refine ⟨277068151473039250099614773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184712100982026166733076515 277068151473039250099614773)
            ·
              refine ⟨25975139200597429696838885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277068151473039250099614773 25975139200597429696838885)
              ·
                refine ⟨4870338600112018068157291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25975139200597429696838885 4870338600112018068157291)
                ·
                  refine ⟨7305507900168027102235937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4870338600112018068157291 7305507900168027102235937)
                  ·
                    refine ⟨5479130925126020326676953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7305507900168027102235937 5479130925126020326676953)
                    ·
                      refine ⟨4109348193844515245007715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479130925126020326676953 4109348193844515245007715)
                      ·
                        rfl

theorem cell23_8002927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 2, 2].length) (baseStart_8002927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002927 prefixEnd_8002927 := by exact prefixLift 8002927
  have htrace : WordTrace (prefixWord ++ tailWord_8002927) baseStart_8002927 baseEnd_8002927 := by
    simpa [prefixWord, tailWord_8002927, baseEnd_8002927] using wordTrace_append hprefix tailTrace_8002927
  have hstable : (prefixWord ++ tailWord_8002927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002927).length < 2 ^ (prefixWord ++ tailWord_8002927).sum := by decide
  have hdescent : baseEnd_8002927 < baseStart_8002927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002956 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_8002956 : Nat := 118140960795 + 8002956 * 2 ^ 59
def prefixEnd_8002956 : Nat := 4983230072969 + 3 ^ 40 * 8002956 * 2
def baseEnd_8002956 : Nat := 4109363084783495631545081

theorem tailTrace_8002956 : CollatzResearch.WordTrace tailWord_8002956 prefixEnd_8002956 4109363084783495631545081 := by
  unfold tailWord_8002956
  simp only [CollatzResearch.WordTrace]
  refine ⟨145945892597332341456858361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194594523463109788609144481 145945892597332341456858361)
  ·
    refine ⟨109459419447999256092643771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145945892597332341456858361 109459419447999256092643771)
    ·
      refine ⟨164189129171998884138965657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109459419447999256092643771 164189129171998884138965657)
      ·
        refine ⟨123141846878999163104224243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164189129171998884138965657 123141846878999163104224243)
        ·
          refine ⟨184712770318498744656336365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123141846878999163104224243 184712770318498744656336365)
          ·
            refine ⟨69267288869437029246126137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184712770318498744656336365 69267288869437029246126137)
            ·
              refine ⟨51950466652077771934594603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69267288869437029246126137 51950466652077771934594603)
              ·
                refine ⟨77925699978116657901891905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51950466652077771934594603 77925699978116657901891905)
                ·
                  refine ⟨58444274983587493426418929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77925699978116657901891905 58444274983587493426418929)
                  ·
                    refine ⟨43833206237690620069814197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58444274983587493426418929 43833206237690620069814197)
                    ·
                      refine ⟨4109363084783495631545081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43833206237690620069814197 4109363084783495631545081)
                      ·
                        rfl

theorem cell23_8002956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_8002956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002956 prefixEnd_8002956 := by exact prefixLift 8002956
  have htrace : WordTrace (prefixWord ++ tailWord_8002956) baseStart_8002956 baseEnd_8002956 := by
    simpa [prefixWord, tailWord_8002956, baseEnd_8002956] using wordTrace_append hprefix tailTrace_8002956
  have hstable : (prefixWord ++ tailWord_8002956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002956).length < 2 ^ (prefixWord ++ tailWord_8002956).sum := by decide
  have hdescent : baseEnd_8002956 < baseStart_8002956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002964 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_8002964 : Nat := 118140960795 + 8002964 * 2 ^ 59
def prefixEnd_8002964 : Nat := 4983230072969 + 3 ^ 40 * 8002964 * 2
def baseEnd_8002964 : Nat := 4109367192628731600245045

theorem tailTrace_8002964 : CollatzResearch.WordTrace tailWord_8002964 prefixEnd_8002964 4109367192628731600245045 := by
  unfold tailWord_8002964
  simp only [CollatzResearch.WordTrace]
  refine ⟨145946038489317850140003973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194594717985757133520005297 145946038489317850140003973)
  ·
    refine ⟨27364882216747096901250745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145946038489317850140003973 27364882216747096901250745)
    ·
      refine ⟨20523661662560322675938059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27364882216747096901250745 20523661662560322675938059)
      ·
        refine ⟨30785492493840484013907089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20523661662560322675938059 30785492493840484013907089)
        ·
          refine ⟨23089119370380363010430317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30785492493840484013907089 23089119370380363010430317)
          ·
            refine ⟨8658419763892636128911369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23089119370380363010430317 8658419763892636128911369)
            ·
              refine ⟨6493814822919477096683527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8658419763892636128911369 6493814822919477096683527)
              ·
                refine ⟨9740722234379215645025291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493814822919477096683527 9740722234379215645025291)
                ·
                  refine ⟨14611083351568823467537937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740722234379215645025291 14611083351568823467537937)
                  ·
                    refine ⟨10958312513676617600653453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14611083351568823467537937 10958312513676617600653453)
                    ·
                      refine ⟨4109367192628731600245045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10958312513676617600653453 4109367192628731600245045)
                      ·
                        rfl

theorem cell23_8002964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_8002964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002964 prefixEnd_8002964 := by exact prefixLift 8002964
  have htrace : WordTrace (prefixWord ++ tailWord_8002964) baseStart_8002964 baseEnd_8002964 := by
    simpa [prefixWord, tailWord_8002964, baseEnd_8002964] using wordTrace_append hprefix tailTrace_8002964
  have hstable : (prefixWord ++ tailWord_8002964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002964).length < 2 ^ (prefixWord ++ tailWord_8002964).sum := by decide
  have hdescent : baseEnd_8002964 < baseStart_8002964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8002976 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 4, 6]
def baseStart_8002976 : Nat := 118140960795 + 8002976 * 2 ^ 59
def prefixEnd_8002976 : Nat := 4983230072969 + 3 ^ 40 * 8002976 * 2
def baseEnd_8002976 : Nat := 1369791118132195184431663

theorem tailTrace_8002976 : CollatzResearch.WordTrace tailWord_8002976 prefixEnd_8002976 1369791118132195184431663 := by
  unfold tailWord_8002976
  simp only [CollatzResearch.WordTrace]
  refine ⟨145946257327296113164722391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194595009769728150886296521 145946257327296113164722391)
  ·
    refine ⟨218919385990944169747083587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145946257327296113164722391 218919385990944169747083587)
    ·
      refine ⟨328379078986416254620625381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218919385990944169747083587 328379078986416254620625381)
      ·
        refine ⟨61571077309953047741367259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328379078986416254620625381 61571077309953047741367259)
        ·
          refine ⟨92356615964929571612050889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61571077309953047741367259 92356615964929571612050889)
          ·
            refine ⟨69267461973697178709038167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92356615964929571612050889 69267461973697178709038167)
            ·
              refine ⟨103901192960545768063557251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69267461973697178709038167 103901192960545768063557251)
              ·
                refine ⟨155851789440818652095335877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103901192960545768063557251 155851789440818652095335877)
                ·
                  refine ⟨29222210520153497267875477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155851789440818652095335877 29222210520153497267875477)
                  ·
                    refine ⟨1369791118132195184431663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29222210520153497267875477 1369791118132195184431663)
                    ·
                      rfl

theorem cell23_8002976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_8002976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8002976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8002976 prefixEnd_8002976 := by exact prefixLift 8002976
  have htrace : WordTrace (prefixWord ++ tailWord_8002976) baseStart_8002976 baseEnd_8002976 := by
    simpa [prefixWord, tailWord_8002976, baseEnd_8002976] using wordTrace_append hprefix tailTrace_8002976
  have hstable : (prefixWord ++ tailWord_8002976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8002976).length < 2 ^ (prefixWord ++ tailWord_8002976).sum := by decide
  have hdescent : baseEnd_8002976 < baseStart_8002976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8002976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003000 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 1, 4, 2]
def baseStart_8003000 : Nat := 118140960795 + 8003000 * 2 ^ 59
def prefixEnd_8003000 : Nat := 4983230072969 + 3 ^ 40 * 8003000 * 2
def baseEnd_8003000 : Nat := 4109385677932293459394879

theorem tailTrace_8003000 : CollatzResearch.WordTrace tailWord_8003000 prefixEnd_8003000 4109385677932293459394879 := by
  unfold tailWord_8003000
  simp only [CollatzResearch.WordTrace]
  refine ⟨145946695003252639214159227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194595593337670185618878969 145946695003252639214159227)
  ·
    refine ⟨218920042504878958821238841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145946695003252639214159227 218920042504878958821238841)
    ·
      refine ⟨164190031878659219115929131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218920042504878958821238841 164190031878659219115929131)
      ·
        refine ⟨246285047817988828673893697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164190031878659219115929131 246285047817988828673893697)
        ·
          refine ⟨184713785863491621505420273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246285047817988828673893697 184713785863491621505420273)
          ·
            refine ⟨138535339397618716129065205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184713785863491621505420273 138535339397618716129065205)
            ·
              refine ⟨12987688068526754637099863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138535339397618716129065205 12987688068526754637099863)
              ·
                refine ⟨19481532102790131955649795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12987688068526754637099863 19481532102790131955649795)
                ·
                  refine ⟨29222298154185197933474693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19481532102790131955649795 29222298154185197933474693)
                  ·
                    refine ⟨5479180903909724612526505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29222298154185197933474693 5479180903909724612526505)
                    ·
                      refine ⟨4109385677932293459394879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479180903909724612526505 4109385677932293459394879)
                      ·
                        rfl

theorem cell23_8003000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_8003000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003000 prefixEnd_8003000 := by exact prefixLift 8003000
  have htrace : WordTrace (prefixWord ++ tailWord_8003000) baseStart_8003000 baseEnd_8003000 := by
    simpa [prefixWord, tailWord_8003000, baseEnd_8003000] using wordTrace_append hprefix tailTrace_8003000
  have hstable : (prefixWord ++ tailWord_8003000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003000).length < 2 ^ (prefixWord ++ tailWord_8003000).sum := by decide
  have hdescent : baseEnd_8003000 < baseStart_8003000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003004 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_8003004 : Nat := 118140960795 + 8003004 * 2 ^ 59
def prefixEnd_8003004 : Nat := 4983230072969 + 3 ^ 40 * 8003004 * 2
def baseEnd_8003004 : Nat := 4109387731854911443744861

theorem tailTrace_8003004 : CollatzResearch.WordTrace tailWord_8003004 prefixEnd_8003004 4109387731854911443744861 := by
  unfold tailWord_8003004
  simp only [CollatzResearch.WordTrace]
  refine ⟨145946767949245393555732033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194595690598993858074309377 145946767949245393555732033)
  ·
    refine ⟨109460075961934045166799025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145946767949245393555732033 109460075961934045166799025)
    ·
      refine ⟨82095056971450533875099269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109460075961934045166799025 82095056971450533875099269)
      ·
        refine ⟨15392823182146975101581113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82095056971450533875099269 15392823182146975101581113)
        ·
          refine ⟨11544617386610231326185835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15392823182146975101581113 11544617386610231326185835)
          ·
            refine ⟨17316926079915346989278753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11544617386610231326185835 17316926079915346989278753)
            ·
              refine ⟨12987694559936510241959065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17316926079915346989278753 12987694559936510241959065)
              ·
                refine ⟨9740770919952382681469299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12987694559936510241959065 9740770919952382681469299)
                ·
                  refine ⟨14611156379928574022203949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740770919952382681469299 14611156379928574022203949)
                  ·
                    refine ⟨5479183642473215258326481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14611156379928574022203949 5479183642473215258326481)
                    ·
                      refine ⟨4109387731854911443744861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479183642473215258326481 4109387731854911443744861)
                      ·
                        rfl

theorem cell23_8003004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_8003004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003004 prefixEnd_8003004 := by exact prefixLift 8003004
  have htrace : WordTrace (prefixWord ++ tailWord_8003004) baseStart_8003004 baseEnd_8003004 := by
    simpa [prefixWord, tailWord_8003004, baseEnd_8003004] using wordTrace_append hprefix tailTrace_8003004
  have hstable : (prefixWord ++ tailWord_8003004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003004).length < 2 ^ (prefixWord ++ tailWord_8003004).sum := by decide
  have hdescent : baseEnd_8003004 < baseStart_8003004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003100 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_8003100 : Nat := 118140960795 + 8003100 * 2 ^ 59
def prefixEnd_8003100 : Nat := 4983230072969 + 3 ^ 40 * 8003100 * 2
def baseEnd_8003100 : Nat := 1369812341999247689381473

theorem tailTrace_8003100 : CollatzResearch.WordTrace tailWord_8003100 prefixEnd_8003100 1369812341999247689381473 := by
  unfold tailWord_8003100
  simp only [CollatzResearch.WordTrace]
  refine ⟨145948518653071497753479377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194598024870761997004639169 145948518653071497753479377)
  ·
    refine ⟨109461388989803623315109533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145948518653071497753479377 109461388989803623315109533)
    ·
      refine ⟨41048020871176358743166075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109461388989803623315109533 41048020871176358743166075)
      ·
        refine ⟨61572031306764538114749113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41048020871176358743166075 61572031306764538114749113)
        ·
          refine ⟨46179023480073403586061835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61572031306764538114749113 46179023480073403586061835)
          ·
            refine ⟨69268535220110105379092753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46179023480073403586061835 69268535220110105379092753)
            ·
              refine ⟨51951401415082579034319565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69268535220110105379092753 51951401415082579034319565)
              ·
                refine ⟨19481775530655967137869837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51951401415082579034319565 19481775530655967137869837)
                ·
                  refine ⟨7305665823995987676701189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19481775530655967137869837 7305665823995987676701189)
                  ·
                    refine ⟨1369812341999247689381473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305665823995987676701189 1369812341999247689381473)
                    ·
                      rfl

theorem cell23_8003100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_8003100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003100 prefixEnd_8003100 := by exact prefixLift 8003100
  have htrace : WordTrace (prefixWord ++ tailWord_8003100) baseStart_8003100 baseEnd_8003100 := by
    simpa [prefixWord, tailWord_8003100, baseEnd_8003100] using wordTrace_append hprefix tailTrace_8003100
  have hstable : (prefixWord ++ tailWord_8003100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003100).length < 2 ^ (prefixWord ++ tailWord_8003100).sum := by decide
  have hdescent : baseEnd_8003100 < baseStart_8003100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003107 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 2, 4, 2]
def baseStart_8003107 : Nat := 118140960795 + 8003107 * 2 ^ 59
def prefixEnd_8003107 : Nat := 4983230072969 + 3 ^ 40 * 8003107 * 2
def baseEnd_8003107 : Nat := 4109440620362324540756887

theorem tailTrace_8003107 : CollatzResearch.WordTrace tailWord_8003107 prefixEnd_8003107 4109440620362324540756887 := by
  unfold tailWord_8003107
  simp only [CollatzResearch.WordTrace]
  refine ⟨291897292617117635702463575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194598195078078423801642383 291897292617117635702463575)
  ·
    refine ⟨437845938925676453553695363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291897292617117635702463575 437845938925676453553695363)
    ·
      refine ⟨656768908388514680330543045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437845938925676453553695363 656768908388514680330543045)
      ·
        refine ⟨123144170322846502561976821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 656768908388514680330543045 123144170322846502561976821)
        ·
          refine ⟨11544765967766859615185327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123144170322846502561976821 11544765967766859615185327)
          ·
            refine ⟨17317148951650289422777991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11544765967766859615185327 17317148951650289422777991)
            ·
              refine ⟨25975723427475434134166987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17317148951650289422777991 25975723427475434134166987)
              ·
                refine ⟨38963585141213151201250481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25975723427475434134166987 38963585141213151201250481)
                ·
                  refine ⟨29222688855909863400937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38963585141213151201250481 29222688855909863400937861)
                  ·
                    refine ⟨5479254160483099387675849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29222688855909863400937861 5479254160483099387675849)
                    ·
                      refine ⟨4109440620362324540756887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479254160483099387675849 4109440620362324540756887)
                      ·
                        rfl

theorem cell23_8003107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_8003107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003107 prefixEnd_8003107 := by exact prefixLift 8003107
  have htrace : WordTrace (prefixWord ++ tailWord_8003107) baseStart_8003107 baseEnd_8003107 := by
    simpa [prefixWord, tailWord_8003107, baseEnd_8003107] using wordTrace_append hprefix tailTrace_8003107
  have hstable : (prefixWord ++ tailWord_8003107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003107).length < 2 ^ (prefixWord ++ tailWord_8003107).sum := by decide
  have hdescent : baseEnd_8003107 < baseStart_8003107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003127 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_8003127 : Nat := 118140960795 + 8003127 * 2 ^ 59
def prefixEnd_8003127 : Nat := 4983230072969 + 3 ^ 40 * 8003127 * 2
def baseEnd_8003127 : Nat := 4109450889975414462506795

theorem tailTrace_8003127 : CollatzResearch.WordTrace tailWord_8003127 prefixEnd_8003127 4109450889975414462506795 := by
  unfold tailWord_8003127
  simp only [CollatzResearch.WordTrace]
  refine ⟨291898022077045179118191635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194598681384696786078794423 291898022077045179118191635)
  ·
    refine ⟨437847033115567768677287453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291898022077045179118191635 437847033115567768677287453)
    ·
      refine ⟨164192637418337913253982795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437847033115567768677287453 164192637418337913253982795)
      ·
        refine ⟨246288956127506869880974193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164192637418337913253982795 246288956127506869880974193)
        ·
          refine ⟨184716717095630152410730645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246288956127506869880974193 184716717095630152410730645)
          ·
            refine ⟨8658596113857663394252999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184716717095630152410730645 8658596113857663394252999)
            ·
              refine ⟨12987894170786495091379499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658596113857663394252999 12987894170786495091379499)
              ·
                refine ⟨19481841256179742637069249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12987894170786495091379499 19481841256179742637069249)
                ·
                  refine ⟨14611380942134806977801937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19481841256179742637069249 14611380942134806977801937)
                  ·
                    refine ⟨10958535706601105233351453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14611380942134806977801937 10958535706601105233351453)
                    ·
                      refine ⟨4109450889975414462506795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10958535706601105233351453 4109450889975414462506795)
                      ·
                        rfl

theorem cell23_8003127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_8003127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003127 prefixEnd_8003127 := by exact prefixLift 8003127
  have htrace : WordTrace (prefixWord ++ tailWord_8003127) baseStart_8003127 baseEnd_8003127 := by
    simpa [prefixWord, tailWord_8003127, baseEnd_8003127] using wordTrace_append hprefix tailTrace_8003127
  have hstable : (prefixWord ++ tailWord_8003127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003127).length < 2 ^ (prefixWord ++ tailWord_8003127).sum := by decide
  have hdescent : baseEnd_8003127 < baseStart_8003127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003180 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 8, 2]
def baseStart_8003180 : Nat := 118140960795 + 8003180 * 2 ^ 59
def prefixEnd_8003180 : Nat := 4983230072969 + 3 ^ 40 * 8003180 * 2
def baseEnd_8003180 : Nat := 4109478104450102755144051

theorem tailTrace_8003180 : CollatzResearch.WordTrace tailWord_8003180 prefixEnd_8003180 4109478104450102755144051 := by
  unfold tailWord_8003180
  simp only [CollatzResearch.WordTrace]
  refine ⟨145949977572926584584935497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194599970097235446113247329 145949977572926584584935497)
  ·
    refine ⟨109462483179694938438701623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145949977572926584584935497 109462483179694938438701623)
    ·
      refine ⟨164193724769542407658052435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109462483179694938438701623 164193724769542407658052435)
      ·
        refine ⟨246290587154313611487078653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164193724769542407658052435 246290587154313611487078653)
        ·
          refine ⟨92358970182867604307654495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246290587154313611487078653 92358970182867604307654495)
          ·
            refine ⟨138538455274301406461481743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92358970182867604307654495 138538455274301406461481743)
            ·
              refine ⟨207807682911452109692222615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138538455274301406461481743 207807682911452109692222615)
              ·
                refine ⟨311711524367178164538333923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207807682911452109692222615 311711524367178164538333923)
                ·
                  refine ⟨467567286550767246807500885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311711524367178164538333923 467567286550767246807500885)
                  ·
                    refine ⟨5479304139266803673525401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 467567286550767246807500885 5479304139266803673525401)
                    ·
                      refine ⟨4109478104450102755144051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479304139266803673525401 4109478104450102755144051)
                      ·
                        rfl

theorem cell23_8003180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_8003180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003180 prefixEnd_8003180 := by exact prefixLift 8003180
  have htrace : WordTrace (prefixWord ++ tailWord_8003180) baseStart_8003180 baseEnd_8003180 := by
    simpa [prefixWord, tailWord_8003180, baseEnd_8003180] using wordTrace_append hprefix tailTrace_8003180
  have hstable : (prefixWord ++ tailWord_8003180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003180).length < 2 ^ (prefixWord ++ tailWord_8003180).sum := by decide
  have hdescent : baseEnd_8003180 < baseStart_8003180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003183 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_8003183 : Nat := 118140960795 + 8003183 * 2 ^ 59
def prefixEnd_8003183 : Nat := 4983230072969 + 3 ^ 40 * 8003183 * 2
def baseEnd_8003183 : Nat := 4109479644892066243406537

theorem tailTrace_8003183 : CollatzResearch.WordTrace tailWord_8003183 prefixEnd_8003183 4109479644892066243406537 := by
  unfold tailWord_8003183
  simp only [CollatzResearch.WordTrace]
  refine ⟨291900064564842300682230203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194600043043228200454820135 291900064564842300682230203)
  ·
    refine ⟨437850096847263451023345305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291900064564842300682230203 437850096847263451023345305)
    ·
      refine ⟨328387572635447588267508979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437850096847263451023345305 328387572635447588267508979)
      ·
        refine ⟨492581358953171382401263469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328387572635447588267508979 492581358953171382401263469)
        ·
          refine ⟨184718009607439268400473801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492581358953171382401263469 184718009607439268400473801)
          ·
            refine ⟨138538507205579451300355351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184718009607439268400473801 138538507205579451300355351)
            ·
              refine ⟨207807760808369176950533027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138538507205579451300355351 207807760808369176950533027)
              ·
                refine ⟨311711641212553765425799541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207807760808369176950533027 311711641212553765425799541)
                ·
                  refine ⟨29222966363676915508668707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311711641212553765425799541 29222966363676915508668707)
                  ·
                    refine ⟨43834449545515373263003061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29222966363676915508668707 43834449545515373263003061)
                    ·
                      refine ⟨4109479644892066243406537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43834449545515373263003061 4109479644892066243406537)
                      ·
                        rfl

theorem cell23_8003183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_8003183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003183 prefixEnd_8003183 := by exact prefixLift 8003183
  have htrace : WordTrace (prefixWord ++ tailWord_8003183) baseStart_8003183 baseEnd_8003183 := by
    simpa [prefixWord, tailWord_8003183, baseEnd_8003183] using wordTrace_append hprefix tailTrace_8003183
  have hstable : (prefixWord ++ tailWord_8003183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003183).length < 2 ^ (prefixWord ++ tailWord_8003183).sum := by decide
  have hdescent : baseEnd_8003183 < baseStart_8003183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003197 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_8003197 : Nat := 118140960795 + 8003197 * 2 ^ 59
def prefixEnd_8003197 : Nat := 4983230072969 + 3 ^ 40 * 8003197 * 2
def baseEnd_8003197 : Nat := 4109486833621229188631473

theorem tailTrace_8003197 : CollatzResearch.WordTrace tailWord_8003197 prefixEnd_8003197 4109486833621229188631473 := by
  unfold tailWord_8003197
  simp only [CollatzResearch.WordTrace]
  refine ⟨291900575186791581073239845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194600383457861054048826563 291900575186791581073239845)
  ·
    refine ⟨54731357847523421451232471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291900575186791581073239845 54731357847523421451232471)
    ·
      refine ⟨82097036771285132176848707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54731357847523421451232471 82097036771285132176848707)
      ·
        refine ⟨123145555156927698265273061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82097036771285132176848707 123145555156927698265273061)
        ·
          refine ⟨23089791591923943424738699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123145555156927698265273061 23089791591923943424738699)
          ·
            refine ⟨34634687387885915137108049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23089791591923943424738699 34634687387885915137108049)
            ·
              refine ⟨25976015540914436352831037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34634687387885915137108049 25976015540914436352831037)
              ·
                refine ⟨9741005827842913632311639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25976015540914436352831037 9741005827842913632311639)
                ·
                  refine ⟨14611508741764370448467459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9741005827842913632311639 14611508741764370448467459)
                  ·
                    refine ⟨21917263112646555672701189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14611508741764370448467459 21917263112646555672701189)
                    ·
                      refine ⟨4109486833621229188631473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21917263112646555672701189 4109486833621229188631473)
                      ·
                        rfl

theorem cell23_8003197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_8003197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003197 prefixEnd_8003197 := by exact prefixLift 8003197
  have htrace : WordTrace (prefixWord ++ tailWord_8003197) baseStart_8003197 baseEnd_8003197 := by
    simpa [prefixWord, tailWord_8003197, baseEnd_8003197] using wordTrace_append hprefix tailTrace_8003197
  have hstable : (prefixWord ++ tailWord_8003197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003197).length < 2 ^ (prefixWord ++ tailWord_8003197).sum := by decide
  have hdescent : baseEnd_8003197 < baseStart_8003197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003200 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5]
def baseStart_8003200 : Nat := 118140960795 + 8003200 * 2 ^ 59
def prefixEnd_8003200 : Nat := 4983230072969 + 3 ^ 40 * 8003200 * 2
def baseEnd_8003200 : Nat := 4109488374063192676893959

theorem tailTrace_8003200 : CollatzResearch.WordTrace tailWord_8003200 prefixEnd_8003200 4109488374063192676893959 := by
  unfold tailWord_8003200
  simp only [CollatzResearch.WordTrace]
  refine ⟨145950342302890356292799527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194600456403853808390399369 145950342302890356292799527)
  ·
    refine ⟨218925513454335534439199291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145950342302890356292799527 218925513454335534439199291)
    ·
      refine ⟨328388270181503301658798937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218925513454335534439199291 328388270181503301658798937)
      ·
        refine ⟨246291202636127476244099203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328388270181503301658798937 246291202636127476244099203)
        ·
          refine ⟨369436803954191214366148805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246291202636127476244099203 369436803954191214366148805)
          ·
            refine ⟨69269400741410852693652901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369436803954191214366148805 69269400741410852693652901)
            ·
              refine ⟨12988012639014534880059919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69269400741410852693652901 12988012639014534880059919)
              ·
                refine ⟨19482018958521802320089879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12988012639014534880059919 19482018958521802320089879)
                ·
                  refine ⟨29223028437782703480134819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19482018958521802320089879 29223028437782703480134819)
                  ·
                    refine ⟨43834542656674055220202229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29223028437782703480134819 43834542656674055220202229)
                    ·
                      refine ⟨4109488374063192676893959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43834542656674055220202229 4109488374063192676893959)
                      ·
                        rfl

theorem cell23_8003200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_8003200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003200 prefixEnd_8003200 := by exact prefixLift 8003200
  have htrace : WordTrace (prefixWord ++ tailWord_8003200) baseStart_8003200 baseEnd_8003200 := by
    simpa [prefixWord, tailWord_8003200, baseEnd_8003200] using wordTrace_append hprefix tailTrace_8003200
  have hstable : (prefixWord ++ tailWord_8003200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003200).length < 2 ^ (prefixWord ++ tailWord_8003200).sum := by decide
  have hdescent : baseEnd_8003200 < baseStart_8003200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003208 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_8003208 : Nat := 118140960795 + 8003208 * 2 ^ 59
def prefixEnd_8003208 : Nat := 4983230072969 + 3 ^ 40 * 8003208 * 2
def baseEnd_8003208 : Nat := 4109492481908428645593923

theorem tailTrace_8003208 : CollatzResearch.WordTrace tailWord_8003208 prefixEnd_8003208 4109492481908428645593923 := by
  unfold tailWord_8003208
  simp only [CollatzResearch.WordTrace]
  refine ⟨145950488194875864975945139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194600650926501153301260185 145950488194875864975945139)
  ·
    refine ⟨218925732292313797463917709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145950488194875864975945139 218925732292313797463917709)
    ·
      refine ⟨82097149609617674048969141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218925732292313797463917709 82097149609617674048969141)
      ·
        refine ⟨7696607775901656942090857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82097149609617674048969141 7696607775901656942090857)
        ·
          refine ⟨5772455831926242706568143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7696607775901656942090857 5772455831926242706568143)
          ·
            refine ⟨8658683747889364059852215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772455831926242706568143 8658683747889364059852215)
            ·
              refine ⟨12988025621834046089778323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658683747889364059852215 12988025621834046089778323)
              ·
                refine ⟨19482038432751069134667485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12988025621834046089778323 19482038432751069134667485)
                ·
                  refine ⟨7305764412281650925500307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19482038432751069134667485 7305764412281650925500307)
                  ·
                    refine ⟨10958646618422476388250461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7305764412281650925500307 10958646618422476388250461)
                    ·
                      refine ⟨4109492481908428645593923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10958646618422476388250461 4109492481908428645593923)
                      ·
                        rfl

theorem cell23_8003208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_8003208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003208 prefixEnd_8003208 := by exact prefixLift 8003208
  have htrace : WordTrace (prefixWord ++ tailWord_8003208) baseStart_8003208 baseEnd_8003208 := by
    simpa [prefixWord, tailWord_8003208, baseEnd_8003208] using wordTrace_append hprefix tailTrace_8003208
  have hstable : (prefixWord ++ tailWord_8003208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003208).length < 2 ^ (prefixWord ++ tailWord_8003208).sum := by decide
  have hdescent : baseEnd_8003208 < baseStart_8003208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003210 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_8003210 : Nat := 118140960795 + 8003210 * 2 ^ 59
def prefixEnd_8003210 : Nat := 4983230072969 + 3 ^ 40 * 8003210 * 2
def baseEnd_8003210 : Nat := 4109493508869737637768913

theorem tailTrace_8003210 : CollatzResearch.WordTrace tailWord_8003210 prefixEnd_8003210 4109493508869737637768913 := by
  unfold tailWord_8003210
  simp only [CollatzResearch.WordTrace]
  refine ⟨72975262333936121073365771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194600699557162989528975389 72975262333936121073365771)
  ·
    refine ⟨109462893500904181610048657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72975262333936121073365771 109462893500904181610048657)
    ·
      refine ⟨82097170125678136207536493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109462893500904181610048657 82097170125678136207536493)
      ·
        refine ⟨30786438797129301077826185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82097170125678136207536493 30786438797129301077826185)
        ·
          refine ⟨23089829097846975808369639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30786438797129301077826185 23089829097846975808369639)
          ·
            refine ⟨34634743646770463712554459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23089829097846975808369639 34634743646770463712554459)
            ·
              refine ⟨51952115470155695568831689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34634743646770463712554459 51952115470155695568831689)
              ·
                refine ⟨38964086602616771676623767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51952115470155695568831689 38964086602616771676623767)
                ·
                  refine ⟨58446129903925157514935651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38964086602616771676623767 58446129903925157514935651)
                  ·
                    refine ⟨87669194855887736272403477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58446129903925157514935651 87669194855887736272403477)
                    ·
                      refine ⟨4109493508869737637768913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87669194855887736272403477 4109493508869737637768913)
                      ·
                        rfl

theorem cell23_8003210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_8003210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003210 prefixEnd_8003210 := by exact prefixLift 8003210
  have htrace : WordTrace (prefixWord ++ tailWord_8003210) baseStart_8003210 baseEnd_8003210 := by
    simpa [prefixWord, tailWord_8003210, baseEnd_8003210] using wordTrace_append hprefix tailTrace_8003210
  have hstable : (prefixWord ++ tailWord_8003210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003210).length < 2 ^ (prefixWord ++ tailWord_8003210).sum := by decide
  have hdescent : baseEnd_8003210 < baseStart_8003210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003224 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 2, 4]
def baseStart_8003224 : Nat := 118140960795 + 8003224 * 2 ^ 59
def prefixEnd_8003224 : Nat := 4983230072969 + 3 ^ 40 * 8003224 * 2
def baseEnd_8003224 : Nat := 1369833565866300194331283

theorem tailTrace_8003224 : CollatzResearch.WordTrace tailWord_8003224 prefixEnd_8003224 1369833565866300194331283 := by
  unfold tailWord_8003224
  simp only [CollatzResearch.WordTrace]
  refine ⟨145950779978846882342236363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194601039971795843122981817 145950779978846882342236363)
  ·
    refine ⟨218926169968270323513354545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145950779978846882342236363 218926169968270323513354545)
    ·
      refine ⟨164194627476202742635015909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218926169968270323513354545 164194627476202742635015909)
      ·
        refine ⟨30786492651788014244065483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164194627476202742635015909 30786492651788014244065483)
        ·
          refine ⟨46179738977682021366098225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30786492651788014244065483 46179738977682021366098225)
          ·
            refine ⟨34634804233261516024573669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46179738977682021366098225 34634804233261516024573669)
            ·
              refine ⟨6494025793736534254607563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34634804233261516024573669 6494025793736534254607563)
              ·
                refine ⟨9741038690604801381911345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494025793736534254607563 9741038690604801381911345)
                ·
                  refine ⟨7305779017953601036433509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9741038690604801381911345 7305779017953601036433509)
                  ·
                    refine ⟨1369833565866300194331283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305779017953601036433509 1369833565866300194331283)
                    ·
                      rfl

theorem cell23_8003224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_8003224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003224 prefixEnd_8003224 := by exact prefixLift 8003224
  have htrace : WordTrace (prefixWord ++ tailWord_8003224) baseStart_8003224 baseEnd_8003224 := by
    simpa [prefixWord, tailWord_8003224, baseEnd_8003224] using wordTrace_append hprefix tailTrace_8003224
  have hstable : (prefixWord ++ tailWord_8003224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003224).length < 2 ^ (prefixWord ++ tailWord_8003224).sum := by decide
  have hdescent : baseEnd_8003224 < baseStart_8003224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003231 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 4]
def baseStart_8003231 : Nat := 118140960795 + 8003231 * 2 ^ 59
def prefixEnd_8003231 : Nat := 4983230072969 + 3 ^ 40 * 8003231 * 2
def baseEnd_8003231 : Nat := 4109504291963482055606317

theorem tailTrace_8003231 : CollatzResearch.WordTrace tailWord_8003231 prefixEnd_8003231 4109504291963482055606317 := by
  unfold tailWord_8003231
  simp only [CollatzResearch.WordTrace]
  refine ⟨291901815268668404879977547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194601210179112269919985031 291901815268668404879977547)
  ·
    refine ⟨437852722903002607319966321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291901815268668404879977547 437852722903002607319966321)
    ·
      refine ⟨328389542177251955489974741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437852722903002607319966321 328389542177251955489974741)
      ·
        refine ⟨7696629894779342706796283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 328389542177251955489974741 7696629894779342706796283)
        ·
          refine ⟨11544944842169014060194425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7696629894779342706796283 11544944842169014060194425)
          ·
            refine ⟨8658708631626760545145819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11544944842169014060194425 8658708631626760545145819)
            ·
              refine ⟨12988062947440140817718729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658708631626760545145819 12988062947440140817718729)
              ·
                refine ⟨9741047210580105613289047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12988062947440140817718729 9741047210580105613289047)
                ·
                  refine ⟨14611570815870158419933571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9741047210580105613289047 14611570815870158419933571)
                  ·
                    refine ⟨21917356223805237629900357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14611570815870158419933571 21917356223805237629900357)
                    ·
                      refine ⟨4109504291963482055606317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21917356223805237629900357 4109504291963482055606317)
                      ·
                        rfl

theorem cell23_8003231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_8003231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003231 prefixEnd_8003231 := by exact prefixLift 8003231
  have htrace : WordTrace (prefixWord ++ tailWord_8003231) baseStart_8003231 baseEnd_8003231 := by
    simpa [prefixWord, tailWord_8003231, baseEnd_8003231] using wordTrace_append hprefix tailTrace_8003231
  have hstable : (prefixWord ++ tailWord_8003231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003231).length < 2 ^ (prefixWord ++ tailWord_8003231).sum := by decide
  have hdescent : baseEnd_8003231 < baseStart_8003231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003264 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 2, 1, 3]
def baseStart_8003264 : Nat := 118140960795 + 8003264 * 2 ^ 59
def prefixEnd_8003264 : Nat := 4983230072969 + 3 ^ 40 * 8003264 * 2
def baseEnd_8003264 : Nat := 4109521236825080426493665

theorem tailTrace_8003264 : CollatzResearch.WordTrace tailWord_8003264 prefixEnd_8003264 4109521236825080426493665 := by
  unfold tailWord_8003264
  simp only [CollatzResearch.WordTrace]
  refine ⟨145951509438774425757964423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194602012585032567677285897 145951509438774425757964423)
  ·
    refine ⟨218927264158161638636946635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145951509438774425757964423 218927264158161638636946635)
    ·
      refine ⟨328390896237242457955419953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218927264158161638636946635 328390896237242457955419953)
      ·
        refine ⟨246293172177931843466564965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328390896237242457955419953 246293172177931843466564965)
        ·
          refine ⟨46179969783362220649980931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246293172177931843466564965 46179969783362220649980931)
          ·
            refine ⟨69269954675043330974971397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46179969783362220649980931 69269954675043330974971397)
            ·
              refine ⟨12988116501570624557807137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69269954675043330974971397 12988116501570624557807137)
              ·
                refine ⟨9741087376177968418355353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12988116501570624557807137 9741087376177968418355353)
                ·
                  refine ⟨7305815532133476313766515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9741087376177968418355353 7305815532133476313766515)
                  ·
                    refine ⟨10958723298200214470649773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7305815532133476313766515 10958723298200214470649773)
                    ·
                      refine ⟨4109521236825080426493665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10958723298200214470649773 4109521236825080426493665)
                      ·
                        rfl

theorem cell23_8003264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_8003264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003264 prefixEnd_8003264 := by exact prefixLift 8003264
  have htrace : WordTrace (prefixWord ++ tailWord_8003264) baseStart_8003264 baseEnd_8003264 := by
    simpa [prefixWord, tailWord_8003264, baseEnd_8003264] using wordTrace_append hprefix tailTrace_8003264
  have hstable : (prefixWord ++ tailWord_8003264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003264).length < 2 ^ (prefixWord ++ tailWord_8003264).sum := by decide
  have hdescent : baseEnd_8003264 < baseStart_8003264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003300 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_8003300 : Nat := 118140960795 + 8003300 * 2 ^ 59
def prefixEnd_8003300 : Nat := 4983230072969 + 3 ^ 40 * 8003300 * 2
def baseEnd_8003300 : Nat := 4109539722128642285643499

theorem tailTrace_8003300 : CollatzResearch.WordTrace tailWord_8003300 prefixEnd_8003300 4109539722128642285643499 := by
  unfold tailWord_8003300
  simp only [CollatzResearch.WordTrace]
  refine ⟨145952165952709214832119677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194602887936945619776159569 145952165952709214832119677)
  ·
    refine ⟨54732062232265955562044879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145952165952709214832119677 54732062232265955562044879)
    ·
      refine ⟨82098093348398933343067319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54732062232265955562044879 82098093348398933343067319)
      ·
        refine ⟨123147140022598400014600979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82098093348398933343067319 123147140022598400014600979)
        ·
          refine ⟨184720710033897600021901469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123147140022598400014600979 184720710033897600021901469)
          ·
            refine ⟨69270266262711600008213051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184720710033897600021901469 69270266262711600008213051)
            ·
              refine ⟨103905399394067400012319577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69270266262711600008213051 103905399394067400012319577)
              ·
                refine ⟨77929049545550550009239683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103905399394067400012319577 77929049545550550009239683)
                ·
                  refine ⟨116893574318325825013859525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77929049545550550009239683 116893574318325825013859525)
                  ·
                    refine ⟨21917545184686092190098661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116893574318325825013859525 21917545184686092190098661)
                    ·
                      refine ⟨4109539722128642285643499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21917545184686092190098661 4109539722128642285643499)
                      ·
                        rfl

theorem cell23_8003300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_8003300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003300 prefixEnd_8003300 := by exact prefixLift 8003300
  have htrace : WordTrace (prefixWord ++ tailWord_8003300) baseStart_8003300 baseEnd_8003300 := by
    simpa [prefixWord, tailWord_8003300, baseEnd_8003300] using wordTrace_append hprefix tailTrace_8003300
  have hstable : (prefixWord ++ tailWord_8003300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003300).length < 2 ^ (prefixWord ++ tailWord_8003300).sum := by decide
  have hdescent : baseEnd_8003300 < baseStart_8003300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003304 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_8003304 : Nat := 118140960795 + 8003304 * 2 ^ 59
def prefixEnd_8003304 : Nat := 4983230072969 + 3 ^ 40 * 8003304 * 2
def baseEnd_8003304 : Nat := 4109541776051260269993481

theorem tailTrace_8003304 : CollatzResearch.WordTrace tailWord_8003304 prefixEnd_8003304 4109541776051260269993481 := by
  unfold tailWord_8003304
  simp only [CollatzResearch.WordTrace]
  refine ⟨145952238898701969173692483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194602985198269292231589977 145952238898701969173692483)
  ·
    refine ⟨218928358348052953760538725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145952238898701969173692483 218928358348052953760538725)
    ·
      refine ⟨41049067190259928830101011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218928358348052953760538725 41049067190259928830101011)
      ·
        refine ⟨61573600785389893245151517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41049067190259928830101011 61573600785389893245151517)
        ·
          refine ⟨23090100294521209966931819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61573600785389893245151517 23090100294521209966931819)
          ·
            refine ⟨34635150441781814950397729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23090100294521209966931819 34635150441781814950397729)
            ·
              refine ⟨25976362831336361212798297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34635150441781814950397729 25976362831336361212798297)
              ·
                refine ⟨19482272123502270909598723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25976362831336361212798297 19482272123502270909598723)
                ·
                  refine ⟨29223408185253406364398085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19482272123502270909598723 29223408185253406364398085)
                  ·
                    refine ⟨5479389034735013693324641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29223408185253406364398085 5479389034735013693324641)
                    ·
                      refine ⟨4109541776051260269993481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479389034735013693324641 4109541776051260269993481)
                      ·
                        rfl

theorem cell23_8003304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_8003304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003304 prefixEnd_8003304 := by exact prefixLift 8003304
  have htrace : WordTrace (prefixWord ++ tailWord_8003304) baseStart_8003304 baseEnd_8003304 := by
    simpa [prefixWord, tailWord_8003304, baseEnd_8003304] using wordTrace_append hprefix tailTrace_8003304
  have hstable : (prefixWord ++ tailWord_8003304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003304).length < 2 ^ (prefixWord ++ tailWord_8003304).sum := by decide
  have hdescent : baseEnd_8003304 < baseStart_8003304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003310 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_8003310 : Nat := 118140960795 + 8003310 * 2 ^ 59
def prefixEnd_8003310 : Nat := 4983230072969 + 3 ^ 40 * 8003310 * 2
def baseEnd_8003310 : Nat := 456616095215020805168717

theorem tailTrace_8003310 : CollatzResearch.WordTrace tailWord_8003310 prefixEnd_8003310 456616095215020805168717 := by
  unfold tailWord_8003310
  simp only [CollatzResearch.WordTrace]
  refine ⟨36488087079422775171512923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194603131090254800914735589 36488087079422775171512923)
  ·
    refine ⟨54732130619134162757269385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36488087079422775171512923 54732130619134162757269385)
    ·
      refine ⟨41049097964350622067952039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54732130619134162757269385 41049097964350622067952039)
      ·
        refine ⟨61573646946525933101928059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41049097964350622067952039 61573646946525933101928059)
        ·
          refine ⟨92360470419788899652892089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61573646946525933101928059 92360470419788899652892089)
          ·
            refine ⟨69270352814841674739669067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92360470419788899652892089 69270352814841674739669067)
            ·
              refine ⟨103905529222262512109503601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69270352814841674739669067 103905529222262512109503601)
              ·
                refine ⟨77929146916696884082127701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103905529222262512109503601 77929146916696884082127701)
                ·
                  refine ⟨456616095215020805168717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77929146916696884082127701 456616095215020805168717)
                  ·
                    rfl

theorem cell23_8003310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_8003310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003310 prefixEnd_8003310 := by exact prefixLift 8003310
  have htrace : WordTrace (prefixWord ++ tailWord_8003310) baseStart_8003310 baseEnd_8003310 := by
    simpa [prefixWord, tailWord_8003310, baseEnd_8003310] using wordTrace_append hprefix tailTrace_8003310
  have hstable : (prefixWord ++ tailWord_8003310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003310).length < 2 ^ (prefixWord ++ tailWord_8003310).sum := by decide
  have hdescent : baseEnd_8003310 < baseStart_8003310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003327 : List Nat := [1, 1, 2, 2, 1, 3, 4, 4, 5]
def baseStart_8003327 : Nat := 118140960795 + 8003327 * 2 ^ 59
def prefixEnd_8003327 : Nat := 4983230072969 + 3 ^ 40 * 8003327 * 2
def baseEnd_8003327 : Nat := 456617065122923742222875

theorem tailTrace_8003327 : CollatzResearch.WordTrace tailWord_8003327 prefixEnd_8003327 456617065122923742222875 := by
  unfold tailWord_8003327
  simp only [CollatzResearch.WordTrace]
  refine ⟨291905316676320613275472235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194603544450880408850314823 291905316676320613275472235)
  ·
    refine ⟨437857975014480919913208353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291905316676320613275472235 437857975014480919913208353)
    ·
      refine ⟨328393481260860689934906265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437857975014480919913208353 328393481260860689934906265)
      ·
        refine ⟨246295110945645517451179699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328393481260860689934906265 246295110945645517451179699)
        ·
          refine ⟨369442666418468276176769549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246295110945645517451179699 369442666418468276176769549)
          ·
            refine ⟨138540999906925603566288581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369442666418468276176769549 138540999906925603566288581)
            ·
              refine ⟨25976437482548550668679109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138540999906925603566288581 25976437482548550668679109)
              ·
                refine ⟨4870582027977853250377333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25976437482548550668679109 4870582027977853250377333)
                ·
                  refine ⟨456617065122923742222875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4870582027977853250377333 456617065122923742222875)
                  ·
                    rfl

theorem cell23_8003327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 5].length) (baseStart_8003327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003327 prefixEnd_8003327 := by exact prefixLift 8003327
  have htrace : WordTrace (prefixWord ++ tailWord_8003327) baseStart_8003327 baseEnd_8003327 := by
    simpa [prefixWord, tailWord_8003327, baseEnd_8003327] using wordTrace_append hprefix tailTrace_8003327
  have hstable : (prefixWord ++ tailWord_8003327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003327).length < 2 ^ (prefixWord ++ tailWord_8003327).sum := by decide
  have hdescent : baseEnd_8003327 < baseStart_8003327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003338 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_8003338 : Nat := 118140960795 + 8003338 * 2 ^ 59
def prefixEnd_8003338 : Nat := 4983230072969 + 3 ^ 40 * 8003338 * 2
def baseEnd_8003338 : Nat := 4109559234393513136968325

theorem tailTrace_8003338 : CollatzResearch.WordTrace tailWord_8003338 prefixEnd_8003338 4109559234393513136968325 := by
  unfold tailWord_8003338
  simp only [CollatzResearch.WordTrace]
  refine ⟨72976429469820190538530667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194603811919520508102748445 72976429469820190538530667)
  ·
    refine ⟨109464644204730285807796001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72976429469820190538530667 109464644204730285807796001)
    ·
      refine ⟨82098483153547714355847001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109464644204730285807796001 82098483153547714355847001)
      ·
        refine ⟨61573862365160785766885251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82098483153547714355847001 61573862365160785766885251)
        ·
          refine ⟨92360793547741178650327877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61573862365160785766885251 92360793547741178650327877)
          ·
            refine ⟨17317648790201470996936477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92360793547741178650327877 17317648790201470996936477)
            ·
              refine ⟨6494118296325551623851179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17317648790201470996936477 6494118296325551623851179)
              ·
                refine ⟨9741177444488327435776769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494118296325551623851179 9741177444488327435776769)
                ·
                  refine ⟨7305883083366245576832577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9741177444488327435776769 7305883083366245576832577)
                  ·
                    refine ⟨5479412312524684182624433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7305883083366245576832577 5479412312524684182624433)
                    ·
                      refine ⟨4109559234393513136968325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479412312524684182624433 4109559234393513136968325)
                      ·
                        rfl

theorem cell23_8003338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_8003338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003338 prefixEnd_8003338 := by exact prefixLift 8003338
  have htrace : WordTrace (prefixWord ++ tailWord_8003338) baseStart_8003338 baseEnd_8003338 := by
    simpa [prefixWord, tailWord_8003338, baseEnd_8003338] using wordTrace_append hprefix tailTrace_8003338
  have hstable : (prefixWord ++ tailWord_8003338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003338).length < 2 ^ (prefixWord ++ tailWord_8003338).sum := by decide
  have hdescent : baseEnd_8003338 < baseStart_8003338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003340 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_8003340 : Nat := 118140960795 + 8003340 * 2 ^ 59
def prefixEnd_8003340 : Nat := 4983230072969 + 3 ^ 40 * 8003340 * 2
def baseEnd_8003340 : Nat := 1369853420451607376381105

theorem tailTrace_8003340 : CollatzResearch.WordTrace tailWord_8003340 prefixEnd_8003340 1369853420451607376381105 := by
  unfold tailWord_8003340
  simp only [CollatzResearch.WordTrace]
  refine ⟨145952895412636758247847737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194603860550182344330463649 145952895412636758247847737)
  ·
    refine ⟨109464671559477568685885803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145952895412636758247847737 109464671559477568685885803)
    ·
      refine ⟨164197007339216353028828705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109464671559477568685885803 164197007339216353028828705)
      ·
        refine ⟨123147755504412264771621529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164197007339216353028828705 123147755504412264771621529)
        ·
          refine ⟨92360816628309198578716147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123147755504412264771621529 92360816628309198578716147)
          ·
            refine ⟨138541224942463797868074221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92360816628309198578716147 138541224942463797868074221)
            ·
              refine ⟨51952959353423924200527833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138541224942463797868074221 51952959353423924200527833)
              ·
                refine ⟨38964719515067943150395875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51952959353423924200527833 38964719515067943150395875)
                ·
                  refine ⟨58447079272601914725593813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38964719515067943150395875 58447079272601914725593813)
                  ·
                    refine ⟨1369853420451607376381105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58447079272601914725593813 1369853420451607376381105)
                    ·
                      rfl

theorem cell23_8003340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_8003340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003340 prefixEnd_8003340 := by exact prefixLift 8003340
  have htrace : WordTrace (prefixWord ++ tailWord_8003340) baseStart_8003340 baseEnd_8003340 := by
    simpa [prefixWord, tailWord_8003340, baseEnd_8003340] using wordTrace_append hprefix tailTrace_8003340
  have hstable : (prefixWord ++ tailWord_8003340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003340).length < 2 ^ (prefixWord ++ tailWord_8003340).sum := by decide
  have hdescent : baseEnd_8003340 < baseStart_8003340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003377 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_8003377 : Nat := 118140960795 + 8003377 * 2 ^ 59
def prefixEnd_8003377 : Nat := 4983230072969 + 3 ^ 40 * 8003377 * 2
def baseEnd_8003377 : Nat := 4109579260139038484380645

theorem tailTrace_8003377 : CollatzResearch.WordTrace tailWord_8003377 prefixEnd_8003377 4109579260139038484380645 := by
  unfold tailWord_8003377
  simp only [CollatzResearch.WordTrace]
  refine ⟨291907140326139471814792385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194604760217426314543194923 291907140326139471814792385)
  ·
    refine ⟨218930355244604603861094289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291907140326139471814792385 218930355244604603861094289)
    ·
      refine ⟨164197766433453452895820717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218930355244604603861094289 164197766433453452895820717)
      ·
        refine ⟨61574162412545044835932769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164197766433453452895820717 61574162412545044835932769)
        ·
          refine ⟨46180621809408783626949577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61574162412545044835932769 46180621809408783626949577)
          ·
            refine ⟨34635466357056587720212183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46180621809408783626949577 34635466357056587720212183)
            ·
              refine ⟨51953199535584881580318275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34635466357056587720212183 51953199535584881580318275)
              ·
                refine ⟨77929799303377322370477413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51953199535584881580318275 77929799303377322370477413)
                ·
                  refine ⟨14611837369383247944464515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77929799303377322370477413 14611837369383247944464515)
                  ·
                    refine ⟨21917756054074871916696773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14611837369383247944464515 21917756054074871916696773)
                    ·
                      refine ⟨4109579260139038484380645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21917756054074871916696773 4109579260139038484380645)
                      ·
                        rfl

theorem cell23_8003377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_8003377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003377 prefixEnd_8003377 := by exact prefixLift 8003377
  have htrace : WordTrace (prefixWord ++ tailWord_8003377) baseStart_8003377 baseEnd_8003377 := by
    simpa [prefixWord, tailWord_8003377, baseEnd_8003377] using wordTrace_append hprefix tailTrace_8003377
  have hstable : (prefixWord ++ tailWord_8003377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003377).length < 2 ^ (prefixWord ++ tailWord_8003377).sum := by decide
  have hdescent : baseEnd_8003377 < baseStart_8003377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003397 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_8003397 : Nat := 118140960795 + 8003397 * 2 ^ 59
def prefixEnd_8003397 : Nat := 4983230072969 + 3 ^ 40 * 8003397 * 2
def baseEnd_8003397 : Nat := 4109589529752128406130553

theorem tailTrace_8003397 : CollatzResearch.WordTrace tailWord_8003397 prefixEnd_8003397 4109589529752128406130553 := by
  unfold tailWord_8003397
  simp only [CollatzResearch.WordTrace]
  refine ⟨291907869786067015230520445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194605246524044676820346963 291907869786067015230520445)
  ·
    refine ⟨109465451169775130711445167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291907869786067015230520445 109465451169775130711445167)
    ·
      refine ⟨164198176754662696067167751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109465451169775130711445167 164198176754662696067167751)
      ·
        refine ⟨246297265131994044100751627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164198176754662696067167751 246297265131994044100751627)
        ·
          refine ⟨369445897697991066151127441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246297265131994044100751627 369445897697991066151127441)
          ·
            refine ⟨277084423273493299613345581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369445897697991066151127441 277084423273493299613345581)
            ·
              refine ⟨103906658727559987355004593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277084423273493299613345581 103906658727559987355004593)
              ·
                refine ⟨77929994045669990516253445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103906658727559987355004593 77929994045669990516253445)
                ·
                  refine ⟨14611873883563123221797521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77929994045669990516253445 14611873883563123221797521)
                  ·
                    refine ⟨10958905412672342416348141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14611873883563123221797521 10958905412672342416348141)
                    ·
                      refine ⟨4109589529752128406130553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10958905412672342416348141 4109589529752128406130553)
                      ·
                        rfl

theorem cell23_8003397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_8003397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003397 prefixEnd_8003397 := by exact prefixLift 8003397
  have htrace : WordTrace (prefixWord ++ tailWord_8003397) baseStart_8003397 baseEnd_8003397 := by
    simpa [prefixWord, tailWord_8003397, baseEnd_8003397] using wordTrace_append hprefix tailTrace_8003397
  have hstable : (prefixWord ++ tailWord_8003397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003397).length < 2 ^ (prefixWord ++ tailWord_8003397).sum := by decide
  have hdescent : baseEnd_8003397 < baseStart_8003397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003438 : List Nat := [4, 1, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_8003438 : Nat := 118140960795 + 8003438 * 2 ^ 59
def prefixEnd_8003438 : Nat := 4983230072969 + 3 ^ 40 * 8003438 * 2
def baseEnd_8003438 : Nat := 1369870194152987581905955

theorem tailTrace_8003438 : CollatzResearch.WordTrace tailWord_8003438 prefixEnd_8003438 1369870194152987581905955 := by
  unfold tailWord_8003438
  simp only [CollatzResearch.WordTrace]
  refine ⟨36488670647364809904095371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194606243452612319488508645 36488670647364809904095371)
  ·
    refine ⟨54733005971047214856143057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36488670647364809904095371 54733005971047214856143057)
    ·
      refine ⟨41049754478285411142107293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54733005971047214856143057 41049754478285411142107293)
      ·
        refine ⟨15393657929357029178290235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41049754478285411142107293 15393657929357029178290235)
        ·
          refine ⟨23090486894035543767435353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15393657929357029178290235 23090486894035543767435353)
          ·
            refine ⟨17317865170526657825576515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23090486894035543767435353 17317865170526657825576515)
            ·
              refine ⟨25976797755789986738364773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17317865170526657825576515 25976797755789986738364773)
              ·
                refine ⟨4870649579210622513443395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25976797755789986738364773 4870649579210622513443395)
                ·
                  refine ⟨7305974368815933770165093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4870649579210622513443395 7305974368815933770165093)
                  ·
                    refine ⟨1369870194152987581905955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7305974368815933770165093 1369870194152987581905955)
                    ·
                      rfl

theorem cell23_8003438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_8003438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003438 prefixEnd_8003438 := by exact prefixLift 8003438
  have htrace : WordTrace (prefixWord ++ tailWord_8003438) baseStart_8003438 baseEnd_8003438 := by
    simpa [prefixWord, tailWord_8003438, baseEnd_8003438] using wordTrace_append hprefix tailTrace_8003438
  have hstable : (prefixWord ++ tailWord_8003438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003438).length < 2 ^ (prefixWord ++ tailWord_8003438).sum := by decide
  have hdescent : baseEnd_8003438 < baseStart_8003438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003477 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_8003477 : Nat := 118140960795 + 8003477 * 2 ^ 59
def prefixEnd_8003477 : Nat := 4983230072969 + 3 ^ 40 * 8003477 * 2
def baseEnd_8003477 : Nat := 1369876869401496031043395

theorem tailTrace_8003477 : CollatzResearch.WordTrace tailWord_8003477 prefixEnd_8003477 1369876869401496031043395 := by
  unfold tailWord_8003477
  simp only [CollatzResearch.WordTrace]
  refine ⟨291910787625777188893432685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194607191750518125928955123 291910787625777188893432685)
  ·
    refine ⟨109466545359666445835037257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291910787625777188893432685 109466545359666445835037257)
    ·
      refine ⟨82099909019749834376277943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109466545359666445835037257 82099909019749834376277943)
      ·
        refine ⟨123149863529624751564416915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82099909019749834376277943 123149863529624751564416915)
        ·
          refine ⟨184724795294437127346625373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123149863529624751564416915 184724795294437127346625373)
          ·
            refine ⟨69271798235413922754984515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184724795294437127346625373 69271798235413922754984515)
            ·
              refine ⟨103907697353120884132476773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69271798235413922754984515 103907697353120884132476773)
              ·
                refine ⟨19482693253710165774839395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103907697353120884132476773 19482693253710165774839395)
                ·
                  refine ⟨29224039880565248662259093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19482693253710165774839395 29224039880565248662259093)
                  ·
                    refine ⟨1369876869401496031043395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29224039880565248662259093 1369876869401496031043395)
                    ·
                      rfl

theorem cell23_8003477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_8003477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003477 prefixEnd_8003477 := by exact prefixLift 8003477
  have htrace : WordTrace (prefixWord ++ tailWord_8003477) baseStart_8003477 baseEnd_8003477 := by
    simpa [prefixWord, tailWord_8003477, baseEnd_8003477] using wordTrace_append hprefix tailTrace_8003477
  have hstable : (prefixWord ++ tailWord_8003477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003477).length < 2 ^ (prefixWord ++ tailWord_8003477).sum := by decide
  have hdescent : baseEnd_8003477 < baseStart_8003477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003518 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_8003518 : Nat := 118140960795 + 8003518 * 2 ^ 59
def prefixEnd_8003518 : Nat := 4983230072969 + 3 ^ 40 * 8003518 * 2
def baseEnd_8003518 : Nat := 4109651660911322432717497

theorem tailTrace_8003518 : CollatzResearch.WordTrace tailWord_8003518 prefixEnd_8003518 4109651660911322432717497 := by
  unfold tailWord_8003518
  simp only [CollatzResearch.WordTrace]
  refine ⟨36489035377328581611959401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194608188679085768597116805 36489035377328581611959401)
  ·
    refine ⟨27366776532996436208969551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36489035377328581611959401 27366776532996436208969551)
    ·
      refine ⟨41050164799494654313454327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27366776532996436208969551 41050164799494654313454327)
      ·
        refine ⟨61575247199241981470181491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41050164799494654313454327 61575247199241981470181491)
        ·
          refine ⟨92362870798862972205272237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61575247199241981470181491 92362870798862972205272237)
          ·
            refine ⟨34636076549573614576977089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92362870798862972205272237 34636076549573614576977089)
            ·
              refine ⟨25977057412180210932732817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34636076549573614576977089 25977057412180210932732817)
              ·
                refine ⟨19482793059135158199549613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25977057412180210932732817 19482793059135158199549613)
                ·
                  refine ⟨7306047397175684324831105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19482793059135158199549613 7306047397175684324831105)
                  ·
                    refine ⟨5479535547881763243623329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7306047397175684324831105 5479535547881763243623329)
                    ·
                      refine ⟨4109651660911322432717497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479535547881763243623329 4109651660911322432717497)
                      ·
                        rfl

theorem cell23_8003518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_8003518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003518 prefixEnd_8003518 := by exact prefixLift 8003518
  have htrace : WordTrace (prefixWord ++ tailWord_8003518) baseStart_8003518 baseEnd_8003518 := by
    simpa [prefixWord, tailWord_8003518, baseEnd_8003518] using wordTrace_append hprefix tailTrace_8003518
  have hstable : (prefixWord ++ tailWord_8003518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003518).length < 2 ^ (prefixWord ++ tailWord_8003518).sum := by decide
  have hdescent : baseEnd_8003518 < baseStart_8003518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003534 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_8003534 : Nat := 118140960795 + 8003534 * 2 ^ 59
def prefixEnd_8003534 : Nat := 4983230072969 + 3 ^ 40 * 8003534 * 2
def baseEnd_8003534 : Nat := 4109659876601794370117423

theorem tailTrace_8003534 : CollatzResearch.WordTrace tailWord_8003534 prefixEnd_8003534 4109659876601794370117423 := by
  unfold tailWord_8003534
  simp only [CollatzResearch.WordTrace]
  refine ⟨36489108323321335953532207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194608577724380458418838437 36489108323321335953532207)
  ·
    refine ⟨54733662484982003930298311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36489108323321335953532207 54733662484982003930298311)
    ·
      refine ⟨82100493727473005895447467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54733662484982003930298311 82100493727473005895447467)
      ·
        refine ⟨123150740591209508843171201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82100493727473005895447467 123150740591209508843171201)
        ·
          refine ⟨92363055443407131632378401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123150740591209508843171201 92363055443407131632378401)
          ·
            refine ⟨69272291582555348724283801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92363055443407131632378401 69272291582555348724283801)
            ·
              refine ⟨51954218686916511543212851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69272291582555348724283801 51954218686916511543212851)
              ·
                refine ⟨77931328030374767314819277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51954218686916511543212851 77931328030374767314819277)
                ·
                  refine ⟨29224248011390537743057229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77931328030374767314819277 29224248011390537743057229)
                  ·
                    refine ⟨10959093004271451653646461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29224248011390537743057229 10959093004271451653646461)
                    ·
                      refine ⟨4109659876601794370117423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10959093004271451653646461 4109659876601794370117423)
                      ·
                        rfl

theorem cell23_8003534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_8003534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003534 prefixEnd_8003534 := by exact prefixLift 8003534
  have htrace : WordTrace (prefixWord ++ tailWord_8003534) baseStart_8003534 baseEnd_8003534 := by
    simpa [prefixWord, tailWord_8003534, baseEnd_8003534] using wordTrace_append hprefix tailTrace_8003534
  have hstable : (prefixWord ++ tailWord_8003534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003534).length < 2 ^ (prefixWord ++ tailWord_8003534).sum := by decide
  have hdescent : baseEnd_8003534 < baseStart_8003534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003551 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 3]
def baseStart_8003551 : Nat := 118140960795 + 8003551 * 2 ^ 59
def prefixEnd_8003551 : Nat := 4983230072969 + 3 ^ 40 * 8003551 * 2
def baseEnd_8003551 : Nat := 4109668605772920803604845

theorem tailTrace_8003551 : CollatzResearch.WordTrace tailWord_8003551 prefixEnd_8003551 4109668605772920803604845 := by
  unfold tailWord_8003551
  simp only [CollatzResearch.WordTrace]
  refine ⟨291913486627509099531626507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194608991085006066354417671 291913486627509099531626507)
  ·
    refine ⟨437870229941263649297439761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291913486627509099531626507 437870229941263649297439761)
    ·
      refine ⟨328402672455947736973079821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437870229941263649297439761 328402672455947736973079821)
      ·
        refine ⟨123151002170980401364904933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328402672455947736973079821 123151002170980401364904933)
        ·
          refine ⟨23090812907058825255919675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123151002170980401364904933 23090812907058825255919675)
          ·
            refine ⟨34636219360588237883879513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23090812907058825255919675 34636219360588237883879513)
            ·
              refine ⟨25977164520441178412909635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34636219360588237883879513 25977164520441178412909635)
              ·
                refine ⟨38965746780661767619364453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25977164520441178412909635 38965746780661767619364453)
                ·
                  refine ⟨7306077521374081428630835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38965746780661767619364453 7306077521374081428630835)
                  ·
                    refine ⟨10959116282061122142946253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7306077521374081428630835 10959116282061122142946253)
                    ·
                      refine ⟨4109668605772920803604845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10959116282061122142946253 4109668605772920803604845)
                      ·
                        rfl

theorem cell23_8003551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_8003551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003551 prefixEnd_8003551 := by exact prefixLift 8003551
  have htrace : WordTrace (prefixWord ++ tailWord_8003551) baseStart_8003551 baseEnd_8003551 := by
    simpa [prefixWord, tailWord_8003551, baseEnd_8003551] using wordTrace_append hprefix tailTrace_8003551
  have hstable : (prefixWord ++ tailWord_8003551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003551).length < 2 ^ (prefixWord ++ tailWord_8003551).sum := by decide
  have hdescent : baseEnd_8003551 < baseStart_8003551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003567 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 1, 8]
def baseStart_8003567 : Nat := 118140960795 + 8003567 * 2 ^ 59
def prefixEnd_8003567 : Nat := 4983230072969 + 3 ^ 40 * 8003567 * 2
def baseEnd_8003567 : Nat := 1369892273821130913668257

theorem tailTrace_8003567 : CollatzResearch.WordTrace tailWord_8003567 prefixEnd_8003567 1369892273821130913668257 := by
  unfold tailWord_8003567
  simp only [CollatzResearch.WordTrace]
  refine ⟨291914070195451134264208955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194609380130300756176139303 291914070195451134264208955)
  ·
    refine ⟨437871105293176701396313433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291914070195451134264208955 437871105293176701396313433)
    ·
      refine ⟨328403328969882526047235075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437871105293176701396313433 328403328969882526047235075)
      ·
        refine ⟨492604993454823789070852613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328403328969882526047235075 492604993454823789070852613)
        ·
          refine ⟨92363436272779460450784865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 492604993454823789070852613 92363436272779460450784865)
          ·
            refine ⟨69272577204584595338088649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92363436272779460450784865 69272577204584595338088649)
            ·
              refine ⟨51954432903438446503566487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69272577204584595338088649 51954432903438446503566487)
              ·
                refine ⟨77931649355157669755349731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51954432903438446503566487 77931649355157669755349731)
                ·
                  refine ⟨116897474032736504633024597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77931649355157669755349731 116897474032736504633024597)
                  ·
                    refine ⟨1369892273821130913668257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116897474032736504633024597 1369892273821130913668257)
                    ·
                      rfl

theorem cell23_8003567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_8003567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003567 prefixEnd_8003567 := by exact prefixLift 8003567
  have htrace : WordTrace (prefixWord ++ tailWord_8003567) baseStart_8003567 baseEnd_8003567 := by
    simpa [prefixWord, tailWord_8003567, baseEnd_8003567] using wordTrace_append hprefix tailTrace_8003567
  have hstable : (prefixWord ++ tailWord_8003567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003567).length < 2 ^ (prefixWord ++ tailWord_8003567).sum := by decide
  have hdescent : baseEnd_8003567 < baseStart_8003567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003568 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 2, 1, 3]
def baseStart_8003568 : Nat := 118140960795 + 8003568 * 2 ^ 59
def prefixEnd_8003568 : Nat := 4983230072969 + 3 ^ 40 * 8003568 * 2
def baseEnd_8003568 : Nat := 4109677334944047237092267

theorem tailTrace_8003568 : CollatzResearch.WordTrace tailWord_8003568 prefixEnd_8003568 4109677334944047237092267 := by
  unfold tailWord_8003568
  simp only [CollatzResearch.WordTrace]
  refine ⟨145957053334223755717497679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194609404445631674289996905 145957053334223755717497679)
  ·
    refine ⟨218935580001335633576246519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145957053334223755717497679 218935580001335633576246519)
    ·
      refine ⟨328403370002003450364369779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218935580001335633576246519 328403370002003450364369779)
      ·
        refine ⟨492605055003005175546554669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328403370002003450364369779 492605055003005175546554669)
        ·
          refine ⟨184726895626126940829958001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492605055003005175546554669 184726895626126940829958001)
          ·
            refine ⟨138545171719595205622468501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184726895626126940829958001 138545171719595205622468501)
            ·
              refine ⟨6494304924356025263553211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138545171719595205622468501 6494304924356025263553211)
              ·
                refine ⟨9741457386534037895329817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494304924356025263553211 9741457386534037895329817)
                ·
                  refine ⟨7306093039900528421497363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9741457386534037895329817 7306093039900528421497363)
                  ·
                    refine ⟨10959139559850792632246045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7306093039900528421497363 10959139559850792632246045)
                    ·
                      refine ⟨4109677334944047237092267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10959139559850792632246045 4109677334944047237092267)
                      ·
                        rfl

theorem cell23_8003568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 1, 3].length) (baseStart_8003568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003568 prefixEnd_8003568 := by exact prefixLift 8003568
  have htrace : WordTrace (prefixWord ++ tailWord_8003568) baseStart_8003568 baseEnd_8003568 := by
    simpa [prefixWord, tailWord_8003568, baseEnd_8003568] using wordTrace_append hprefix tailTrace_8003568
  have hstable : (prefixWord ++ tailWord_8003568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003568).length < 2 ^ (prefixWord ++ tailWord_8003568).sum := by decide
  have hdescent : baseEnd_8003568 < baseStart_8003568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003591 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_8003591 : Nat := 118140960795 + 8003591 * 2 ^ 59
def prefixEnd_8003591 : Nat := 4983230072969 + 3 ^ 40 * 8003591 * 2
def baseEnd_8003591 : Nat := 4109689144999100647104661

theorem tailTrace_8003591 : CollatzResearch.WordTrace tailWord_8003591 prefixEnd_8003591 4109689144999100647104661 := by
  unfold tailWord_8003591
  simp only [CollatzResearch.WordTrace]
  refine ⟨291914945547364186363082627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194609963698242790908721751 291914945547364186363082627)
  ·
    refine ⟨437872418321046279544623941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291914945547364186363082627 437872418321046279544623941)
    ·
      refine ⟨82101078435196177414616989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437872418321046279544623941 82101078435196177414616989)
      ·
        refine ⟨30787904413198566530481371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82101078435196177414616989 30787904413198566530481371)
        ·
          refine ⟨46181856619797849795722057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30787904413198566530481371 46181856619797849795722057)
          ·
            refine ⟨34636392464848387346791543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46181856619797849795722057 34636392464848387346791543)
            ·
              refine ⟨51954588697272581020187315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34636392464848387346791543 51954588697272581020187315)
              ·
                refine ⟨77931883045908871530280973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51954588697272581020187315 77931883045908871530280973)
                ·
                  refine ⟨29224456142215826823855365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77931883045908871530280973 29224456142215826823855365)
                  ·
                    refine ⟨5479585526665467529472881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29224456142215826823855365 5479585526665467529472881)
                    ·
                      refine ⟨4109689144999100647104661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479585526665467529472881 4109689144999100647104661)
                      ·
                        rfl

theorem cell23_8003591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_8003591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003591 prefixEnd_8003591 := by exact prefixLift 8003591
  have htrace : WordTrace (prefixWord ++ tailWord_8003591) baseStart_8003591 baseEnd_8003591 := by
    simpa [prefixWord, tailWord_8003591, baseEnd_8003591] using wordTrace_append hprefix tailTrace_8003591
  have hstable : (prefixWord ++ tailWord_8003591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003591).length < 2 ^ (prefixWord ++ tailWord_8003591).sum := by decide
  have hdescent : baseEnd_8003591 < baseStart_8003591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003644 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_8003644 : Nat := 118140960795 + 8003644 * 2 ^ 59
def prefixEnd_8003644 : Nat := 4983230072969 + 3 ^ 40 * 8003644 * 2
def baseEnd_8003644 : Nat := 1369905453157929646580639

theorem tailTrace_8003644 : CollatzResearch.WordTrace tailWord_8003644 prefixEnd_8003644 1369905453157929646580639 := by
  unfold tailWord_8003644
  simp only [CollatzResearch.WordTrace]
  refine ⟨145958439308086088207380993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194611252410781450943174657 145958439308086088207380993)
  ·
    refine ⟨109468829481064566155535745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145958439308086088207380993 109468829481064566155535745)
    ·
      refine ⟨82101622110798424616651809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109468829481064566155535745 82101622110798424616651809)
      ·
        refine ⟨61576216583098818462488857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82101622110798424616651809 61576216583098818462488857)
        ·
          refine ⟨46182162437324113846866643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61576216583098818462488857 46182162437324113846866643)
          ·
            refine ⟨69273243655986170770299965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46182162437324113846866643 69273243655986170770299965)
            ·
              refine ⟨25977466370994814038862487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69273243655986170770299965 25977466370994814038862487)
              ·
                refine ⟨38966199556492221058293731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25977466370994814038862487 38966199556492221058293731)
                ·
                  refine ⟨58449299334738331587440597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38966199556492221058293731 58449299334738331587440597)
                  ·
                    refine ⟨1369905453157929646580639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58449299334738331587440597 1369905453157929646580639)
                    ·
                      rfl

theorem cell23_8003644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_8003644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003644 prefixEnd_8003644 := by exact prefixLift 8003644
  have htrace : WordTrace (prefixWord ++ tailWord_8003644) baseStart_8003644 baseEnd_8003644 := by
    simpa [prefixWord, tailWord_8003644, baseEnd_8003644] using wordTrace_append hprefix tailTrace_8003644
  have hstable : (prefixWord ++ tailWord_8003644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003644).length < 2 ^ (prefixWord ++ tailWord_8003644).sum := by decide
  have hdescent : baseEnd_8003644 < baseStart_8003644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003661 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_8003661 : Nat := 118140960795 + 8003661 * 2 ^ 59
def prefixEnd_8003661 : Nat := 4983230072969 + 3 ^ 40 * 8003661 * 2
def baseEnd_8003661 : Nat := 1369908362881638457743113

theorem tailTrace_8003661 : CollatzResearch.WordTrace tailWord_8003661 prefixEnd_8003661 1369908362881638457743113 := by
  unfold tailWord_8003661
  simp only [CollatzResearch.WordTrace]
  refine ⟨291917498657110588318130837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194611665771407058878753891 291917498657110588318130837)
  ·
    refine ⟨13683632749552058827412383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 291917498657110588318130837 13683632749552058827412383)
    ·
      refine ⟨20525449124328088241118575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13683632749552058827412383 20525449124328088241118575)
      ·
        refine ⟨30788173686492132361677863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20525449124328088241118575 30788173686492132361677863)
        ·
          refine ⟨46182260529738198542516795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30788173686492132361677863 46182260529738198542516795)
          ·
            refine ⟨69273390794607297813775193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46182260529738198542516795 69273390794607297813775193)
            ·
              refine ⟨51955043095955473360331395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69273390794607297813775193 51955043095955473360331395)
              ·
                refine ⟨77932564643933210040497093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51955043095955473360331395 77932564643933210040497093)
                ·
                  refine ⟨14612355870737476882593205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77932564643933210040497093 14612355870737476882593205)
                  ·
                    refine ⟨1369908362881638457743113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14612355870737476882593205 1369908362881638457743113)
                    ·
                      rfl

theorem cell23_8003661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_8003661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003661 prefixEnd_8003661 := by exact prefixLift 8003661
  have htrace : WordTrace (prefixWord ++ tailWord_8003661) baseStart_8003661 baseEnd_8003661 := by
    simpa [prefixWord, tailWord_8003661, baseEnd_8003661] using wordTrace_append hprefix tailTrace_8003661
  have hstable : (prefixWord ++ tailWord_8003661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003661).length < 2 ^ (prefixWord ++ tailWord_8003661).sum := by decide
  have hdescent : baseEnd_8003661 < baseStart_8003661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003738 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 6]
def baseStart_8003738 : Nat := 118140960795 + 8003738 * 2 ^ 59
def prefixEnd_8003738 : Nat := 4983230072969 + 3 ^ 40 * 8003738 * 2
def baseEnd_8003738 : Nat := 456640514072812396885165

theorem tailTrace_8003738 : CollatzResearch.WordTrace tailWord_8003738 prefixEnd_8003738 456640514072812396885165 := by
  unfold tailWord_8003738
  simp only [CollatzResearch.WordTrace]
  refine ⟨72980076769457907617170967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194613538051887753645789245 72980076769457907617170967)
  ·
    refine ⟨109470115154186861425756451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72980076769457907617170967 109470115154186861425756451)
    ·
      refine ⟨164205172731280292138634677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109470115154186861425756451 164205172731280292138634677)
      ·
        refine ⟨15394234943557527387997001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164205172731280292138634677 15394234943557527387997001)
        ·
          refine ⟨11545676207668145540997751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15394234943557527387997001 11545676207668145540997751)
          ·
            refine ⟨17318514311502218311496627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11545676207668145540997751 17318514311502218311496627)
            ·
              refine ⟨25977771467253327467244941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17318514311502218311496627 25977771467253327467244941)
              ·
                refine ⟨9741664300219997800216853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25977771467253327467244941 9741664300219997800216853)
                ·
                  refine ⟨456640514072812396885165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9741664300219997800216853 456640514072812396885165)
                  ·
                    rfl

theorem cell23_8003738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_8003738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003738 prefixEnd_8003738 := by exact prefixLift 8003738
  have htrace : WordTrace (prefixWord ++ tailWord_8003738) baseStart_8003738 baseEnd_8003738 := by
    simpa [prefixWord, tailWord_8003738, baseEnd_8003738] using wordTrace_append hprefix tailTrace_8003738
  have hstable : (prefixWord ++ tailWord_8003738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003738).length < 2 ^ (prefixWord ++ tailWord_8003738).sum := by decide
  have hdescent : baseEnd_8003738 < baseStart_8003738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003768 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 1, 5]
def baseStart_8003768 : Nat := 118140960795 + 8003768 * 2 ^ 59
def prefixEnd_8003768 : Nat := 4983230072969 + 3 ^ 40 * 8003768 * 2
def baseEnd_8003768 : Nat := 1369926677024982151530449

theorem tailTrace_8003768 : CollatzResearch.WordTrace tailWord_8003768 prefixEnd_8003768 1369926677024982151530449 := by
  unfold tailWord_8003768
  simp only [CollatzResearch.WordTrace]
  refine ⟨145960700633861472796137979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194614267511815297061517305 145960700633861472796137979)
  ·
    refine ⟨218941050950792209194206969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145960700633861472796137979 218941050950792209194206969)
    ·
      refine ⟨164205788213094156895655227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218941050950792209194206969 164205788213094156895655227)
      ·
        refine ⟨246308682319641235343482841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164205788213094156895655227 246308682319641235343482841)
        ·
          refine ⟨184731511739730926507612131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246308682319641235343482841 184731511739730926507612131)
          ·
            refine ⟨277097267609596389761418197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184731511739730926507612131 277097267609596389761418197)
            ·
              refine ⟨6494467209599915385033239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 277097267609596389761418197 6494467209599915385033239)
              ·
                refine ⟨9741700814399873077549859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494467209599915385033239 9741700814399873077549859)
                ·
                  refine ⟨14612551221599809616324789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9741700814399873077549859 14612551221599809616324789)
                  ·
                    refine ⟨1369926677024982151530449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14612551221599809616324789 1369926677024982151530449)
                    ·
                      rfl

theorem cell23_8003768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_8003768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003768 prefixEnd_8003768 := by exact prefixLift 8003768
  have htrace : WordTrace (prefixWord ++ tailWord_8003768) baseStart_8003768 baseEnd_8003768 := by
    simpa [prefixWord, tailWord_8003768, baseEnd_8003768] using wordTrace_append hprefix tailTrace_8003768
  have hstable : (prefixWord ++ tailWord_8003768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003768).length < 2 ^ (prefixWord ++ tailWord_8003768).sum := by decide
  have hdescent : baseEnd_8003768 < baseStart_8003768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003781 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_8003781 : Nat := 118140960795 + 8003781 * 2 ^ 59
def prefixEnd_8003781 : Nat := 4983230072969 + 3 ^ 40 * 8003781 * 2
def baseEnd_8003781 : Nat := 1369928902107818301242929

theorem tailTrace_8003781 : CollatzResearch.WordTrace tailWord_8003781 prefixEnd_8003781 1369928902107818301242929 := by
  unfold tailWord_8003781
  simp only [CollatzResearch.WordTrace]
  refine ⟨291921875416675848812499197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194614583611117232541666131 291921875416675848812499197)
  ·
    refine ⟨109470703281253443304687199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291921875416675848812499197 109470703281253443304687199)
    ·
      refine ⟨164206054921880164957030799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109470703281253443304687199 164206054921880164957030799)
      ·
        refine ⟨246309082382820247435546199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164206054921880164957030799 246309082382820247435546199)
        ·
          refine ⟨369463623574230371153319299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246309082382820247435546199 369463623574230371153319299)
          ·
            refine ⟨554195435361345556729978949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369463623574230371153319299 554195435361345556729978949)
            ·
              refine ⟨103911644130252291886871053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 554195435361345556729978949 103911644130252291886871053)
              ·
                refine ⟨38966866548844609457576645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103911644130252291886871053 38966866548844609457576645)
                ·
                  refine ⟨7306287477908364273295621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38966866548844609457576645 7306287477908364273295621)
                  ·
                    refine ⟨1369928902107818301242929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7306287477908364273295621 1369928902107818301242929)
                    ·
                      rfl

theorem cell23_8003781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_8003781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003781 prefixEnd_8003781 := by exact prefixLift 8003781
  have htrace : WordTrace (prefixWord ++ tailWord_8003781) baseStart_8003781 baseEnd_8003781 := by
    simpa [prefixWord, tailWord_8003781, baseEnd_8003781] using wordTrace_append hprefix tailTrace_8003781
  have hstable : (prefixWord ++ tailWord_8003781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003781).length < 2 ^ (prefixWord ++ tailWord_8003781).sum := by decide
  have hdescent : baseEnd_8003781 < baseStart_8003781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003791 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 3]
def baseStart_8003791 : Nat := 118140960795 + 8003791 * 2 ^ 59
def prefixEnd_8003791 : Nat := 4983230072969 + 3 ^ 40 * 8003791 * 2
def baseEnd_8003791 : Nat := 4109791841129999864603741

theorem tailTrace_8003791 : CollatzResearch.WordTrace tailWord_8003791 prefixEnd_8003791 4109791841129999864603741 := by
  unfold tailWord_8003791
  simp only [CollatzResearch.WordTrace]
  refine ⟨291922240146639620520363227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194614826764426413680242151 291922240146639620520363227)
  ·
    refine ⟨437883360219959430780544841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291922240146639620520363227 437883360219959430780544841)
    ·
      refine ⟨328412520164969573085408631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437883360219959430780544841 328412520164969573085408631)
      ·
        refine ⟨492618780247454359628112947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328412520164969573085408631 492618780247454359628112947)
        ·
          refine ⟨738928170371181539442169421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492618780247454359628112947 738928170371181539442169421)
          ·
            refine ⟨277098063889193077290813533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 738928170371181539442169421 277098063889193077290813533)
            ·
              refine ⟨103911773958447403984055075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277098063889193077290813533 103911773958447403984055075)
              ·
                refine ⟨155867660937671105976082613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103911773958447403984055075 155867660937671105976082613)
                ·
                  refine ⟨14612593212906666185257745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155867660937671105976082613 14612593212906666185257745)
                  ·
                    refine ⟨10959444909679999638943309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14612593212906666185257745 10959444909679999638943309)
                    ·
                      refine ⟨4109791841129999864603741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10959444909679999638943309 4109791841129999864603741)
                      ·
                        rfl

theorem cell23_8003791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_8003791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003791 prefixEnd_8003791 := by exact prefixLift 8003791
  have htrace : WordTrace (prefixWord ++ tailWord_8003791) baseStart_8003791 baseEnd_8003791 := by
    simpa [prefixWord, tailWord_8003791, baseEnd_8003791] using wordTrace_append hprefix tailTrace_8003791
  have hstable : (prefixWord ++ tailWord_8003791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003791).length < 2 ^ (prefixWord ++ tailWord_8003791).sum := by decide
  have hdescent : baseEnd_8003791 < baseStart_8003791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003801 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_8003801 : Nat := 118140960795 + 8003801 * 2 ^ 59
def prefixEnd_8003801 : Nat := 4983230072969 + 3 ^ 40 * 8003801 * 2
def baseEnd_8003801 : Nat := 4109796975936544825478695

theorem tailTrace_8003801 : CollatzResearch.WordTrace tailWord_8003801 prefixEnd_8003801 4109796975936544825478695 := by
  unfold tailWord_8003801
  simp only [CollatzResearch.WordTrace]
  refine ⟨291922604876603392228227257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194615069917735594818818171 291922604876603392228227257)
  ·
    refine ⟨218941953657452544171170443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291922604876603392228227257 218941953657452544171170443)
    ·
      refine ⟨328412930486178816256755665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218941953657452544171170443 328412930486178816256755665)
      ·
        refine ⟨246309697864634112192566749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328412930486178816256755665 246309697864634112192566749)
        ·
          refine ⟨92366136699237792072212531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246309697864634112192566749 92366136699237792072212531)
          ·
            refine ⟨138549205048856688108318797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92366136699237792072212531 138549205048856688108318797)
            ·
              refine ⟨51955951893321258040619549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138549205048856688108318797 51955951893321258040619549)
              ·
                refine ⟨19483481959995471765232331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51955951893321258040619549 19483481959995471765232331)
                ·
                  refine ⟨29225222939993207647848497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19483481959995471765232331 29225222939993207647848497)
                  ·
                    refine ⟨21918917204994905735886373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29225222939993207647848497 21918917204994905735886373)
                    ·
                      refine ⟨4109796975936544825478695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21918917204994905735886373 4109796975936544825478695)
                      ·
                        rfl

theorem cell23_8003801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_8003801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003801 prefixEnd_8003801 := by exact prefixLift 8003801
  have htrace : WordTrace (prefixWord ++ tailWord_8003801) baseStart_8003801 baseEnd_8003801 := by
    simpa [prefixWord, tailWord_8003801, baseEnd_8003801] using wordTrace_append hprefix tailTrace_8003801
  have hstable : (prefixWord ++ tailWord_8003801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003801).length < 2 ^ (prefixWord ++ tailWord_8003801).sum := by decide
  have hdescent : baseEnd_8003801 < baseStart_8003801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003808 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3]
def baseStart_8003808 : Nat := 118140960795 + 8003808 * 2 ^ 59
def prefixEnd_8003808 : Nat := 4983230072969 + 3 ^ 40 * 8003808 * 2
def baseEnd_8003808 : Nat := 4109800570301126298091163

theorem tailTrace_8003808 : CollatzResearch.WordTrace tailWord_8003808 prefixEnd_8003808 4109800570301126298091163 := by
  unfold tailWord_8003808
  simp only [CollatzResearch.WordTrace]
  refine ⟨145961430093789016211866039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194615240125052021615821385 145961430093789016211866039)
  ·
    refine ⟨218942145140683524317799059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145961430093789016211866039 218942145140683524317799059)
    ·
      refine ⟨328413217711025286476698589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218942145140683524317799059 328413217711025286476698589)
      ·
        refine ⟨123154956641634482428761971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328413217711025286476698589 123154956641634482428761971)
        ·
          refine ⟨184732434962451723643142957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123154956641634482428761971 184732434962451723643142957)
          ·
            refine ⟨69274663110919396366178609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184732434962451723643142957 69274663110919396366178609)
            ·
              refine ⟨51955997333189547274633957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69274663110919396366178609 51955997333189547274633957)
              ·
                refine ⟨9741749499973040113993867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51955997333189547274633957 9741749499973040113993867)
                ·
                  refine ⟨14612624249959560170990801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9741749499973040113993867 14612624249959560170990801)
                  ·
                    refine ⟨10959468187469670128243101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14612624249959560170990801 10959468187469670128243101)
                    ·
                      refine ⟨4109800570301126298091163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10959468187469670128243101 4109800570301126298091163)
                      ·
                        rfl

theorem cell23_8003808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_8003808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003808 prefixEnd_8003808 := by exact prefixLift 8003808
  have htrace : WordTrace (prefixWord ++ tailWord_8003808) baseStart_8003808 baseEnd_8003808 := by
    simpa [prefixWord, tailWord_8003808, baseEnd_8003808] using wordTrace_append hprefix tailTrace_8003808
  have hstable : (prefixWord ++ tailWord_8003808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003808).length < 2 ^ (prefixWord ++ tailWord_8003808).sum := by decide
  have hdescent : baseEnd_8003808 < baseStart_8003808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003825 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 1, 2, 3]
def baseStart_8003825 : Nat := 118140960795 + 8003825 * 2 ^ 59
def prefixEnd_8003825 : Nat := 4983230072969 + 3 ^ 40 * 8003825 * 2
def baseEnd_8003825 : Nat := 4109809299472252731578585

theorem tailTrace_8003825 : CollatzResearch.WordTrace tailWord_8003825 prefixEnd_8003825 4109809299472252731578585 := by
  unfold tailWord_8003825
  simp only [CollatzResearch.WordTrace]
  refine ⟨291923480228516444327100929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194615653485677629551400619 291923480228516444327100929)
  ·
    refine ⟨218942610171387333245325697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291923480228516444327100929 218942610171387333245325697)
    ·
      refine ⟨164206957628540499933994273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218942610171387333245325697 164206957628540499933994273)
      ·
        refine ⟨123155218221405374950495705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164206957628540499933994273 123155218221405374950495705)
        ·
          refine ⟨92366413666054031212871779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123155218221405374950495705 92366413666054031212871779)
          ·
            refine ⟨138549620499081046819307669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92366413666054031212871779 138549620499081046819307669)
            ·
              refine ⟨6494513460894424069655047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138549620499081046819307669 6494513460894424069655047)
              ·
                refine ⟨9741770191341636104482571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6494513460894424069655047 9741770191341636104482571)
                ·
                  refine ⟨14612655287012454156723857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9741770191341636104482571 14612655287012454156723857)
                  ·
                    refine ⟨10959491465259340617542893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14612655287012454156723857 10959491465259340617542893)
                    ·
                      refine ⟨4109809299472252731578585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10959491465259340617542893 4109809299472252731578585)
                      ·
                        rfl

theorem cell23_8003825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_8003825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003825 prefixEnd_8003825 := by exact prefixLift 8003825
  have htrace : WordTrace (prefixWord ++ tailWord_8003825) baseStart_8003825 baseEnd_8003825 := by
    simpa [prefixWord, tailWord_8003825, baseEnd_8003825] using wordTrace_append hprefix tailTrace_8003825
  have hstable : (prefixWord ++ tailWord_8003825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003825).length < 2 ^ (prefixWord ++ tailWord_8003825).sum := by decide
  have hdescent : baseEnd_8003825 < baseStart_8003825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003861 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_8003861 : Nat := 118140960795 + 8003861 * 2 ^ 59
def prefixEnd_8003861 : Nat := 4983230072969 + 3 ^ 40 * 8003861 * 2
def baseEnd_8003861 : Nat := 4109827784775814590728419

theorem tailTrace_8003861 : CollatzResearch.WordTrace tailWord_8003861 prefixEnd_8003861 4109827784775814590728419 := by
  unfold tailWord_8003861
  simp only [CollatzResearch.WordTrace]
  refine ⟨291924793256386022475411437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194616528837590681650274291 291924793256386022475411437)
  ·
    refine ⟨109471797471144758428279289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291924793256386022475411437 109471797471144758428279289)
    ·
      refine ⟨82103848103358568821209467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109471797471144758428279289 82103848103358568821209467)
      ·
        refine ⟨123155772155037853231814201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82103848103358568821209467 123155772155037853231814201)
        ·
          refine ⟨92366829116278389923860651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123155772155037853231814201 92366829116278389923860651)
          ·
            refine ⟨138550243674417584885790977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92366829116278389923860651 138550243674417584885790977)
            ·
              refine ⟨103912682755813188664343233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138550243674417584885790977 103912682755813188664343233)
              ·
                refine ⟨77934512066859891498257425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103912682755813188664343233 77934512066859891498257425)
                ·
                  refine ⟨58450884050144918623693069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77934512066859891498257425 58450884050144918623693069)
                  ·
                    refine ⟨21919081518804344483884901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58450884050144918623693069 21919081518804344483884901)
                    ·
                      refine ⟨4109827784775814590728419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21919081518804344483884901 4109827784775814590728419)
                      ·
                        rfl

theorem cell23_8003861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_8003861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003861 prefixEnd_8003861 := by exact prefixLift 8003861
  have htrace : WordTrace (prefixWord ++ tailWord_8003861) baseStart_8003861 baseEnd_8003861 := by
    simpa [prefixWord, tailWord_8003861, baseEnd_8003861] using wordTrace_append hprefix tailTrace_8003861
  have hstable : (prefixWord ++ tailWord_8003861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003861).length < 2 ^ (prefixWord ++ tailWord_8003861).sum := by decide
  have hdescent : baseEnd_8003861 < baseStart_8003861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003952 : List Nat := [2, 1, 1, 1, 4, 5, 2, 2, 5]
def baseStart_8003952 : Nat := 118140960795 + 8003952 * 2 ^ 59
def prefixEnd_8003952 : Nat := 4983230072969 + 3 ^ 40 * 8003952 * 2
def baseEnd_8003952 : Nat := 456652723501708192743389

theorem tailTrace_8003952 : CollatzResearch.WordTrace tailWord_8003952 prefixEnd_8003952 456652723501708192743389 := by
  unfold tailWord_8003952
  simp only [CollatzResearch.WordTrace]
  refine ⟨145964056149528172508487055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194618741532704230011316073 145964056149528172508487055)
  ·
    refine ⟨218946084224292258762730583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145964056149528172508487055 218946084224292258762730583)
    ·
      refine ⟨328419126336438388144095875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218946084224292258762730583 328419126336438388144095875)
      ·
        refine ⟨492628689504657582216143813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328419126336438388144095875 492628689504657582216143813)
        ·
          refine ⟨92367879282123296665526965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 492628689504657582216143813 92367879282123296665526965)
          ·
            refine ⟨8659488682699059062393153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92367879282123296665526965 8659488682699059062393153)
            ·
              refine ⟨6494616512024294296794865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8659488682699059062393153 6494616512024294296794865)
              ·
                refine ⟨4870962384018220722596149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6494616512024294296794865 4870962384018220722596149)
                ·
                  refine ⟨456652723501708192743389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4870962384018220722596149 456652723501708192743389)
                  ·
                    rfl

theorem cell23_8003952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 5].length) (baseStart_8003952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003952 prefixEnd_8003952 := by exact prefixLift 8003952
  have htrace : WordTrace (prefixWord ++ tailWord_8003952) baseStart_8003952 baseEnd_8003952 := by
    simpa [prefixWord, tailWord_8003952, baseEnd_8003952] using wordTrace_append hprefix tailTrace_8003952
  have hstable : (prefixWord ++ tailWord_8003952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003952).length < 2 ^ (prefixWord ++ tailWord_8003952).sum := by decide
  have hdescent : baseEnd_8003952 < baseStart_8003952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003961 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 2, 8]
def baseStart_8003961 : Nat := 118140960795 + 8003961 * 2 ^ 59
def prefixEnd_8003961 : Nat := 4983230072969 + 3 ^ 40 * 8003961 * 2
def baseEnd_8003961 : Nat := 1369959710947088066492653

theorem tailTrace_8003961 : CollatzResearch.WordTrace tailWord_8003961 prefixEnd_8003961 1369959710947088066492653 := by
  unfold tailWord_8003961
  simp only [CollatzResearch.WordTrace]
  refine ⟨291928440556023739554051737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194618960370682493036034491 291928440556023739554051737)
  ·
    refine ⟨218946330417017804665538803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291928440556023739554051737 218946330417017804665538803)
    ·
      refine ⟨328419495625526706998308205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218946330417017804665538803 328419495625526706998308205)
      ·
        refine ⟨123157310859572515124365577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328419495625526706998308205 123157310859572515124365577)
        ·
          refine ⟨92367983144679386343274183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123157310859572515124365577 92367983144679386343274183)
          ·
            refine ⟨138551974717019079514911275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92367983144679386343274183 138551974717019079514911275)
            ·
              refine ⟨207827962075528619272366913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138551974717019079514911275 207827962075528619272366913)
              ·
                refine ⟨155870971556646464454275185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207827962075528619272366913 155870971556646464454275185)
                ·
                  refine ⟨116903228667484848340706389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155870971556646464454275185 116903228667484848340706389)
                  ·
                    refine ⟨1369959710947088066492653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116903228667484848340706389 1369959710947088066492653)
                    ·
                      rfl

theorem cell23_8003961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_8003961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003961 prefixEnd_8003961 := by exact prefixLift 8003961
  have htrace : WordTrace (prefixWord ++ tailWord_8003961) baseStart_8003961 baseEnd_8003961 := by
    simpa [prefixWord, tailWord_8003961, baseEnd_8003961] using wordTrace_append hprefix tailTrace_8003961
  have hstable : (prefixWord ++ tailWord_8003961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003961).length < 2 ^ (prefixWord ++ tailWord_8003961).sum := by decide
  have hdescent : baseEnd_8003961 < baseStart_8003961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8003982 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_8003982 : Nat := 118140960795 + 8003982 * 2 ^ 59
def prefixEnd_8003982 : Nat := 4983230072969 + 3 ^ 40 * 8003982 * 2
def baseEnd_8003982 : Nat := 1369963305311669539105121

theorem tailTrace_8003982 : CollatzResearch.WordTrace tailWord_8003982 prefixEnd_8003982 1369963305311669539105121 := by
  unfold tailWord_8003982
  simp only [CollatzResearch.WordTrace]
  refine ⟨36491150811118457517570775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194619470992631773427044133 36491150811118457517570775)
  ·
    refine ⟨54736726216677686276356163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36491150811118457517570775 54736726216677686276356163)
    ·
      refine ⟨82105089325016529414534245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54736726216677686276356163 82105089325016529414534245)
      ·
        refine ⟨15394704248440599265225171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82105089325016529414534245 15394704248440599265225171)
        ·
          refine ⟨23092056372660898897837757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15394704248440599265225171 23092056372660898897837757)
          ·
            refine ⟨8659521139747837086689159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23092056372660898897837757 8659521139747837086689159)
            ·
              refine ⟨12989281709621755630033739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8659521139747837086689159 12989281709621755630033739)
              ·
                refine ⟨19483922564432633445050609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12989281709621755630033739 19483922564432633445050609)
                ·
                  refine ⟨14612941923324475083787957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19483922564432633445050609 14612941923324475083787957)
                  ·
                    refine ⟨1369963305311669539105121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14612941923324475083787957 1369963305311669539105121)
                    ·
                      rfl

theorem cell23_8003982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_8003982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8003982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8003982 prefixEnd_8003982 := by exact prefixLift 8003982
  have htrace : WordTrace (prefixWord ++ tailWord_8003982) baseStart_8003982 baseEnd_8003982 := by
    simpa [prefixWord, tailWord_8003982, baseEnd_8003982] using wordTrace_append hprefix tailTrace_8003982
  have hstable : (prefixWord ++ tailWord_8003982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8003982).length < 2 ^ (prefixWord ++ tailWord_8003982).sum := by decide
  have hdescent : baseEnd_8003982 < baseStart_8003982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8003982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004088 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_8004088 : Nat := 118140960795 + 8004088 * 2 ^ 59
def prefixEnd_8004088 : Nat := 4983230072969 + 3 ^ 40 * 8004088 * 2
def baseEnd_8004088 : Nat := 4109944344884385202589875

theorem tailTrace_8004088 : CollatzResearch.WordTrace tailWord_8004088 prefixEnd_8004088 4109944344884385202589875 := by
  unfold tailWord_8004088
  simp only [CollatzResearch.WordTrace]
  refine ⟨145966536313281820121962459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194622048417709093495949945 145966536313281820121962459)
  ·
    refine ⟨218949804469922730182943689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145966536313281820121962459 218949804469922730182943689)
    ·
      refine ⟨164212353352442047637207767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218949804469922730182943689 164212353352442047637207767)
      ·
        refine ⟨246318530028663071455811651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164212353352442047637207767 246318530028663071455811651)
        ·
          refine ⟨369477795042994607183717477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246318530028663071455811651 369477795042994607183717477)
          ·
            refine ⟨69277086570561488846947027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369477795042994607183717477 69277086570561488846947027)
            ·
              refine ⟨103915629855842233270420541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69277086570561488846947027 103915629855842233270420541)
              ·
                refine ⟨38968361195940837476407703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103915629855842233270420541 38968361195940837476407703)
                ·
                  refine ⟨58452541793911256214611555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38968361195940837476407703 58452541793911256214611555)
                  ·
                    refine ⟨87678812690866884321917333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58452541793911256214611555 87678812690866884321917333)
                    ·
                      refine ⟨4109944344884385202589875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87678812690866884321917333 4109944344884385202589875)
                      ·
                        rfl

theorem cell23_8004088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_8004088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004088 prefixEnd_8004088 := by exact prefixLift 8004088
  have htrace : WordTrace (prefixWord ++ tailWord_8004088) baseStart_8004088 baseEnd_8004088 := by
    simpa [prefixWord, tailWord_8004088, baseEnd_8004088] using wordTrace_append hprefix tailTrace_8004088
  have hstable : (prefixWord ++ tailWord_8004088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004088).length < 2 ^ (prefixWord ++ tailWord_8004088).sum := by decide
  have hdescent : baseEnd_8004088 < baseStart_8004088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004092 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_8004092 : Nat := 118140960795 + 8004092 * 2 ^ 59
def prefixEnd_8004092 : Nat := 4983230072969 + 3 ^ 40 * 8004092 * 2
def baseEnd_8004092 : Nat := 4109946398807003186939857

theorem tailTrace_8004092 : CollatzResearch.WordTrace tailWord_8004092 prefixEnd_8004092 4109946398807003186939857 := by
  unfold tailWord_8004092
  simp only [CollatzResearch.WordTrace]
  refine ⟨145966609259274574463535265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194622145679032765951380353 145966609259274574463535265)
  ·
    refine ⟨109474956944455930847651449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145966609259274574463535265 109474956944455930847651449)
    ·
      refine ⟨82106217708341948135738587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109474956944455930847651449 82106217708341948135738587)
      ·
        refine ⟨123159326562512922203607881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82106217708341948135738587 123159326562512922203607881)
        ·
          refine ⟨92369494921884691652705911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123159326562512922203607881 92369494921884691652705911)
          ·
            refine ⟨138554242382827037479058867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92369494921884691652705911 138554242382827037479058867)
            ·
              refine ⟨207831363574240556218588301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138554242382827037479058867 207831363574240556218588301)
              ·
                refine ⟨77936761340340208581970613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207831363574240556218588301 77936761340340208581970613)
                ·
                  refine ⟨7306571375656894554559745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77936761340340208581970613 7306571375656894554559745)
                  ·
                    refine ⟨5479928531742670915919809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7306571375656894554559745 5479928531742670915919809)
                    ·
                      refine ⟨4109946398807003186939857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479928531742670915919809 4109946398807003186939857)
                      ·
                        rfl

theorem cell23_8004092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_8004092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004092 prefixEnd_8004092 := by exact prefixLift 8004092
  have htrace : WordTrace (prefixWord ++ tailWord_8004092) baseStart_8004092 baseEnd_8004092 := by
    simpa [prefixWord, tailWord_8004092, baseEnd_8004092] using wordTrace_append hprefix tailTrace_8004092
  have hstable : (prefixWord ++ tailWord_8004092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004092).length < 2 ^ (prefixWord ++ tailWord_8004092).sum := by decide
  have hdescent : baseEnd_8004092 < baseStart_8004092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004095 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 3]
def baseStart_8004095 : Nat := 118140960795 + 8004095 * 2 ^ 59
def prefixEnd_8004095 : Nat := 4983230072969 + 3 ^ 40 * 8004095 * 2
def baseEnd_8004095 : Nat := 4109947939248966675202343

theorem tailTrace_8004095 : CollatzResearch.WordTrace tailWord_8004095 prefixEnd_8004095 4109947939248966675202343 := by
  unfold tailWord_8004095
  simp only [CollatzResearch.WordTrace]
  refine ⟨291933327937538280439429739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194622218625025520292953159 291933327937538280439429739)
  ·
    refine ⟨437899991906307420659144609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291933327937538280439429739 437899991906307420659144609)
    ·
      refine ⟨328424993929730565494358457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437899991906307420659144609 328424993929730565494358457)
      ·
        refine ⟨246318745447297924120768843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328424993929730565494358457 246318745447297924120768843)
        ·
          refine ⟨369478118170946886181153265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246318745447297924120768843 369478118170946886181153265)
          ·
            refine ⟨277108588628210164635864949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369478118170946886181153265 277108588628210164635864949)
            ·
              refine ⟨25978930183894702934612339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277108588628210164635864949 25978930183894702934612339)
              ·
                refine ⟨38968395275842054401918509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25978930183894702934612339 38968395275842054401918509)
                ·
                  refine ⟨14613148228440770400719441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38968395275842054401918509 14613148228440770400719441)
                  ·
                    refine ⟨10959861171330577800539581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14613148228440770400719441 10959861171330577800539581)
                    ·
                      refine ⟨4109947939248966675202343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10959861171330577800539581 4109947939248966675202343)
                      ·
                        rfl

theorem cell23_8004095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_8004095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004095 prefixEnd_8004095 := by exact prefixLift 8004095
  have htrace : WordTrace (prefixWord ++ tailWord_8004095) baseStart_8004095 baseEnd_8004095 := by
    simpa [prefixWord, tailWord_8004095, baseEnd_8004095] using wordTrace_append hprefix tailTrace_8004095
  have hstable : (prefixWord ++ tailWord_8004095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004095).length < 2 ^ (prefixWord ++ tailWord_8004095).sum := by decide
  have hdescent : baseEnd_8004095 < baseStart_8004095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004152 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 3, 3, 2]
def baseStart_8004152 : Nat := 118140960795 + 8004152 * 2 ^ 59
def prefixEnd_8004152 : Nat := 4983230072969 + 3 ^ 40 * 8004152 * 2
def baseEnd_8004152 : Nat := 4109977207646272952189581

theorem tailTrace_8004152 : CollatzResearch.WordTrace tailWord_8004152 prefixEnd_8004152 4109977207646272952189581 := by
  unfold tailWord_8004152
  simp only [CollatzResearch.WordTrace]
  refine ⟨145967703449165889587127355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194623604598887852782836473 145967703449165889587127355)
  ·
    refine ⟨218951555173748834380691033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145967703449165889587127355 218951555173748834380691033)
    ·
      refine ⟨164213666380311625785518275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218951555173748834380691033 164213666380311625785518275)
      ·
        refine ⟨246320499570467438678277413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164213666380311625785518275 246320499570467438678277413)
        ·
          refine ⟨46185093669462644752177015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246320499570467438678277413 46185093669462644752177015)
          ·
            refine ⟨69277640504193967128265523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46185093669462644752177015 69277640504193967128265523)
            ·
              refine ⟨103916460756290950692398285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69277640504193967128265523 103916460756290950692398285)
              ·
                refine ⟨38968672783609106509649357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103916460756290950692398285 38968672783609106509649357)
                ·
                  refine ⟨14613252293853414941118509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38968672783609106509649357 14613252293853414941118509)
                  ·
                    refine ⟨5479969610195030602919441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14613252293853414941118509 5479969610195030602919441)
                    ·
                      refine ⟨4109977207646272952189581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5479969610195030602919441 4109977207646272952189581)
                      ·
                        rfl

theorem cell23_8004152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_8004152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004152 prefixEnd_8004152 := by exact prefixLift 8004152
  have htrace : WordTrace (prefixWord ++ tailWord_8004152) baseStart_8004152 baseEnd_8004152 := by
    simpa [prefixWord, tailWord_8004152, baseEnd_8004152] using wordTrace_append hprefix tailTrace_8004152
  have hstable : (prefixWord ++ tailWord_8004152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004152).length < 2 ^ (prefixWord ++ tailWord_8004152).sum := by decide
  have hdescent : baseEnd_8004152 < baseStart_8004152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004190 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_8004190 : Nat := 118140960795 + 8004190 * 2 ^ 59
def prefixEnd_8004190 : Nat := 4983230072969 + 3 ^ 40 * 8004190 * 2
def baseEnd_8004190 : Nat := 4109996719911143803514407

theorem tailTrace_8004190 : CollatzResearch.WordTrace tailWord_8004190 prefixEnd_8004190 4109996719911143803514407 := by
  unfold tailWord_8004190
  simp only [CollatzResearch.WordTrace]
  refine ⟨36492099109024263958017253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194624528581462741109425349 36492099109024263958017253)
  ·
    refine ⟨6842268582942049492128235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36492099109024263958017253 6842268582942049492128235)
    ·
      refine ⟨10263402874413074238192353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6842268582942049492128235 10263402874413074238192353)
      ·
        refine ⟨7697552155809805678644265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10263402874413074238192353 7697552155809805678644265)
        ·
          refine ⟨5773164116857354258983199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697552155809805678644265 5773164116857354258983199)
          ·
            refine ⟨8659746175286031388474799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773164116857354258983199 8659746175286031388474799)
            ·
              refine ⟨12989619262929047082712199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8659746175286031388474799 12989619262929047082712199)
              ·
                refine ⟨19484428894393570624068299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12989619262929047082712199 19484428894393570624068299)
                ·
                  refine ⟨29226643341590355936102449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19484428894393570624068299 29226643341590355936102449)
                  ·
                    refine ⟨21919982506192766952076837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29226643341590355936102449 21919982506192766952076837)
                    ·
                      refine ⟨4109996719911143803514407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21919982506192766952076837 4109996719911143803514407)
                      ·
                        rfl

theorem cell23_8004190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_8004190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004190 prefixEnd_8004190 := by exact prefixLift 8004190
  have htrace : WordTrace (prefixWord ++ tailWord_8004190) baseStart_8004190 baseEnd_8004190 := by
    simpa [prefixWord, tailWord_8004190, baseEnd_8004190] using wordTrace_append hprefix tailTrace_8004190
  have hstable : (prefixWord ++ tailWord_8004190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004190).length < 2 ^ (prefixWord ++ tailWord_8004190).sum := by decide
  have hdescent : baseEnd_8004190 < baseStart_8004190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004195 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4]
def baseStart_8004195 : Nat := 118140960795 + 8004195 * 2 ^ 59
def prefixEnd_8004195 : Nat := 4983230072969 + 3 ^ 40 * 8004195 * 2
def baseEnd_8004195 : Nat := 4109999287314416283951883

theorem tailTrace_8004195 : CollatzResearch.WordTrace tailWord_8004195 prefixEnd_8004195 4109999287314416283951883 := by
  unfold tailWord_8004195
  simp only [CollatzResearch.WordTrace]
  refine ⟨291936975237175997518070039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194624650158117331678713359 291936975237175997518070039)
  ·
    refine ⟨437905462855763996277105059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291936975237175997518070039 437905462855763996277105059)
    ·
      refine ⟨656858194283645994415657589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437905462855763996277105059 656858194283645994415657589)
      ·
        refine ⟨61580455714091811976467899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656858194283645994415657589 61580455714091811976467899)
        ·
          refine ⟨92370683571137717964701849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61580455714091811976467899 92370683571137717964701849)
          ·
            refine ⟨69278012678353288473526387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92370683571137717964701849 69278012678353288473526387)
            ·
              refine ⟨103917019017529932710289581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69278012678353288473526387 103917019017529932710289581)
              ·
                refine ⟨38968882131573724766358593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103917019017529932710289581 38968882131573724766358593)
                ·
                  refine ⟨29226661598680293574768945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38968882131573724766358593 29226661598680293574768945)
                  ·
                    refine ⟨21919996199010220181076709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29226661598680293574768945 21919996199010220181076709)
                    ·
                      refine ⟨4109999287314416283951883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21919996199010220181076709 4109999287314416283951883)
                      ·
                        rfl

theorem cell23_8004195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_8004195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004195 prefixEnd_8004195 := by exact prefixLift 8004195
  have htrace : WordTrace (prefixWord ++ tailWord_8004195) baseStart_8004195 baseEnd_8004195 := by
    simpa [prefixWord, tailWord_8004195, baseEnd_8004195] using wordTrace_append hprefix tailTrace_8004195
  have hstable : (prefixWord ++ tailWord_8004195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004195).length < 2 ^ (prefixWord ++ tailWord_8004195).sum := by decide
  have hdescent : baseEnd_8004195 < baseStart_8004195 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004215 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_8004215 : Nat := 118140960795 + 8004215 * 2 ^ 59
def prefixEnd_8004215 : Nat := 4983230072969 + 3 ^ 40 * 8004215 * 2
def baseEnd_8004215 : Nat := 4110009556927506205701791

theorem tailTrace_8004215 : CollatzResearch.WordTrace tailWord_8004215 prefixEnd_8004215 4110009556927506205701791 := by
  unfold tailWord_8004215
  simp only [CollatzResearch.WordTrace]
  refine ⟨291937704697103540933798099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194625136464735693955865399 291937704697103540933798099)
  ·
    refine ⟨437906557045655311400697149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291937704697103540933798099 437906557045655311400697149)
    ·
      refine ⟨164214958892120741775261431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437906557045655311400697149 164214958892120741775261431)
      ·
        refine ⟨246322438338181112662892147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164214958892120741775261431 246322438338181112662892147)
        ·
          refine ⟨369483657507271668994338221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246322438338181112662892147 369483657507271668994338221)
          ·
            refine ⟨138556371565226875872876833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369483657507271668994338221 138556371565226875872876833)
            ·
              refine ⟨103917278673920156904657625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138556371565226875872876833 103917278673920156904657625)
              ·
                refine ⟨77937959005440117678493219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103917278673920156904657625 77937959005440117678493219)
                ·
                  refine ⟨116906938508160176517739829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77937959005440117678493219 116906938508160176517739829)
                  ·
                    refine ⟨10960025485140016548538109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116906938508160176517739829 10960025485140016548538109)
                    ·
                      refine ⟨4110009556927506205701791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960025485140016548538109 4110009556927506205701791)
                      ·
                        rfl

theorem cell23_8004215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_8004215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004215 prefixEnd_8004215 := by exact prefixLift 8004215
  have htrace : WordTrace (prefixWord ++ tailWord_8004215) baseStart_8004215 baseEnd_8004215 := by
    simpa [prefixWord, tailWord_8004215, baseEnd_8004215] using wordTrace_append hprefix tailTrace_8004215
  have hstable : (prefixWord ++ tailWord_8004215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004215).length < 2 ^ (prefixWord ++ tailWord_8004215).sum := by decide
  have hdescent : baseEnd_8004215 < baseStart_8004215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004269 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_8004269 : Nat := 118140960795 + 8004269 * 2 ^ 59
def prefixEnd_8004269 : Nat := 4983230072969 + 3 ^ 40 * 8004269 * 2
def baseEnd_8004269 : Nat := 1370012428294282998142181

theorem tailTrace_8004269 : CollatzResearch.WordTrace tailWord_8004269 prefixEnd_8004269 1370012428294282998142181 := by
  unfold tailWord_8004269
  simp only [CollatzResearch.WordTrace]
  refine ⟨291939674238907908156263861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194626449492605272104175907 291939674238907908156263861)
  ·
    refine ⟨27369344459897616389649737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 291939674238907908156263861 27369344459897616389649737)
    ·
      refine ⟨20527008344923212292237303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27369344459897616389649737 20527008344923212292237303)
      ·
        refine ⟨30790512517384818438355955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20527008344923212292237303 30790512517384818438355955)
        ·
          refine ⟨46185768776077227657533933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30790512517384818438355955 46185768776077227657533933)
          ·
            refine ⟨17319663291028960371575225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46185768776077227657533933 17319663291028960371575225)
            ·
              refine ⟨12989747468271720278681419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17319663291028960371575225 12989747468271720278681419)
              ·
                refine ⟨19484621202407580418022129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12989747468271720278681419 19484621202407580418022129)
                ·
                  refine ⟨14613465901805685313516597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19484621202407580418022129 14613465901805685313516597)
                  ·
                    refine ⟨1370012428294282998142181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14613465901805685313516597 1370012428294282998142181)
                    ·
                      rfl

theorem cell23_8004269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_8004269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004269 prefixEnd_8004269 := by exact prefixLift 8004269
  have htrace : WordTrace (prefixWord ++ tailWord_8004269) baseStart_8004269 baseEnd_8004269 := by
    simpa [prefixWord, tailWord_8004269, baseEnd_8004269] using wordTrace_append hprefix tailTrace_8004269
  have hstable : (prefixWord ++ tailWord_8004269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004269).length < 2 ^ (prefixWord ++ tailWord_8004269).sum := by decide
  have hdescent : baseEnd_8004269 < baseStart_8004269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004272 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 4, 4, 2]
def baseStart_8004272 : Nat := 118140960795 + 8004272 * 2 ^ 59
def prefixEnd_8004272 : Nat := 4983230072969 + 3 ^ 40 * 8004272 * 2
def baseEnd_8004272 : Nat := 4110038825324812482689029

theorem tailTrace_8004272 : CollatzResearch.WordTrace tailWord_8004272 prefixEnd_8004272 4110038825324812482689029 := by
  unfold tailWord_8004272
  simp only [CollatzResearch.WordTrace]
  refine ⟨145969891828948519834311535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194626522438598026445748713 145969891828948519834311535)
  ·
    refine ⟨218954837743422779751467303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145969891828948519834311535 218954837743422779751467303)
    ·
      refine ⟨328432256615134169627200955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218954837743422779751467303 328432256615134169627200955)
      ·
        refine ⟨492648384922701254440801433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328432256615134169627200955 492648384922701254440801433)
        ·
          refine ⟨369486288692025940830601075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492648384922701254440801433 369486288692025940830601075)
          ·
            refine ⟨554229433038038911245901613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369486288692025940830601075 554229433038038911245901613)
            ·
              refine ⟨207836037389264591717213105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554229433038038911245901613 207836037389264591717213105)
              ·
                refine ⟨155877028041948443787909829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207836037389264591717213105 155877028041948443787909829)
                ·
                  refine ⟨29226942757865333210233093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155877028041948443787909829 29226942757865333210233093)
                  ·
                    refine ⟨5480051767099749976918705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29226942757865333210233093 5480051767099749976918705)
                    ·
                      refine ⟨4110038825324812482689029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480051767099749976918705 4110038825324812482689029)
                      ·
                        rfl

theorem cell23_8004272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 4, 2].length) (baseStart_8004272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004272 prefixEnd_8004272 := by exact prefixLift 8004272
  have htrace : WordTrace (prefixWord ++ tailWord_8004272) baseStart_8004272 baseEnd_8004272 := by
    simpa [prefixWord, tailWord_8004272, baseEnd_8004272] using wordTrace_append hprefix tailTrace_8004272
  have hstable : (prefixWord ++ tailWord_8004272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004272).length < 2 ^ (prefixWord ++ tailWord_8004272).sum := by decide
  have hdescent : baseEnd_8004272 < baseStart_8004272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004306 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_8004306 : Nat := 118140960795 + 8004306 * 2 ^ 59
def prefixEnd_8004306 : Nat := 4983230072969 + 3 ^ 40 * 8004306 * 2
def baseEnd_8004306 : Nat := 4110056283667065349663873

theorem tailTrace_8004306 : CollatzResearch.WordTrace tailWord_8004306 prefixEnd_8004306 4110056283667065349663873 := by
  unfold tailWord_8004306
  simp only [CollatzResearch.WordTrace]
  refine ⟨72985255934943465868840193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194627349159849242316907181 72985255934943465868840193)
  ·
    refine ⟨54738941951207599401630145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72985255934943465868840193 54738941951207599401630145)
    ·
      refine ⟨41054206463405699551222609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54738941951207599401630145 41054206463405699551222609)
      ·
        refine ⟨30790654847554274663416957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41054206463405699551222609 30790654847554274663416957)
        ·
          refine ⟨11546495567832852998781359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30790654847554274663416957 11546495567832852998781359)
          ·
            refine ⟨17319743351749279498172039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11546495567832852998781359 17319743351749279498172039)
            ·
              refine ⟨25979615027623919247258059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17319743351749279498172039 25979615027623919247258059)
              ·
                refine ⟨38969422541435878870887089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25979615027623919247258059 38969422541435878870887089)
                ·
                  refine ⟨29227066906076909153165317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38969422541435878870887089 29227066906076909153165317)
                  ·
                    refine ⟨5480075044889420466218497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29227066906076909153165317 5480075044889420466218497)
                    ·
                      refine ⟨4110056283667065349663873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480075044889420466218497 4110056283667065349663873)
                      ·
                        rfl

theorem cell23_8004306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_8004306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004306 prefixEnd_8004306 := by exact prefixLift 8004306
  have htrace : WordTrace (prefixWord ++ tailWord_8004306) baseStart_8004306 baseEnd_8004306 := by
    simpa [prefixWord, tailWord_8004306, baseEnd_8004306] using wordTrace_append hprefix tailTrace_8004306
  have hstable : (prefixWord ++ tailWord_8004306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004306).length < 2 ^ (prefixWord ++ tailWord_8004306).sum := by decide
  have hdescent : baseEnd_8004306 < baseStart_8004306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004312 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 6]
def baseStart_8004312 : Nat := 118140960795 + 8004312 * 2 ^ 59
def prefixEnd_8004312 : Nat := 4983230072969 + 3 ^ 40 * 8004312 * 2
def baseEnd_8004312 : Nat := 456673262727888036243205

theorem tailTrace_8004312 : CollatzResearch.WordTrace tailWord_8004312 prefixEnd_8004312 456673262727888036243205 := by
  unfold tailWord_8004312
  simp only [CollatzResearch.WordTrace]
  refine ⟨145970621288876063250039595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194627495051834751000052793 145970621288876063250039595)
  ·
    refine ⟨218955931933314094875059393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145970621288876063250039595 218955931933314094875059393)
    ·
      refine ⟨164216948949985571156294545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218955931933314094875059393 164216948949985571156294545)
      ·
        refine ⟨123162711712489178367220909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164216948949985571156294545 123162711712489178367220909)
        ·
          refine ⟨46186016892183441887707841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123162711712489178367220909 46186016892183441887707841)
          ·
            refine ⟨34639512669137581415780881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46186016892183441887707841 34639512669137581415780881)
            ·
              refine ⟨25979634501853186061835661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34639512669137581415780881 25979634501853186061835661)
              ·
                refine ⟨9742362938194944773188373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25979634501853186061835661 9742362938194944773188373)
                ·
                  refine ⟨456673262727888036243205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9742362938194944773188373 456673262727888036243205)
                  ·
                    rfl

theorem cell23_8004312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 6].length) (baseStart_8004312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004312 prefixEnd_8004312 := by exact prefixLift 8004312
  have htrace : WordTrace (prefixWord ++ tailWord_8004312) baseStart_8004312 baseEnd_8004312 := by
    simpa [prefixWord, tailWord_8004312, baseEnd_8004312] using wordTrace_append hprefix tailTrace_8004312
  have hstable : (prefixWord ++ tailWord_8004312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004312).length < 2 ^ (prefixWord ++ tailWord_8004312).sum := by decide
  have hdescent : baseEnd_8004312 < baseStart_8004312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004316 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_8004316 : Nat := 118140960795 + 8004316 * 2 ^ 59
def prefixEnd_8004316 : Nat := 4983230072969 + 3 ^ 40 * 8004316 * 2
def baseEnd_8004316 : Nat := 1370020472824536770179609

theorem tailTrace_8004316 : CollatzResearch.WordTrace tailWord_8004316 prefixEnd_8004316 1370020472824536770179609 := by
  unfold tailWord_8004316
  simp only [CollatzResearch.WordTrace]
  refine ⟨145970694234868817591612401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194627592313158423455483201 145970694234868817591612401)
  ·
    refine ⟨109478020676151613193709301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145970694234868817591612401 109478020676151613193709301)
    ·
      refine ⟨10263564438389213736910247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109478020676151613193709301 10263564438389213736910247)
      ·
        refine ⟨15395346657583820605365371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10263564438389213736910247 15395346657583820605365371)
        ·
          refine ⟨23093019986375730908048057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15395346657583820605365371 23093019986375730908048057)
          ·
            refine ⟨17319764989781798181036043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23093019986375730908048057 17319764989781798181036043)
            ·
              refine ⟨25979647484672697271554065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17319764989781798181036043 25979647484672697271554065)
              ·
                refine ⟨19484735613504522953665549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25979647484672697271554065 19484735613504522953665549)
                ·
                  refine ⟨7306775855064196107624581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19484735613504522953665549 7306775855064196107624581)
                  ·
                    refine ⟨1370020472824536770179609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7306775855064196107624581 1370020472824536770179609)
                    ·
                      rfl

theorem cell23_8004316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_8004316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004316 prefixEnd_8004316 := by exact prefixLift 8004316
  have htrace : WordTrace (prefixWord ++ tailWord_8004316) baseStart_8004316 baseEnd_8004316 := by
    simpa [prefixWord, tailWord_8004316, baseEnd_8004316] using wordTrace_append hprefix tailTrace_8004316
  have hstable : (prefixWord ++ tailWord_8004316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004316).length < 2 ^ (prefixWord ++ tailWord_8004316).sum := by decide
  have hdescent : baseEnd_8004316 < baseStart_8004316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004349 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_8004349 : Nat := 118140960795 + 8004349 * 2 ^ 59
def prefixEnd_8004349 : Nat := 4983230072969 + 3 ^ 40 * 8004349 * 2
def baseEnd_8004349 : Nat := 4110078363335208681426175

theorem tailTrace_8004349 : CollatzResearch.WordTrace tailWord_8004349 prefixEnd_8004349 4110078363335208681426175 := by
  unfold tailWord_8004349
  simp only [CollatzResearch.WordTrace]
  refine ⟨291942592078618081819176101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194628394719078721212784067 291942592078618081819176101)
  ·
    refine ⟨54739236014740890341095519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291942592078618081819176101 54739236014740890341095519)
    ·
      refine ⟨82108854022111335511643279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54739236014740890341095519 82108854022111335511643279)
      ·
        refine ⟨123163281033167003267464919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82108854022111335511643279 123163281033167003267464919)
        ·
          refine ⟨184744921549750504901197379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123163281033167003267464919 184744921549750504901197379)
          ·
            refine ⟨277117382324625757351796069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184744921549750504901197379 277117382324625757351796069)
            ·
              refine ⟨51959509185867329503461763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277117382324625757351796069 51959509185867329503461763)
              ·
                refine ⟨77939263778800994255192645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51959509185867329503461763 77939263778800994255192645)
                ·
                  refine ⟨14613611958525186422848621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77939263778800994255192645 14613611958525186422848621)
                  ·
                    refine ⟨5480104484446944908568233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14613611958525186422848621 5480104484446944908568233)
                    ·
                      refine ⟨4110078363335208681426175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480104484446944908568233 4110078363335208681426175)
                      ·
                        rfl

theorem cell23_8004349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_8004349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004349 prefixEnd_8004349 := by exact prefixLift 8004349
  have htrace : WordTrace (prefixWord ++ tailWord_8004349) baseStart_8004349 baseEnd_8004349 := by
    simpa [prefixWord, tailWord_8004349, baseEnd_8004349] using wordTrace_append hprefix tailTrace_8004349
  have hstable : (prefixWord ++ tailWord_8004349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004349).length < 2 ^ (prefixWord ++ tailWord_8004349).sum := by decide
  have hdescent : baseEnd_8004349 < baseStart_8004349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004356 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_8004356 : Nat := 118140960795 + 8004356 * 2 ^ 59
def prefixEnd_8004356 : Nat := 4983230072969 + 3 ^ 40 * 8004356 * 2
def baseEnd_8004356 : Nat := 4110081957699790154038643

theorem tailTrace_8004356 : CollatzResearch.WordTrace tailWord_8004356 prefixEnd_8004356 4110081957699790154038643 := by
  unfold tailWord_8004356
  simp only [CollatzResearch.WordTrace]
  refine ⟨145971423694796361007340461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194628564926395148009787281 145971423694796361007340461)
  ·
    refine ⟨54739283885548635377752673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145971423694796361007340461 54739283885548635377752673)
    ·
      refine ⟨41054462914161476533314505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54739283885548635377752673 41054462914161476533314505)
      ·
        refine ⟨30790847185621107399985879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41054462914161476533314505 30790847185621107399985879)
        ·
          refine ⟨46186270778431661099978819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30790847185621107399985879 46186270778431661099978819)
          ·
            refine ⟨69279406167647491649968229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46186270778431661099978819 69279406167647491649968229)
            ·
              refine ⟨12989888656433904684369043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69279406167647491649968229 12989888656433904684369043)
              ·
                refine ⟨19484832984650857026553565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12989888656433904684369043 19484832984650857026553565)
                ·
                  refine ⟨7306812369244071384957587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19484832984650857026553565 7306812369244071384957587)
                  ·
                    refine ⟨10960218553866107077436381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7306812369244071384957587 10960218553866107077436381)
                    ·
                      refine ⟨4110081957699790154038643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960218553866107077436381 4110081957699790154038643)
                      ·
                        rfl

theorem cell23_8004356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_8004356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004356 prefixEnd_8004356 := by exact prefixLift 8004356
  have htrace : WordTrace (prefixWord ++ tailWord_8004356) baseStart_8004356 baseEnd_8004356 := by
    simpa [prefixWord, tailWord_8004356, baseEnd_8004356] using wordTrace_append hprefix tailTrace_8004356
  have hstable : (prefixWord ++ tailWord_8004356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004356).length < 2 ^ (prefixWord ++ tailWord_8004356).sum := by decide
  have hdescent : baseEnd_8004356 < baseStart_8004356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004433 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_8004433 : Nat := 118140960795 + 8004433 * 2 ^ 59
def prefixEnd_8004433 : Nat := 4983230072969 + 3 ^ 40 * 8004433 * 2
def baseEnd_8004433 : Nat := 4110121495710186352775789

theorem tailTrace_8004433 : CollatzResearch.WordTrace tailWord_8004433 prefixEnd_8004433 4110121495710186352775789 := by
  unfold tailWord_8004433
  simp only [CollatzResearch.WordTrace]
  refine ⟨291945655810313764165233953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194630437206875842776822635 291945655810313764165233953)
  ·
    refine ⟨218959241857735323123925465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291945655810313764165233953 218959241857735323123925465)
    ·
      refine ⟨164219431393301492342944099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218959241857735323123925465 164219431393301492342944099)
      ·
        refine ⟨246329147089952238514416149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164219431393301492342944099 246329147089952238514416149)
        ·
          refine ⟨11546678769841511180363257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246329147089952238514416149 11546678769841511180363257)
          ·
            refine ⟨8660009077381133385272443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11546678769841511180363257 8660009077381133385272443)
            ·
              refine ⟨12990013616071700077908665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660009077381133385272443 12990013616071700077908665)
              ·
                refine ⟨9742510212053775058431499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12990013616071700077908665 9742510212053775058431499)
                ·
                  refine ⟨14613765318080662587647249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9742510212053775058431499 14613765318080662587647249)
                  ·
                    refine ⟨10960323988560496940735437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14613765318080662587647249 10960323988560496940735437)
                    ·
                      refine ⟨4110121495710186352775789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960323988560496940735437 4110121495710186352775789)
                      ·
                        rfl

theorem cell23_8004433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_8004433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004433 prefixEnd_8004433 := by exact prefixLift 8004433
  have htrace : WordTrace (prefixWord ++ tailWord_8004433) baseStart_8004433 baseEnd_8004433 := by
    simpa [prefixWord, tailWord_8004433, baseEnd_8004433] using wordTrace_append hprefix tailTrace_8004433
  have hstable : (prefixWord ++ tailWord_8004433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004433).length < 2 ^ (prefixWord ++ tailWord_8004433).sum := by decide
  have hdescent : baseEnd_8004433 < baseStart_8004433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004450 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_8004450 : Nat := 118140960795 + 8004450 * 2 ^ 59
def prefixEnd_8004450 : Nat := 4983230072969 + 3 ^ 40 * 8004450 * 2
def baseEnd_8004450 : Nat := 4110130224881312786263211

theorem tailTrace_8004450 : CollatzResearch.WordTrace tailWord_8004450 prefixEnd_8004450 4110130224881312786263211 := by
  unfold tailWord_8004450
  simp only [CollatzResearch.WordTrace]
  refine ⟨72986568962813044017150701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194630850567501450712401869 72986568962813044017150701)
  ·
    refine ⟨27369963361054891506431513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72986568962813044017150701 27369963361054891506431513)
    ·
      refine ⟨20527472520791168629823635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27369963361054891506431513 20527472520791168629823635)
      ·
        refine ⟨30791208781186752944735453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20527472520791168629823635 30791208781186752944735453)
        ·
          refine ⟨11546703292945032354275795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30791208781186752944735453 11546703292945032354275795)
          ·
            refine ⟨17320054939417548531413693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11546703292945032354275795 17320054939417548531413693)
            ·
              refine ⟨6495020602281580699280135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17320054939417548531413693 6495020602281580699280135)
              ·
                refine ⟨9742530903422371048920203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495020602281580699280135 9742530903422371048920203)
                ·
                  refine ⟨14613796355133556573380305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9742530903422371048920203 14613796355133556573380305)
                  ·
                    refine ⟨10960347266350167430035229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14613796355133556573380305 10960347266350167430035229)
                    ·
                      refine ⟨4110130224881312786263211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960347266350167430035229 4110130224881312786263211)
                      ·
                        rfl

theorem cell23_8004450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_8004450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004450 prefixEnd_8004450 := by exact prefixLift 8004450
  have htrace : WordTrace (prefixWord ++ tailWord_8004450) baseStart_8004450 baseEnd_8004450 := by
    simpa [prefixWord, tailWord_8004450, baseEnd_8004450] using wordTrace_append hprefix tailTrace_8004450
  have hstable : (prefixWord ++ tailWord_8004450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004450).length < 2 ^ (prefixWord ++ tailWord_8004450).sum := by decide
  have hdescent : baseEnd_8004450 < baseStart_8004450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004469 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_8004469 : Nat := 118140960795 + 8004469 * 2 ^ 59
def prefixEnd_8004469 : Nat := 4983230072969 + 3 ^ 40 * 8004469 * 2
def baseEnd_8004469 : Nat := 4110139981013748211925623

theorem tailTrace_8004469 : CollatzResearch.WordTrace tailWord_8004469 prefixEnd_8004469 4110139981013748211925623 := by
  unfold tailWord_8004469
  simp only [CollatzResearch.WordTrace]
  refine ⟨291946968838183342313544461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194631312558788894875696307 291946968838183342313544461)
  ·
    refine ⟨109480113314318753367579173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291946968838183342313544461 109480113314318753367579173)
    ·
      refine ⟨20527521246434766256421095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109480113314318753367579173 20527521246434766256421095)
      ·
        refine ⟨30791281869652149384631643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20527521246434766256421095 30791281869652149384631643)
        ·
          refine ⟨46186922804478224076947465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30791281869652149384631643 46186922804478224076947465)
          ·
            refine ⟨34640192103358668057710599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46186922804478224076947465 34640192103358668057710599)
            ·
              refine ⟨51960288155038002086565899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34640192103358668057710599 51960288155038002086565899)
              ·
                refine ⟨77940432232557003129848849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51960288155038002086565899 77940432232557003129848849)
                ·
                  refine ⟨58455324174417752347386637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77940432232557003129848849 58455324174417752347386637)
                  ·
                    refine ⟨21920746565406657130269989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58455324174417752347386637 21920746565406657130269989)
                    ·
                      refine ⟨4110139981013748211925623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21920746565406657130269989 4110139981013748211925623)
                      ·
                        rfl

theorem cell23_8004469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_8004469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004469 prefixEnd_8004469 := by exact prefixLift 8004469
  have htrace : WordTrace (prefixWord ++ tailWord_8004469) baseStart_8004469 baseEnd_8004469 := by
    simpa [prefixWord, tailWord_8004469, baseEnd_8004469] using wordTrace_append hprefix tailTrace_8004469
  have hstable : (prefixWord ++ tailWord_8004469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004469).length < 2 ^ (prefixWord ++ tailWord_8004469).sum := by decide
  have hdescent : baseEnd_8004469 < baseStart_8004469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004472 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_8004472 : Nat := 118140960795 + 8004472 * 2 ^ 59
def prefixEnd_8004472 : Nat := 4983230072969 + 3 ^ 40 * 8004472 * 2
def baseEnd_8004472 : Nat := 4110141521455711700188109

theorem tailTrace_8004472 : CollatzResearch.WordTrace tailWord_8004472 prefixEnd_8004472 4110141521455711700188109 := by
  unfold tailWord_8004472
  simp only [CollatzResearch.WordTrace]
  refine ⟨145973539128586236912951835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194631385504781649217269113 145973539128586236912951835)
  ·
    refine ⟨218960308692879355369427753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145973539128586236912951835 218960308692879355369427753)
    ·
      refine ⟨164220231519659516527070815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218960308692879355369427753 164220231519659516527070815)
      ·
        refine ⟨246330347279489274790606223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164220231519659516527070815 246330347279489274790606223)
        ·
          refine ⟨369495520919233912185909335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246330347279489274790606223 369495520919233912185909335)
          ·
            refine ⟨554243281378850868278864003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369495520919233912185909335 554243281378850868278864003)
            ·
              refine ⟨831364922068276302418296005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554243281378850868278864003 831364922068276302418296005)
              ·
                refine ⟨155880922887801806703430501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831364922068276302418296005 155880922887801806703430501)
                ·
                  refine ⟨29227673041462838756893219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155880922887801806703430501 29227673041462838756893219)
                  ·
                    refine ⟨43841509562194258135339829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29227673041462838756893219 43841509562194258135339829)
                    ·
                      refine ⟨4110141521455711700188109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43841509562194258135339829 4110141521455711700188109)
                      ·
                        rfl

theorem cell23_8004472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_8004472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004472 prefixEnd_8004472 := by exact prefixLift 8004472
  have htrace : WordTrace (prefixWord ++ tailWord_8004472) baseStart_8004472 baseEnd_8004472 := by
    simpa [prefixWord, tailWord_8004472, baseEnd_8004472] using wordTrace_append hprefix tailTrace_8004472
  have hstable : (prefixWord ++ tailWord_8004472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004472).length < 2 ^ (prefixWord ++ tailWord_8004472).sum := by decide
  have hdescent : baseEnd_8004472 < baseStart_8004472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004492 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 9]
def baseStart_8004492 : Nat := 118140960795 + 8004492 * 2 ^ 59
def prefixEnd_8004492 : Nat := 4983230072969 + 3 ^ 40 * 8004492 * 2
def baseEnd_8004492 : Nat := 456683532340977957993113

theorem tailTrace_8004492 : CollatzResearch.WordTrace tailWord_8004492 prefixEnd_8004492 456683532340977957993113 := by
  unfold tailWord_8004492
  simp only [CollatzResearch.WordTrace]
  refine ⟨145973903858550008620815865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194631871811400011494421153 145973903858550008620815865)
  ·
    refine ⟨109480427893912506465611899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145973903858550008620815865 109480427893912506465611899)
    ·
      refine ⟨164220641840868759698417849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109480427893912506465611899 164220641840868759698417849)
      ·
        refine ⟨123165481380651569773813387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164220641840868759698417849 123165481380651569773813387)
        ·
          refine ⟨184748222070977354660720081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123165481380651569773813387 184748222070977354660720081)
          ·
            refine ⟨138561166553233015995540061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184748222070977354660720081 138561166553233015995540061)
            ·
              refine ⟨51960437457462380998327523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138561166553233015995540061 51960437457462380998327523)
              ·
                refine ⟨77940656186193571497491285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51960437457462380998327523 77940656186193571497491285)
                ·
                  refine ⟨456683532340977957993113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77940656186193571497491285 456683532340977957993113)
                  ·
                    rfl

theorem cell23_8004492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_8004492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004492 prefixEnd_8004492 := by exact prefixLift 8004492
  have htrace : WordTrace (prefixWord ++ tailWord_8004492) baseStart_8004492 baseEnd_8004492 := by
    simpa [prefixWord, tailWord_8004492, baseEnd_8004492] using wordTrace_append hprefix tailTrace_8004492
  have hstable : (prefixWord ++ tailWord_8004492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004492).length < 2 ^ (prefixWord ++ tailWord_8004492).sum := by decide
  have hdescent : baseEnd_8004492 < baseStart_8004492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004559 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_8004559 : Nat := 118140960795 + 8004559 * 2 ^ 59
def prefixEnd_8004559 : Nat := 4983230072969 + 3 ^ 40 * 8004559 * 2
def baseEnd_8004559 : Nat := 4110186194272652859800209

theorem tailTrace_8004559 : CollatzResearch.WordTrace tailWord_8004559 prefixEnd_8004559 4110186194272652859800209 := by
  unfold tailWord_8004559
  simp only [CollatzResearch.WordTrace]
  refine ⟨291950251407857287684320731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194633500938571525122880487 291950251407857287684320731)
  ·
    refine ⟨437925377111785931526481097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291950251407857287684320731 437925377111785931526481097)
    ·
      refine ⟨328444032833839448644860823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437925377111785931526481097 328444032833839448644860823)
      ·
        refine ⟨492666049250759172967291235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328444032833839448644860823 492666049250759172967291235)
        ·
          refine ⟨738999073876138759450936853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492666049250759172967291235 738999073876138759450936853)
          ·
            refine ⟨34640581587944004349262665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 738999073876138759450936853 34640581587944004349262665)
            ·
              refine ⟨25980436190958003261946999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34640581587944004349262665 25980436190958003261946999)
              ·
                refine ⟨38970654286437004892920499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25980436190958003261946999 38970654286437004892920499)
                ·
                  refine ⟨58455981429655507339380749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38970654286437004892920499 58455981429655507339380749)
                  ·
                    refine ⟨21920993036120815252267781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58455981429655507339380749 21920993036120815252267781)
                    ·
                      refine ⟨4110186194272652859800209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21920993036120815252267781 4110186194272652859800209)
                      ·
                        rfl

theorem cell23_8004559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_8004559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004559 prefixEnd_8004559 := by exact prefixLift 8004559
  have htrace : WordTrace (prefixWord ++ tailWord_8004559) baseStart_8004559 baseEnd_8004559 := by
    simpa [prefixWord, tailWord_8004559, baseEnd_8004559] using wordTrace_append hprefix tailTrace_8004559
  have hstable : (prefixWord ++ tailWord_8004559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004559).length < 2 ^ (prefixWord ++ tailWord_8004559).sum := by decide
  have hdescent : baseEnd_8004559 < baseStart_8004559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004660 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_8004660 : Nat := 118140960795 + 8004660 * 2 ^ 59
def prefixEnd_8004660 : Nat := 4983230072969 + 3 ^ 40 * 8004660 * 2
def baseEnd_8004660 : Nat := 4110238055818756964637245

theorem tailTrace_8004660 : CollatzResearch.WordTrace tailWord_8004660 prefixEnd_8004660 4110238055818756964637245 := by
  unfold tailWord_8004660
  simp only [CollatzResearch.WordTrace]
  refine ⟨145976967590245690966873717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194635956786994254622498289 145976967590245690966873717)
  ·
    refine ⟨13685340711585533528144411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145976967590245690966873717 13685340711585533528144411)
    ·
      refine ⟨20528011067378300292216617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13685340711585533528144411 20528011067378300292216617)
      ·
        refine ⟨15396008300533725219162463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20528011067378300292216617 15396008300533725219162463)
        ·
          refine ⟨23094012450800587828743695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15396008300533725219162463 23094012450800587828743695)
          ·
            refine ⟨34641018676200881743115543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23094012450800587828743695 34641018676200881743115543)
            ·
              refine ⟨51961528014301322614673315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34641018676200881743115543 51961528014301322614673315)
              ·
                refine ⟨77942292021451983922009973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51961528014301322614673315 77942292021451983922009973)
                ·
                  refine ⟨7307089877011123492688435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77942292021451983922009973 7307089877011123492688435)
                  ·
                    refine ⟨10960634815516685239032653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307089877011123492688435 10960634815516685239032653)
                    ·
                      refine ⟨4110238055818756964637245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960634815516685239032653 4110238055818756964637245)
                      ·
                        rfl

theorem cell23_8004660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_8004660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004660 prefixEnd_8004660 := by exact prefixLift 8004660
  have htrace : WordTrace (prefixWord ++ tailWord_8004660) baseStart_8004660 baseEnd_8004660 := by
    simpa [prefixWord, tailWord_8004660, baseEnd_8004660] using wordTrace_append hprefix tailTrace_8004660
  have hstable : (prefixWord ++ tailWord_8004660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004660).length < 2 ^ (prefixWord ++ tailWord_8004660).sum := by decide
  have hdescent : baseEnd_8004660 < baseStart_8004660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004666 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_8004666 : Nat := 118140960795 + 8004666 * 2 ^ 59
def prefixEnd_8004666 : Nat := 4983230072969 + 3 ^ 40 * 8004666 * 2
def baseEnd_8004666 : Nat := 4110241136702683941162217

theorem tailTrace_8004666 : CollatzResearch.WordTrace tailWord_8004666 prefixEnd_8004666 4110241136702683941162217 := by
  unfold tailWord_8004666
  simp only [CollatzResearch.WordTrace]
  refine ⟨72988538504617411239616463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194636102678979763305643901 72988538504617411239616463)
  ·
    refine ⟨109482807756926116859424695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72988538504617411239616463 109482807756926116859424695)
    ·
      refine ⟨164224211635389175289137043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109482807756926116859424695 164224211635389175289137043)
      ·
        refine ⟨246336317453083762933705565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164224211635389175289137043 246336317453083762933705565)
        ·
          refine ⟨92376119044906411100139587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246336317453083762933705565 92376119044906411100139587)
          ·
            refine ⟨138564178567359616650209381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92376119044906411100139587 138564178567359616650209381)
            ·
              refine ⟨25980783481379928121914259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138564178567359616650209381 25980783481379928121914259)
              ·
                refine ⟨38971175222069892182871389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25980783481379928121914259 38971175222069892182871389)
                ·
                  refine ⟨14614190708276209568576771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38971175222069892182871389 14614190708276209568576771)
                  ·
                    refine ⟨21921286062414314352865157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14614190708276209568576771 21921286062414314352865157)
                    ·
                      refine ⟨4110241136702683941162217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21921286062414314352865157 4110241136702683941162217)
                      ·
                        rfl

theorem cell23_8004666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_8004666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004666 prefixEnd_8004666 := by exact prefixLift 8004666
  have htrace : WordTrace (prefixWord ++ tailWord_8004666) baseStart_8004666 baseEnd_8004666 := by
    simpa [prefixWord, tailWord_8004666, baseEnd_8004666] using wordTrace_append hprefix tailTrace_8004666
  have hstable : (prefixWord ++ tailWord_8004666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004666).length < 2 ^ (prefixWord ++ tailWord_8004666).sum := by decide
  have hdescent : baseEnd_8004666 < baseStart_8004666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004670 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_8004670 : Nat := 118140960795 + 8004670 * 2 ^ 59
def prefixEnd_8004670 : Nat := 4983230072969 + 3 ^ 40 * 8004670 * 2
def baseEnd_8004670 : Nat := 4110243190625301925512199

theorem tailTrace_8004670 : CollatzResearch.WordTrace tailWord_8004670 prefixEnd_8004670 4110243190625301925512199 := by
  unfold tailWord_8004670
  simp only [CollatzResearch.WordTrace]
  refine ⟨36494287488806894205201433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194636199940303435761074309 36494287488806894205201433)
  ·
    refine ⟨27370715616605170653901075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36494287488806894205201433 27370715616605170653901075)
    ·
      refine ⟨41056073424907755980851613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27370715616605170653901075 41056073424907755980851613)
      ·
        refine ⟨15396027534340408492819355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41056073424907755980851613 15396027534340408492819355)
        ·
          refine ⟨23094041301510612739229033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15396027534340408492819355 23094041301510612739229033)
          ·
            refine ⟨17320530976132959554421775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23094041301510612739229033 17320530976132959554421775)
            ·
              refine ⟨25980796464199439331632663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17320530976132959554421775 25980796464199439331632663)
              ·
                refine ⟨38971194696299158997448995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25980796464199439331632663 38971194696299158997448995)
                ·
                  refine ⟨58456792044448738496173493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38971194696299158997448995 58456792044448738496173493)
                  ·
                    refine ⟨5480324254167069234016265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58456792044448738496173493 5480324254167069234016265)
                    ·
                      refine ⟨4110243190625301925512199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480324254167069234016265 4110243190625301925512199)
                      ·
                        rfl

theorem cell23_8004670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_8004670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004670 prefixEnd_8004670 := by exact prefixLift 8004670
  have htrace : WordTrace (prefixWord ++ tailWord_8004670) baseStart_8004670 baseEnd_8004670 := by
    simpa [prefixWord, tailWord_8004670, baseEnd_8004670] using wordTrace_append hprefix tailTrace_8004670
  have hstable : (prefixWord ++ tailWord_8004670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004670).length < 2 ^ (prefixWord ++ tailWord_8004670).sum := by decide
  have hdescent : baseEnd_8004670 < baseStart_8004670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004686 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_8004686 : Nat := 118140960795 + 8004686 * 2 ^ 59
def prefixEnd_8004686 : Nat := 4983230072969 + 3 ^ 40 * 8004686 * 2
def baseEnd_8004686 : Nat := 4110251406315773862912125

theorem tailTrace_8004686 : CollatzResearch.WordTrace tailWord_8004686 prefixEnd_8004686 4110251406315773862912125 := by
  unfold tailWord_8004686
  simp only [CollatzResearch.WordTrace]
  refine ⟨36494360434799648546774239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194636588985598125582795941 36494360434799648546774239)
  ·
    refine ⟨54741540652199472820161359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36494360434799648546774239 54741540652199472820161359)
    ·
      refine ⟨82112310978299209230242039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54741540652199472820161359 82112310978299209230242039)
      ·
        refine ⟨123168466467448813845363059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82112310978299209230242039 123168466467448813845363059)
        ·
          refine ⟨184752699701173220768044589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123168466467448813845363059 184752699701173220768044589)
          ·
            refine ⟨69282262387939957788016721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184752699701173220768044589 69282262387939957788016721)
            ·
              refine ⟨51961696790954968341012541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69282262387939957788016721 51961696790954968341012541)
              ·
                refine ⟨19485636296608113127879703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51961696790954968341012541 19485636296608113127879703)
                ·
                  refine ⟨29228454444912169691819555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19485636296608113127879703 29228454444912169691819555)
                  ·
                    refine ⟨43842681667368254537729333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29228454444912169691819555 43842681667368254537729333)
                    ·
                      refine ⟨4110251406315773862912125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43842681667368254537729333 4110251406315773862912125)
                      ·
                        rfl

theorem cell23_8004686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_8004686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004686 prefixEnd_8004686 := by exact prefixLift 8004686
  have htrace : WordTrace (prefixWord ++ tailWord_8004686) baseStart_8004686 baseEnd_8004686 := by
    simpa [prefixWord, tailWord_8004686, baseEnd_8004686] using wordTrace_append hprefix tailTrace_8004686
  have hstable : (prefixWord ++ tailWord_8004686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004686).length < 2 ^ (prefixWord ++ tailWord_8004686).sum := by decide
  have hdescent : baseEnd_8004686 < baseStart_8004686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004694 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_8004694 : Nat := 118140960795 + 8004694 * 2 ^ 59
def prefixEnd_8004694 : Nat := 4983230072969 + 3 ^ 40 * 8004694 * 2
def baseEnd_8004694 : Nat := 4110255514161009831612089

theorem tailTrace_8004694 : CollatzResearch.WordTrace tailWord_8004694 prefixEnd_8004694 4110255514161009831612089 := by
  unfold tailWord_8004694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18247198453898012858780321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194636783508245470493656757 18247198453898012858780321)
  ·
    refine ⟨13685398840423509644085241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18247198453898012858780321 13685398840423509644085241)
    ·
      refine ⟨10264049130317632233063931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13685398840423509644085241 10264049130317632233063931)
      ·
        refine ⟨15396073695476448349595897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264049130317632233063931 15396073695476448349595897)
        ·
          refine ⟨11547055271607336262196923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15396073695476448349595897 11547055271607336262196923)
          ·
            refine ⟨17320582907411004393295385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547055271607336262196923 17320582907411004393295385)
            ·
              refine ⟨12990437180558253294971539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17320582907411004393295385 12990437180558253294971539)
              ·
                refine ⟨19485655770837379942457309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12990437180558253294971539 19485655770837379942457309)
                ·
                  refine ⟨7307120914064017478421491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19485655770837379942457309 7307120914064017478421491)
                  ·
                    refine ⟨10960681371096026217632237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307120914064017478421491 10960681371096026217632237)
                    ·
                      refine ⟨4110255514161009831612089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960681371096026217632237 4110255514161009831612089)
                      ·
                        rfl

theorem cell23_8004694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_8004694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004694 prefixEnd_8004694 := by exact prefixLift 8004694
  have htrace : WordTrace (prefixWord ++ tailWord_8004694) baseStart_8004694 baseEnd_8004694 := by
    simpa [prefixWord, tailWord_8004694, baseEnd_8004694] using wordTrace_append hprefix tailTrace_8004694
  have hstable : (prefixWord ++ tailWord_8004694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004694).length < 2 ^ (prefixWord ++ tailWord_8004694).sum := by decide
  have hdescent : baseEnd_8004694 < baseStart_8004694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004713 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 4]
def baseStart_8004713 : Nat := 118140960795 + 8004713 * 2 ^ 59
def prefixEnd_8004713 : Nat := 4983230072969 + 3 ^ 40 * 8004713 * 2
def baseEnd_8004713 : Nat := 4110265270293445257274501

theorem tailTrace_8004713 : CollatzResearch.WordTrace tailWord_8004713 prefixEnd_8004713 4110265270293445257274501 := by
  unfold tailWord_8004713
  simp only [CollatzResearch.WordTrace]
  refine ⟨291955868249299371985426793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194637245499532914656951195 291955868249299371985426793)
  ·
    refine ⟨218966901186974528989070095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291955868249299371985426793 218966901186974528989070095)
    ·
      refine ⟨328450351780461793483605143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218966901186974528989070095 328450351780461793483605143)
      ·
        refine ⟨492675527670692690225407715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328450351780461793483605143 492675527670692690225407715)
        ·
          refine ⟨739013291506039035338111573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492675527670692690225407715 739013291506039035338111573)
          ·
            refine ⟨8660312009836394945368495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 739013291506039035338111573 8660312009836394945368495)
            ·
              refine ⟨12990468014754592418052743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660312009836394945368495 12990468014754592418052743)
              ·
                refine ⟨19485702022131888627079115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12990468014754592418052743 19485702022131888627079115)
                ·
                  refine ⟨29228553033197832940618673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19485702022131888627079115 29228553033197832940618673)
                  ·
                    refine ⟨21921414774898374705464005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29228553033197832940618673 21921414774898374705464005)
                    ·
                      refine ⟨4110265270293445257274501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21921414774898374705464005 4110265270293445257274501)
                      ·
                        rfl

theorem cell23_8004713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_8004713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004713 prefixEnd_8004713 := by exact prefixLift 8004713
  have htrace : WordTrace (prefixWord ++ tailWord_8004713) baseStart_8004713 baseEnd_8004713 := by
    simpa [prefixWord, tailWord_8004713, baseEnd_8004713] using wordTrace_append hprefix tailTrace_8004713
  have hstable : (prefixWord ++ tailWord_8004713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004713).length < 2 ^ (prefixWord ++ tailWord_8004713).sum := by decide
  have hdescent : baseEnd_8004713 < baseStart_8004713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004733 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_8004733 : Nat := 118140960795 + 8004733 * 2 ^ 59
def prefixEnd_8004733 : Nat := 4983230072969 + 3 ^ 40 * 8004733 * 2
def baseEnd_8004733 : Nat := 4110275539906535179024409

theorem tailTrace_8004733 : CollatzResearch.WordTrace tailWord_8004733 prefixEnd_8004733 4110275539906535179024409 := by
  unfold tailWord_8004733
  simp only [CollatzResearch.WordTrace]
  refine ⟨291956597709226915401154853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194637731806151276934103235 291956597709226915401154853)
  ·
    refine ⟨54741862070480046637716535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291956597709226915401154853 54741862070480046637716535)
    ·
      refine ⟨82112793105720069956574803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54741862070480046637716535 82112793105720069956574803)
      ·
        refine ⟨123169189658580104934862205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82112793105720069956574803 123169189658580104934862205)
        ·
          refine ⟨46188446121967539350573327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123169189658580104934862205 46188446121967539350573327)
          ·
            refine ⟨69282669182951309025859991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46188446121967539350573327 69282669182951309025859991)
            ·
              refine ⟨103924003774426963538789987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69282669182951309025859991 103924003774426963538789987)
              ·
                refine ⟨155886005661640445308184981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103924003774426963538789987 155886005661640445308184981)
                ·
                  refine ⟨7307156515389395873821171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155886005661640445308184981 7307156515389395873821171)
                  ·
                    refine ⟨10960734773084093810731757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307156515389395873821171 10960734773084093810731757)
                    ·
                      refine ⟨4110275539906535179024409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960734773084093810731757 4110275539906535179024409)
                      ·
                        rfl

theorem cell23_8004733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_8004733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004733 prefixEnd_8004733 := by exact prefixLift 8004733
  have htrace : WordTrace (prefixWord ++ tailWord_8004733) baseStart_8004733 baseEnd_8004733 := by
    simpa [prefixWord, tailWord_8004733, baseEnd_8004733] using wordTrace_append hprefix tailTrace_8004733
  have hstable : (prefixWord ++ tailWord_8004733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004733).length < 2 ^ (prefixWord ++ tailWord_8004733).sum := by decide
  have hdescent : baseEnd_8004733 < baseStart_8004733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004743 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_8004743 : Nat := 118140960795 + 8004743 * 2 ^ 59
def prefixEnd_8004743 : Nat := 4983230072969 + 3 ^ 40 * 8004743 * 2
def baseEnd_8004743 : Nat := 4110280674713080139899363

theorem tailTrace_8004743 : CollatzResearch.WordTrace tailWord_8004743 prefixEnd_8004743 4110280674713080139899363 := by
  unfold tailWord_8004743
  simp only [CollatzResearch.WordTrace]
  refine ⟨291956962439190687109018883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194637974959460458072679255 291956962439190687109018883)
  ·
    refine ⟨437935443658786030663528325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291956962439190687109018883 437935443658786030663528325)
    ·
      refine ⟨82112895686022380749411561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 437935443658786030663528325 82112895686022380749411561)
      ·
        refine ⟨61584671764516785562058671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82112895686022380749411561 61584671764516785562058671)
        ·
          refine ⟨92377007646775178343088007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61584671764516785562058671 92377007646775178343088007)
          ·
            refine ⟨138565511470162767514632011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92377007646775178343088007 138565511470162767514632011)
            ·
              refine ⟨207848267205244151271948017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138565511470162767514632011 207848267205244151271948017)
              ·
                refine ⟨155886200403933113453961013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207848267205244151271948017 155886200403933113453961013)
                ·
                  refine ⟨14614331287868729386308845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155886200403933113453961013 14614331287868729386308845)
                  ·
                    refine ⟨5480374232950773519865817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14614331287868729386308845 5480374232950773519865817)
                    ·
                      refine ⟨4110280674713080139899363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480374232950773519865817 4110280674713080139899363)
                      ·
                        rfl

theorem cell23_8004743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_8004743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004743 prefixEnd_8004743 := by exact prefixLift 8004743
  have htrace : WordTrace (prefixWord ++ tailWord_8004743) baseStart_8004743 baseEnd_8004743 := by
    simpa [prefixWord, tailWord_8004743, baseEnd_8004743] using wordTrace_append hprefix tailTrace_8004743
  have hstable : (prefixWord ++ tailWord_8004743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004743).length < 2 ^ (prefixWord ++ tailWord_8004743).sum := by decide
  have hdescent : baseEnd_8004743 < baseStart_8004743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004746 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_8004746 : Nat := 118140960795 + 8004746 * 2 ^ 59
def prefixEnd_8004746 : Nat := 4983230072969 + 3 ^ 40 * 8004746 * 2
def baseEnd_8004746 : Nat := 4110282215155043628161849

theorem tailTrace_8004746 : CollatzResearch.WordTrace tailWord_8004746 prefixEnd_8004746 4110282215155043628161849 := by
  unfold tailWord_8004746
  simp only [CollatzResearch.WordTrace]
  refine ⟨72989267964544954655344523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194638047905453212414252061 72989267964544954655344523)
  ·
    refine ⟨109483901946817431983016785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72989267964544954655344523 109483901946817431983016785)
    ·
      refine ⟨82112926460113073987262589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109483901946817431983016785 82112926460113073987262589)
      ·
        refine ⟨30792347422542402745223471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82112926460113073987262589 30792347422542402745223471)
        ·
          refine ⟨46188521133813604117835207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30792347422542402745223471 46188521133813604117835207)
          ·
            refine ⟨69282781700720406176752811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46188521133813604117835207 69282781700720406176752811)
            ·
              refine ⟨103924172551080609265129217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69282781700720406176752811 103924172551080609265129217)
              ·
                refine ⟨77943129413310456948846913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103924172551080609265129217 77943129413310456948846913)
                ·
                  refine ⟨58457347059982842711635185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77943129413310456948846913 58457347059982842711635185)
                  ·
                    refine ⟨43843010294987132033726389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58457347059982842711635185 43843010294987132033726389)
                    ·
                      refine ⟨4110282215155043628161849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43843010294987132033726389 4110282215155043628161849)
                      ·
                        rfl

theorem cell23_8004746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_8004746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004746 prefixEnd_8004746 := by exact prefixLift 8004746
  have htrace : WordTrace (prefixWord ++ tailWord_8004746) baseStart_8004746 baseEnd_8004746 := by
    simpa [prefixWord, tailWord_8004746, baseEnd_8004746] using wordTrace_append hprefix tailTrace_8004746
  have hstable : (prefixWord ++ tailWord_8004746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004746).length < 2 ^ (prefixWord ++ tailWord_8004746).sum := by decide
  have hdescent : baseEnd_8004746 < baseStart_8004746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004750 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_8004750 : Nat := 118140960795 + 8004750 * 2 ^ 59
def prefixEnd_8004750 : Nat := 4983230072969 + 3 ^ 40 * 8004750 * 2
def baseEnd_8004750 : Nat := 4110284269077661612511831

theorem tailTrace_8004750 : CollatzResearch.WordTrace tailWord_8004750 prefixEnd_8004750 4110284269077661612511831 := by
  unfold tailWord_8004750
  simp only [CollatzResearch.WordTrace]
  refine ⟨36494652218770665913065463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194638145166776884869682469 36494652218770665913065463)
  ·
    refine ⟨54741978328155998869598195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36494652218770665913065463 54741978328155998869598195)
    ·
      refine ⟨82112967492233998304397293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54741978328155998869598195 82112967492233998304397293)
      ·
        refine ⟨30792362809587749364148985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82112967492233998304397293 30792362809587749364148985)
        ·
          refine ⟨23094272107190812023111739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30792362809587749364148985 23094272107190812023111739)
          ·
            refine ⟨34641408160786218034667609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23094272107190812023111739 34641408160786218034667609)
            ·
              refine ⟨25981056120589663526000707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34641408160786218034667609 25981056120589663526000707)
              ·
                refine ⟨38971584180884495289001061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25981056120589663526000707 38971584180884495289001061)
                ·
                  refine ⟨7307172033915842866687699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38971584180884495289001061 7307172033915842866687699)
                  ·
                    refine ⟨10960758050873764300031549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307172033915842866687699 10960758050873764300031549)
                    ·
                      refine ⟨4110284269077661612511831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960758050873764300031549 4110284269077661612511831)
                      ·
                        rfl

theorem cell23_8004750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_8004750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004750 prefixEnd_8004750 := by exact prefixLift 8004750
  have htrace : WordTrace (prefixWord ++ tailWord_8004750) baseStart_8004750 baseEnd_8004750 := by
    simpa [prefixWord, tailWord_8004750, baseEnd_8004750] using wordTrace_append hprefix tailTrace_8004750
  have hstable : (prefixWord ++ tailWord_8004750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004750).length < 2 ^ (prefixWord ++ tailWord_8004750).sum := by decide
  have hdescent : baseEnd_8004750 < baseStart_8004750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004767 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 3]
def baseStart_8004767 : Nat := 118140960795 + 8004767 * 2 ^ 59
def prefixEnd_8004767 : Nat := 4983230072969 + 3 ^ 40 * 8004767 * 2
def baseEnd_8004767 : Nat := 4110292998248788045999253

theorem tailTrace_8004767 : CollatzResearch.WordTrace tailWord_8004767 prefixEnd_8004767 4110292998248788045999253 := by
  unfold tailWord_8004767
  simp only [CollatzResearch.WordTrace]
  refine ⟨291957837791103739207892555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194638558527402492805261703 291957837791103739207892555)
  ·
    refine ⟨437936756686655608811838833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291957837791103739207892555 437936756686655608811838833)
    ·
      refine ⟨328452567514991706608879125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437936756686655608811838833 328452567514991706608879125)
      ·
        refine ⟨15396214102265236247291209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 328452567514991706608879125 15396214102265236247291209)
        ·
          refine ⟨11547160576698927185468407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15396214102265236247291209 11547160576698927185468407)
          ·
            refine ⟨17320740865048390778202611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547160576698927185468407 17320740865048390778202611)
            ·
              refine ⟨25981111297572586167303917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17320740865048390778202611 25981111297572586167303917)
              ·
                refine ⟨9742916736589719812738969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25981111297572586167303917 9742916736589719812738969)
                ·
                  refine ⟨7307187552442289859554227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9742916736589719812738969 7307187552442289859554227)
                  ·
                    refine ⟨10960781328663434789331341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307187552442289859554227 10960781328663434789331341)
                    ·
                      refine ⟨4110292998248788045999253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960781328663434789331341 4110292998248788045999253)
                      ·
                        rfl

theorem cell23_8004767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_8004767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004767 prefixEnd_8004767 := by exact prefixLift 8004767
  have htrace : WordTrace (prefixWord ++ tailWord_8004767) baseStart_8004767 baseEnd_8004767 := by
    simpa [prefixWord, tailWord_8004767, baseEnd_8004767] using wordTrace_append hprefix tailTrace_8004767
  have hstable : (prefixWord ++ tailWord_8004767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004767).length < 2 ^ (prefixWord ++ tailWord_8004767).sum := by decide
  have hdescent : baseEnd_8004767 < baseStart_8004767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004802 : List Nat := [3, 5, 1, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_8004802 : Nat := 118140960795 + 8004802 * 2 ^ 59
def prefixEnd_8004802 : Nat := 4983230072969 + 3 ^ 40 * 8004802 * 2
def baseEnd_8004802 : Nat := 4110310970071695409061593

theorem tailTrace_8004802 : CollatzResearch.WordTrace tailWord_8004802 prefixEnd_8004802 4110310970071695409061593 := by
  unfold tailWord_8004802
  simp only [CollatzResearch.WordTrace]
  refine ⟨72989778586494235046354165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194639409563984626790277773 72989778586494235046354165)
  ·
    refine ⟨6842791742483834535595703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72989778586494235046354165 6842791742483834535595703)
    ·
      refine ⟨10264187613725751803393555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6842791742483834535595703 10264187613725751803393555)
      ·
        refine ⟨15396281420588627705090333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10264187613725751803393555 15396281420588627705090333)
        ·
          refine ⟨5773605532720735389408875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15396281420588627705090333 5773605532720735389408875)
          ·
            refine ⟨8660408299081103084113313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773605532720735389408875 8660408299081103084113313)
            ·
              refine ⟨6495306224310827313084985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8660408299081103084113313 6495306224310827313084985)
              ·
                refine ⟨4871479668233120484813739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6495306224310827313084985 4871479668233120484813739)
                ·
                  refine ⟨7307219502349680727220609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871479668233120484813739 7307219502349680727220609)
                  ·
                    refine ⟨5480414626762260545415457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7307219502349680727220609 5480414626762260545415457)
                    ·
                      refine ⟨4110310970071695409061593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480414626762260545415457 4110310970071695409061593)
                      ·
                        rfl

theorem cell23_8004802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_8004802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004802 prefixEnd_8004802 := by exact prefixLift 8004802
  have htrace : WordTrace (prefixWord ++ tailWord_8004802) baseStart_8004802 baseEnd_8004802 := by
    simpa [prefixWord, tailWord_8004802, baseEnd_8004802] using wordTrace_append hprefix tailTrace_8004802
  have hstable : (prefixWord ++ tailWord_8004802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004802).length < 2 ^ (prefixWord ++ tailWord_8004802).sum := by decide
  have hdescent : baseEnd_8004802 < baseStart_8004802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004826 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_8004826 : Nat := 118140960795 + 8004826 * 2 ^ 59
def prefixEnd_8004826 : Nat := 4983230072969 + 3 ^ 40 * 8004826 * 2
def baseEnd_8004826 : Nat := 1370107764535801105053827

theorem tailTrace_8004826 : CollatzResearch.WordTrace tailWord_8004826 prefixEnd_8004826 1370107764535801105053827 := by
  unfold tailWord_8004826
  simp only [CollatzResearch.WordTrace]
  refine ⟨72989997424472498071072583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194639993131926661522860221 72989997424472498071072583)
  ·
    refine ⟨109484996136708747106608875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72989997424472498071072583 109484996136708747106608875)
    ·
      refine ⟨164227494205063120659913313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109484996136708747106608875 164227494205063120659913313)
      ·
        refine ⟨123170620653797340494934985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164227494205063120659913313 123170620653797340494934985)
        ·
          refine ⟨92377965490348005371201239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123170620653797340494934985 92377965490348005371201239)
          ·
            refine ⟨138566948235522008056801859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92377965490348005371201239 138566948235522008056801859)
            ·
              refine ⟨207850422353283012085202789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138566948235522008056801859 207850422353283012085202789)
              ·
                refine ⟨38971954191240564765975523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207850422353283012085202789 38971954191240564765975523)
                ·
                  refine ⟨58457931286860847148963285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38971954191240564765975523 58457931286860847148963285)
                  ·
                    refine ⟨1370107764535801105053827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58457931286860847148963285 1370107764535801105053827)
                    ·
                      rfl

theorem cell23_8004826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_8004826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004826 prefixEnd_8004826 := by exact prefixLift 8004826
  have htrace : WordTrace (prefixWord ++ tailWord_8004826) baseStart_8004826 baseEnd_8004826 := by
    simpa [prefixWord, tailWord_8004826, baseEnd_8004826] using wordTrace_append hprefix tailTrace_8004826
  have hstable : (prefixWord ++ tailWord_8004826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004826).length < 2 ^ (prefixWord ++ tailWord_8004826).sum := by decide
  have hdescent : baseEnd_8004826 < baseStart_8004826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004836 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_8004836 : Nat := 118140960795 + 8004836 * 2 ^ 59
def prefixEnd_8004836 : Nat := 4983230072969 + 3 ^ 40 * 8004836 * 2
def baseEnd_8004836 : Nat := 4110328428413948276036435

theorem tailTrace_8004836 : CollatzResearch.WordTrace tailWord_8004836 prefixEnd_8004836 4110328428413948276036435 := by
  unfold tailWord_8004836
  simp only [CollatzResearch.WordTrace]
  refine ⟨145980177213926881996077181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194640236285235842661436241 145980177213926881996077181)
  ·
    refine ⟨54742566455222580748528943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145980177213926881996077181 54742566455222580748528943)
    ·
      refine ⟨82113849682833871122793415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54742566455222580748528943 82113849682833871122793415)
      ·
        refine ⟨123170774524250806684190123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82113849682833871122793415 123170774524250806684190123)
        ·
          refine ⟨184756161786376210026285185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123170774524250806684190123 184756161786376210026285185)
          ·
            refine ⟨138567121339782157519713889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184756161786376210026285185 138567121339782157519713889)
            ·
              refine ⟨103925341004836618139785417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138567121339782157519713889 103925341004836618139785417)
              ·
                refine ⟨77944005753627463604839063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103925341004836618139785417 77944005753627463604839063)
                ·
                  refine ⟨116916008630441195407258595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77944005753627463604839063 116916008630441195407258595)
                  ·
                    refine ⟨175374012945661793110887893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116916008630441195407258595 175374012945661793110887893)
                    ·
                      refine ⟨4110328428413948276036435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175374012945661793110887893 4110328428413948276036435)
                      ·
                        rfl

theorem cell23_8004836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_8004836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004836 prefixEnd_8004836 := by exact prefixLift 8004836
  have htrace : WordTrace (prefixWord ++ tailWord_8004836) baseStart_8004836 baseEnd_8004836 := by
    simpa [prefixWord, tailWord_8004836, baseEnd_8004836] using wordTrace_append hprefix tailTrace_8004836
  have hstable : (prefixWord ++ tailWord_8004836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004836).length < 2 ^ (prefixWord ++ tailWord_8004836).sum := by decide
  have hdescent : baseEnd_8004836 < baseStart_8004836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004843 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 2, 5]
def baseStart_8004843 : Nat := 118140960795 + 8004843 * 2 ^ 59
def prefixEnd_8004843 : Nat := 4983230072969 + 3 ^ 40 * 8004843 * 2
def baseEnd_8004843 : Nat := 1370110674259509916216301

theorem tailTrace_8004843 : CollatzResearch.WordTrace tailWord_8004843 prefixEnd_8004843 1370110674259509916216301 := by
  unfold tailWord_8004843
  simp only [CollatzResearch.WordTrace]
  refine ⟨291960609738828404187659183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194640406492552269458439455 291960609738828404187659183)
  ·
    refine ⟨437940914608242606281488775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291960609738828404187659183 437940914608242606281488775)
    ·
      refine ⟨656911371912363909422233163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437940914608242606281488775 656911371912363909422233163)
      ·
        refine ⟨985367057868545864133349745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656911371912363909422233163 985367057868545864133349745)
        ·
          refine ⟨739025293401409398100012309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985367057868545864133349745 739025293401409398100012309)
          ·
            refine ⟨34641810628191065535938077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 739025293401409398100012309 34641810628191065535938077)
            ·
              refine ⟨12990678985571649575976779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34641810628191065535938077 12990678985571649575976779)
              ·
                refine ⟨19486018478357474363965169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12990678985571649575976779 19486018478357474363965169)
                ·
                  refine ⟨14614513858768105772973877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19486018478357474363965169 14614513858768105772973877)
                  ·
                    refine ⟨1370110674259509916216301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14614513858768105772973877 1370110674259509916216301)
                    ·
                      rfl

theorem cell23_8004843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 5].length) (baseStart_8004843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004843 prefixEnd_8004843 := by exact prefixLift 8004843
  have htrace : WordTrace (prefixWord ++ tailWord_8004843) baseStart_8004843 baseEnd_8004843 := by
    simpa [prefixWord, tailWord_8004843, baseEnd_8004843] using wordTrace_append hprefix tailTrace_8004843
  have hstable : (prefixWord ++ tailWord_8004843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004843).length < 2 ^ (prefixWord ++ tailWord_8004843).sum := by decide
  have hdescent : baseEnd_8004843 < baseStart_8004843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004890 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_8004890 : Nat := 118140960795 + 8004890 * 2 ^ 59
def prefixEnd_8004890 : Nat := 4983230072969 + 3 ^ 40 * 8004890 * 2
def baseEnd_8004890 : Nat := 1370118718789763688253729

theorem tailTrace_8004890 : CollatzResearch.WordTrace tailWord_8004890 prefixEnd_8004890 1370118718789763688253729 := by
  unfold tailWord_8004890
  simp only [CollatzResearch.WordTrace]
  refine ⟨72990580992414532803655031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194641549313105420809746749 72990580992414532803655031)
  ·
    refine ⟨109485871488621799205482547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72990580992414532803655031 109485871488621799205482547)
    ·
      refine ⟨164228807232932698808223821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109485871488621799205482547 164228807232932698808223821)
      ·
        refine ⟨61585802712349762053083933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164228807232932698808223821 61585802712349762053083933)
        ·
          refine ⟨23094676017131160769906475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61585802712349762053083933 23094676017131160769906475)
          ·
            refine ⟨34642014025696741154859713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23094676017131160769906475 34642014025696741154859713)
            ·
              refine ⟨25981510519272555866144785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34642014025696741154859713 25981510519272555866144785)
              ·
                refine ⟨19486132889454416899608589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25981510519272555866144785 19486132889454416899608589)
                ·
                  refine ⟨7307299833545406337353221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19486132889454416899608589 7307299833545406337353221)
                  ·
                    refine ⟨1370118718789763688253729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7307299833545406337353221 1370118718789763688253729)
                    ·
                      rfl

theorem cell23_8004890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_8004890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004890 prefixEnd_8004890 := by exact prefixLift 8004890
  have htrace : WordTrace (prefixWord ++ tailWord_8004890) baseStart_8004890 baseEnd_8004890 := by
    simpa [prefixWord, tailWord_8004890, baseEnd_8004890] using wordTrace_append hprefix tailTrace_8004890
  have hstable : (prefixWord ++ tailWord_8004890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004890).length < 2 ^ (prefixWord ++ tailWord_8004890).sum := by decide
  have hdescent : baseEnd_8004890 < baseStart_8004890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004900 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_8004900 : Nat := 118140960795 + 8004900 * 2 ^ 59
def prefixEnd_8004900 : Nat := 4983230072969 + 3 ^ 40 * 8004900 * 2
def baseEnd_8004900 : Nat := 4110361291175836025636141

theorem tailTrace_8004900 : CollatzResearch.WordTrace tailWord_8004900 prefixEnd_8004900 4110361291175836025636141 := by
  unfold tailWord_8004900
  simp only [CollatzResearch.WordTrace]
  refine ⟨145981344349810951461242077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194641792466414601948322769 145981344349810951461242077)
  ·
    refine ⟨54743004131179106797965779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145981344349810951461242077 54743004131179106797965779)
    ·
      refine ⟨82114506196768660196948669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54743004131179106797965779 82114506196768660196948669)
      ·
        refine ⟨30792939823788247573855751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82114506196768660196948669 30792939823788247573855751)
        ·
          refine ⟨46189409735682371360783627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30792939823788247573855751 46189409735682371360783627)
          ·
            refine ⟨69284114603523557041175441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46189409735682371360783627 69284114603523557041175441)
            ·
              refine ⟨51963085952642667780881581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69284114603523557041175441 51963085952642667780881581)
              ·
                refine ⟨19486157232241000417830593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51963085952642667780881581 19486157232241000417830593)
                ·
                  refine ⟨14614617924180750313372945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19486157232241000417830593 14614617924180750313372945)
                  ·
                    refine ⟨10960963443135562735029709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14614617924180750313372945 10960963443135562735029709)
                    ·
                      refine ⟨4110361291175836025636141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10960963443135562735029709 4110361291175836025636141)
                      ·
                        rfl

theorem cell23_8004900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_8004900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004900 prefixEnd_8004900 := by exact prefixLift 8004900
  have htrace : WordTrace (prefixWord ++ tailWord_8004900) baseStart_8004900 baseEnd_8004900 := by
    simpa [prefixWord, tailWord_8004900, baseEnd_8004900] using wordTrace_append hprefix tailTrace_8004900
  have hstable : (prefixWord ++ tailWord_8004900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004900).length < 2 ^ (prefixWord ++ tailWord_8004900).sum := by decide
  have hdescent : baseEnd_8004900 < baseStart_8004900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004924 : List Nat := [2, 2, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_8004924 : Nat := 118140960795 + 8004924 * 2 ^ 59
def prefixEnd_8004924 : Nat := 4983230072969 + 3 ^ 40 * 8004924 * 2
def baseEnd_8004924 : Nat := 1370124538237181310578677

theorem tailTrace_8004924 : CollatzResearch.WordTrace tailWord_8004924 prefixEnd_8004924 1370124538237181310578677 := by
  unfold tailWord_8004924
  simp only [CollatzResearch.WordTrace]
  refine ⟨145981782025767477510678913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194642376034356636680905217 145981782025767477510678913)
  ·
    refine ⟨109486336519325608133009185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145981782025767477510678913 109486336519325608133009185)
    ·
      refine ⟨82114752389494206099756889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109486336519325608133009185 82114752389494206099756889)
      ·
        refine ⟨61586064292120654574817667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82114752389494206099756889 61586064292120654574817667)
        ·
          refine ⟨92379096438180981862226501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61586064292120654574817667 92379096438180981862226501)
          ·
            refine ⟨17321080582158934099167469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92379096438180981862226501 17321080582158934099167469)
            ·
              refine ⟨6495405218309600287187801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17321080582158934099167469 6495405218309600287187801)
              ·
                refine ⟨4871553913732200215390851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6495405218309600287187801 4871553913732200215390851)
                ·
                  refine ⟨7307330870598300323086277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871553913732200215390851 7307330870598300323086277)
                  ·
                    refine ⟨1370124538237181310578677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7307330870598300323086277 1370124538237181310578677)
                    ·
                      rfl

theorem cell23_8004924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_8004924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004924 prefixEnd_8004924 := by exact prefixLift 8004924
  have htrace : WordTrace (prefixWord ++ tailWord_8004924) baseStart_8004924 baseEnd_8004924 := by
    simpa [prefixWord, tailWord_8004924, baseEnd_8004924] using wordTrace_append hprefix tailTrace_8004924
  have hstable : (prefixWord ++ tailWord_8004924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004924).length < 2 ^ (prefixWord ++ tailWord_8004924).sum := by decide
  have hdescent : baseEnd_8004924 < baseStart_8004924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004963 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 3, 6]
def baseStart_8004963 : Nat := 118140960795 + 8004963 * 2 ^ 59
def prefixEnd_8004963 : Nat := 4983230072969 + 3 ^ 40 * 8004963 * 2
def baseEnd_8004963 : Nat := 1370131213485689759716117

theorem tailTrace_8004963 : CollatzResearch.WordTrace tailWord_8004963 prefixEnd_8004963 1370131213485689759716117 := by
  unfold tailWord_8004963
  simp only [CollatzResearch.WordTrace]
  refine ⟨291964986498393664682027543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194643324332262443121351695 291964986498393664682027543)
  ·
    refine ⟨437947479747590497023041315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291964986498393664682027543 437947479747590497023041315)
    ·
      refine ⟨656921219621385745534561973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437947479747590497023041315 656921219621385745534561973)
      ·
        refine ⟨61586364339504913643865185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656921219621385745534561973 61586364339504913643865185)
        ·
          refine ⟨46189773254628685232898889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61586364339504913643865185 46189773254628685232898889)
          ·
            refine ⟨34642329940971513924674167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46189773254628685232898889 34642329940971513924674167)
            ·
              refine ⟨51963494911457270887011251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34642329940971513924674167 51963494911457270887011251)
              ·
                refine ⟨77945242367185906330516877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51963494911457270887011251 77945242367185906330516877)
                ·
                  refine ⟨29229465887694714873943829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77945242367185906330516877 29229465887694714873943829)
                  ·
                    refine ⟨1370131213485689759716117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29229465887694714873943829 1370131213485689759716117)
                    ·
                      rfl

theorem cell23_8004963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 6].length) (baseStart_8004963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004963 prefixEnd_8004963 := by exact prefixLift 8004963
  have htrace : WordTrace (prefixWord ++ tailWord_8004963) baseStart_8004963 baseEnd_8004963 := by
    simpa [prefixWord, tailWord_8004963, baseEnd_8004963] using wordTrace_append hprefix tailTrace_8004963
  have hstable : (prefixWord ++ tailWord_8004963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004963).length < 2 ^ (prefixWord ++ tailWord_8004963).sum := by decide
  have hdescent : baseEnd_8004963 < baseStart_8004963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004981 : List Nat := [1, 3, 4, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_8004981 : Nat := 118140960795 + 8004981 * 2 ^ 59
def prefixEnd_8004981 : Nat := 4983230072969 + 3 ^ 40 * 8004981 * 2
def baseEnd_8004981 : Nat := 4110402883108850208723269

theorem tailTrace_8004981 : CollatzResearch.WordTrace tailWord_8004981 prefixEnd_8004981 4110402883108850208723269 := by
  unfold tailWord_8004981
  simp only [CollatzResearch.WordTrace]
  refine ⟨291965643012328453756182797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194643762008218969170788531 291965643012328453756182797)
  ·
    refine ⟨109487116129623170158568549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291965643012328453756182797 109487116129623170158568549)
    ·
      refine ⟨20528834274304344404731603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109487116129623170158568549 20528834274304344404731603)
      ·
        refine ⟨30793251411456516607097405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20528834274304344404731603 30793251411456516607097405)
        ·
          refine ⟨11547469279296193727661527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30793251411456516607097405 11547469279296193727661527)
          ·
            refine ⟨17321203918944290591492291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547469279296193727661527 17321203918944290591492291)
            ·
              refine ⟨25981805878416435887238437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17321203918944290591492291 25981805878416435887238437)
              ·
                refine ⟨4871588602203081728857207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25981805878416435887238437 4871588602203081728857207)
                ·
                  refine ⟨7307382903304622593285811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871588602203081728857207 7307382903304622593285811)
                  ·
                    refine ⟨10961074354956933889928717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307382903304622593285811 10961074354956933889928717)
                    ·
                      refine ⟨4110402883108850208723269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10961074354956933889928717 4110402883108850208723269)
                      ·
                        rfl

theorem cell23_8004981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_8004981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004981 prefixEnd_8004981 := by exact prefixLift 8004981
  have htrace : WordTrace (prefixWord ++ tailWord_8004981) baseStart_8004981 baseEnd_8004981 := by
    simpa [prefixWord, tailWord_8004981, baseEnd_8004981] using wordTrace_append hprefix tailTrace_8004981
  have hstable : (prefixWord ++ tailWord_8004981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004981).length < 2 ^ (prefixWord ++ tailWord_8004981).sum := by decide
  have hdescent : baseEnd_8004981 < baseStart_8004981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004983 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_8004983 : Nat := 118140960795 + 8004983 * 2 ^ 59
def prefixEnd_8004983 : Nat := 4983230072969 + 3 ^ 40 * 8004983 * 2
def baseEnd_8004983 : Nat := 4110403910070159200898259

theorem tailTrace_8004983 : CollatzResearch.WordTrace tailWord_8004983 prefixEnd_8004983 4110403910070159200898259 := by
  unfold tailWord_8004983
  simp only [CollatzResearch.WordTrace]
  refine ⟨291965715958321208097755603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194643810638880805398503735 291965715958321208097755603)
  ·
    refine ⟨437948573937481812146633405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291965715958321208097755603 437948573937481812146633405)
    ·
      refine ⟨164230715226555679554987527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437948573937481812146633405 164230715226555679554987527)
      ·
        refine ⟨246346072839833519332481291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164230715226555679554987527 246346072839833519332481291)
        ·
          refine ⟨369519109259750278998721937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246346072839833519332481291 369519109259750278998721937)
          ·
            refine ⟨277139331944812709249041453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369519109259750278998721937 277139331944812709249041453)
            ·
              refine ⟨103927249479304765968390545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277139331944812709249041453 103927249479304765968390545)
              ·
                refine ⟨77945437109478574476292909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103927249479304765968390545 77945437109478574476292909)
                ·
                  refine ⟨29229538916054465428609841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77945437109478574476292909 29229538916054465428609841)
                  ·
                    refine ⟨21922154187040849071457381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29229538916054465428609841 21922154187040849071457381)
                    ·
                      refine ⟨4110403910070159200898259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21922154187040849071457381 4110403910070159200898259)
                      ·
                        rfl

theorem cell23_8004983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_8004983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004983 prefixEnd_8004983 := by exact prefixLift 8004983
  have htrace : WordTrace (prefixWord ++ tailWord_8004983) baseStart_8004983 baseEnd_8004983 := by
    simpa [prefixWord, tailWord_8004983, baseEnd_8004983] using wordTrace_append hprefix tailTrace_8004983
  have hstable : (prefixWord ++ tailWord_8004983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004983).length < 2 ^ (prefixWord ++ tailWord_8004983).sum := by decide
  have hdescent : baseEnd_8004983 < baseStart_8004983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8004987 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 3, 2, 2]
def baseStart_8004987 : Nat := 118140960795 + 8004987 * 2 ^ 59
def prefixEnd_8004987 : Nat := 4983230072969 + 3 ^ 40 * 8004987 * 2
def baseEnd_8004987 : Nat := 4110405963992777185248241

theorem tailTrace_8004987 : CollatzResearch.WordTrace tailWord_8004987 prefixEnd_8004987 4110405963992777185248241 := by
  unfold tailWord_8004987
  simp only [CollatzResearch.WordTrace]
  refine ⟨291965861850306716780901215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194643907900204477853934143 291965861850306716780901215)
  ·
    refine ⟨437948792775460075171351823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291965861850306716780901215 437948792775460075171351823)
    ·
      refine ⟨656923189163190112757027735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437948792775460075171351823 656923189163190112757027735)
      ·
        refine ⟨985384783744785169135541603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656923189163190112757027735 985384783744785169135541603)
        ·
          refine ⟨1478077175617177753703312405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985384783744785169135541603 1478077175617177753703312405)
          ·
            refine ⟨69284867607055207204842769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1478077175617177753703312405 69284867607055207204842769)
            ·
              refine ⟨51963650705291405403632077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69284867607055207204842769 51963650705291405403632077)
              ·
                refine ⟨19486369014484277026362029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51963650705291405403632077 19486369014484277026362029)
                ·
                  refine ⟨7307388380431603884885761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19486369014484277026362029 7307388380431603884885761)
                  ·
                    refine ⟨5480541285323702913664321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7307388380431603884885761 5480541285323702913664321)
                    ·
                      refine ⟨4110405963992777185248241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480541285323702913664321 4110405963992777185248241)
                      ·
                        rfl

theorem cell23_8004987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 2, 2].length) (baseStart_8004987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8004987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8004987 prefixEnd_8004987 := by exact prefixLift 8004987
  have htrace : WordTrace (prefixWord ++ tailWord_8004987) baseStart_8004987 baseEnd_8004987 := by
    simpa [prefixWord, tailWord_8004987, baseEnd_8004987] using wordTrace_append hprefix tailTrace_8004987
  have hstable : (prefixWord ++ tailWord_8004987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8004987).length < 2 ^ (prefixWord ++ tailWord_8004987).sum := by decide
  have hdescent : baseEnd_8004987 < baseStart_8004987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8004987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005000 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_8005000 : Nat := 118140960795 + 8005000 * 2 ^ 59
def prefixEnd_8005000 : Nat := 4983230072969 + 3 ^ 40 * 8005000 * 2
def baseEnd_8005000 : Nat := 4110412639241285634385681

theorem tailTrace_8005000 : CollatzResearch.WordTrace tailWord_8005000 prefixEnd_8005000 4110412639241285634385681 := by
  unfold tailWord_8005000
  simp only [CollatzResearch.WordTrace]
  refine ⟨145983167999629810000562227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194644223999506413334082969 145983167999629810000562227)
  ·
    refine ⟨218974751999444715000843341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145983167999629810000562227 218974751999444715000843341)
    ·
      refine ⟨82115531999791768125316253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218974751999444715000843341 82115531999791768125316253)
      ·
        refine ⟨30793324499921913046993595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82115531999791768125316253 30793324499921913046993595)
        ·
          refine ⟨46189986749882869570490393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30793324499921913046993595 46189986749882869570490393)
          ·
            refine ⟨34642490062412152177867795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46189986749882869570490393 34642490062412152177867795)
            ·
              refine ⟨51963735093618228266801693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34642490062412152177867795 51963735093618228266801693)
              ·
                refine ⟨19486400660106835600050635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51963735093618228266801693 19486400660106835600050635)
                ·
                  refine ⟨29229600990160253400075953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19486400660106835600050635 29229600990160253400075953)
                  ·
                    refine ⟨21922200742620190050056965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29229600990160253400075953 21922200742620190050056965)
                    ·
                      refine ⟨4110412639241285634385681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21922200742620190050056965 4110412639241285634385681)
                      ·
                        rfl

theorem cell23_8005000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_8005000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005000 prefixEnd_8005000 := by exact prefixLift 8005000
  have htrace : WordTrace (prefixWord ++ tailWord_8005000) baseStart_8005000 baseEnd_8005000 := by
    simpa [prefixWord, tailWord_8005000, baseEnd_8005000] using wordTrace_append hprefix tailTrace_8005000
  have hstable : (prefixWord ++ tailWord_8005000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005000).length < 2 ^ (prefixWord ++ tailWord_8005000).sum := by decide
  have hdescent : baseEnd_8005000 < baseStart_8005000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005021 : List Nat := [1, 4, 2, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_8005021 : Nat := 118140960795 + 8005021 * 2 ^ 59
def prefixEnd_8005021 : Nat := 4983230072969 + 3 ^ 40 * 8005021 * 2
def baseEnd_8005021 : Nat := 4110423422335030052223085

theorem tailTrace_8005021 : CollatzResearch.WordTrace tailWord_8005021 prefixEnd_8005021 4110423422335030052223085 := by
  unfold tailWord_8005021
  simp only [CollatzResearch.WordTrace]
  refine ⟨291967101932183540587638917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194644734621455693725092611 291967101932183540587638917)
  ·
    refine ⟨54743831612284413860182297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291967101932183540587638917 54743831612284413860182297)
    ·
      refine ⟨41057873709213310395136723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54743831612284413860182297 41057873709213310395136723)
      ·
        refine ⟨61586810563819965592705085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41057873709213310395136723 61586810563819965592705085)
        ·
          refine ⟨23095053961432487097264407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61586810563819965592705085 23095053961432487097264407)
          ·
            refine ⟨34642580942148730645896611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23095053961432487097264407 34642580942148730645896611)
            ·
              refine ⟨51963871413223095968844917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34642580942148730645896611 51963871413223095968844917)
              ·
                refine ⟨4871612944989665247079211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51963871413223095968844917 4871612944989665247079211)
                ·
                  refine ⟨7307419417484497870618817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871612944989665247079211 7307419417484497870618817)
                  ·
                    refine ⟨5480564563113373402964113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7307419417484497870618817 5480564563113373402964113)
                    ·
                      refine ⟨4110423422335030052223085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480564563113373402964113 4110423422335030052223085)
                      ·
                        rfl

theorem cell23_8005021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_8005021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005021 prefixEnd_8005021 := by exact prefixLift 8005021
  have htrace : WordTrace (prefixWord ++ tailWord_8005021) baseStart_8005021 baseEnd_8005021 := by
    simpa [prefixWord, tailWord_8005021, baseEnd_8005021] using wordTrace_append hprefix tailTrace_8005021
  have hstable : (prefixWord ++ tailWord_8005021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005021).length < 2 ^ (prefixWord ++ tailWord_8005021).sum := by decide
  have hdescent : baseEnd_8005021 < baseStart_8005021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005043 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4]
def baseStart_8005043 : Nat := 118140960795 + 8005043 * 2 ^ 59
def prefixEnd_8005043 : Nat := 4983230072969 + 3 ^ 40 * 8005043 * 2
def baseEnd_8005043 : Nat := 4110434718909428966147983

theorem tailTrace_8005043 : CollatzResearch.WordTrace tailWord_8005043 prefixEnd_8005043 4110434718909428966147983 := by
  unfold tailWord_8005043
  simp only [CollatzResearch.WordTrace]
  refine ⟨291967904338103838344939783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194645269558735892229959855 291967904338103838344939783)
  ·
    refine ⟨437951856507155757517409675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291967904338103838344939783 437951856507155757517409675)
    ·
      refine ⟨656927784760733636276114513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437951856507155757517409675 656927784760733636276114513)
      ·
        refine ⟨492695838570550227207085885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656927784760733636276114513 492695838570550227207085885)
        ·
          refine ⟨184760939463956335202657207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492695838570550227207085885 184760939463956335202657207)
          ·
            refine ⟨277141409195934502803985811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184760939463956335202657207 277141409195934502803985811)
            ·
              refine ⟨415712113793901754205978717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277141409195934502803985811 415712113793901754205978717)
              ·
                refine ⟨155892042672713157827242019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415712113793901754205978717 155892042672713157827242019)
                ·
                  refine ⟨233838064009069736740863029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155892042672713157827242019 233838064009069736740863029)
                  ·
                    refine ⟨21922318500850287819455909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233838064009069736740863029 21922318500850287819455909)
                    ·
                      refine ⟨4110434718909428966147983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21922318500850287819455909 4110434718909428966147983)
                      ·
                        rfl

theorem cell23_8005043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_8005043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005043 prefixEnd_8005043 := by exact prefixLift 8005043
  have htrace : WordTrace (prefixWord ++ tailWord_8005043) baseStart_8005043 baseEnd_8005043 := by
    simpa [prefixWord, tailWord_8005043, baseEnd_8005043] using wordTrace_append hprefix tailTrace_8005043
  have hstable : (prefixWord ++ tailWord_8005043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005043).length < 2 ^ (prefixWord ++ tailWord_8005043).sum := by decide
  have hdescent : baseEnd_8005043 < baseStart_8005043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005064 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_8005064 : Nat := 118140960795 + 8005064 * 2 ^ 59
def prefixEnd_8005064 : Nat := 4983230072969 + 3 ^ 40 * 8005064 * 2
def baseEnd_8005064 : Nat := 4110445502003173383985387

theorem tailTrace_8005064 : CollatzResearch.WordTrace tailWord_8005064 prefixEnd_8005064 4110445502003173383985387 := by
  unfold tailWord_8005064
  simp only [CollatzResearch.WordTrace]
  refine ⟨145984335135513879465727123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194645780180685172620969497 145984335135513879465727123)
  ·
    refine ⟨218976502703270819198590685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145984335135513879465727123 218976502703270819198590685)
    ·
      refine ⟨82116188513726557199471507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218976502703270819198590685 82116188513726557199471507)
      ·
        refine ⟨123174282770589835799207261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82116188513726557199471507 123174282770589835799207261)
        ·
          refine ⟨46190356038971188424702723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123174282770589835799207261 46190356038971188424702723)
          ·
            refine ⟨69285534058456782637054085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46190356038971188424702723 69285534058456782637054085)
            ·
              refine ⟨12991037635960646744447641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69285534058456782637054085 12991037635960646744447641)
              ·
                refine ⟨9743278226970485058335731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12991037635960646744447641 9743278226970485058335731)
                ·
                  refine ⟨14614917340455727587503597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9743278226970485058335731 14614917340455727587503597)
                  ·
                    refine ⟨5480594002670897845313849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14614917340455727587503597 5480594002670897845313849)
                    ·
                      refine ⟨4110445502003173383985387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480594002670897845313849 4110445502003173383985387)
                      ·
                        rfl

theorem cell23_8005064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_8005064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005064 prefixEnd_8005064 := by exact prefixLift 8005064
  have htrace : WordTrace (prefixWord ++ tailWord_8005064) baseStart_8005064 baseEnd_8005064 := by
    simpa [prefixWord, tailWord_8005064, baseEnd_8005064] using wordTrace_append hprefix tailTrace_8005064
  have hstable : (prefixWord ++ tailWord_8005064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005064).length < 2 ^ (prefixWord ++ tailWord_8005064).sum := by decide
  have hdescent : baseEnd_8005064 < baseStart_8005064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005077 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_8005077 : Nat := 118140960795 + 8005077 * 2 ^ 59
def prefixEnd_8005077 : Nat := 4983230072969 + 3 ^ 40 * 8005077 * 2
def baseEnd_8005077 : Nat := 4110452177251681833122827

theorem tailTrace_8005077 : CollatzResearch.WordTrace tailWord_8005077 prefixEnd_8005077 4110452177251681833122827 := by
  unfold tailWord_8005077
  simp only [CollatzResearch.WordTrace]
  refine ⟨291969144419980662151677485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194646096279987108101118323 291969144419980662151677485)
  ·
    refine ⟨109488429157492748306879057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291969144419980662151677485 109488429157492748306879057)
    ·
      refine ⟨82116321868119561230159293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109488429157492748306879057 82116321868119561230159293)
      ·
        refine ⟨30793620700544835461309735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82116321868119561230159293 30793620700544835461309735)
        ·
          refine ⟨46190431050817253191964603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30793620700544835461309735 46190431050817253191964603)
          ·
            refine ⟨69285646576225879787946905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46190431050817253191964603 69285646576225879787946905)
            ·
              refine ⟨51964234932169409840960179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69285646576225879787946905 51964234932169409840960179)
              ·
                refine ⟨77946352398254114761440269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51964234932169409840960179 77946352398254114761440269)
                ·
                  refine ⟨29229882149345293035540101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77946352398254114761440269 29229882149345293035540101)
                  ·
                    refine ⟨5480602903002242444163769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29229882149345293035540101 5480602903002242444163769)
                    ·
                      refine ⟨4110452177251681833122827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480602903002242444163769 4110452177251681833122827)
                      ·
                        rfl

theorem cell23_8005077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_8005077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005077 prefixEnd_8005077 := by exact prefixLift 8005077
  have htrace : WordTrace (prefixWord ++ tailWord_8005077) baseStart_8005077 baseEnd_8005077 := by
    simpa [prefixWord, tailWord_8005077, baseEnd_8005077] using wordTrace_append hprefix tailTrace_8005077
  have hstable : (prefixWord ++ tailWord_8005077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005077).length < 2 ^ (prefixWord ++ tailWord_8005077).sum := by decide
  have hdescent : baseEnd_8005077 < baseStart_8005077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005177 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 5, 4]
def baseStart_8005177 : Nat := 118140960795 + 8005177 * 2 ^ 59
def prefixEnd_8005177 : Nat := 4983230072969 + 3 ^ 40 * 8005177 * 2
def baseEnd_8005177 : Nat := 1370167841772377147290789

theorem tailTrace_8005177 : CollatzResearch.WordTrace tailWord_8005177 prefixEnd_8005177 1370167841772377147290789 := by
  unfold tailWord_8005177
  simp only [CollatzResearch.WordTrace]
  refine ⟨291972791719618379230317785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194648527813078919486878523 291972791719618379230317785)
  ·
    refine ⟨218979593789713784422738339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291972791719618379230317785 218979593789713784422738339)
    ·
      refine ⟨328469390684570676634107509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218979593789713784422738339 328469390684570676634107509)
      ·
        refine ⟨30794005376678500934447579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328469390684570676634107509 30794005376678500934447579)
        ·
          refine ⟨46191008065017751401671369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30794005376678500934447579 46191008065017751401671369)
          ·
            refine ⟨34643256048763313551253527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46191008065017751401671369 34643256048763313551253527)
            ·
              refine ⟨51964884073144970326880291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34643256048763313551253527 51964884073144970326880291)
              ·
                refine ⟨77947326109717455490320437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51964884073144970326880291 77947326109717455490320437)
                ·
                  refine ⟨7307561822786011452217541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77947326109717455490320437 7307561822786011452217541)
                  ·
                    refine ⟨1370167841772377147290789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7307561822786011452217541 1370167841772377147290789)
                    ·
                      rfl

theorem cell23_8005177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_8005177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005177 prefixEnd_8005177 := by exact prefixLift 8005177
  have htrace : WordTrace (prefixWord ++ tailWord_8005177) baseStart_8005177 baseEnd_8005177 := by
    simpa [prefixWord, tailWord_8005177, baseEnd_8005177] using wordTrace_append hprefix tailTrace_8005177
  have hstable : (prefixWord ++ tailWord_8005177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005177).length < 2 ^ (prefixWord ++ tailWord_8005177).sum := by decide
  have hdescent : baseEnd_8005177 < baseStart_8005177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005181 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_8005181 : Nat := 118140960795 + 8005181 * 2 ^ 59
def prefixEnd_8005181 : Nat := 4983230072969 + 3 ^ 40 * 8005181 * 2
def baseEnd_8005181 : Nat := 1370168526413249808740783

theorem tailTrace_8005181 : CollatzResearch.WordTrace tailWord_8005181 prefixEnd_8005181 1370168526413249808740783 := by
  unfold tailWord_8005181
  simp only [CollatzResearch.WordTrace]
  refine ⟨291972937611603887913463397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194648625074402591942308931 291972937611603887913463397)
  ·
    refine ⟨54744925802175728983774387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291972937611603887913463397 54744925802175728983774387)
    ·
      refine ⟨82117388703263593475661581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54744925802175728983774387 82117388703263593475661581)
      ·
        refine ⟨30794020763723847553373093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82117388703263593475661581 30794020763723847553373093)
        ·
          refine ⟨5773878893198221416257455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30794020763723847553373093 5773878893198221416257455)
          ·
            refine ⟨8660818339797332124386183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773878893198221416257455 8660818339797332124386183)
            ·
              refine ⟨12991227509695998186579275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660818339797332124386183 12991227509695998186579275)
              ·
                refine ⟨19486841264543997279868913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12991227509695998186579275 19486841264543997279868913)
                ·
                  refine ⟨14615130948407997959901685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19486841264543997279868913 14615130948407997959901685)
                  ·
                    refine ⟨1370168526413249808740783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14615130948407997959901685 1370168526413249808740783)
                    ·
                      rfl

theorem cell23_8005181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_8005181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005181 prefixEnd_8005181 := by exact prefixLift 8005181
  have htrace : WordTrace (prefixWord ++ tailWord_8005181) baseStart_8005181 baseEnd_8005181 := by
    simpa [prefixWord, tailWord_8005181, baseEnd_8005181] using wordTrace_append hprefix tailTrace_8005181
  have hstable : (prefixWord ++ tailWord_8005181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005181).length < 2 ^ (prefixWord ++ tailWord_8005181).sum := by decide
  have hdescent : baseEnd_8005181 < baseStart_8005181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005207 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 6]
def baseStart_8005207 : Nat := 118140960795 + 8005207 * 2 ^ 59
def prefixEnd_8005207 : Nat := 4983230072969 + 3 ^ 40 * 8005207 * 2
def baseEnd_8005207 : Nat := 456724325526307369388581

theorem tailTrace_8005207 : CollatzResearch.WordTrace tailWord_8005207 prefixEnd_8005207 456724325526307369388581 := by
  unfold tailWord_8005207
  simp only [CollatzResearch.WordTrace]
  refine ⟨291973885909509694353909875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194649257273006462902606583 291973885909509694353909875)
  ·
    refine ⟨437960828864264541530864813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291973885909509694353909875 437960828864264541530864813)
    ·
      refine ⟨164235310824099203074074305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437960828864264541530864813 164235310824099203074074305)
      ·
        refine ⟨123176483118074402305555729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164235310824099203074074305 123176483118074402305555729)
        ·
          refine ⟨92382362338555801729166797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123176483118074402305555729 92382362338555801729166797)
          ·
            refine ⟨34643385876958425648437549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92382362338555801729166797 34643385876958425648437549)
            ·
              refine ⟨12991269703859409618164081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34643385876958425648437549 12991269703859409618164081)
              ·
                refine ⟨9743452277894557213623061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12991269703859409618164081 9743452277894557213623061)
                ·
                  refine ⟨456724325526307369388581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9743452277894557213623061 456724325526307369388581)
                  ·
                    rfl

theorem cell23_8005207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 6].length) (baseStart_8005207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005207 prefixEnd_8005207 := by exact prefixLift 8005207
  have htrace : WordTrace (prefixWord ++ tailWord_8005207) baseStart_8005207 baseEnd_8005207 := by
    simpa [prefixWord, tailWord_8005207, baseEnd_8005207] using wordTrace_append hprefix tailTrace_8005207
  have hstable : (prefixWord ++ tailWord_8005207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005207).length < 2 ^ (prefixWord ++ tailWord_8005207).sum := by decide
  have hdescent : baseEnd_8005207 < baseStart_8005207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005244 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_8005244 : Nat := 118140960795 + 8005244 * 2 ^ 59
def prefixEnd_8005244 : Nat := 4983230072969 + 3 ^ 40 * 8005244 * 2
def baseEnd_8005244 : Nat := 4110537928520982679734559

theorem tailTrace_8005244 : CollatzResearch.WordTrace tailWord_8005244 prefixEnd_8005244 4110537928520982679734559 := by
  unfold tailWord_8005244
  simp only [CollatzResearch.WordTrace]
  refine ⟨145987617705187824836503393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194650156940250433115337857 145987617705187824836503393)
  ·
    refine ⟨109490713278890868627377545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145987617705187824836503393 109490713278890868627377545)
    ·
      refine ⟨82118034959168151470533159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109490713278890868627377545 82118034959168151470533159)
      ·
        refine ⟨123177052438752227205799739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82118034959168151470533159 123177052438752227205799739)
        ·
          refine ⟨184765578658128340808699609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123177052438752227205799739 184765578658128340808699609)
          ·
            refine ⟨138574183993596255606524707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184765578658128340808699609 138574183993596255606524707)
            ·
              refine ⟨207861275990394383409787061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138574183993596255606524707 207861275990394383409787061)
              ·
                refine ⟨19486994624099473444667537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207861275990394383409787061 19486994624099473444667537)
                ·
                  refine ⟨14615245968074605083500653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19486994624099473444667537 14615245968074605083500653)
                  ·
                    refine ⟨5480717238027976906312745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14615245968074605083500653 5480717238027976906312745)
                    ·
                      refine ⟨4110537928520982679734559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480717238027976906312745 4110537928520982679734559)
                      ·
                        rfl

theorem cell23_8005244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_8005244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005244 prefixEnd_8005244 := by exact prefixLift 8005244
  have htrace : WordTrace (prefixWord ++ tailWord_8005244) baseStart_8005244 baseEnd_8005244 := by
    simpa [prefixWord, tailWord_8005244, baseEnd_8005244] using wordTrace_append hprefix tailTrace_8005244
  have hstable : (prefixWord ++ tailWord_8005244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005244).length < 2 ^ (prefixWord ++ tailWord_8005244).sum := by decide
  have hdescent : baseEnd_8005244 < baseStart_8005244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005277 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_8005277 : Nat := 118140960795 + 8005277 * 2 ^ 59
def prefixEnd_8005277 : Nat := 4983230072969 + 3 ^ 40 * 8005277 * 2
def baseEnd_8005277 : Nat := 4110554873382581050621907

theorem tailTrace_8005277 : CollatzResearch.WordTrace tailWord_8005277 prefixEnd_8005277 4110554873382581050621907 := by
  unfold tailWord_8005277
  simp only [CollatzResearch.WordTrace]
  refine ⟨291976439019256096308958085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194650959346170730872638723 291976439019256096308958085)
  ·
    refine ⟨54745582316110518057929641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291976439019256096308958085 54745582316110518057929641)
    ·
      refine ⟨41059186737082888543447231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54745582316110518057929641 41059186737082888543447231)
      ·
        refine ⟨61588780105624332815170847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41059186737082888543447231 61588780105624332815170847)
        ·
          refine ⟨92383170158436499222756271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61588780105624332815170847 92383170158436499222756271)
          ·
            refine ⟨138574755237654748834134407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92383170158436499222756271 138574755237654748834134407)
            ·
              refine ⟨207862132856482123251201611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138574755237654748834134407 207862132856482123251201611)
              ·
                refine ⟨311793199284723184876802417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207862132856482123251201611 311793199284723184876802417)
                ·
                  refine ⟨233844899463542388657601813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311793199284723184876802417 233844899463542388657601813)
                  ·
                    refine ⟨10961479662353549468325085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 233844899463542388657601813 10961479662353549468325085)
                    ·
                      refine ⟨4110554873382581050621907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10961479662353549468325085 4110554873382581050621907)
                      ·
                        rfl

theorem cell23_8005277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_8005277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005277 prefixEnd_8005277 := by exact prefixLift 8005277
  have htrace : WordTrace (prefixWord ++ tailWord_8005277) baseStart_8005277 baseEnd_8005277 := by
    simpa [prefixWord, tailWord_8005277, baseEnd_8005277] using wordTrace_append hprefix tailTrace_8005277
  have hstable : (prefixWord ++ tailWord_8005277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005277).length < 2 ^ (prefixWord ++ tailWord_8005277).sum := by decide
  have hdescent : baseEnd_8005277 < baseStart_8005277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005288 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 3, 5]
def baseStart_8005288 : Nat := 118140960795 + 8005288 * 2 ^ 59
def prefixEnd_8005288 : Nat := 4983230072969 + 3 ^ 40 * 8005288 * 2
def baseEnd_8005288 : Nat := 1370186840556593502528119

theorem tailTrace_8005288 : CollatzResearch.WordTrace tailWord_8005288 prefixEnd_8005288 1370186840556593502528119 := by
  unfold tailWord_8005288
  simp only [CollatzResearch.WordTrace]
  refine ⟨145988420111108122593804259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194651226814810830125072345 145988420111108122593804259)
  ·
    refine ⟨218982630166662183890706389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145988420111108122593804259 218982630166662183890706389)
    ·
      refine ⟨5132405394531144934938431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 218982630166662183890706389 5132405394531144934938431)
      ·
        refine ⟨7698608091796717402407647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132405394531144934938431 7698608091796717402407647)
        ·
          refine ⟨11547912137695076103611471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7698608091796717402407647 11547912137695076103611471)
          ·
            refine ⟨17321868206542614155417207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11547912137695076103611471 17321868206542614155417207)
            ·
              refine ⟨25982802309813921233125811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17321868206542614155417207 25982802309813921233125811)
              ·
                refine ⟨38974203464720881849688717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25982802309813921233125811 38974203464720881849688717)
                ·
                  refine ⟨14615326299270330693633269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38974203464720881849688717 14615326299270330693633269)
                  ·
                    refine ⟨1370186840556593502528119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14615326299270330693633269 1370186840556593502528119)
                    ·
                      rfl

theorem cell23_8005288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_8005288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005288 prefixEnd_8005288 := by exact prefixLift 8005288
  have htrace : WordTrace (prefixWord ++ tailWord_8005288) baseStart_8005288 baseEnd_8005288 := by
    simpa [prefixWord, tailWord_8005288, baseEnd_8005288] using wordTrace_append hprefix tailTrace_8005288
  have hstable : (prefixWord ++ tailWord_8005288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005288).length < 2 ^ (prefixWord ++ tailWord_8005288).sum := by decide
  have hdescent : baseEnd_8005288 < baseStart_8005288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005311 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 1, 2, 3]
def baseStart_8005311 : Nat := 118140960795 + 8005311 * 2 ^ 59
def prefixEnd_8005311 : Nat := 4983230072969 + 3 ^ 40 * 8005311 * 2
def baseEnd_8005311 : Nat := 4110572331724833917596751

theorem tailTrace_8005311 : CollatzResearch.WordTrace tailWord_8005311 prefixEnd_8005311 4110572331724833917596751 := by
  unfold tailWord_8005311
  simp only [CollatzResearch.WordTrace]
  refine ⟨291977679101132920115695787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194651786067421946743797191 291977679101132920115695787)
  ·
    refine ⟨437966518651699380173543681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291977679101132920115695787 437966518651699380173543681)
    ·
      refine ⟨328474888988774535130157761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437966518651699380173543681 328474888988774535130157761)
      ·
        refine ⟨246356166741580901347618321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328474888988774535130157761 246356166741580901347618321)
        ·
          refine ⟨184767125056185676010713741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246356166741580901347618321 184767125056185676010713741)
          ·
            refine ⟨69287671896069628504017653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184767125056185676010713741 69287671896069628504017653)
            ·
              refine ⟨6495719240256527672251655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69287671896069628504017653 6495719240256527672251655)
              ·
                refine ⟨9743578860384791508377483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495719240256527672251655 9743578860384791508377483)
                ·
                  refine ⟨14615368290577187262566225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9743578860384791508377483 14615368290577187262566225)
                  ·
                    refine ⟨10961526217932890446924669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14615368290577187262566225 10961526217932890446924669)
                    ·
                      refine ⟨4110572331724833917596751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10961526217932890446924669 4110572331724833917596751)
                      ·
                        rfl

theorem cell23_8005311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_8005311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005311 prefixEnd_8005311 := by exact prefixLift 8005311
  have htrace : WordTrace (prefixWord ++ tailWord_8005311) baseStart_8005311 baseEnd_8005311 := by
    simpa [prefixWord, tailWord_8005311, baseEnd_8005311] using wordTrace_append hprefix tailTrace_8005311
  have hstable : (prefixWord ++ tailWord_8005311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005311).length < 2 ^ (prefixWord ++ tailWord_8005311).sum := by decide
  have hdescent : baseEnd_8005311 < baseStart_8005311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005367 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_8005367 : Nat := 118140960795 + 8005367 * 2 ^ 59
def prefixEnd_8005367 : Nat := 4983230072969 + 3 ^ 40 * 8005367 * 2
def baseEnd_8005367 : Nat := 4110601086641485698496493

theorem tailTrace_8005367 : CollatzResearch.WordTrace tailWord_8005367 prefixEnd_8005367 4110601086641485698496493 := by
  unfold tailWord_8005367
  simp only [CollatzResearch.WordTrace]
  refine ⟨291979721588930041679734355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194653147725953361119822903 291979721588930041679734355)
  ·
    refine ⟨437969582383395062519601533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291979721588930041679734355 437969582383395062519601533)
    ·
      refine ⟨164238593393773148444850575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437969582383395062519601533 164238593393773148444850575)
      ·
        refine ⟨246357890090659722667275863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164238593393773148444850575 246357890090659722667275863)
        ·
          refine ⟨369536835135989584000913795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246357890090659722667275863 369536835135989584000913795)
          ·
            refine ⟨554305252703984376001370693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369536835135989584000913795 554305252703984376001370693)
            ·
              refine ⟨103932234881997070500257005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 554305252703984376001370693 103932234881997070500257005)
              ·
                refine ⟨38974588080748901437596377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103932234881997070500257005 38974588080748901437596377)
                ·
                  refine ⟨29230941060561676078197283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38974588080748901437596377 29230941060561676078197283)
                  ·
                    refine ⟨43846411590842514117295925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29230941060561676078197283 43846411590842514117295925)
                    ·
                      refine ⟨4110601086641485698496493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43846411590842514117295925 4110601086641485698496493)
                      ·
                        rfl

theorem cell23_8005367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_8005367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005367 prefixEnd_8005367 := by exact prefixLift 8005367
  have htrace : WordTrace (prefixWord ++ tailWord_8005367) baseStart_8005367 baseEnd_8005367 := by
    simpa [prefixWord, tailWord_8005367, baseEnd_8005367] using wordTrace_append hprefix tailTrace_8005367
  have hstable : (prefixWord ++ tailWord_8005367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005367).length < 2 ^ (prefixWord ++ tailWord_8005367).sum := by decide
  have hdescent : baseEnd_8005367 < baseStart_8005367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005387 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 7]
def baseStart_8005387 : Nat := 118140960795 + 8005387 * 2 ^ 59
def prefixEnd_8005387 : Nat := 4983230072969 + 3 ^ 40 * 8005387 * 2
def baseEnd_8005387 : Nat := 456734595139397291138489

theorem tailTrace_8005387 : CollatzResearch.WordTrace tailWord_8005387 prefixEnd_8005387 456734595139397291138489 := by
  unfold tailWord_8005387
  simp only [CollatzResearch.WordTrace]
  refine ⟨291980451048857585095462415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194653634032571723396974943 291980451048857585095462415)
  ·
    refine ⟨437970676573286377643193623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291980451048857585095462415 437970676573286377643193623)
    ·
      refine ⟨656956014859929566464790435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437970676573286377643193623 656956014859929566464790435)
      ·
        refine ⟨985434022289894349697185653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656956014859929566464790435 985434022289894349697185653)
        ·
          refine ⟨92384439589677595284111155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 985434022289894349697185653 92384439589677595284111155)
          ·
            refine ⟨138576659384516392926166733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92384439589677595284111155 138576659384516392926166733)
            ·
              refine ⟨51966247269193647347312525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138576659384516392926166733 51966247269193647347312525)
              ·
                refine ⟨19487342725947617755242197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51966247269193647347312525 19487342725947617755242197)
                ·
                  refine ⟨456734595139397291138489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19487342725947617755242197 456734595139397291138489)
                  ·
                    rfl

theorem cell23_8005387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 7].length) (baseStart_8005387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005387 prefixEnd_8005387 := by exact prefixLift 8005387
  have htrace : WordTrace (prefixWord ++ tailWord_8005387) baseStart_8005387 baseEnd_8005387 := by
    simpa [prefixWord, tailWord_8005387, baseEnd_8005387] using wordTrace_append hprefix tailTrace_8005387
  have hstable : (prefixWord ++ tailWord_8005387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005387).length < 2 ^ (prefixWord ++ tailWord_8005387).sum := by decide
  have hdescent : baseEnd_8005387 < baseStart_8005387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005389 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_8005389 : Nat := 118140960795 + 8005389 * 2 ^ 59
def prefixEnd_8005389 : Nat := 4983230072969 + 3 ^ 40 * 8005389 * 2
def baseEnd_8005389 : Nat := 4110612383215884612421393

theorem tailTrace_8005389 : CollatzResearch.WordTrace tailWord_8005389 prefixEnd_8005389 4110612383215884612421393 := by
  unfold tailWord_8005389
  simp only [CollatzResearch.WordTrace]
  refine ⟨291980523994850339437035221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194653682663233559624690147 291980523994850339437035221)
  ·
    refine ⟨6843293531129304830555513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 291980523994850339437035221 6843293531129304830555513)
    ·
      refine ⟨5132470148346978622916635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6843293531129304830555513 5132470148346978622916635)
      ·
        refine ⟨7698705222520467934374953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132470148346978622916635 7698705222520467934374953)
        ·
          refine ⟨5774028916890350950781215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7698705222520467934374953 5774028916890350950781215)
          ·
            refine ⟨8661043375335526426171823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5774028916890350950781215 8661043375335526426171823)
            ·
              refine ⟨12991565063003289639257735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8661043375335526426171823 12991565063003289639257735)
              ·
                refine ⟨19487347594504934458886603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12991565063003289639257735 19487347594504934458886603)
                ·
                  refine ⟨29231021391757401688329905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19487347594504934458886603 29231021391757401688329905)
                  ·
                    refine ⟨21923266043818051266247429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29231021391757401688329905 21923266043818051266247429)
                    ·
                      refine ⟨4110612383215884612421393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21923266043818051266247429 4110612383215884612421393)
                      ·
                        rfl

theorem cell23_8005389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_8005389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005389 prefixEnd_8005389 := by exact prefixLift 8005389
  have htrace : WordTrace (prefixWord ++ tailWord_8005389) baseStart_8005389 baseEnd_8005389 := by
    simpa [prefixWord, tailWord_8005389, baseEnd_8005389] using wordTrace_append hprefix tailTrace_8005389
  have hstable : (prefixWord ++ tailWord_8005389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005389).length < 2 ^ (prefixWord ++ tailWord_8005389).sum := by decide
  have hdescent : baseEnd_8005389 < baseStart_8005389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005424 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 7, 2]
def baseStart_8005424 : Nat := 118140960795 + 8005424 * 2 ^ 59
def prefixEnd_8005424 : Nat := 4983230072969 + 3 ^ 40 * 8005424 * 2
def baseEnd_8005424 : Nat := 4110630355038791975483731

theorem tailTrace_8005424 : CollatzResearch.WordTrace tailWord_8005424 prefixEnd_8005424 4110630355038791975483731 := by
  unfold tailWord_8005424
  simp only [CollatzResearch.WordTrace]
  refine ⟨145990900274861770207279663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194654533699815693609706217 145990900274861770207279663)
  ·
    refine ⟨218986350412292655310919495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145990900274861770207279663 218986350412292655310919495)
    ·
      refine ⟨328479525618438982966379243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218986350412292655310919495 328479525618438982966379243)
      ·
        refine ⟨492719288427658474449568865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328479525618438982966379243 492719288427658474449568865)
        ·
          refine ⟨369539466320743855837176649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492719288427658474449568865 369539466320743855837176649)
          ·
            refine ⟨277154599740557891877882487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369539466320743855837176649 277154599740557891877882487)
            ·
              refine ⟨415731899610836837816823731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277154599740557891877882487 415731899610836837816823731)
              ·
                refine ⟨623597849416255256725235597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415731899610836837816823731 623597849416255256725235597)
                ·
                  refine ⟨233849193531095721271963349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623597849416255256725235597 233849193531095721271963349)
                  ·
                    refine ⟨5480840473385055967311641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 233849193531095721271963349 5480840473385055967311641)
                    ·
                      refine ⟨4110630355038791975483731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480840473385055967311641 4110630355038791975483731)
                      ·
                        rfl

theorem cell23_8005424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 7, 2].length) (baseStart_8005424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005424 prefixEnd_8005424 := by exact prefixLift 8005424
  have htrace : WordTrace (prefixWord ++ tailWord_8005424) baseStart_8005424 baseEnd_8005424 := by
    simpa [prefixWord, tailWord_8005424, baseEnd_8005424] using wordTrace_append hprefix tailTrace_8005424
  have hstable : (prefixWord ++ tailWord_8005424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005424).length < 2 ^ (prefixWord ++ tailWord_8005424).sum := by decide
  have hdescent : baseEnd_8005424 < baseStart_8005424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005434 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_8005434 : Nat := 118140960795 + 8005434 * 2 ^ 59
def prefixEnd_8005434 : Nat := 4983230072969 + 3 ^ 40 * 8005434 * 2
def baseEnd_8005434 : Nat := 1370211829948445645452895

theorem tailTrace_8005434 : CollatzResearch.WordTrace tailWord_8005434 prefixEnd_8005434 1370211829948445645452895 := by
  unfold tailWord_8005434
  simp only [CollatzResearch.WordTrace]
  refine ⟨72995541319921828030605839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194654776853124874748282237 72995541319921828030605839)
  ·
    refine ⟨109493311979882742045908759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72995541319921828030605839 109493311979882742045908759)
    ·
      refine ⟨164239967969824113068863139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109493311979882742045908759 164239967969824113068863139)
      ·
        refine ⟨246359951954736169603294709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164239967969824113068863139 246359951954736169603294709)
        ·
          refine ⟨23096245495756515900308879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246359951954736169603294709 23096245495756515900308879)
          ·
            refine ⟨34644368243634773850463319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23096245495756515900308879 34644368243634773850463319)
            ·
              refine ⟨51966552365452160775694979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34644368243634773850463319 51966552365452160775694979)
              ·
                refine ⟨77949828548178241163542469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51966552365452160775694979 77949828548178241163542469)
                ·
                  refine ⟨14615592852783420218164213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77949828548178241163542469 14615592852783420218164213)
                  ·
                    refine ⟨1370211829948445645452895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14615592852783420218164213 1370211829948445645452895)
                    ·
                      rfl

theorem cell23_8005434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_8005434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005434 prefixEnd_8005434 := by exact prefixLift 8005434
  have htrace : WordTrace (prefixWord ++ tailWord_8005434) baseStart_8005434 baseEnd_8005434 := by
    simpa [prefixWord, tailWord_8005434, baseEnd_8005434] using wordTrace_append hprefix tailTrace_8005434
  have hstable : (prefixWord ++ tailWord_8005434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005434).length < 2 ^ (prefixWord ++ tailWord_8005434).sum := by decide
  have hdescent : baseEnd_8005434 < baseStart_8005434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005468 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_8005468 : Nat := 118140960795 + 8005468 * 2 ^ 59
def prefixEnd_8005468 : Nat := 4983230072969 + 3 ^ 40 * 8005468 * 2
def baseEnd_8005468 : Nat := 1370217649395863267777843

theorem tailTrace_8005468 : CollatzResearch.WordTrace tailWord_8005468 prefixEnd_8005468 1370217649395863267777843 := by
  unfold tailWord_8005468
  simp only [CollatzResearch.WordTrace]
  refine ⟨145991702680782067964580529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194655603574376090619440705 145991702680782067964580529)
  ·
    refine ⟨109493777010586550973435397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145991702680782067964580529 109493777010586550973435397)
    ·
      refine ⟨20530083189484978307519137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109493777010586550973435397 20530083189484978307519137)
      ·
        refine ⟨15397562392113733730639353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20530083189484978307519137 15397562392113733730639353)
        ·
          refine ⟨11548171794085300297979515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15397562392113733730639353 11548171794085300297979515)
          ·
            refine ⟨17322257691127950446969273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548171794085300297979515 17322257691127950446969273)
            ·
              refine ⟨12991693268345962835226955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17322257691127950446969273 12991693268345962835226955)
              ·
                refine ⟨19487539902518944252840433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12991693268345962835226955 19487539902518944252840433)
                ·
                  refine ⟨14615654926889208189630325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19487539902518944252840433 14615654926889208189630325)
                  ·
                    refine ⟨1370217649395863267777843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14615654926889208189630325 1370217649395863267777843)
                    ·
                      rfl

theorem cell23_8005468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_8005468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005468 prefixEnd_8005468 := by exact prefixLift 8005468
  have htrace : WordTrace (prefixWord ++ tailWord_8005468) baseStart_8005468 baseEnd_8005468 := by
    simpa [prefixWord, tailWord_8005468, baseEnd_8005468] using wordTrace_append hprefix tailTrace_8005468
  have hstable : (prefixWord ++ tailWord_8005468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005468).length < 2 ^ (prefixWord ++ tailWord_8005468).sum := by decide
  have hdescent : baseEnd_8005468 < baseStart_8005468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005471 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 4]
def baseStart_8005471 : Nat := 118140960795 + 8005471 * 2 ^ 59
def prefixEnd_8005471 : Nat := 4983230072969 + 3 ^ 40 * 8005471 * 2
def baseEnd_8005471 : Nat := 4110654488629553291596015

theorem tailTrace_8005471 : CollatzResearch.WordTrace tailWord_8005471 prefixEnd_8005471 4110654488629553291596015 := by
  unfold tailWord_8005471
  simp only [CollatzResearch.WordTrace]
  refine ⟨291983514780553267441520267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194655676520368844961013511 291983514780553267441520267)
  ·
    refine ⟨437975272170829901162280401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291983514780553267441520267 437975272170829901162280401)
    ·
      refine ⟨328481454128122425871710301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437975272170829901162280401 328481454128122425871710301)
      ·
        refine ⟨123180545298045909701891363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328481454128122425871710301 123180545298045909701891363)
        ·
          refine ⟨184770817947068864552837045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123180545298045909701891363 184770817947068864552837045)
          ·
            refine ⟨17322264182537706051828473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184770817947068864552837045 17322264182537706051828473)
            ·
              refine ⟨12991698136903279538871355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17322264182537706051828473 12991698136903279538871355)
              ·
                refine ⟨19487547205354919308307033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12991698136903279538871355 19487547205354919308307033)
                ·
                  refine ⟨14615660404016189481230275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19487547205354919308307033 14615660404016189481230275)
                  ·
                    refine ⟨21923490606024284221845413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14615660404016189481230275 21923490606024284221845413)
                    ·
                      refine ⟨4110654488629553291596015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21923490606024284221845413 4110654488629553291596015)
                      ·
                        rfl

theorem cell23_8005471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_8005471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005471 prefixEnd_8005471 := by exact prefixLift 8005471
  have htrace : WordTrace (prefixWord ++ tailWord_8005471) baseStart_8005471 baseEnd_8005471 := by
    simpa [prefixWord, tailWord_8005471, baseEnd_8005471] using wordTrace_append hprefix tailTrace_8005471
  have hstable : (prefixWord ++ tailWord_8005471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005471).length < 2 ^ (prefixWord ++ tailWord_8005471).sum := by decide
  have hdescent : baseEnd_8005471 < baseStart_8005471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005505 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_8005505 : Nat := 118140960795 + 8005505 * 2 ^ 59
def prefixEnd_8005505 : Nat := 4983230072969 + 3 ^ 40 * 8005505 * 2
def baseEnd_8005505 : Nat := 4110671946971806158570859

theorem tailTrace_8005505 : CollatzResearch.WordTrace tailWord_8005505 prefixEnd_8005505 4110671946971806158570859 := by
  unfold tailWord_8005505
  simp only [CollatzResearch.WordTrace]
  refine ⟨291984754862430091248257969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194656503241620060832171979 291984754862430091248257969)
  ·
    refine ⟨218988566146822568436193477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291984754862430091248257969 218988566146822568436193477)
    ·
      refine ⟨41060356152529231581786277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218988566146822568436193477 41060356152529231581786277)
      ·
        refine ⟨7698816778599230921584927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41060356152529231581786277 7698816778599230921584927)
        ·
          refine ⟨11548225167898846382377391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7698816778599230921584927 11548225167898846382377391)
          ·
            refine ⟨17322337751848269573566087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548225167898846382377391 17322337751848269573566087)
            ·
              refine ⟨25983506627772404360349131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17322337751848269573566087 25983506627772404360349131)
              ·
                refine ⟨38975259941658606540523697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25983506627772404360349131 38975259941658606540523697)
                ·
                  refine ⟨29231444956243954905392773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38975259941658606540523697 29231444956243954905392773)
                  ·
                    refine ⟨5480895929295741544761145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29231444956243954905392773 5480895929295741544761145)
                    ·
                      refine ⟨4110671946971806158570859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5480895929295741544761145 4110671946971806158570859)
                      ·
                        rfl

theorem cell23_8005505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_8005505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005505 prefixEnd_8005505 := by exact prefixLift 8005505
  have htrace : WordTrace (prefixWord ++ tailWord_8005505) baseStart_8005505 baseEnd_8005505 := by
    simpa [prefixWord, tailWord_8005505, baseEnd_8005505] using wordTrace_append hprefix tailTrace_8005505
  have hstable : (prefixWord ++ tailWord_8005505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005505).length < 2 ^ (prefixWord ++ tailWord_8005505).sum := by decide
  have hdescent : baseEnd_8005505 < baseStart_8005505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005521 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_8005521 : Nat := 118140960795 + 8005521 * 2 ^ 59
def prefixEnd_8005521 : Nat := 4983230072969 + 3 ^ 40 * 8005521 * 2
def baseEnd_8005521 : Nat := 4110680162662278095970785

theorem tailTrace_8005521 : CollatzResearch.WordTrace tailWord_8005521 prefixEnd_8005521 4110680162662278095970785 := by
  unfold tailWord_8005521
  simp only [CollatzResearch.WordTrace]
  refine ⟨291985338430372125980840417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194656892286914750653893611 291985338430372125980840417)
  ·
    refine ⟨218989003822779094485630313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291985338430372125980840417 218989003822779094485630313)
    ·
      refine ⟨164241752867084320864222735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218989003822779094485630313 164241752867084320864222735)
      ·
        refine ⟨246362629300626481296334103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164241752867084320864222735 246362629300626481296334103)
        ·
          refine ⟨369543943950939721944501155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246362629300626481296334103 369543943950939721944501155)
          ·
            refine ⟨554315915926409582916751733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369543943950939721944501155 554315915926409582916751733)
            ·
              refine ⟨51967117118100898398445475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 554315915926409582916751733 51967117118100898398445475)
              ·
                refine ⟨77950675677151347597668213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51967117118100898398445475 77950675677151347597668213)
                ·
                  refine ⟨7307875844732938837281395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77950675677151347597668213 7307875844732938837281395)
                  ·
                    refine ⟨10961813767099408255922093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307875844732938837281395 10961813767099408255922093)
                    ·
                      refine ⟨4110680162662278095970785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10961813767099408255922093 4110680162662278095970785)
                      ·
                        rfl

theorem cell23_8005521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_8005521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005521 prefixEnd_8005521 := by exact prefixLift 8005521
  have htrace : WordTrace (prefixWord ++ tailWord_8005521) baseStart_8005521 baseEnd_8005521 := by
    simpa [prefixWord, tailWord_8005521, baseEnd_8005521] using wordTrace_append hprefix tailTrace_8005521
  have hstable : (prefixWord ++ tailWord_8005521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005521).length < 2 ^ (prefixWord ++ tailWord_8005521).sum := by decide
  have hdescent : baseEnd_8005521 < baseStart_8005521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005554 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_8005554 : Nat := 118140960795 + 8005554 * 2 ^ 59
def prefixEnd_8005554 : Nat := 4983230072969 + 3 ^ 40 * 8005554 * 2
def baseEnd_8005554 : Nat := 1370232369174625488952711

theorem tailTrace_8005554 : CollatzResearch.WordTrace tailWord_8005554 prefixEnd_8005554 1370232369174625488952711 := by
  unfold tailWord_8005554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72996635509813143154197929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194657694692835048411194477 72996635509813143154197929)
  ·
    refine ⟨54747476632359857365648447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72996635509813143154197929 54747476632359857365648447)
    ·
      refine ⟨82121214948539786048472671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54747476632359857365648447 82121214948539786048472671)
      ·
        refine ⟨123181822422809679072709007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82121214948539786048472671 123181822422809679072709007)
        ·
          refine ⟨184772733634214518609063511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123181822422809679072709007 184772733634214518609063511)
          ·
            refine ⟨277159100451321777913595267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184772733634214518609063511 277159100451321777913595267)
            ·
              refine ⟨415738650676982666870392901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277159100451321777913595267 415738650676982666870392901)
              ·
                refine ⟨77950997001934250038198669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415738650676982666870392901 77950997001934250038198669)
                ·
                  refine ⟨29231623875725343764324501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77950997001934250038198669 29231623875725343764324501)
                  ·
                    refine ⟨1370232369174625488952711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29231623875725343764324501 1370232369174625488952711)
                    ·
                      rfl

theorem cell23_8005554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_8005554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005554 prefixEnd_8005554 := by exact prefixLift 8005554
  have htrace : WordTrace (prefixWord ++ tailWord_8005554) baseStart_8005554 baseEnd_8005554 := by
    simpa [prefixWord, tailWord_8005554, baseEnd_8005554] using wordTrace_append hprefix tailTrace_8005554
  have hstable : (prefixWord ++ tailWord_8005554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005554).length < 2 ^ (prefixWord ++ tailWord_8005554).sum := by decide
  have hdescent : baseEnd_8005554 < baseStart_8005554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005678 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_8005678 : Nat := 118140960795 + 8005678 * 2 ^ 59
def prefixEnd_8005678 : Nat := 4983230072969 + 3 ^ 40 * 8005678 * 2
def baseEnd_8005678 : Nat := 1370253593041677993902521

theorem tailTrace_8005678 : CollatzResearch.WordTrace tailWord_8005678 prefixEnd_8005678 1370253593041677993902521 := by
  unfold tailWord_8005678
  simp only [CollatzResearch.WordTrace]
  refine ⟨36498883086350417724288211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194660709793868894529537125 36498883086350417724288211)
  ·
    refine ⟨54748324629525626586432317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36498883086350417724288211 54748324629525626586432317)
    ·
      refine ⟨20530621736072109969912119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54748324629525626586432317 20530621736072109969912119)
      ·
        refine ⟨30795932604108164954868179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20530621736072109969912119 30795932604108164954868179)
        ·
          refine ⟨46193898906162247432302269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30795932604108164954868179 46193898906162247432302269)
          ·
            refine ⟨17322712089810842787113351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46193898906162247432302269 17322712089810842787113351)
            ·
              refine ⟨25984068134716264180670027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17322712089810842787113351 25984068134716264180670027)
              ·
                refine ⟨38976102202074396271005041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25984068134716264180670027 38976102202074396271005041)
                ·
                  refine ⟨29232076651555797203253781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38976102202074396271005041 29232076651555797203253781)
                  ·
                    refine ⟨1370253593041677993902521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29232076651555797203253781 1370253593041677993902521)
                    ·
                      rfl

theorem cell23_8005678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_8005678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005678 prefixEnd_8005678 := by exact prefixLift 8005678
  have htrace : WordTrace (prefixWord ++ tailWord_8005678) baseStart_8005678 baseEnd_8005678 := by
    simpa [prefixWord, tailWord_8005678, baseEnd_8005678] using wordTrace_append hprefix tailTrace_8005678
  have hstable : (prefixWord ++ tailWord_8005678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005678).length < 2 ^ (prefixWord ++ tailWord_8005678).sum := by decide
  have hdescent : baseEnd_8005678 < baseStart_8005678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005681 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_8005681 : Nat := 118140960795 + 8005681 * 2 ^ 59
def prefixEnd_8005681 : Nat := 4983230072969 + 3 ^ 40 * 8005681 * 2
def baseEnd_8005681 : Nat := 4110762319566997469970049

theorem tailTrace_8005681 : CollatzResearch.WordTrace tailWord_8005681 prefixEnd_8005681 4110762319566997469970049 := by
  unfold tailWord_8005681
  simp only [CollatzResearch.WordTrace]
  refine ⟨291991174109792473306664897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194660782739861648871109931 291991174109792473306664897)
  ·
    refine ⟨218993380582344354979998673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291991174109792473306664897 218993380582344354979998673)
    ·
      refine ⟨164245035436758266234999005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218993380582344354979998673 164245035436758266234999005)
      ·
        refine ⟨61591888288784349838124627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164245035436758266234999005 61591888288784349838124627)
        ·
          refine ⟨92387832433176524757186941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61591888288784349838124627 92387832433176524757186941)
          ·
            refine ⟨34645437162441196783945103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92387832433176524757186941 34645437162441196783945103)
            ·
              refine ⟨51968155743661795175917655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34645437162441196783945103 51968155743661795175917655)
              ·
                refine ⟨77952233615492692763876483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51968155743661795175917655 77952233615492692763876483)
                ·
                  refine ⟨116928350423239039145814725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77952233615492692763876483 116928350423239039145814725)
                  ·
                    refine ⟨21924065704357319839840261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116928350423239039145814725 21924065704357319839840261)
                    ·
                      refine ⟨4110762319566997469970049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21924065704357319839840261 4110762319566997469970049)
                      ·
                        rfl

theorem cell23_8005681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_8005681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005681 prefixEnd_8005681 := by exact prefixLift 8005681
  have htrace : WordTrace (prefixWord ++ tailWord_8005681) baseStart_8005681 baseEnd_8005681 := by
    simpa [prefixWord, tailWord_8005681, baseEnd_8005681] using wordTrace_append hprefix tailTrace_8005681
  have hstable : (prefixWord ++ tailWord_8005681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005681).length < 2 ^ (prefixWord ++ tailWord_8005681).sum := by decide
  have hdescent : baseEnd_8005681 < baseStart_8005681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005701 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_8005701 : Nat := 118140960795 + 8005701 * 2 ^ 59
def prefixEnd_8005701 : Nat := 4983230072969 + 3 ^ 40 * 8005701 * 2
def baseEnd_8005701 : Nat := 4110772589180087391719957

theorem tailTrace_8005701 : CollatzResearch.WordTrace tailWord_8005701 prefixEnd_8005701 4110772589180087391719957 := by
  unfold tailWord_8005701
  simp only [CollatzResearch.WordTrace]
  refine ⟨291991903569720016722392957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194661269046480011148261971 291991903569720016722392957)
  ·
    refine ⟨109496963838645006270897359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291991903569720016722392957 109496963838645006270897359)
    ·
      refine ⟨164245445757967509406346039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109496963838645006270897359 164245445757967509406346039)
      ·
        refine ⟨246368168636951264109519059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164245445757967509406346039 246368168636951264109519059)
        ·
          refine ⟨369552252955426896164278589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246368168636951264109519059 369552252955426896164278589)
          ·
            refine ⟨138582094858285086061604471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369552252955426896164278589 138582094858285086061604471)
            ·
              refine ⟨207873142287427629092406707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138582094858285086061604471 207873142287427629092406707)
              ·
                refine ⟨311809713431141443638610061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207873142287427629092406707 311809713431141443638610061)
                ·
                  refine ⟨116928642536678041364478773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311809713431141443638610061 116928642536678041364478773)
                  ·
                    refine ⟨10962060237813566377919885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116928642536678041364478773 10962060237813566377919885)
                    ·
                      refine ⟨4110772589180087391719957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10962060237813566377919885 4110772589180087391719957)
                      ·
                        rfl

theorem cell23_8005701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_8005701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005701 prefixEnd_8005701 := by exact prefixLift 8005701
  have htrace : WordTrace (prefixWord ++ tailWord_8005701) baseStart_8005701 baseEnd_8005701 := by
    simpa [prefixWord, tailWord_8005701, baseEnd_8005701] using wordTrace_append hprefix tailTrace_8005701
  have hstable : (prefixWord ++ tailWord_8005701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005701).length < 2 ^ (prefixWord ++ tailWord_8005701).sum := by decide
  have hdescent : baseEnd_8005701 < baseStart_8005701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005702 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_8005702 : Nat := 118140960795 + 8005702 * 2 ^ 59
def prefixEnd_8005702 : Nat := 4983230072969 + 3 ^ 40 * 8005702 * 2
def baseEnd_8005702 : Nat := 4110773102660741887807453

theorem tailTrace_8005702 : CollatzResearch.WordTrace tailWord_8005702 prefixEnd_8005702 4110773102660741887807453 := by
  unfold tailWord_8005702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124748126334887309161855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194661293361810929262119573 9124748126334887309161855)
  ·
    refine ⟨13687122189502330963742783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9124748126334887309161855 13687122189502330963742783)
    ·
      refine ⟨20530683284253496445614175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13687122189502330963742783 20530683284253496445614175)
      ·
        refine ⟨30796024926380244668421263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20530683284253496445614175 30796024926380244668421263)
        ·
          refine ⟨46194037389570367002631895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30796024926380244668421263 46194037389570367002631895)
          ·
            refine ⟨69291056084355550503947843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46194037389570367002631895 69291056084355550503947843)
            ·
              refine ⟨103936584126533325755921765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69291056084355550503947843 103936584126533325755921765)
              ·
                refine ⟨19488109523724998579235331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103936584126533325755921765 19488109523724998579235331)
                ·
                  refine ⟨29232164285587497868852997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19488109523724998579235331 29232164285587497868852997)
                  ·
                    refine ⟨5481030803547655850409937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29232164285587497868852997 5481030803547655850409937)
                    ·
                      refine ⟨4110773102660741887807453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481030803547655850409937 4110773102660741887807453)
                      ·
                        rfl

theorem cell23_8005702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_8005702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005702 prefixEnd_8005702 := by exact prefixLift 8005702
  have htrace : WordTrace (prefixWord ++ tailWord_8005702) baseStart_8005702 baseEnd_8005702 := by
    simpa [prefixWord, tailWord_8005702, baseEnd_8005702] using wordTrace_append hprefix tailTrace_8005702
  have hstable : (prefixWord ++ tailWord_8005702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005702).length < 2 ^ (prefixWord ++ tailWord_8005702).sum := by decide
  have hdescent : baseEnd_8005702 < baseStart_8005702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005708 : List Nat := [2, 2, 1, 3, 1, 1, 3, 5, 5]
def baseStart_8005708 : Nat := 118140960795 + 8005708 * 2 ^ 59
def prefixEnd_8005708 : Nat := 4983230072969 + 3 ^ 40 * 8005708 * 2
def baseEnd_8005708 : Nat := 456752909282740984925825

theorem tailTrace_8005708 : CollatzResearch.WordTrace tailWord_8005708 prefixEnd_8005708 456752909282740984925825 := by
  unfold tailWord_8005708
  simp only [CollatzResearch.WordTrace]
  refine ⟨145996079440347328458948889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194661439253796437945265185 145996079440347328458948889)
  ·
    refine ⟨109497059580260496344211667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145996079440347328458948889 109497059580260496344211667)
    ·
      refine ⟨164245589370390744516317501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109497059580260496344211667 164245589370390744516317501)
      ·
        refine ⟨61592096013896529193619063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164245589370390744516317501 61592096013896529193619063)
        ·
          refine ⟨92388144020844793790428595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61592096013896529193619063 92388144020844793790428595)
          ·
            refine ⟨138582216031267190685642893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92388144020844793790428595 138582216031267190685642893)
            ·
              refine ⟨51968331011725196507116085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138582216031267190685642893 51968331011725196507116085)
              ·
                refine ⟨4872031032349237172542133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51968331011725196507116085 4872031032349237172542133)
                ·
                  refine ⟨456752909282740984925825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4872031032349237172542133 456752909282740984925825)
                  ·
                    rfl

theorem cell23_8005708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_8005708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005708 prefixEnd_8005708 := by exact prefixLift 8005708
  have htrace : WordTrace (prefixWord ++ tailWord_8005708) baseStart_8005708 baseEnd_8005708 := by
    simpa [prefixWord, tailWord_8005708, baseEnd_8005708] using wordTrace_append hprefix tailTrace_8005708
  have hstable : (prefixWord ++ tailWord_8005708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005708).length < 2 ^ (prefixWord ++ tailWord_8005708).sum := by decide
  have hdescent : baseEnd_8005708 < baseStart_8005708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005721 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 4, 5]
def baseStart_8005721 : Nat := 118140960795 + 8005721 * 2 ^ 59
def prefixEnd_8005721 : Nat := 4983230072969 + 3 ^ 40 * 8005721 * 2
def baseEnd_8005721 : Nat := 1370260952931059104489955

theorem tailTrace_8005721 : CollatzResearch.WordTrace tailWord_8005721 prefixEnd_8005721 1370260952931059104489955 := by
  unfold tailWord_8005721
  simp only [CollatzResearch.WordTrace]
  refine ⟨291992633029647560138121017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194661755353098373425414011 291992633029647560138121017)
  ·
    refine ⟨218994474772235670103590763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291992633029647560138121017 218994474772235670103590763)
    ·
      refine ⟨328491712158353505155386145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218994474772235670103590763 328491712158353505155386145)
      ·
        refine ⟨246368784118765128866539609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328491712158353505155386145 246368784118765128866539609)
        ·
          refine ⟨184776588089073846649904707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246368784118765128866539609 184776588089073846649904707)
          ·
            refine ⟨277164882133610769974857061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184776588089073846649904707 277164882133610769974857061)
            ·
              refine ⟨51968415400052019370285699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277164882133610769974857061 51968415400052019370285699)
              ·
                refine ⟨77952623100078029055428549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51968415400052019370285699 77952623100078029055428549)
                ·
                  refine ⟨14616116831264630447892853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77952623100078029055428549 14616116831264630447892853)
                  ·
                    refine ⟨1370260952931059104489955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14616116831264630447892853 1370260952931059104489955)
                    ·
                      rfl

theorem cell23_8005721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_8005721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005721 prefixEnd_8005721 := by exact prefixLift 8005721
  have htrace : WordTrace (prefixWord ++ tailWord_8005721) baseStart_8005721 baseEnd_8005721 := by
    simpa [prefixWord, tailWord_8005721, baseEnd_8005721] using wordTrace_append hprefix tailTrace_8005721
  have hstable : (prefixWord ++ tailWord_8005721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005721).length < 2 ^ (prefixWord ++ tailWord_8005721).sum := by decide
  have hdescent : baseEnd_8005721 < baseStart_8005721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005725 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 7]
def baseStart_8005725 : Nat := 118140960795 + 8005725 * 2 ^ 59
def prefixEnd_8005725 : Nat := 4983230072969 + 3 ^ 40 * 8005725 * 2
def baseEnd_8005725 : Nat := 456753879190643921979983

theorem tailTrace_8005725 : CollatzResearch.WordTrace tailWord_8005725 prefixEnd_8005725 456753879190643921979983 := by
  unfold tailWord_8005725
  simp only [CollatzResearch.WordTrace]
  refine ⟨291992778921633068821266629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194661852614422045880844419 291992778921633068821266629)
  ·
    refine ⟨54748646047806200403987493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291992778921633068821266629 54748646047806200403987493)
    ·
      refine ⟨10265371133963662575747655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54748646047806200403987493 10265371133963662575747655)
      ·
        refine ⟨15398056700945493863621483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10265371133963662575747655 15398056700945493863621483)
        ·
          refine ⟨23097085051418240795432225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15398056700945493863621483 23097085051418240795432225)
          ·
            refine ⟨17322813788563680596574169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23097085051418240795432225 17322813788563680596574169)
            ·
              refine ⟨12992110341422760447430627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17322813788563680596574169 12992110341422760447430627)
              ·
                refine ⟨19488165512134140671145941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12992110341422760447430627 19488165512134140671145941)
                ·
                  refine ⟨456753879190643921979983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19488165512134140671145941 456753879190643921979983)
                  ·
                    rfl

theorem cell23_8005725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_8005725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005725 prefixEnd_8005725 := by exact prefixLift 8005725
  have htrace : WordTrace (prefixWord ++ tailWord_8005725) baseStart_8005725 baseEnd_8005725 := by
    simpa [prefixWord, tailWord_8005725, baseEnd_8005725] using wordTrace_append hprefix tailTrace_8005725
  have hstable : (prefixWord ++ tailWord_8005725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005725).length < 2 ^ (prefixWord ++ tailWord_8005725).sum := by decide
  have hdescent : baseEnd_8005725 < baseStart_8005725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005731 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5]
def baseStart_8005731 : Nat := 118140960795 + 8005731 * 2 ^ 59
def prefixEnd_8005731 : Nat := 4983230072969 + 3 ^ 40 * 8005731 * 2
def baseEnd_8005731 : Nat := 4110787993599722274344819

theorem tailTrace_8005731 : CollatzResearch.WordTrace tailWord_8005731 prefixEnd_8005731 4110787993599722274344819 := by
  unfold tailWord_8005731
  simp only [CollatzResearch.WordTrace]
  refine ⟨291992997759611331845985047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194661998506407554563990031 291992997759611331845985047)
  ·
    refine ⟨437989496639416997768977571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291992997759611331845985047 437989496639416997768977571)
    ·
      refine ⟨656984244959125496653466357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437989496639416997768977571 656984244959125496653466357)
      ·
        refine ⟨61592272964918015311262471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 656984244959125496653466357 61592272964918015311262471)
        ·
          refine ⟨92388409447377022966893707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61592272964918015311262471 92388409447377022966893707)
          ·
            refine ⟨138582614171065534450340561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92388409447377022966893707 138582614171065534450340561)
            ·
              refine ⟨103936960628299150837755421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138582614171065534450340561 103936960628299150837755421)
              ·
                refine ⟨38976360235612181564158283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103936960628299150837755421 38976360235612181564158283)
                ·
                  refine ⟨58464540353418272346237425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38976360235612181564158283 58464540353418272346237425)
                  ·
                    refine ⟨43848405265063704259678069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58464540353418272346237425 43848405265063704259678069)
                    ·
                      refine ⟨4110787993599722274344819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43848405265063704259678069 4110787993599722274344819)
                      ·
                        rfl

theorem cell23_8005731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_8005731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005731 prefixEnd_8005731 := by exact prefixLift 8005731
  have htrace : WordTrace (prefixWord ++ tailWord_8005731) baseStart_8005731 baseEnd_8005731 := by
    simpa [prefixWord, tailWord_8005731, baseEnd_8005731] using wordTrace_append hprefix tailTrace_8005731
  have hstable : (prefixWord ++ tailWord_8005731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005731).length < 2 ^ (prefixWord ++ tailWord_8005731).sum := by decide
  have hdescent : baseEnd_8005731 < baseStart_8005731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005781 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 8]
def baseStart_8005781 : Nat := 118140960795 + 8005781 * 2 ^ 59
def prefixEnd_8005781 : Nat := 4983230072969 + 3 ^ 40 * 8005781 * 2
def baseEnd_8005781 : Nat := 456757074181383008746621

theorem tailTrace_8005781 : CollatzResearch.WordTrace tailWord_8005781 prefixEnd_8005781 456757074181383008746621 := by
  unfold tailWord_8005781
  simp only [CollatzResearch.WordTrace]
  refine ⟨291994821409430190385305197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194663214272953460256870131 291994821409430190385305197)
  ·
    refine ⟨109498058028536321394489449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291994821409430190385305197 109498058028536321394489449)
    ·
      refine ⟨82123543521402241045867087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109498058028536321394489449 82123543521402241045867087)
      ·
        refine ⟨123185315282103361568800631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82123543521402241045867087 123185315282103361568800631)
        ·
          refine ⟨184777972923155042353200947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123185315282103361568800631 184777972923155042353200947)
          ·
            refine ⟨277166959384732563529801421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184777972923155042353200947 277166959384732563529801421)
            ·
              refine ⟨103937609769274711323675533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277166959384732563529801421 103937609769274711323675533)
              ·
                refine ⟨38976603663478016746378325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103937609769274711323675533 38976603663478016746378325)
                ·
                  refine ⟨456757074181383008746621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38976603663478016746378325 456757074181383008746621)
                  ·
                    rfl

theorem cell23_8005781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_8005781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005781 prefixEnd_8005781 := by exact prefixLift 8005781
  have htrace : WordTrace (prefixWord ++ tailWord_8005781) baseStart_8005781 baseEnd_8005781 := by
    simpa [prefixWord, tailWord_8005781, baseEnd_8005781] using wordTrace_append hprefix tailTrace_8005781
  have hstable : (prefixWord ++ tailWord_8005781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005781).length < 2 ^ (prefixWord ++ tailWord_8005781).sum := by decide
  have hdescent : baseEnd_8005781 < baseStart_8005781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005785 : List Nat := [1, 2, 1, 2, 1, 2, 1, 8, 1, 4]
def baseStart_8005785 : Nat := 118140960795 + 8005785 * 2 ^ 59
def prefixEnd_8005785 : Nat := 4983230072969 + 3 ^ 40 * 8005785 * 2
def baseEnd_8005785 : Nat := 1370271907185021687689857

theorem tailTrace_8005785 : CollatzResearch.WordTrace tailWord_8005785 prefixEnd_8005785 1370271907185021687689857 := by
  unfold tailWord_8005785
  simp only [CollatzResearch.WordTrace]
  refine ⟨291994967301415699068450809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194663311534277132712300539 291994967301415699068450809)
  ·
    refine ⟨218996225476061774301338107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291994967301415699068450809 218996225476061774301338107)
    ·
      refine ⟨328494338214092661452007161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218996225476061774301338107 328494338214092661452007161)
      ·
        refine ⟨246370753660569496089005371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328494338214092661452007161 246370753660569496089005371)
        ·
          refine ⟨369556130490854244133508057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246370753660569496089005371 369556130490854244133508057)
          ·
            refine ⟨277167097868140683100131043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369556130490854244133508057 277167097868140683100131043)
            ·
              refine ⟨415750646802211024650196565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277167097868140683100131043 415750646802211024650196565)
              ·
                refine ⟨4872077892213410445119491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 415750646802211024650196565 4872077892213410445119491)
                ·
                  refine ⟨7308116838320115667679237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872077892213410445119491 7308116838320115667679237)
                  ·
                    refine ⟨1370271907185021687689857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7308116838320115667679237 1370271907185021687689857)
                    ·
                      rfl

theorem cell23_8005785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 4].length) (baseStart_8005785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005785 prefixEnd_8005785 := by exact prefixLift 8005785
  have htrace : WordTrace (prefixWord ++ tailWord_8005785) baseStart_8005785 baseEnd_8005785 := by
    simpa [prefixWord, tailWord_8005785, baseEnd_8005785] using wordTrace_append hprefix tailTrace_8005785
  have hstable : (prefixWord ++ tailWord_8005785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005785).length < 2 ^ (prefixWord ++ tailWord_8005785).sum := by decide
  have hdescent : baseEnd_8005785 < baseStart_8005785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005835 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 2, 3, 2]
def baseStart_8005835 : Nat := 118140960795 + 8005835 * 2 ^ 59
def prefixEnd_8005835 : Nat := 4983230072969 + 3 ^ 40 * 8005835 * 2
def baseEnd_8005835 : Nat := 4110841395587789867444341

theorem tailTrace_8005835 : CollatzResearch.WordTrace tailWord_8005835 prefixEnd_8005835 4110841395587789867444341 := by
  unfold tailWord_8005835
  simp only [CollatzResearch.WordTrace]
  refine ⟨291996790951234557607770959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194664527300823038405180639 291996790951234557607770959)
  ·
    refine ⟨437995186426851836411656439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291996790951234557607770959 437995186426851836411656439)
    ·
      refine ⟨656992779640277754617484659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437995186426851836411656439 656992779640277754617484659)
      ·
        refine ⟨985489169460416631926226989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656992779640277754617484659 985489169460416631926226989)
        ·
          refine ⟨369558438547656236972335121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985489169460416631926226989 369558438547656236972335121)
          ·
            refine ⟨277168828910742177729251341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369558438547656236972335121 277168828910742177729251341)
            ·
              refine ⟨103938310841528316648469253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277168828910742177729251341 103938310841528316648469253)
              ·
                refine ⟨19488433282786559371587985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103938310841528316648469253 19488433282786559371587985)
                ·
                  refine ⟨14616324962089919528690989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19488433282786559371587985 14616324962089919528690989)
                  ·
                    refine ⟨5481121860783719823259121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14616324962089919528690989 5481121860783719823259121)
                    ·
                      refine ⟨4110841395587789867444341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481121860783719823259121 4110841395587789867444341)
                      ·
                        rfl

theorem cell23_8005835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3, 2].length) (baseStart_8005835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005835 prefixEnd_8005835 := by exact prefixLift 8005835
  have htrace : WordTrace (prefixWord ++ tailWord_8005835) baseStart_8005835 baseEnd_8005835 := by
    simpa [prefixWord, tailWord_8005835, baseEnd_8005835] using wordTrace_append hprefix tailTrace_8005835
  have hstable : (prefixWord ++ tailWord_8005835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005835).length < 2 ^ (prefixWord ++ tailWord_8005835).sum := by decide
  have hdescent : baseEnd_8005835 < baseStart_8005835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005859 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 3]
def baseStart_8005859 : Nat := 118140960795 + 8005859 * 2 ^ 59
def prefixEnd_8005859 : Nat := 4983230072969 + 3 ^ 40 * 8005859 * 2
def baseEnd_8005859 : Nat := 4110853719123497773544231

theorem tailTrace_8005859 : CollatzResearch.WordTrace tailWord_8005859 prefixEnd_8005859 4110853719123497773544231 := by
  unfold tailWord_8005859
  simp only [CollatzResearch.WordTrace]
  refine ⟨291997666303147609706644631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194665110868765073137763087 291997666303147609706644631)
  ·
    refine ⟨437996499454721414559966947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291997666303147609706644631 437996499454721414559966947)
    ·
      refine ⟨656994749182082121839950421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437996499454721414559966947 656994749182082121839950421)
      ·
        refine ⟨7699157216977524865311919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 656994749182082121839950421 7699157216977524865311919)
        ·
          refine ⟨11548735825466287297967879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7699157216977524865311919 11548735825466287297967879)
          ·
            refine ⟨17323103738199430946951819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548735825466287297967879 17323103738199430946951819)
            ·
              refine ⟨25984655607299146420427729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17323103738199430946951819 25984655607299146420427729)
              ·
                refine ⟨19488491705474359815320797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25984655607299146420427729 19488491705474359815320797)
                ·
                  refine ⟨7308184389552884930745299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19488491705474359815320797 7308184389552884930745299)
                  ·
                    refine ⟨10962276584329327396117949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7308184389552884930745299 10962276584329327396117949)
                    ·
                      refine ⟨4110853719123497773544231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10962276584329327396117949 4110853719123497773544231)
                      ·
                        rfl

theorem cell23_8005859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_8005859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005859 prefixEnd_8005859 := by exact prefixLift 8005859
  have htrace : WordTrace (prefixWord ++ tailWord_8005859) baseStart_8005859 baseEnd_8005859 := by
    simpa [prefixWord, tailWord_8005859, baseEnd_8005859] using wordTrace_append hprefix tailTrace_8005859
  have hstable : (prefixWord ++ tailWord_8005859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005859).length < 2 ^ (prefixWord ++ tailWord_8005859).sum := by decide
  have hdescent : baseEnd_8005859 < baseStart_8005859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005882 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4]
def baseStart_8005882 : Nat := 118140960795 + 8005882 * 2 ^ 59
def prefixEnd_8005882 : Nat := 4983230072969 + 3 ^ 40 * 8005882 * 2
def baseEnd_8005882 : Nat := 4110865529178551183556625

theorem tailTrace_8005882 : CollatzResearch.WordTrace tailWord_8005882 prefixEnd_8005882 4110865529178551183556625 := by
  unfold tailWord_8005882
  simp only [CollatzResearch.WordTrace]
  refine ⟨72999626295516071158682975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194665670121376189756487933 72999626295516071158682975)
  ·
    refine ⟨109499439443274106738024463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72999626295516071158682975 109499439443274106738024463)
    ·
      refine ⟨164249159164911160107036695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109499439443274106738024463 164249159164911160107036695)
      ·
        refine ⟨246373738747366740160555043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164249159164911160107036695 246373738747366740160555043)
        ·
          refine ⟨369560608121050110240832565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246373738747366740160555043 369560608121050110240832565)
          ·
            refine ⟨34646307011348447835078053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369560608121050110240832565 34646307011348447835078053)
            ·
              refine ⟨6496182564627833969077135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34646307011348447835078053 6496182564627833969077135)
              ·
                refine ⟨9744273846941750953615703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496182564627833969077135 9744273846941750953615703)
                ·
                  refine ⟨14616410770412626430423555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9744273846941750953615703 14616410770412626430423555)
                  ·
                    refine ⟨21924616155618939645635333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14616410770412626430423555 21924616155618939645635333)
                    ·
                      refine ⟨4110865529178551183556625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21924616155618939645635333 4110865529178551183556625)
                      ·
                        rfl

theorem cell23_8005882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_8005882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005882 prefixEnd_8005882 := by exact prefixLift 8005882
  have htrace : WordTrace (prefixWord ++ tailWord_8005882) baseStart_8005882 baseEnd_8005882 := by
    simpa [prefixWord, tailWord_8005882, baseEnd_8005882] using wordTrace_append hprefix tailTrace_8005882
  have hstable : (prefixWord ++ tailWord_8005882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005882).length < 2 ^ (prefixWord ++ tailWord_8005882).sum := by decide
  have hdescent : baseEnd_8005882 < baseStart_8005882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005892 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_8005892 : Nat := 118140960795 + 8005892 * 2 ^ 59
def prefixEnd_8005892 : Nat := 4983230072969 + 3 ^ 40 * 8005892 * 2
def baseEnd_8005892 : Nat := 1370290221328365381477193

theorem tailTrace_8005892 : CollatzResearch.WordTrace tailWord_8005892 prefixEnd_8005892 1370290221328365381477193 := by
  unfold tailWord_8005892
  simp only [CollatzResearch.WordTrace]
  refine ⟨145999434956014028171297965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194665913274685370895063953 145999434956014028171297965)
  ·
    refine ⟨54749788108505260564236737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145999434956014028171297965 54749788108505260564236737)
    ·
      refine ⟨41062341081378945423177553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54749788108505260564236737 41062341081378945423177553)
      ·
        refine ⟨30796755811034209067383165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41062341081378945423177553 30796755811034209067383165)
        ·
          refine ⟨11548783429137828400268687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30796755811034209067383165 11548783429137828400268687)
          ·
            refine ⟨17323175143706742600403031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548783429137828400268687 17323175143706742600403031)
            ·
              refine ⟨25984762715560113900604547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17323175143706742600403031 25984762715560113900604547)
              ·
                refine ⟨38977144073340170850906821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25984762715560113900604547 38977144073340170850906821)
                ·
                  refine ⟨7308214513751282034545029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38977144073340170850906821 7308214513751282034545029)
                  ·
                    refine ⟨1370290221328365381477193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7308214513751282034545029 1370290221328365381477193)
                    ·
                      rfl

theorem cell23_8005892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_8005892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005892 prefixEnd_8005892 := by exact prefixLift 8005892
  have htrace : WordTrace (prefixWord ++ tailWord_8005892) baseStart_8005892 baseEnd_8005892 := by
    simpa [prefixWord, tailWord_8005892, baseEnd_8005892] using wordTrace_append hprefix tailTrace_8005892
  have hstable : (prefixWord ++ tailWord_8005892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005892).length < 2 ^ (prefixWord ++ tailWord_8005892).sum := by decide
  have hdescent : baseEnd_8005892 < baseStart_8005892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005899 : List Nat := [1, 1, 1, 1, 5, 2, 1, 6, 1, 2, 2]
def baseStart_8005899 : Nat := 118140960795 + 8005899 * 2 ^ 59
def prefixEnd_8005899 : Nat := 4983230072969 + 3 ^ 40 * 8005899 * 2
def baseEnd_8005899 : Nat := 4110874258349677617044047

theorem tailTrace_8005899 : CollatzResearch.WordTrace tailWord_8005899 prefixEnd_8005899 4110874258349677617044047 := by
  unfold tailWord_8005899
  simp only [CollatzResearch.WordTrace]
  refine ⟨291999125223002696538100751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194666083482001797692067167 291999125223002696538100751)
  ·
    refine ⟨437998687834504044807151127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291999125223002696538100751 437998687834504044807151127)
    ·
      refine ⟨656998031751756067210726691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437998687834504044807151127 656998031751756067210726691)
      ·
        refine ⟨985497047627634100816090037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656998031751756067210726691 985497047627634100816090037)
        ·
          refine ⟨92390348215090696951508441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 985497047627634100816090037 92390348215090696951508441)
          ·
            refine ⟨69292761161318022713631331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92390348215090696951508441 69292761161318022713631331)
            ·
              refine ⟨103939141741977034070446997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69292761161318022713631331 103939141741977034070446997)
              ·
                refine ⟨4872147269155173472052203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103939141741977034070446997 4872147269155173472052203)
                ·
                  refine ⟨7308220903732760208078305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872147269155173472052203 7308220903732760208078305)
                  ·
                    refine ⟨5481165677799570156058729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7308220903732760208078305 5481165677799570156058729)
                    ·
                      refine ⟨4110874258349677617044047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481165677799570156058729 4110874258349677617044047)
                      ·
                        rfl

theorem cell23_8005899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 2, 2].length) (baseStart_8005899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005899 prefixEnd_8005899 := by exact prefixLift 8005899
  have htrace : WordTrace (prefixWord ++ tailWord_8005899) baseStart_8005899 baseEnd_8005899 := by
    simpa [prefixWord, tailWord_8005899, baseEnd_8005899] using wordTrace_append hprefix tailTrace_8005899
  have hstable : (prefixWord ++ tailWord_8005899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005899).length < 2 ^ (prefixWord ++ tailWord_8005899).sum := by decide
  have hdescent : baseEnd_8005899 < baseStart_8005899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005915 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 3]
def baseStart_8005915 : Nat := 118140960795 + 8005915 * 2 ^ 59
def prefixEnd_8005915 : Nat := 4983230072969 + 3 ^ 40 * 8005915 * 2
def baseEnd_8005915 : Nat := 4110882474040149554443973

theorem tailTrace_8005915 : CollatzResearch.WordTrace tailWord_8005915 prefixEnd_8005915 4110882474040149554443973 := by
  unfold tailWord_8005915
  simp only [CollatzResearch.WordTrace]
  refine ⟨291999708790944731270683199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194666472527296487513788799 291999708790944731270683199)
  ·
    refine ⟨437999563186417096906024799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291999708790944731270683199 437999563186417096906024799)
    ·
      refine ⟨656999344779625645359037199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437999563186417096906024799 656999344779625645359037199)
      ·
        refine ⟨985499017169438468038555799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656999344779625645359037199 985499017169438468038555799)
        ·
          refine ⟨1478248525754157702057833699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985499017169438468038555799 1478248525754157702057833699)
          ·
            refine ⟨2217372788631236553086750549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478248525754157702057833699 2217372788631236553086750549)
            ·
              refine ⟨12992418683386151678242679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2217372788631236553086750549 12992418683386151678242679)
              ·
                refine ⟨19488628025079227517364019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12992418683386151678242679 19488628025079227517364019)
                ·
                  refine ⟨29232942037618841276046029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19488628025079227517364019 29232942037618841276046029)
                  ·
                    refine ⟨10962353264107065478517261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29232942037618841276046029 10962353264107065478517261)
                    ·
                      refine ⟨4110882474040149554443973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10962353264107065478517261 4110882474040149554443973)
                      ·
                        rfl

theorem cell23_8005915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 3].length) (baseStart_8005915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005915 prefixEnd_8005915 := by exact prefixLift 8005915
  have htrace : WordTrace (prefixWord ++ tailWord_8005915) baseStart_8005915 baseEnd_8005915 := by
    simpa [prefixWord, tailWord_8005915, baseEnd_8005915] using wordTrace_append hprefix tailTrace_8005915
  have hstable : (prefixWord ++ tailWord_8005915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005915).length < 2 ^ (prefixWord ++ tailWord_8005915).sum := by decide
  have hdescent : baseEnd_8005915 < baseStart_8005915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005922 : List Nat := [3, 3, 1, 1, 3, 3, 2, 7]
def baseStart_8005922 : Nat := 118140960795 + 8005922 * 2 ^ 59
def prefixEnd_8005922 : Nat := 4983230072969 + 3 ^ 40 * 8005922 * 2
def baseEnd_8005922 : Nat := 152255039570545593594683

theorem tailTrace_8005922 : CollatzResearch.WordTrace tailWord_8005922 prefixEnd_8005922 152255039570545593594683 := by
  unfold tailWord_8005922
  simp only [CollatzResearch.WordTrace]
  refine ⟨72999991025479842866547005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194666642734612914310792013 72999991025479842866547005)
  ·
    refine ⟨27374996634554941074955127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72999991025479842866547005 27374996634554941074955127)
    ·
      refine ⟨41062494951832411612432691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27374996634554941074955127 41062494951832411612432691)
      ·
        refine ⟨61593742427748617418649037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41062494951832411612432691 61593742427748617418649037)
        ·
          refine ⟨23097653410405731531993389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61593742427748617418649037 23097653410405731531993389)
          ·
            refine ⟨8661620028902149324497521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23097653410405731531993389 8661620028902149324497521)
            ·
              refine ⟨6496215021676611993373141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8661620028902149324497521 6496215021676611993373141)
              ·
                refine ⟨152255039570545593594683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6496215021676611993373141 152255039570545593594683)
                ·
                  rfl

theorem cell23_8005922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 7].length) (baseStart_8005922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005922 prefixEnd_8005922 := by exact prefixLift 8005922
  have htrace : WordTrace (prefixWord ++ tailWord_8005922) baseStart_8005922 baseEnd_8005922 := by
    simpa [prefixWord, tailWord_8005922, baseEnd_8005922] using wordTrace_append hprefix tailTrace_8005922
  have hstable : (prefixWord ++ tailWord_8005922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005922).length < 2 ^ (prefixWord ++ tailWord_8005922).sum := by decide
  have hdescent : baseEnd_8005922 < baseStart_8005922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005927 : List Nat := [1, 1, 8, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_8005927 : Nat := 118140960795 + 8005927 * 2 ^ 59
def prefixEnd_8005927 : Nat := 4983230072969 + 3 ^ 40 * 8005927 * 2
def baseEnd_8005927 : Nat := 4110888635808003507493919

theorem tailTrace_8005927 : CollatzResearch.WordTrace tailWord_8005927 prefixEnd_8005927 4110888635808003507493919 := by
  unfold tailWord_8005927
  simp only [CollatzResearch.WordTrace]
  refine ⟨292000146466901257320120035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194666764311267504880080023 292000146466901257320120035)
  ·
    refine ⟨438000219700351885980180053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292000146466901257320120035 438000219700351885980180053)
    ·
      refine ⟨5132815074613498663830235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 438000219700351885980180053 5132815074613498663830235)
      ·
        refine ⟨7699222611920247995745353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5132815074613498663830235 7699222611920247995745353)
        ·
          refine ⟨5774416958940185996809015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7699222611920247995745353 5774416958940185996809015)
          ·
            refine ⟨8661625438410278995213523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5774416958940185996809015 8661625438410278995213523)
            ·
              refine ⟨12992438157615418492820285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8661625438410278995213523 12992438157615418492820285)
              ·
                refine ⟨4872164309105781934807607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12992438157615418492820285 4872164309105781934807607)
                ·
                  refine ⟨7308246463658672902211411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872164309105781934807607 7308246463658672902211411)
                  ·
                    refine ⟨10962369695488009353317117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7308246463658672902211411 10962369695488009353317117)
                    ·
                      refine ⟨4110888635808003507493919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10962369695488009353317117 4110888635808003507493919)
                      ·
                        rfl

theorem cell23_8005927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_8005927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005927 prefixEnd_8005927 := by exact prefixLift 8005927
  have htrace : WordTrace (prefixWord ++ tailWord_8005927) baseStart_8005927 baseEnd_8005927 := by
    simpa [prefixWord, tailWord_8005927, baseEnd_8005927] using wordTrace_append hprefix tailTrace_8005927
  have hstable : (prefixWord ++ tailWord_8005927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005927).length < 2 ^ (prefixWord ++ tailWord_8005927).sum := by decide
  have hdescent : baseEnd_8005927 < baseStart_8005927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8005978 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 9]
def baseStart_8005978 : Nat := 118140960795 + 8005978 * 2 ^ 59
def prefixEnd_8005978 : Nat := 4983230072969 + 3 ^ 40 * 8005978 * 2
def baseEnd_8005978 : Nat := 456768313702375867550687

theorem tailTrace_8005978 : CollatzResearch.WordTrace tailWord_8005978 prefixEnd_8005978 456768313702375867550687 := by
  unfold tailWord_8005978
  simp only [CollatzResearch.WordTrace]
  refine ⟨73000501647429123257556647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194668004393144328686817725 73000501647429123257556647)
  ·
    refine ⟨109500752471143684886334971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73000501647429123257556647 109500752471143684886334971)
    ·
      refine ⟨164251128706715527329502457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109500752471143684886334971 164251128706715527329502457)
      ·
        refine ⟨123188346530036645497126843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164251128706715527329502457 123188346530036645497126843)
        ·
          refine ⟨184782519795054968245690265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123188346530036645497126843 184782519795054968245690265)
          ·
            refine ⟨138586889846291226184267699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184782519795054968245690265 138586889846291226184267699)
            ·
              refine ⟨207880334769436839276401549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138586889846291226184267699 207880334769436839276401549)
              ·
                refine ⟨77955125538538814728650581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207880334769436839276401549 77955125538538814728650581)
                ·
                  refine ⟨456768313702375867550687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77955125538538814728650581 456768313702375867550687)
                  ·
                    rfl

theorem cell23_8005978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_8005978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8005978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8005978 prefixEnd_8005978 := by exact prefixLift 8005978
  have htrace : WordTrace (prefixWord ++ tailWord_8005978) baseStart_8005978 baseEnd_8005978 := by
    simpa [prefixWord, tailWord_8005978, baseEnd_8005978] using wordTrace_append hprefix tailTrace_8005978
  have hstable : (prefixWord ++ tailWord_8005978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8005978).length < 2 ^ (prefixWord ++ tailWord_8005978).sum := by decide
  have hdescent : baseEnd_8005978 < baseStart_8005978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8005978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006042 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_8006042 : Nat := 118140960795 + 8006042 * 2 ^ 59
def prefixEnd_8006042 : Nat := 4983230072969 + 3 ^ 40 * 8006042 * 2
def baseEnd_8006042 : Nat := 1370315895361090185851963

theorem tailTrace_8006042 : CollatzResearch.WordTrace tailWord_8006042 prefixEnd_8006042 1370315895361090185851963 := by
  unfold tailWord_8006042
  simp only [CollatzResearch.WordTrace]
  refine ⟨73001085215371157990139095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194669560574323087973704253 73001085215371157990139095)
  ·
    refine ⟨109501627823056736985208643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73001085215371157990139095 109501627823056736985208643)
    ·
      refine ⟨164252441734585105477812965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109501627823056736985208643 164252441734585105477812965)
      ·
        refine ⟨30797332825234707277089931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164252441734585105477812965 30797332825234707277089931)
        ·
          refine ⟨46195999237852060915634897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30797332825234707277089931 46195999237852060915634897)
          ·
            refine ⟨34646999428389045686726173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46195999237852060915634897 34646999428389045686726173)
            ·
              refine ⟨12992624785645892132522315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34646999428389045686726173 12992624785645892132522315)
              ·
                refine ⟨19488937178468838198783473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12992624785645892132522315 19488937178468838198783473)
                ·
                  refine ⟨14616702883851628649087605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19488937178468838198783473 14616702883851628649087605)
                  ·
                    refine ⟨1370315895361090185851963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14616702883851628649087605 1370315895361090185851963)
                    ·
                      rfl

theorem cell23_8006042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_8006042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006042 prefixEnd_8006042 := by exact prefixLift 8006042
  have htrace : WordTrace (prefixWord ++ tailWord_8006042) baseStart_8006042 baseEnd_8006042 := by
    simpa [prefixWord, tailWord_8006042, baseEnd_8006042] using wordTrace_append hprefix tailTrace_8006042
  have hstable : (prefixWord ++ tailWord_8006042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006042).length < 2 ^ (prefixWord ++ tailWord_8006042).sum := by decide
  have hdescent : baseEnd_8006042 < baseStart_8006042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006046 : List Nat := [4, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_8006046 : Nat := 118140960795 + 8006046 * 2 ^ 59
def prefixEnd_8006046 : Nat := 4983230072969 + 3 ^ 40 * 8006046 * 2
def baseEnd_8006046 : Nat := 456772193333987615767319

theorem tailTrace_8006046 : CollatzResearch.WordTrace tailWord_8006046 prefixEnd_8006046 456772193333987615767319 := by
  unfold tailWord_8006046
  simp only [CollatzResearch.WordTrace]
  refine ⟨36500560844183767580462749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194669657835646760429134661 36500560844183767580462749)
  ·
    refine ⟨13687710316568912842673531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36500560844183767580462749 13687710316568912842673531)
    ·
      refine ⟨20531565474853369264010297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13687710316568912842673531 20531565474853369264010297)
      ·
        refine ⟨15398674106140026948007723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20531565474853369264010297 15398674106140026948007723)
        ·
          refine ⟨23098011159210040422011585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15398674106140026948007723 23098011159210040422011585)
          ·
            refine ⟨17323508369407530316508689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23098011159210040422011585 17323508369407530316508689)
            ·
              refine ⟨12992631277055647737381517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17323508369407530316508689 12992631277055647737381517)
              ·
                refine ⟨4872236728895867901518069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12992631277055647737381517 4872236728895867901518069)
                ·
                  refine ⟨456772193333987615767319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4872236728895867901518069 456772193333987615767319)
                  ·
                    rfl

theorem cell23_8006046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_8006046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006046 prefixEnd_8006046 := by exact prefixLift 8006046
  have htrace : WordTrace (prefixWord ++ tailWord_8006046) baseStart_8006046 baseEnd_8006046 := by
    simpa [prefixWord, tailWord_8006046, baseEnd_8006046] using wordTrace_append hprefix tailTrace_8006046
  have hstable : (prefixWord ++ tailWord_8006046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006046).length < 2 ^ (prefixWord ++ tailWord_8006046).sum := by decide
  have hdescent : baseEnd_8006046 < baseStart_8006046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006095 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 3]
def baseStart_8006095 : Nat := 118140960795 + 8006095 * 2 ^ 59
def prefixEnd_8006095 : Nat := 4983230072969 + 3 ^ 40 * 8006095 * 2
def baseEnd_8006095 : Nat := 4110974900557958850193145

theorem tailTrace_8006095 : CollatzResearch.WordTrace tailWord_8006095 prefixEnd_8006095 4110974900557958850193145 := by
  unfold tailWord_8006095
  simp only [CollatzResearch.WordTrace]
  refine ⟨292006273930292622012235739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194670849286861748008157159 292006273930292622012235739)
  ·
    refine ⟨438009410895438933018353609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292006273930292622012235739 438009410895438933018353609)
    ·
      refine ⟨328507058171579199763765207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438009410895438933018353609 328507058171579199763765207)
      ·
        refine ⟨492760587257368799645647811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328507058171579199763765207 492760587257368799645647811)
        ·
          refine ⟨739140880886053199468471717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492760587257368799645647811 739140880886053199468471717)
          ·
            refine ⟨138588915166134974900338447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 739140880886053199468471717 138588915166134974900338447)
            ·
              refine ⟨207883372749202462350507671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138588915166134974900338447 207883372749202462350507671)
              ·
                refine ⟨311825059123803693525761507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207883372749202462350507671 311825059123803693525761507)
                ·
                  refine ⟨467737588685705540288642261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311825059123803693525761507 467737588685705540288642261)
                  ·
                    refine ⟨10962599734821223600515053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 467737588685705540288642261 10962599734821223600515053)
                    ·
                      refine ⟨4110974900557958850193145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10962599734821223600515053 4110974900557958850193145)
                      ·
                        rfl

theorem cell23_8006095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_8006095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006095 prefixEnd_8006095 := by exact prefixLift 8006095
  have htrace : WordTrace (prefixWord ++ tailWord_8006095) baseStart_8006095 baseEnd_8006095 := by
    simpa [prefixWord, tailWord_8006095, baseEnd_8006095] using wordTrace_append hprefix tailTrace_8006095
  have hstable : (prefixWord ++ tailWord_8006095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006095).length < 2 ^ (prefixWord ++ tailWord_8006095).sum := by decide
  have hdescent : baseEnd_8006095 < baseStart_8006095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006102 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_8006102 : Nat := 118140960795 + 8006102 * 2 ^ 59
def prefixEnd_8006102 : Nat := 4983230072969 + 3 ^ 40 * 8006102 * 2
def baseEnd_8006102 : Nat := 456775388324726702533957

theorem tailTrace_8006102 : CollatzResearch.WordTrace tailWord_8006102 prefixEnd_8006102 456775388324726702533957 := by
  unfold tailWord_8006102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18250408077579203887983785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194671019494178174805160373 18250408077579203887983785)
  ·
    refine ⟨13687806058184402915987839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18250408077579203887983785 13687806058184402915987839)
    ·
      refine ⟨20531709087276604373981759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13687806058184402915987839 20531709087276604373981759)
      ·
        refine ⟨30797563630914906560972639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20531709087276604373981759 30797563630914906560972639)
        ·
          refine ⟨46196345446372359841458959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30797563630914906560972639 46196345446372359841458959)
          ·
            refine ⟨69294518169558539762188439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46196345446372359841458959 69294518169558539762188439)
            ·
              refine ⟨103941777254337809643282659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69294518169558539762188439 103941777254337809643282659)
              ·
                refine ⟨155912665881506714464923989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103941777254337809643282659 155912665881506714464923989)
                ·
                  refine ⟨456775388324726702533957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155912665881506714464923989 456775388324726702533957)
                  ·
                    rfl

theorem cell23_8006102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_8006102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006102 prefixEnd_8006102 := by exact prefixLift 8006102
  have htrace : WordTrace (prefixWord ++ tailWord_8006102) baseStart_8006102 baseEnd_8006102 := by
    simpa [prefixWord, tailWord_8006102, baseEnd_8006102] using wordTrace_append hprefix tailTrace_8006102
  have hstable : (prefixWord ++ tailWord_8006102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006102).length < 2 ^ (prefixWord ++ tailWord_8006102).sum := by decide
  have hdescent : baseEnd_8006102 < baseStart_8006102 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006150 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_8006150 : Nat := 118140960795 + 8006150 * 2 ^ 59
def prefixEnd_8006150 : Nat := 4983230072969 + 3 ^ 40 * 8006150 * 2
def baseEnd_8006150 : Nat := 4111003141993956135005393

theorem tailTrace_8006150 : CollatzResearch.WordTrace tailWord_8006150 prefixEnd_8006150 4111003141993956135005393 := by
  unfold tailWord_8006150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9125258748284167700171497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194672186630062244270325269 9125258748284167700171497)
  ·
    refine ⟨6843944061213125775128623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9125258748284167700171497 6843944061213125775128623)
    ·
      refine ⟨10265916091819688662692935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6843944061213125775128623 10265916091819688662692935)
      ·
        refine ⟨15398874137729532994039403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10265916091819688662692935 15398874137729532994039403)
        ·
          refine ⟨23098311206594299491059105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15398874137729532994039403 23098311206594299491059105)
          ·
            refine ⟨17323733404945724618294329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23098311206594299491059105 17323733404945724618294329)
            ·
              refine ⟨12992800053709293463720747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17323733404945724618294329 12992800053709293463720747)
              ·
                refine ⟨19489200080563940195581121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12992800053709293463720747 19489200080563940195581121)
                ·
                  refine ⟨14616900060422955146685841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19489200080563940195581121 14616900060422955146685841)
                  ·
                    refine ⟨10962675045317216360014381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14616900060422955146685841 10962675045317216360014381)
                    ·
                      refine ⟨4111003141993956135005393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10962675045317216360014381 4111003141993956135005393)
                      ·
                        rfl

theorem cell23_8006150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_8006150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006150 prefixEnd_8006150 := by exact prefixLift 8006150
  have htrace : WordTrace (prefixWord ++ tailWord_8006150) baseStart_8006150 baseEnd_8006150 := by
    simpa [prefixWord, tailWord_8006150, baseEnd_8006150] using wordTrace_append hprefix tailTrace_8006150
  have hstable : (prefixWord ++ tailWord_8006150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006150).length < 2 ^ (prefixWord ++ tailWord_8006150).sum := by decide
  have hdescent : baseEnd_8006150 < baseStart_8006150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006156 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 2, 3, 2]
def baseStart_8006156 : Nat := 118140960795 + 8006156 * 2 ^ 59
def prefixEnd_8006156 : Nat := 4983230072969 + 3 ^ 40 * 8006156 * 2
def baseEnd_8006156 : Nat := 4111006222877883111530365

theorem tailTrace_8006156 : CollatzResearch.WordTrace tailWord_8006156 prefixEnd_8006156 4111006222877883111530365 := by
  unfold tailWord_8006156
  simp only [CollatzResearch.WordTrace]
  refine ⟨146004249391535814715103161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194672332522047752953470881 146004249391535814715103161)
  ·
    refine ⟨109503187043651861036327371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146004249391535814715103161 109503187043651861036327371)
    ·
      refine ⟨164254780565477791554491057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109503187043651861036327371 164254780565477791554491057)
      ·
        refine ⟨123191085424108343665868293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164254780565477791554491057 123191085424108343665868293)
        ·
          refine ⟨23098328517020314437350305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123191085424108343665868293 23098328517020314437350305)
          ·
            refine ⟨17323746387765235828012729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23098328517020314437350305 17323746387765235828012729)
            ·
              refine ⟨12992809790823926871009547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17323746387765235828012729 12992809790823926871009547)
              ·
                refine ⟨19489214686235890306514321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12992809790823926871009547 19489214686235890306514321)
                ·
                  refine ⟨14616911014676917729885741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19489214686235890306514321 14616911014676917729885741)
                  ·
                    refine ⟨5481341630503844148707153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14616911014676917729885741 5481341630503844148707153)
                    ·
                      refine ⟨4111006222877883111530365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481341630503844148707153 4111006222877883111530365)
                      ·
                        rfl

theorem cell23_8006156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_8006156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006156 prefixEnd_8006156 := by exact prefixLift 8006156
  have htrace : WordTrace (prefixWord ++ tailWord_8006156) baseStart_8006156 baseEnd_8006156 := by
    simpa [prefixWord, tailWord_8006156, baseEnd_8006156] using wordTrace_append hprefix tailTrace_8006156
  have hstable : (prefixWord ++ tailWord_8006156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006156).length < 2 ^ (prefixWord ++ tailWord_8006156).sum := by decide
  have hdescent : baseEnd_8006156 < baseStart_8006156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006169 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 5, 2, 2]
def baseStart_8006169 : Nat := 118140960795 + 8006169 * 2 ^ 59
def prefixEnd_8006169 : Nat := 4983230072969 + 3 ^ 40 * 8006169 * 2
def baseEnd_8006169 : Nat := 4111012898126391560667805

theorem tailTrace_8006169 : CollatzResearch.WordTrace tailWord_8006169 prefixEnd_8006169 4111012898126391560667805 := by
  unfold tailWord_8006169
  simp only [CollatzResearch.WordTrace]
  refine ⟨292008972932024532650429561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194672648621349688433619707 292008972932024532650429561)
  ·
    refine ⟨219006729699018399487822171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292008972932024532650429561 219006729699018399487822171)
    ·
      refine ⟨328510094548527599231733257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219006729699018399487822171 328510094548527599231733257)
      ·
        refine ⟨246382570911395699423799943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328510094548527599231733257 246382570911395699423799943)
        ·
          refine ⟨369573856367093549135699915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246382570911395699423799943 369573856367093549135699915)
          ·
            refine ⟨554360784550640323703549873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369573856367093549135699915 554360784550640323703549873)
            ·
              refine ⟨415770588412980242777662405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554360784550640323703549873 415770588412980242777662405)
              ·
                refine ⟨77956985327433795520811701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415770588412980242777662405 77956985327433795520811701)
                ·
                  refine ⟨7308467374446918330076097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77956985327433795520811701 7308467374446918330076097)
                  ·
                    refine ⟨5481350530835188747557073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7308467374446918330076097 5481350530835188747557073)
                    ·
                      refine ⟨4111012898126391560667805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481350530835188747557073 4111012898126391560667805)
                      ·
                        rfl

theorem cell23_8006169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_8006169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006169 prefixEnd_8006169 := by exact prefixLift 8006169
  have htrace : WordTrace (prefixWord ++ tailWord_8006169) baseStart_8006169 baseEnd_8006169 := by
    simpa [prefixWord, tailWord_8006169, baseEnd_8006169] using wordTrace_append hprefix tailTrace_8006169
  have hstable : (prefixWord ++ tailWord_8006169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006169).length < 2 ^ (prefixWord ++ tailWord_8006169).sum := by decide
  have hdescent : baseEnd_8006169 < baseStart_8006169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006179 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 2, 4]
def baseStart_8006179 : Nat := 118140960795 + 8006179 * 2 ^ 59
def prefixEnd_8006179 : Nat := 4983230072969 + 3 ^ 40 * 8006179 * 2
def baseEnd_8006179 : Nat := 1370339344310978840514253

theorem tailTrace_8006179 : CollatzResearch.WordTrace tailWord_8006179 prefixEnd_8006179 1370339344310978840514253 := by
  unfold tailWord_8006179
  simp only [CollatzResearch.WordTrace]
  refine ⟨292009337661988304358293591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194672891774658869572195727 292009337661988304358293591)
  ·
    refine ⟨438014006492982456537440387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292009337661988304358293591 438014006492982456537440387)
    ·
      refine ⟨657021009739473684806160581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438014006492982456537440387 657021009739473684806160581)
      ·
        refine ⟨123191439326151315901155109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657021009739473684806160581 123191439326151315901155109)
        ·
          refine ⟨23098394873653371731466583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123191439326151315901155109 23098394873653371731466583)
          ·
            refine ⟨34647592310480057597199875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23098394873653371731466583 34647592310480057597199875)
            ·
              refine ⟨51971388465720086395799813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34647592310480057597199875 51971388465720086395799813)
              ·
                refine ⟨9744635337322516199212465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51971388465720086395799813 9744635337322516199212465)
                ·
                  refine ⟨7308476502991887149409349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9744635337322516199212465 7308476502991887149409349)
                  ·
                    refine ⟨1370339344310978840514253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7308476502991887149409349 1370339344310978840514253)
                    ·
                      rfl

theorem cell23_8006179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 4].length) (baseStart_8006179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006179 prefixEnd_8006179 := by exact prefixLift 8006179
  have htrace : WordTrace (prefixWord ++ tailWord_8006179) baseStart_8006179 baseEnd_8006179 := by
    simpa [prefixWord, tailWord_8006179, baseEnd_8006179] using wordTrace_append hprefix tailTrace_8006179
  have hstable : (prefixWord ++ tailWord_8006179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006179).length < 2 ^ (prefixWord ++ tailWord_8006179).sum := by decide
  have hdescent : baseEnd_8006179 < baseStart_8006179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006180 : List Nat := [2, 3, 1, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_8006180 : Nat := 118140960795 + 8006180 * 2 ^ 59
def prefixEnd_8006180 : Nat := 4983230072969 + 3 ^ 40 * 8006180 * 2
def baseEnd_8006180 : Nat := 4111018546413591017630255

theorem tailTrace_8006180 : CollatzResearch.WordTrace tailWord_8006180 prefixEnd_8006180 4111018546413591017630255 := by
  unfold tailWord_8006180
  simp only [CollatzResearch.WordTrace]
  refine ⟨146004687067492340764539997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194672916089989787686053329 146004687067492340764539997)
  ·
    refine ⟨54751757650309627786702499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146004687067492340764539997 54751757650309627786702499)
    ·
      refine ⟨82127636475464441680053749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54751757650309627786702499 82127636475464441680053749)
      ·
        refine ⟨7699465919574791407505039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82127636475464441680053749 7699465919574791407505039)
        ·
          refine ⟨11549198879362187111257559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7699465919574791407505039 11549198879362187111257559)
          ·
            refine ⟨17323798319043280666886339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11549198879362187111257559 17323798319043280666886339)
            ·
              refine ⟨25985697478564921000329509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17323798319043280666886339 25985697478564921000329509)
              ·
                refine ⟨4872318277230922687561783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25985697478564921000329509 4872318277230922687561783)
                ·
                  refine ⟨7308477415846384031342675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872318277230922687561783 7308477415846384031342675)
                  ·
                    refine ⟨10962716123769576047014013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7308477415846384031342675 10962716123769576047014013)
                    ·
                      refine ⟨4111018546413591017630255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10962716123769576047014013 4111018546413591017630255)
                      ·
                        rfl

theorem cell23_8006180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_8006180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006180 prefixEnd_8006180 := by exact prefixLift 8006180
  have htrace : WordTrace (prefixWord ++ tailWord_8006180) baseStart_8006180 baseEnd_8006180 := by
    simpa [prefixWord, tailWord_8006180, baseEnd_8006180] using wordTrace_append hprefix tailTrace_8006180
  have hstable : (prefixWord ++ tailWord_8006180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006180).length < 2 ^ (prefixWord ++ tailWord_8006180).sum := by decide
  have hdescent : baseEnd_8006180 < baseStart_8006180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006209 : List Nat := [1, 2, 5, 1, 1, 3, 3, 7]
def baseStart_8006209 : Nat := 118140960795 + 8006209 * 2 ^ 59
def prefixEnd_8006209 : Nat := 4983230072969 + 3 ^ 40 * 8006209 * 2
def baseEnd_8006209 : Nat := 152260497679724866821023

theorem tailTrace_8006209 : CollatzResearch.WordTrace tailWord_8006209 prefixEnd_8006209 152260497679724866821023 := by
  unfold tailWord_8006209
  simp only [CollatzResearch.WordTrace]
  refine ⟨292010431851879619481885681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194673621234586412987923787 292010431851879619481885681)
  ·
    refine ⟨219007823888909714611414261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292010431851879619481885681 219007823888909714611414261)
    ·
      refine ⟨20531983489585285744820087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219007823888909714611414261 20531983489585285744820087)
      ·
        refine ⟨30797975234377928617230131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20531983489585285744820087 30797975234377928617230131)
        ·
          refine ⟨46196962851566892925845197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30797975234377928617230131 46196962851566892925845197)
          ·
            refine ⟨17323861069337584847191949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46196962851566892925845197 17323861069337584847191949)
            ·
              refine ⟨6496447901001594317696981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17323861069337584847191949 6496447901001594317696981)
              ·
                refine ⟨152260497679724866821023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6496447901001594317696981 152260497679724866821023)
                ·
                  rfl

theorem cell23_8006209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 7].length) (baseStart_8006209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006209 prefixEnd_8006209 := by exact prefixLift 8006209
  have htrace : WordTrace (prefixWord ++ tailWord_8006209) baseStart_8006209 baseEnd_8006209 := by
    simpa [prefixWord, tailWord_8006209, baseEnd_8006209] using wordTrace_append hprefix tailTrace_8006209
  have hstable : (prefixWord ++ tailWord_8006209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006209).length < 2 ^ (prefixWord ++ tailWord_8006209).sum := by decide
  have hdescent : baseEnd_8006209 < baseStart_8006209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006235 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 14]
def baseStart_8006235 : Nat := 118140960795 + 8006235 * 2 ^ 59
def prefixEnd_8006235 : Nat := 4983230072969 + 3 ^ 40 * 8006235 * 2
def baseEnd_8006235 : Nat := 1370348929283196100814167

theorem tailTrace_8006235 : CollatzResearch.WordTrace tailWord_8006235 prefixEnd_8006235 1370348929283196100814167 := by
  unfold tailWord_8006235
  simp only [CollatzResearch.WordTrace]
  refine ⟨292011380149785425922332159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194674253433190283948221439 292011380149785425922332159)
  ·
    refine ⟨438017070224678138883498239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292011380149785425922332159 438017070224678138883498239)
    ·
      refine ⟨657025605337017208325247359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438017070224678138883498239 657025605337017208325247359)
      ·
        refine ⟨985538408005525812487871039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657025605337017208325247359 985538408005525812487871039)
        ·
          refine ⟨1478307612008288718731806559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985538408005525812487871039 1478307612008288718731806559)
          ·
            refine ⟨2217461418012433078097709839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478307612008288718731806559 2217461418012433078097709839)
            ·
              refine ⟨3326192127018649617146564759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217461418012433078097709839 3326192127018649617146564759)
              ·
                refine ⟨4989288190527974425719847139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326192127018649617146564759 4989288190527974425719847139)
                ·
                  refine ⟨7483932285791961638579770709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989288190527974425719847139 7483932285791961638579770709)
                  ·
                    refine ⟨1370348929283196100814167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 14 7483932285791961638579770709 1370348929283196100814167)
                    ·
                      rfl

theorem cell23_8006235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_8006235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006235 prefixEnd_8006235 := by exact prefixLift 8006235
  have htrace : WordTrace (prefixWord ++ tailWord_8006235) baseStart_8006235 baseEnd_8006235 := by
    simpa [prefixWord, tailWord_8006235, baseEnd_8006235] using wordTrace_append hprefix tailTrace_8006235
  have hstable : (prefixWord ++ tailWord_8006235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006235).length < 2 ^ (prefixWord ++ tailWord_8006235).sum := by decide
  have hdescent : baseEnd_8006235 < baseStart_8006235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006252 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_8006252 : Nat := 118140960795 + 8006252 * 2 ^ 59
def prefixEnd_8006252 : Nat := 4983230072969 + 3 ^ 40 * 8006252 * 2
def baseEnd_8006252 : Nat := 1370351839006904911976641

theorem tailTrace_8006252 : CollatzResearch.WordTrace tailWord_8006252 prefixEnd_8006252 1370351839006904911976641 := by
  unfold tailWord_8006252
  simp only [CollatzResearch.WordTrace]
  refine ⟨146006000095361918912850505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194674666793815891883800673 146006000095361918912850505)
  ·
    refine ⟨109504500071521439184637879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146006000095361918912850505 109504500071521439184637879)
    ·
      refine ⟨164256750107282158776956819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109504500071521439184637879 164256750107282158776956819)
      ·
        refine ⟨246385125160923238165435229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164256750107282158776956819 246385125160923238165435229)
        ·
          refine ⟨92394421935346214312038211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246385125160923238165435229 92394421935346214312038211)
          ·
            refine ⟨138591632903019321468057317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92394421935346214312038211 138591632903019321468057317)
            ·
              refine ⟨25985931169316122775260747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138591632903019321468057317 25985931169316122775260747)
              ·
                refine ⟨38978896753974184162891121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25985931169316122775260747 38978896753974184162891121)
                ·
                  refine ⟨29234172565480638122168341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38978896753974184162891121 29234172565480638122168341)
                  ·
                    refine ⟨1370351839006904911976641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29234172565480638122168341 1370351839006904911976641)
                    ·
                      rfl

theorem cell23_8006252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_8006252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006252 prefixEnd_8006252 := by exact prefixLift 8006252
  have htrace : WordTrace (prefixWord ++ tailWord_8006252) baseStart_8006252 baseEnd_8006252 := by
    simpa [prefixWord, tailWord_8006252, baseEnd_8006252] using wordTrace_append hprefix tailTrace_8006252
  have hstable : (prefixWord ++ tailWord_8006252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006252).length < 2 ^ (prefixWord ++ tailWord_8006252).sum := by decide
  have hdescent : baseEnd_8006252 < baseStart_8006252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006259 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 1, 4, 2]
def baseStart_8006259 : Nat := 118140960795 + 8006259 * 2 ^ 59
def prefixEnd_8006259 : Nat := 4983230072969 + 3 ^ 40 * 8006259 * 2
def baseEnd_8006259 : Nat := 4111059111385296208542391

theorem tailTrace_8006259 : CollatzResearch.WordTrace tailWord_8006259 prefixEnd_8006259 4111059111385296208542391 := by
  unfold tailWord_8006259
  simp only [CollatzResearch.WordTrace]
  refine ⟨292012255501698478021205831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194674837001132318680803887 292012255501698478021205831)
  ·
    refine ⟨438018383252547717031808747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292012255501698478021205831 438018383252547717031808747)
    ·
      refine ⟨657027574878821575547713121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438018383252547717031808747 657027574878821575547713121)
      ·
        refine ⟨492770681159116181660784841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657027574878821575547713121 492770681159116181660784841)
        ·
          refine ⟨369578010869337136245588631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492770681159116181660784841 369578010869337136245588631)
          ·
            refine ⟨554367016304005704368382947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369578010869337136245588631 554367016304005704368382947)
            ·
              refine ⟨831550524456008556552574421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554367016304005704368382947 831550524456008556552574421)
              ·
                refine ⟨19489465416937700544200963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 831550524456008556552574421 19489465416937700544200963)
                ·
                  refine ⟨29234198125406550816301445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19489465416937700544200963 29234198125406550816301445)
                  ·
                    refine ⟨5481412148513728278056521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29234198125406550816301445 5481412148513728278056521)
                    ·
                      refine ⟨4111059111385296208542391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481412148513728278056521 4111059111385296208542391)
                      ·
                        rfl

theorem cell23_8006259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 4, 2].length) (baseStart_8006259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006259 prefixEnd_8006259 := by exact prefixLift 8006259
  have htrace : WordTrace (prefixWord ++ tailWord_8006259) baseStart_8006259 baseEnd_8006259 := by
    simpa [prefixWord, tailWord_8006259, baseEnd_8006259] using wordTrace_append hprefix tailTrace_8006259
  have hstable : (prefixWord ++ tailWord_8006259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006259).length < 2 ^ (prefixWord ++ tailWord_8006259).sum := by decide
  have hdescent : baseEnd_8006259 < baseStart_8006259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006314 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_8006314 : Nat := 118140960795 + 8006314 * 2 ^ 59
def prefixEnd_8006314 : Nat := 4983230072969 + 3 ^ 40 * 8006314 * 2
def baseEnd_8006314 : Nat := 4111087352821293493354639

theorem tailTrace_8006314 : CollatzResearch.WordTrace tailWord_8006314 prefixEnd_8006314 4111087352821293493354639 := by
  unfold tailWord_8006314
  simp only [CollatzResearch.WordTrace]
  refine ⟨73003565379124805603614499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194676174344332814942971997 73003565379124805603614499)
  ·
    refine ⟨109505348068687208405421749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73003565379124805603614499 109505348068687208405421749)
    ·
      refine ⟨10266126381439425788008289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109505348068687208405421749 10266126381439425788008289)
      ·
        refine ⟨7699594786079569341006217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10266126381439425788008289 7699594786079569341006217)
        ·
          refine ⟨5774696089559677005754663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7699594786079569341006217 5774696089559677005754663)
          ·
            refine ⟨8662044134339515508631995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5774696089559677005754663 8662044134339515508631995)
            ·
              refine ⟨12993066201509273262947993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8662044134339515508631995 12993066201509273262947993)
              ·
                refine ⟨9744799651131954947210995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12993066201509273262947993 9744799651131954947210995)
                ·
                  refine ⟨14617199476697932420816493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9744799651131954947210995 14617199476697932420816493)
                  ·
                    refine ⟨5481449803761724657806185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14617199476697932420816493 5481449803761724657806185)
                    ·
                      refine ⟨4111087352821293493354639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481449803761724657806185 4111087352821293493354639)
                      ·
                        rfl

theorem cell23_8006314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_8006314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006314 prefixEnd_8006314 := by exact prefixLift 8006314
  have htrace : WordTrace (prefixWord ++ tailWord_8006314) baseStart_8006314 baseEnd_8006314 := by
    simpa [prefixWord, tailWord_8006314, baseEnd_8006314] using wordTrace_append hprefix tailTrace_8006314
  have hstable : (prefixWord ++ tailWord_8006314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006314).length < 2 ^ (prefixWord ++ tailWord_8006314).sum := by decide
  have hdescent : baseEnd_8006314 < baseStart_8006314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006322 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_8006322 : Nat := 118140960795 + 8006322 * 2 ^ 59
def prefixEnd_8006322 : Nat := 4983230072969 + 3 ^ 40 * 8006322 * 2
def baseEnd_8006322 : Nat := 4111091460666529462054601

theorem tailTrace_8006322 : CollatzResearch.WordTrace tailWord_8006322 prefixEnd_8006322 4111091460666529462054601 := by
  unfold tailWord_8006322
  simp only [CollatzResearch.WordTrace]
  refine ⟨73003638325117559945187305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194676368866980159853832813 73003638325117559945187305)
  ·
    refine ⟨54752728743838169958890479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73003638325117559945187305 54752728743838169958890479)
    ·
      refine ⟨82129093115757254938335719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54752728743838169958890479 82129093115757254938335719)
      ·
        refine ⟨123193639673635882407503579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82129093115757254938335719 123193639673635882407503579)
        ·
          refine ⟨184790459510453823611255369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123193639673635882407503579 184790459510453823611255369)
          ·
            refine ⟨138592844632840367708441527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184790459510453823611255369 138592844632840367708441527)
            ·
              refine ⟨207889266949260551562662291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138592844632840367708441527 207889266949260551562662291)
              ·
                refine ⟨311833900423890827343993437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207889266949260551562662291 311833900423890827343993437)
                ·
                  refine ⟨116937712658959060253997539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311833900423890827343993437 116937712658959060253997539)
                  ·
                    refine ⟨175406568988438590380996309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116937712658959060253997539 175406568988438590380996309)
                    ·
                      refine ⟨4111091460666529462054601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175406568988438590380996309 4111091460666529462054601)
                      ·
                        rfl

theorem cell23_8006322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_8006322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006322 prefixEnd_8006322 := by exact prefixLift 8006322
  have htrace : WordTrace (prefixWord ++ tailWord_8006322) baseStart_8006322 baseEnd_8006322 := by
    simpa [prefixWord, tailWord_8006322, baseEnd_8006322] using wordTrace_append hprefix tailTrace_8006322
  have hstable : (prefixWord ++ tailWord_8006322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006322).length < 2 ^ (prefixWord ++ tailWord_8006322).sum := by decide
  have hdescent : baseEnd_8006322 < baseStart_8006322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006386 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_8006386 : Nat := 118140960795 + 8006386 * 2 ^ 59
def prefixEnd_8006386 : Nat := 4983230072969 + 3 ^ 40 * 8006386 * 2
def baseEnd_8006386 : Nat := 4111124323428417211654307

theorem tailTrace_8006386 : CollatzResearch.WordTrace tailWord_8006386 prefixEnd_8006386 4111124323428417211654307 := by
  unfold tailWord_8006386
  simp only [CollatzResearch.WordTrace]
  refine ⟨73004221893059594677769753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194677925048158919140719341 73004221893059594677769753)
  ·
    refine ⟨54753166419794696008327315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73004221893059594677769753 54753166419794696008327315)
    ·
      refine ⟨82129749629692044012490973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54753166419794696008327315 82129749629692044012490973)
      ·
        refine ⟨30798656111134516504684115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82129749629692044012490973 30798656111134516504684115)
        ·
          refine ⟨46197984166701774757026173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30798656111134516504684115 46197984166701774757026173)
          ·
            refine ⟨17324244062513165533884815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46197984166701774757026173 17324244062513165533884815)
            ·
              refine ⟨25986366093769748300827223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17324244062513165533884815 25986366093769748300827223)
              ·
                refine ⟨38979549140654622451240835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25986366093769748300827223 38979549140654622451240835)
                ·
                  refine ⟨58469323710981933676861253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38979549140654622451240835 58469323710981933676861253)
                  ·
                    refine ⟨10962998195809112564411485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58469323710981933676861253 10962998195809112564411485)
                    ·
                      refine ⟨4111124323428417211654307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10962998195809112564411485 4111124323428417211654307)
                      ·
                        rfl

theorem cell23_8006386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_8006386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006386 prefixEnd_8006386 := by exact prefixLift 8006386
  have htrace : WordTrace (prefixWord ++ tailWord_8006386) baseStart_8006386 baseEnd_8006386 := by
    simpa [prefixWord, tailWord_8006386, baseEnd_8006386] using wordTrace_append hprefix tailTrace_8006386
  have hstable : (prefixWord ++ tailWord_8006386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006386).length < 2 ^ (prefixWord ++ tailWord_8006386).sum := by decide
  have hdescent : baseEnd_8006386 < baseStart_8006386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006423 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 6]
def baseStart_8006423 : Nat := 118140960795 + 8006423 * 2 ^ 59
def prefixEnd_8006423 : Nat := 4983230072969 + 3 ^ 40 * 8006423 * 2
def baseEnd_8006423 : Nat := 456793702468070396321293

theorem tailTrace_8006423 : CollatzResearch.WordTrace tailWord_8006423 prefixEnd_8006423 456793702468070396321293 := by
  unfold tailWord_8006423
  simp only [CollatzResearch.WordTrace]
  refine ⟨292018237073104334030175923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194678824715402889353450615 292018237073104334030175923)
  ·
    refine ⟨438027355609656501045263885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292018237073104334030175923 438027355609656501045263885)
    ·
      refine ⟨164260258353621187891973957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438027355609656501045263885 164260258353621187891973957)
      ·
        refine ⟨30798798441303972729745117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164260258353621187891973957 30798798441303972729745117)
        ·
          refine ⟨11549549415488989773654419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30798798441303972729745117 11549549415488989773654419)
          ·
            refine ⟨17324324123233484660481629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11549549415488989773654419 17324324123233484660481629)
            ·
              refine ⟨6496621546212556747680611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17324324123233484660481629 6496621546212556747680611)
              ·
                refine ⟨9744932319318835121520917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6496621546212556747680611 9744932319318835121520917)
                ·
                  refine ⟨456793702468070396321293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9744932319318835121520917 456793702468070396321293)
                  ·
                    rfl

theorem cell23_8006423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 6].length) (baseStart_8006423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006423 prefixEnd_8006423 := by exact prefixLift 8006423
  have htrace : WordTrace (prefixWord ++ tailWord_8006423) baseStart_8006423 baseEnd_8006423 := by
    simpa [prefixWord, tailWord_8006423, baseEnd_8006423] using wordTrace_append hprefix tailTrace_8006423
  have hstable : (prefixWord ++ tailWord_8006423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006423).length < 2 ^ (prefixWord ++ tailWord_8006423).sum := by decide
  have hdescent : baseEnd_8006423 < baseStart_8006423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006426 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2]
def baseStart_8006426 : Nat := 118140960795 + 8006426 * 2 ^ 59
def prefixEnd_8006426 : Nat := 4983230072969 + 3 ^ 40 * 8006426 * 2
def baseEnd_8006426 : Nat := 4111144862654597055154123

theorem tailTrace_8006426 : CollatzResearch.WordTrace tailWord_8006426 prefixEnd_8006426 4111144862654597055154123 := by
  unfold tailWord_8006426
  simp only [CollatzResearch.WordTrace]
  refine ⟨73004586623023366385633783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194678897661395643695023421 73004586623023366385633783)
  ·
    refine ⟨109506879934535049578450675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73004586623023366385633783 109506879934535049578450675)
    ·
      refine ⟨164260319901802574367676013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109506879934535049578450675 164260319901802574367676013)
      ·
        refine ⟨61597619963175965387878505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164260319901802574367676013 61597619963175965387878505)
        ·
          refine ⟨46198214972381974040908879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61597619963175965387878505 46198214972381974040908879)
          ·
            refine ⟨69297322458572961061363319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46198214972381974040908879 69297322458572961061363319)
            ·
              refine ⟨103945983687859441592044979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69297322458572961061363319 103945983687859441592044979)
              ·
                refine ⟨155918975531789162388067469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103945983687859441592044979 155918975531789162388067469)
                ·
                  refine ⟨58469615824420935895525301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155918975531789162388067469 58469615824420935895525301)
                  ·
                    refine ⟨5481526483539462740205497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58469615824420935895525301 5481526483539462740205497)
                    ·
                      refine ⟨4111144862654597055154123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481526483539462740205497 4111144862654597055154123)
                      ·
                        rfl

theorem cell23_8006426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_8006426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006426 prefixEnd_8006426 := by exact prefixLift 8006426
  have htrace : WordTrace (prefixWord ++ tailWord_8006426) baseStart_8006426 baseEnd_8006426 := by
    simpa [prefixWord, tailWord_8006426, baseEnd_8006426] using wordTrace_append hprefix tailTrace_8006426
  have hstable : (prefixWord ++ tailWord_8006426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006426).length < 2 ^ (prefixWord ++ tailWord_8006426).sum := by decide
  have hdescent : baseEnd_8006426 < baseStart_8006426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006449 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 3, 6]
def baseStart_8006449 : Nat := 118140960795 + 8006449 * 2 ^ 59
def prefixEnd_8006449 : Nat := 4983230072969 + 3 ^ 40 * 8006449 * 2
def baseEnd_8006449 : Nat := 1370385557569883488388839

theorem tailTrace_8006449 : CollatzResearch.WordTrace tailWord_8006449 prefixEnd_8006449 1370385557569883488388839 := by
  unfold tailWord_8006449
  simp only [CollatzResearch.WordTrace]
  refine ⟨292019185371010140470622401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194679456914006760313748267 292019185371010140470622401)
  ·
    refine ⟨219014389028257605352966801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292019185371010140470622401 219014389028257605352966801)
    ·
      refine ⟨164260791771193204014725101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219014389028257605352966801 164260791771193204014725101)
      ·
        refine ⟨61597796914197451505521913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164260791771193204014725101 61597796914197451505521913)
        ·
          refine ⟨46198347685648088629141435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61597796914197451505521913 46198347685648088629141435)
          ·
            refine ⟨69297521528472132943712153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46198347685648088629141435 69297521528472132943712153)
            ·
              refine ⟨51973141146354099707784115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69297521528472132943712153 51973141146354099707784115)
              ·
                refine ⟨77959711719531149561676173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51973141146354099707784115 77959711719531149561676173)
                ·
                  refine ⟨29234891894824181085628565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77959711719531149561676173 29234891894824181085628565)
                  ·
                    refine ⟨1370385557569883488388839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29234891894824181085628565 1370385557569883488388839)
                    ·
                      rfl

theorem cell23_8006449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_8006449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006449 prefixEnd_8006449 := by exact prefixLift 8006449
  have htrace : WordTrace (prefixWord ++ tailWord_8006449) baseStart_8006449 baseEnd_8006449 := by
    simpa [prefixWord, tailWord_8006449, baseEnd_8006449] using wordTrace_append hprefix tailTrace_8006449
  have hstable : (prefixWord ++ tailWord_8006449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006449).length < 2 ^ (prefixWord ++ tailWord_8006449).sum := by decide
  have hdescent : baseEnd_8006449 < baseStart_8006449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006456 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_8006456 : Nat := 118140960795 + 8006456 * 2 ^ 59
def prefixEnd_8006456 : Nat := 4983230072969 + 3 ^ 40 * 8006456 * 2
def baseEnd_8006456 : Nat := 4111160267074231937778985

theorem tailTrace_8006456 : CollatzResearch.WordTrace tailWord_8006456 prefixEnd_8006456 4111160267074231937778985 := by
  unfold tailWord_8006456
  simp only [CollatzResearch.WordTrace]
  refine ⟨146009720340992390333063611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194679627121323187110751481 146009720340992390333063611)
  ·
    refine ⟨219014580511488585499595417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146009720340992390333063611 219014580511488585499595417)
    ·
      refine ⟨164260935383616439124696563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219014580511488585499595417 164260935383616439124696563)
      ·
        refine ⟨246391403075424658687044845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164260935383616439124696563 246391403075424658687044845)
        ·
          refine ⟨92396776153284247007641817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246391403075424658687044845 92396776153284247007641817)
          ·
            refine ⟨69297582114963185255731363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92396776153284247007641817 69297582114963185255731363)
            ·
              refine ⟨103946373172444777883597045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69297582114963185255731363 103946373172444777883597045)
              ·
                refine ⟨9744972484916697926587223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103946373172444777883597045 9744972484916697926587223)
                ·
                  refine ⟨14617458727375046889880835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9744972484916697926587223 14617458727375046889880835)
                  ·
                    refine ⟨21926188091062570334821253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14617458727375046889880835 21926188091062570334821253)
                    ·
                      refine ⟨4111160267074231937778985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21926188091062570334821253 4111160267074231937778985)
                      ·
                        rfl

theorem cell23_8006456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_8006456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006456 prefixEnd_8006456 := by exact prefixLift 8006456
  have htrace : WordTrace (prefixWord ++ tailWord_8006456) baseStart_8006456 baseEnd_8006456 := by
    simpa [prefixWord, tailWord_8006456, baseEnd_8006456] using wordTrace_append hprefix tailTrace_8006456
  have hstable : (prefixWord ++ tailWord_8006456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006456).length < 2 ^ (prefixWord ++ tailWord_8006456).sum := by decide
  have hdescent : baseEnd_8006456 < baseStart_8006456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006469 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_8006469 : Nat := 118140960795 + 8006469 * 2 ^ 59
def prefixEnd_8006469 : Nat := 4983230072969 + 3 ^ 40 * 8006469 * 2
def baseEnd_8006469 : Nat := 4111166942322740386916425

theorem tailTrace_8006469 : CollatzResearch.WordTrace tailWord_8006469 prefixEnd_8006469 4111166942322740386916425 := by
  unfold tailWord_8006469
  simp only [CollatzResearch.WordTrace]
  refine ⟨292019914830937683886350461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194679943220625122590900307 292019914830937683886350461)
  ·
    refine ⟨109507468061601631457381423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292019914830937683886350461 109507468061601631457381423)
    ·
      refine ⟨164261202092402447186072135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109507468061601631457381423 164261202092402447186072135)
      ·
        refine ⟨246391803138603670779108203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164261202092402447186072135 246391803138603670779108203)
        ·
          refine ⟨369587704707905506168662305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246391803138603670779108203 369587704707905506168662305)
          ·
            refine ⟨277190778530929129626496729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369587704707905506168662305 277190778530929129626496729)
            ·
              refine ⟨207893083898196847219872547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277190778530929129626496729 207893083898196847219872547)
              ·
                refine ⟨311839625847295270829808821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207893083898196847219872547 311839625847295270829808821)
                ·
                  refine ⟨29234964923183931640294577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311839625847295270829808821 29234964923183931640294577)
                  ·
                    refine ⟨21926223692387948730220933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29234964923183931640294577 21926223692387948730220933)
                    ·
                      refine ⟨4111166942322740386916425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21926223692387948730220933 4111166942322740386916425)
                      ·
                        rfl

theorem cell23_8006469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_8006469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006469 prefixEnd_8006469 := by exact prefixLift 8006469
  have htrace : WordTrace (prefixWord ++ tailWord_8006469) baseStart_8006469 baseEnd_8006469 := by
    simpa [prefixWord, tailWord_8006469, baseEnd_8006469] using wordTrace_append hprefix tailTrace_8006469
  have hstable : (prefixWord ++ tailWord_8006469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006469).length < 2 ^ (prefixWord ++ tailWord_8006469).sum := by decide
  have hdescent : baseEnd_8006469 < baseStart_8006469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006476 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_8006476 : Nat := 118140960795 + 8006476 * 2 ^ 59
def prefixEnd_8006476 : Nat := 4983230072969 + 3 ^ 40 * 8006476 * 2
def baseEnd_8006476 : Nat := 4111170536687321859528893

theorem tailTrace_8006476 : CollatzResearch.WordTrace tailWord_8006476 prefixEnd_8006476 4111170536687321859528893 := by
  unfold tailWord_8006476
  simp only [CollatzResearch.WordTrace]
  refine ⟨146010085070956162040927641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194680113427941549387903521 146010085070956162040927641)
  ·
    refine ⟨109507563803217121530695731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146010085070956162040927641 109507563803217121530695731)
    ·
      refine ⟨164261345704825682296043597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109507563803217121530695731 164261345704825682296043597)
      ·
        refine ⟨61598004639309630861016349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164261345704825682296043597 61598004639309630861016349)
        ·
          refine ⟨23099251739741111572881131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61598004639309630861016349 23099251739741111572881131)
          ·
            refine ⟨34648877609611667359321697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23099251739741111572881131 34648877609611667359321697)
            ·
              refine ⟨25986658207208750519491273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34648877609611667359321697 25986658207208750519491273)
              ·
                refine ⟨19489993655406562889618455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25986658207208750519491273 19489993655406562889618455)
                ·
                  refine ⟨29234990483109844334427683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19489993655406562889618455 29234990483109844334427683)
                  ·
                    refine ⟨43852485724664766501641525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29234990483109844334427683 43852485724664766501641525)
                    ·
                      refine ⟨4111170536687321859528893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43852485724664766501641525 4111170536687321859528893)
                      ·
                        rfl

theorem cell23_8006476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_8006476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006476 prefixEnd_8006476 := by exact prefixLift 8006476
  have htrace : WordTrace (prefixWord ++ tailWord_8006476) baseStart_8006476 baseEnd_8006476 := by
    simpa [prefixWord, tailWord_8006476, baseEnd_8006476] using wordTrace_append hprefix tailTrace_8006476
  have hstable : (prefixWord ++ tailWord_8006476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006476).length < 2 ^ (prefixWord ++ tailWord_8006476).sum := by decide
  have hdescent : baseEnd_8006476 < baseStart_8006476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006510 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_8006510 : Nat := 118140960795 + 8006510 * 2 ^ 59
def prefixEnd_8006510 : Nat := 4983230072969 + 3 ^ 40 * 8006510 * 2
def baseEnd_8006510 : Nat := 4111187995029574726503737

theorem tailTrace_8006510 : CollatzResearch.WordTrace tailWord_8006510 prefixEnd_8006510 4111187995029574726503737 := by
  unfold tailWord_8006510
  simp only [CollatzResearch.WordTrace]
  refine ⟨36502676277973643486074123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194680940149192765259061989 36502676277973643486074123)
  ·
    refine ⟨54754014416960465229111185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36502676277973643486074123 54754014416960465229111185)
    ·
      refine ⟨41065510812720348921833389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54754014416960465229111185 41065510812720348921833389)
      ·
        refine ⟨15399566554770130845687521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41065510812720348921833389 15399566554770130845687521)
        ·
          refine ⟨11549674916077598134265641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15399566554770130845687521 11549674916077598134265641)
          ·
            refine ⟨8662256187058198600699231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11549674916077598134265641 8662256187058198600699231)
            ·
              refine ⟨12993384280587297901048847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8662256187058198600699231 12993384280587297901048847)
              ·
                refine ⟨19490076420880946851573271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12993384280587297901048847 19490076420880946851573271)
                ·
                  refine ⟨29235114631321420277359907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19490076420880946851573271 29235114631321420277359907)
                  ·
                    refine ⟨43852671946982130416039861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29235114631321420277359907 43852671946982130416039861)
                    ·
                      refine ⟨4111187995029574726503737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43852671946982130416039861 4111187995029574726503737)
                      ·
                        rfl

theorem cell23_8006510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_8006510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006510 prefixEnd_8006510 := by exact prefixLift 8006510
  have htrace : WordTrace (prefixWord ++ tailWord_8006510) baseStart_8006510 baseEnd_8006510 := by
    simpa [prefixWord, tailWord_8006510, baseEnd_8006510] using wordTrace_append hprefix tailTrace_8006510
  have hstable : (prefixWord ++ tailWord_8006510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006510).length < 2 ^ (prefixWord ++ tailWord_8006510).sum := by decide
  have hdescent : baseEnd_8006510 < baseStart_8006510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006519 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_8006519 : Nat := 118140960795 + 8006519 * 2 ^ 59
def prefixEnd_8006519 : Nat := 4983230072969 + 3 ^ 40 * 8006519 * 2
def baseEnd_8006519 : Nat := 4111192616355465191291195

theorem tailTrace_8006519 : CollatzResearch.WordTrace tailWord_8006519 prefixEnd_8006519 4111192616355465191291195 := by
  unfold tailWord_8006519
  simp only [CollatzResearch.WordTrace]
  refine ⟨292021738480756542425670611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194681158987171028283780407 292021738480756542425670611)
  ·
    refine ⟨438032607721134813638505917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292021738480756542425670611 438032607721134813638505917)
    ·
      refine ⟨164262227895425555114439719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438032607721134813638505917 164262227895425555114439719)
      ·
        refine ⟨246393341843138332671659579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164262227895425555114439719 246393341843138332671659579)
        ·
          refine ⟨369590012764707499007489369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246393341843138332671659579 369590012764707499007489369)
          ·
            refine ⟨277192509573530624255617027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369590012764707499007489369 277192509573530624255617027)
            ·
              refine ⟨415788764360295936383425541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277192509573530624255617027 415788764360295936383425541)
              ·
                refine ⟨77960393317555488071892289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415788764360295936383425541 77960393317555488071892289)
                ·
                  refine ⟨58470294988166616053919217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77960393317555488071892289 58470294988166616053919217)
                  ·
                    refine ⟨43852721241124962040439413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58470294988166616053919217 43852721241124962040439413)
                    ·
                      refine ⟨4111192616355465191291195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43852721241124962040439413 4111192616355465191291195)
                      ·
                        rfl

theorem cell23_8006519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_8006519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006519 prefixEnd_8006519 := by exact prefixLift 8006519
  have htrace : WordTrace (prefixWord ++ tailWord_8006519) baseStart_8006519 baseEnd_8006519 := by
    simpa [prefixWord, tailWord_8006519, baseEnd_8006519] using wordTrace_append hprefix tailTrace_8006519
  have hstable : (prefixWord ++ tailWord_8006519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006519).length < 2 ^ (prefixWord ++ tailWord_8006519).sum := by decide
  have hdescent : baseEnd_8006519 < baseStart_8006519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006523 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 3]
def baseStart_8006523 : Nat := 118140960795 + 8006523 * 2 ^ 59
def prefixEnd_8006523 : Nat := 4983230072969 + 3 ^ 40 * 8006523 * 2
def baseEnd_8006523 : Nat := 4111194670278083175641177

theorem tailTrace_8006523 : CollatzResearch.WordTrace tailWord_8006523 prefixEnd_8006523 4111194670278083175641177 := by
  unfold tailWord_8006523
  simp only [CollatzResearch.WordTrace]
  refine ⟨292021884372742051108816223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194681256248494700739210815 292021884372742051108816223)
  ·
    refine ⟨438032826559113076663224335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292021884372742051108816223 438032826559113076663224335)
    ·
      refine ⟨657049239838669614994836503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438032826559113076663224335 657049239838669614994836503)
      ·
        refine ⟨985573859758004422492254755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657049239838669614994836503 985573859758004422492254755)
        ·
          refine ⟨1478360789637006633738382133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985573859758004422492254755 1478360789637006633738382133)
          ·
            refine ⟨138596324028469371912973325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1478360789637006633738382133 138596324028469371912973325)
            ·
              refine ⟨51973621510676014467364997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138596324028469371912973325 51973621510676014467364997)
              ·
                refine ⟨9745054033251752712630937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51973621510676014467364997 9745054033251752712630937)
                ·
                  refine ⟨7308790524938814534473203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9745054033251752712630937 7308790524938814534473203)
                  ·
                    refine ⟨10963185787408221801709805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7308790524938814534473203 10963185787408221801709805)
                    ·
                      refine ⟨4111194670278083175641177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963185787408221801709805 4111194670278083175641177)
                      ·
                        rfl

theorem cell23_8006523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 3].length) (baseStart_8006523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006523 prefixEnd_8006523 := by exact prefixLift 8006523
  have htrace : WordTrace (prefixWord ++ tailWord_8006523) baseStart_8006523 baseEnd_8006523 := by
    simpa [prefixWord, tailWord_8006523, baseEnd_8006523] using wordTrace_append hprefix tailTrace_8006523
  have hstable : (prefixWord ++ tailWord_8006523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006523).length < 2 ^ (prefixWord ++ tailWord_8006523).sum := by decide
  have hdescent : baseEnd_8006523 < baseStart_8006523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006533 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 3, 3, 2]
def baseStart_8006533 : Nat := 118140960795 + 8006533 * 2 ^ 59
def prefixEnd_8006533 : Nat := 4983230072969 + 3 ^ 40 * 8006533 * 2
def baseEnd_8006533 : Nat := 4111199805084628136516131

theorem tailTrace_8006533 : CollatzResearch.WordTrace tailWord_8006533 prefixEnd_8006533 4111199805084628136516131 := by
  unfold tailWord_8006533
  simp only [CollatzResearch.WordTrace]
  refine ⟨292022249102705822816680253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194681499401803881877786835 292022249102705822816680253)
  ·
    refine ⟨109508343413514683556255095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292022249102705822816680253 109508343413514683556255095)
    ·
      refine ⟨164262515120272025334382643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109508343413514683556255095 164262515120272025334382643)
      ·
        refine ⟨246393772680408038001573965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164262515120272025334382643 246393772680408038001573965)
        ·
          refine ⟨92397664755153014250590237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246393772680408038001573965 92397664755153014250590237)
          ·
            refine ⟨34649124283182380343971339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92397664755153014250590237 34649124283182380343971339)
            ·
              refine ⟨51973686424773570515957009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34649124283182380343971339 51973686424773570515957009)
              ·
                refine ⟨38980264818580177886967757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51973686424773570515957009 38980264818580177886967757)
                ·
                  refine ⟨14617599306967566707612909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38980264818580177886967757 14617599306967566707612909)
                  ·
                    refine ⟨5481599740112837515354841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14617599306967566707612909 5481599740112837515354841)
                    ·
                      refine ⟨4111199805084628136516131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481599740112837515354841 4111199805084628136516131)
                      ·
                        rfl

theorem cell23_8006533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_8006533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006533 prefixEnd_8006533 := by exact prefixLift 8006533
  have htrace : WordTrace (prefixWord ++ tailWord_8006533) baseStart_8006533 baseEnd_8006533 := by
    simpa [prefixWord, tailWord_8006533, baseEnd_8006533] using wordTrace_append hprefix tailTrace_8006533
  have hstable : (prefixWord ++ tailWord_8006533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006533).length < 2 ^ (prefixWord ++ tailWord_8006533).sum := by decide
  have hdescent : baseEnd_8006533 < baseStart_8006533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006539 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 1, 8]
def baseStart_8006539 : Nat := 118140960795 + 8006539 * 2 ^ 59
def prefixEnd_8006539 : Nat := 4983230072969 + 3 ^ 40 * 8006539 * 2
def baseEnd_8006539 : Nat := 1370400961989518371013701

theorem tailTrace_8006539 : CollatzResearch.WordTrace tailWord_8006539 prefixEnd_8006539 1370400961989518371013701 := by
  unfold tailWord_8006539
  simp only [CollatzResearch.WordTrace]
  refine ⟨292022467940684085841398671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194681645293789390560932447 292022467940684085841398671)
  ·
    refine ⟨438033701911026128762098007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292022467940684085841398671 438033701911026128762098007)
    ·
      refine ⟨657050552866539193143147011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438033701911026128762098007 657050552866539193143147011)
      ·
        refine ⟨985575829299808789714720517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657050552866539193143147011 985575829299808789714720517)
        ·
          refine ⟨184795467993714148071510097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 985575829299808789714720517 184795467993714148071510097)
          ·
            refine ⟨138596600995285611053632573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184795467993714148071510097 138596600995285611053632573)
            ·
              refine ⟨51973725373232104145112215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138596600995285611053632573 51973725373232104145112215)
              ·
                refine ⟨77960588059848156217668323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51973725373232104145112215 77960588059848156217668323)
                ·
                  refine ⟨116940882089772234326502485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77960588059848156217668323 116940882089772234326502485)
                  ·
                    refine ⟨1370400961989518371013701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116940882089772234326502485 1370400961989518371013701)
                    ·
                      rfl

theorem cell23_8006539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_8006539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006539 prefixEnd_8006539 := by exact prefixLift 8006539
  have htrace : WordTrace (prefixWord ++ tailWord_8006539) baseStart_8006539 baseEnd_8006539 := by
    simpa [prefixWord, tailWord_8006539, baseEnd_8006539] using wordTrace_append hprefix tailTrace_8006539
  have hstable : (prefixWord ++ tailWord_8006539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006539).length < 2 ^ (prefixWord ++ tailWord_8006539).sum := by decide
  have hdescent : baseEnd_8006539 < baseStart_8006539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006563 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 1, 4, 2]
def baseStart_8006563 : Nat := 118140960795 + 8006563 * 2 ^ 59
def prefixEnd_8006563 : Nat := 4983230072969 + 3 ^ 40 * 8006563 * 2
def baseEnd_8006563 : Nat := 4111215209504263019140993

theorem tailTrace_8006563 : CollatzResearch.WordTrace tailWord_8006563 prefixEnd_8006563 4111215209504263019140993 := by
  unfold tailWord_8006563
  simp only [CollatzResearch.WordTrace]
  refine ⟨292023343292597137940272343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194682228861731425293514895 292023343292597137940272343)
  ·
    refine ⟨438035014938895706910408515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292023343292597137940272343 438035014938895706910408515)
    ·
      refine ⟨657052522408343560365612773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438035014938895706910408515 657052522408343560365612773)
      ·
        refine ⟨123197347951564417568552395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657052522408343560365612773 123197347951564417568552395)
        ·
          refine ⟨184796021927346626352828593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123197347951564417568552395 184796021927346626352828593)
          ·
            refine ⟨138597016445509969764621445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184796021927346626352828593 138597016445509969764621445)
            ·
              refine ⟨25986940583533119330866521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138597016445509969764621445 25986940583533119330866521)
              ·
                refine ⟨19490205437649839498149891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25986940583533119330866521 19490205437649839498149891)
                ·
                  refine ⟨29235308156474759247224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19490205437649839498149891 29235308156474759247224837)
                  ·
                    refine ⟨5481620279339017358854657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29235308156474759247224837 5481620279339017358854657)
                    ·
                      refine ⟨4111215209504263019140993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481620279339017358854657 4111215209504263019140993)
                      ·
                        rfl

theorem cell23_8006563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_8006563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006563 prefixEnd_8006563 := by exact prefixLift 8006563
  have htrace : WordTrace (prefixWord ++ tailWord_8006563) baseStart_8006563 baseEnd_8006563 := by
    simpa [prefixWord, tailWord_8006563, baseEnd_8006563] using wordTrace_append hprefix tailTrace_8006563
  have hstable : (prefixWord ++ tailWord_8006563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006563).length < 2 ^ (prefixWord ++ tailWord_8006563).sum := by decide
  have hdescent : baseEnd_8006563 < baseStart_8006563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006567 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_8006567 : Nat := 118140960795 + 8006567 * 2 ^ 59
def prefixEnd_8006567 : Nat := 4983230072969 + 3 ^ 40 * 8006567 * 2
def baseEnd_8006567 : Nat := 4111217263426881003490975

theorem tailTrace_8006567 : CollatzResearch.WordTrace tailWord_8006567 prefixEnd_8006567 4111217263426881003490975 := by
  unfold tailWord_8006567
  simp only [CollatzResearch.WordTrace]
  refine ⟨292023489184582646623417955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194682326123055097748945303 292023489184582646623417955)
  ·
    refine ⟨438035233776873969935126933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292023489184582646623417955 438035233776873969935126933)
    ·
      refine ⟨20532901583290967340709075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 438035233776873969935126933 20532901583290967340709075)
      ·
        refine ⟨30799352374936451011063613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20532901583290967340709075 30799352374936451011063613)
        ·
          refine ⟨11549757140601169129148855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30799352374936451011063613 11549757140601169129148855)
          ·
            refine ⟨17324635710901753693723283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11549757140601169129148855 17324635710901753693723283)
            ·
              refine ⟨25986953566352630540584925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17324635710901753693723283 25986953566352630540584925)
              ·
                refine ⟨9745107587382236452719347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25986953566352630540584925 9745107587382236452719347)
                ·
                  refine ⟨14617661381073354679079021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745107587382236452719347 14617661381073354679079021)
                  ·
                    refine ⟨5481623017902508004654633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14617661381073354679079021 5481623017902508004654633)
                    ·
                      refine ⟨4111217263426881003490975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481623017902508004654633 4111217263426881003490975)
                      ·
                        rfl

theorem cell23_8006567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_8006567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006567 prefixEnd_8006567 := by exact prefixLift 8006567
  have htrace : WordTrace (prefixWord ++ tailWord_8006567) baseStart_8006567 baseEnd_8006567 := by
    simpa [prefixWord, tailWord_8006567, baseEnd_8006567] using wordTrace_append hprefix tailTrace_8006567
  have hstable : (prefixWord ++ tailWord_8006567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006567).length < 2 ^ (prefixWord ++ tailWord_8006567).sum := by decide
  have hdescent : baseEnd_8006567 < baseStart_8006567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006569 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 9]
def baseStart_8006569 : Nat := 118140960795 + 8006569 * 2 ^ 59
def prefixEnd_8006569 : Nat := 4983230072969 + 3 ^ 40 * 8006569 * 2
def baseEnd_8006569 : Nat := 456802032265354443962885

theorem tailTrace_8006569 : CollatzResearch.WordTrace tailWord_8006569 prefixEnd_8006569 456802032265354443962885 := by
  unfold tailWord_8006569
  simp only [CollatzResearch.WordTrace]
  refine ⟨292023562130575400964990761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194682374753716933976660507 292023562130575400964990761)
  ·
    refine ⟨219017671597931550723743071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292023562130575400964990761 219017671597931550723743071)
    ·
      refine ⟨328526507396897326085614607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219017671597931550723743071 328526507396897326085614607)
      ·
        refine ⟨492789761095345989128421911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328526507396897326085614607 492789761095345989128421911)
        ·
          refine ⟨739184641643018983692632867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492789761095345989128421911 739184641643018983692632867)
          ·
            refine ⟨1108776962464528475538949301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739184641643018983692632867 1108776962464528475538949301)
            ·
              refine ⟨103947840231049544581776497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1108776962464528475538949301 103947840231049544581776497)
              ·
                refine ⟨77960880173287158436332373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103947840231049544581776497 77960880173287158436332373)
                ·
                  refine ⟨456802032265354443962885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77960880173287158436332373 456802032265354443962885)
                  ·
                    rfl

theorem cell23_8006569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_8006569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006569 prefixEnd_8006569 := by exact prefixLift 8006569
  have htrace : WordTrace (prefixWord ++ tailWord_8006569) baseStart_8006569 baseEnd_8006569 := by
    simpa [prefixWord, tailWord_8006569, baseEnd_8006569] using wordTrace_append hprefix tailTrace_8006569
  have hstable : (prefixWord ++ tailWord_8006569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006569).length < 2 ^ (prefixWord ++ tailWord_8006569).sum := by decide
  have hdescent : baseEnd_8006569 < baseStart_8006569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006579 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9]
def baseStart_8006579 : Nat := 118140960795 + 8006579 * 2 ^ 59
def prefixEnd_8006579 : Nat := 4983230072969 + 3 ^ 40 * 8006579 * 2
def baseEnd_8006579 : Nat := 4111223425194734956540919

theorem tailTrace_8006579 : CollatzResearch.WordTrace tailWord_8006579 prefixEnd_8006579 4111223425194734956540919 := by
  unfold tailWord_8006579
  simp only [CollatzResearch.WordTrace]
  refine ⟨292023926860539172672854791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194682617907026115115236527 292023926860539172672854791)
  ·
    refine ⟨438035890290808759009282187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292023926860539172672854791 438035890290808759009282187)
    ·
      refine ⟨657053835436213138513923281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438035890290808759009282187 657053835436213138513923281)
      ·
        refine ⟨492790376577159853885442461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657053835436213138513923281 492790376577159853885442461)
        ·
          refine ⟨184796391216434945207040923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492790376577159853885442461 184796391216434945207040923)
          ·
            refine ⟨277194586824652417810561385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184796391216434945207040923 277194586824652417810561385)
            ·
              refine ⟨207895940118489313357921039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277194586824652417810561385 207895940118489313357921039)
              ·
                refine ⟨311843910177733970036881559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207895940118489313357921039 311843910177733970036881559)
                ·
                  refine ⟨467765865266600955055322339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311843910177733970036881559 467765865266600955055322339)
                  ·
                    refine ⟨701648797899901432582983509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467765865266600955055322339 701648797899901432582983509)
                    ·
                      refine ⟨4111223425194734956540919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 701648797899901432582983509 4111223425194734956540919)
                      ·
                        rfl

theorem cell23_8006579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_8006579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006579 prefixEnd_8006579 := by exact prefixLift 8006579
  have htrace : WordTrace (prefixWord ++ tailWord_8006579) baseStart_8006579 baseEnd_8006579 := by
    simpa [prefixWord, tailWord_8006579, baseEnd_8006579] using wordTrace_append hprefix tailTrace_8006579
  have hstable : (prefixWord ++ tailWord_8006579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006579).length < 2 ^ (prefixWord ++ tailWord_8006579).sum := by decide
  have hdescent : baseEnd_8006579 < baseStart_8006579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006586 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 7]
def baseStart_8006586 : Nat := 118140960795 + 8006586 * 2 ^ 59
def prefixEnd_8006586 : Nat := 4983230072969 + 3 ^ 40 * 8006586 * 2
def baseEnd_8006586 : Nat := 456803002173257381017043

theorem tailTrace_8006586 : CollatzResearch.WordTrace tailWord_8006586 prefixEnd_8006586 456803002173257381017043 := by
  unfold tailWord_8006586
  simp only [CollatzResearch.WordTrace]
  refine ⟨73006045542878453217089903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194682788114342541912239741 73006045542878453217089903)
  ·
    refine ⟨109509068314317679825634855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73006045542878453217089903 109509068314317679825634855)
    ·
      refine ⟨164263602471476519738452283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109509068314317679825634855 164263602471476519738452283)
      ·
        refine ⟨246395403707214779607678425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164263602471476519738452283 246395403707214779607678425)
        ·
          refine ⟨184796552780411084705758819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246395403707214779607678425 184796552780411084705758819)
          ·
            refine ⟨277194829170616627058638229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184796552780411084705758819 277194829170616627058638229)
            ·
              refine ⟨12993507617372654393373667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277194829170616627058638229 12993507617372654393373667)
              ·
                refine ⟨19490261426058981590060501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12993507617372654393373667 19490261426058981590060501)
                ·
                  refine ⟨456803002173257381017043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19490261426058981590060501 456803002173257381017043)
                  ·
                    rfl

theorem cell23_8006586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_8006586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006586 prefixEnd_8006586 := by exact prefixLift 8006586
  have htrace : WordTrace (prefixWord ++ tailWord_8006586) baseStart_8006586 baseEnd_8006586 := by
    simpa [prefixWord, tailWord_8006586, baseEnd_8006586] using wordTrace_append hprefix tailTrace_8006586
  have hstable : (prefixWord ++ tailWord_8006586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006586).length < 2 ^ (prefixWord ++ tailWord_8006586).sum := by decide
  have hdescent : baseEnd_8006586 < baseStart_8006586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
