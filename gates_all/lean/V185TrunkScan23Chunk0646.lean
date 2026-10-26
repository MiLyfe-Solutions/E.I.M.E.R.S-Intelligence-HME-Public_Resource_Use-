import V185TrunkScan23Chunk0645

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3819854 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3819854 : Nat := 118140960795 + 3819854 * 2 ^ 59
def prefixEnd_3819854 : Nat := 4983230072969 + 3 ^ 40 * 3819854 * 2
def baseEnd_3819854 : Nat := 1961421131999603037357817

theorem tailTrace_3819854 : CollatzResearch.WordTrace tailWord_3819854 prefixEnd_3819854 1961421131999603037357817 := by
  unfold tailWord_3819854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415190137916101496219327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92881014068885874646503077 17415190137916101496219327)
  ·
    refine ⟨26122785206874152244328991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17415190137916101496219327 26122785206874152244328991)
    ·
      refine ⟨39184177810311228366493487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26122785206874152244328991 39184177810311228366493487)
      ·
        refine ⟨58776266715466842549740231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39184177810311228366493487 58776266715466842549740231)
        ·
          refine ⟨88164400073200263824610347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58776266715466842549740231 88164400073200263824610347)
          ·
            refine ⟨132246600109800395736915521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88164400073200263824610347 132246600109800395736915521)
            ·
              refine ⟨99184950082350296802686641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132246600109800395736915521 99184950082350296802686641)
              ·
                refine ⟨74388712561762722602014981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99184950082350296802686641 74388712561762722602014981)
                ·
                  refine ⟨13947883605330510487877809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74388712561762722602014981 13947883605330510487877809)
                  ·
                    refine ⟨10460912703997882865908357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13947883605330510487877809 10460912703997882865908357)
                    ·
                      refine ⟨1961421131999603037357817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10460912703997882865908357 1961421131999603037357817)
                      ·
                        rfl

theorem cell23_3819854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3819854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819854 prefixEnd_3819854 := by exact prefixLift 3819854
  have htrace : WordTrace (prefixWord ++ tailWord_3819854) baseStart_3819854 baseEnd_3819854 := by
    simpa [prefixWord, tailWord_3819854, baseEnd_3819854] using wordTrace_append hprefix tailTrace_3819854
  have hstable : (prefixWord ++ tailWord_3819854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819854).length < 2 ^ (prefixWord ++ tailWord_3819854).sum := by decide
  have hdescent : baseEnd_3819854 < baseStart_3819854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819858 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_3819858 : Nat := 118140960795 + 3819858 * 2 ^ 59
def prefixEnd_3819858 : Nat := 4983230072969 + 3 ^ 40 * 3819858 * 2
def baseEnd_3819858 : Nat := 1961423185922221021707799

theorem tailTrace_3819858 : CollatzResearch.WordTrace tailWord_3819858 prefixEnd_3819858 1961423185922221021707799 := by
  unfold tailWord_3819858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34830416748828580163225057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92881111330209547101933485 34830416748828580163225057)
  ·
    refine ⟨26122812561621435122418793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34830416748828580163225057 26122812561621435122418793)
    ·
      refine ⟨19592109421216076341814095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26122812561621435122418793 19592109421216076341814095)
      ·
        refine ⟨29388164131824114512721143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592109421216076341814095 29388164131824114512721143)
        ·
          refine ⟨44082246197736171769081715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29388164131824114512721143 44082246197736171769081715)
          ·
            refine ⟨66123369296604257653622573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44082246197736171769081715 66123369296604257653622573)
            ·
              refine ⟨24796263486226596620108465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66123369296604257653622573 24796263486226596620108465)
              ·
                refine ⟨18597197614669947465081349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24796263486226596620108465 18597197614669947465081349)
                ·
                  refine ⟨3486974552750615149702753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18597197614669947465081349 3486974552750615149702753)
                  ·
                    refine ⟨2615230914562961362277065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3486974552750615149702753 2615230914562961362277065)
                    ·
                      refine ⟨1961423185922221021707799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615230914562961362277065 1961423185922221021707799)
                      ·
                        rfl

theorem cell23_3819858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_3819858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819858 prefixEnd_3819858 := by exact prefixLift 3819858
  have htrace : WordTrace (prefixWord ++ tailWord_3819858) baseStart_3819858 baseEnd_3819858 := by
    simpa [prefixWord, tailWord_3819858, baseEnd_3819858] using wordTrace_append hprefix tailTrace_3819858
  have hstable : (prefixWord ++ tailWord_3819858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819858).length < 2 ^ (prefixWord ++ tailWord_3819858).sum := by decide
  have hdescent : baseEnd_3819858 < baseStart_3819858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819861 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3819861 : Nat := 118140960795 + 3819861 * 2 ^ 59
def prefixEnd_3819861 : Nat := 4983230072969 + 3 ^ 40 * 3819861 * 2
def baseEnd_3819861 : Nat := 1961424726364184509970285

theorem tailTrace_3819861 : CollatzResearch.WordTrace tailWord_3819861 prefixEnd_3819861 1961424726364184509970285 := by
  unfold tailWord_3819861
  simp only [CollatzResearch.WordTrace]
  refine ⟨139321776414303452165259437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92881184276202301443506291 139321776414303452165259437)
  ·
    refine ⟨52245666155363794561972289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139321776414303452165259437 52245666155363794561972289)
    ·
      refine ⟨39184249616522845921479217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52245666155363794561972289 39184249616522845921479217)
      ·
        refine ⟨29388187212392134441109413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39184249616522845921479217 29388187212392134441109413)
        ·
          refine ⟨5510285102323525207708015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29388187212392134441109413 5510285102323525207708015)
          ·
            refine ⟨8265427653485287811562023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510285102323525207708015 8265427653485287811562023)
            ·
              refine ⟨12398141480227931717343035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8265427653485287811562023 12398141480227931717343035)
              ·
                refine ⟨18597212220341897576014553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12398141480227931717343035 18597212220341897576014553)
                ·
                  refine ⟨13947909165256423182010915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18597212220341897576014553 13947909165256423182010915)
                  ·
                    refine ⟨20921863747884634773016373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13947909165256423182010915 20921863747884634773016373)
                    ·
                      refine ⟨1961424726364184509970285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20921863747884634773016373 1961424726364184509970285)
                      ·
                        rfl

theorem cell23_3819861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3819861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819861 prefixEnd_3819861 := by exact prefixLift 3819861
  have htrace : WordTrace (prefixWord ++ tailWord_3819861) baseStart_3819861 baseEnd_3819861 := by
    simpa [prefixWord, tailWord_3819861, baseEnd_3819861] using wordTrace_append hprefix tailTrace_3819861
  have hstable : (prefixWord ++ tailWord_3819861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819861).length < 2 ^ (prefixWord ++ tailWord_3819861).sum := by decide
  have hdescent : baseEnd_3819861 < baseStart_3819861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819870 : List Nat := [4, 4, 2, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3819870 : Nat := 118140960795 + 3819870 * 2 ^ 59
def prefixEnd_3819870 : Nat := 4983230072969 + 3 ^ 40 * 3819870 * 2
def baseEnd_3819870 : Nat := 1961429347690074974757745

theorem tailTrace_3819870 : CollatzResearch.WordTrace tailWord_3819870 prefixEnd_3819870 1961429347690074974757745 := by
  unfold tailWord_3819870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415263083908855837792133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92881403114180564468224709 17415263083908855837792133)
  ·
    refine ⟨3265361828232910469586025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17415263083908855837792133 3265361828232910469586025)
    ·
      refine ⟨2449021371174682852189519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3265361828232910469586025 2449021371174682852189519)
      ·
        refine ⟨3673532056762024278284279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449021371174682852189519 3673532056762024278284279)
        ·
          refine ⟨5510298085143036417426419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673532056762024278284279 5510298085143036417426419)
          ·
            refine ⟨8265447127714554626139629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510298085143036417426419 8265447127714554626139629)
            ·
              refine ⟨3099542672892957984802361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8265447127714554626139629 3099542672892957984802361)
              ·
                refine ⟨2324657004669718488601771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099542672892957984802361 2324657004669718488601771)
                ·
                  refine ⟨3486985507004577732902657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324657004669718488601771 3486985507004577732902657)
                  ·
                    refine ⟨2615239130253433299676993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3486985507004577732902657 2615239130253433299676993)
                    ·
                      refine ⟨1961429347690074974757745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615239130253433299676993 1961429347690074974757745)
                      ·
                        rfl

theorem cell23_3819870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3819870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819870 prefixEnd_3819870 := by exact prefixLift 3819870
  have htrace : WordTrace (prefixWord ++ tailWord_3819870) baseStart_3819870 baseEnd_3819870 := by
    simpa [prefixWord, tailWord_3819870, baseEnd_3819870] using wordTrace_append hprefix tailTrace_3819870
  have hstable : (prefixWord ++ tailWord_3819870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819870).length < 2 ^ (prefixWord ++ tailWord_3819870).sum := by decide
  have hdescent : baseEnd_3819870 < baseStart_3819870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819911 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 2, 5]
def baseStart_3819911 : Nat := 118140960795 + 3819911 * 2 ^ 59
def prefixEnd_3819911 : Nat := 4983230072969 + 3 ^ 40 * 3819911 * 2
def baseEnd_3819911 : Nat := 653816800132303104781685

theorem tailTrace_3819911 : CollatzResearch.WordTrace tailWord_3819911 prefixEnd_3819911 653816800132303104781685 := by
  unfold tailWord_3819911
  simp only [CollatzResearch.WordTrace]
  refine ⟨139323600064122310704579587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92882400042748207136386391 139323600064122310704579587)
  ·
    refine ⟨208985400096183466056869381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139323600064122310704579587 208985400096183466056869381)
    ·
      refine ⟨39184762518034399885663009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208985400096183466056869381 39184762518034399885663009)
      ·
        refine ⟨29388571888525799914247257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39184762518034399885663009 29388571888525799914247257)
        ·
          refine ⟨22041428916394349935685443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29388571888525799914247257 22041428916394349935685443)
          ·
            refine ⟨33062143374591524903528165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22041428916394349935685443 33062143374591524903528165)
            ·
              refine ⟨6199151882735910919411531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33062143374591524903528165 6199151882735910919411531)
              ·
                refine ⟨9298727824103866379117297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6199151882735910919411531 9298727824103866379117297)
                ·
                  refine ⟨6974045868077899784337973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9298727824103866379117297 6974045868077899784337973)
                  ·
                    refine ⟨653816800132303104781685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6974045868077899784337973 653816800132303104781685)
                    ·
                      rfl

theorem cell23_3819911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_3819911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819911 prefixEnd_3819911 := by exact prefixLift 3819911
  have htrace : WordTrace (prefixWord ++ tailWord_3819911) baseStart_3819911 baseEnd_3819911 := by
    simpa [prefixWord, tailWord_3819911, baseEnd_3819911] using wordTrace_append hprefix tailTrace_3819911
  have hstable : (prefixWord ++ tailWord_3819911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819911).length < 2 ^ (prefixWord ++ tailWord_3819911).sum := by decide
  have hdescent : baseEnd_3819911 < baseStart_3819911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819941 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_3819941 : Nat := 118140960795 + 3819941 * 2 ^ 59
def prefixEnd_3819941 : Nat := 4983230072969 + 3 ^ 40 * 3819941 * 2
def baseEnd_3819941 : Nat := 653821934938848065656639

theorem tailTrace_3819941 : CollatzResearch.WordTrace tailWord_3819941 prefixEnd_3819941 653821934938848065656639 := by
  unfold tailWord_3819941
  simp only [CollatzResearch.WordTrace]
  refine ⟨139324694254013625828171677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92883129502675750552114451 139324694254013625828171677)
  ·
    refine ⟨52246760345255109685564379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139324694254013625828171677 52246760345255109685564379)
    ·
      refine ⟨78370140517882664528346569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52246760345255109685564379 78370140517882664528346569)
      ·
        refine ⟨58777605388411998396259927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78370140517882664528346569 58777605388411998396259927)
        ·
          refine ⟨88166408082617997594389891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58777605388411998396259927 88166408082617997594389891)
          ·
            refine ⟨132249612123926996391584837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88166408082617997594389891 132249612123926996391584837)
            ·
              refine ⟨24796802273236311823422157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132249612123926996391584837 24796802273236311823422157)
              ·
                refine ⟨9298800852463616933783309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24796802273236311823422157 9298800852463616933783309)
                ·
                  refine ⟨3487050319673856350168741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9298800852463616933783309 3487050319673856350168741)
                  ·
                    refine ⟨653821934938848065656639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487050319673856350168741 653821934938848065656639)
                    ·
                      rfl

theorem cell23_3819941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_3819941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819941 prefixEnd_3819941 := by exact prefixLift 3819941
  have htrace : WordTrace (prefixWord ++ tailWord_3819941) baseStart_3819941 baseEnd_3819941 := by
    simpa [prefixWord, tailWord_3819941, baseEnd_3819941] using wordTrace_append hprefix tailTrace_3819941
  have hstable : (prefixWord ++ tailWord_3819941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819941).length < 2 ^ (prefixWord ++ tailWord_3819941).sum := by decide
  have hdescent : baseEnd_3819941 < baseStart_3819941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819975 : List Nat := [1, 1, 4, 1, 1, 5, 2, 3, 1, 4]
def baseStart_3819975 : Nat := 118140960795 + 3819975 * 2 ^ 59
def prefixEnd_3819975 : Nat := 4983230072969 + 3 ^ 40 * 3819975 * 2
def baseEnd_3819975 : Nat := 653827754386265687981587

theorem tailTrace_3819975 : CollatzResearch.WordTrace tailWord_3819975 prefixEnd_3819975 653827754386265687981587 := by
  unfold tailWord_3819975
  simp only [CollatzResearch.WordTrace]
  refine ⟨139325934335890449634909379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92883956223926966423272919 139325934335890449634909379)
  ·
    refine ⟨208988901503835674452364069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139325934335890449634909379 208988901503835674452364069)
    ·
      refine ⟨39185419031969188959818263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208988901503835674452364069 39185419031969188959818263)
      ·
        refine ⟨58778128547953783439727395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39185419031969188959818263 58778128547953783439727395)
        ·
          refine ⟨88167192821930675159591093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58778128547953783439727395 88167192821930675159591093)
          ·
            refine ⟨8265674327056000796211665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88167192821930675159591093 8265674327056000796211665)
            ·
              refine ⟨6199255745292000597158749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8265674327056000796211665 6199255745292000597158749)
              ·
                refine ⟨2324720904484500223934531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6199255745292000597158749 2324720904484500223934531)
                ·
                  refine ⟨3487081356726750335901797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324720904484500223934531 3487081356726750335901797)
                  ·
                    refine ⟨653827754386265687981587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487081356726750335901797 653827754386265687981587)
                    ·
                      rfl

theorem cell23_3819975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_3819975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819975 prefixEnd_3819975 := by exact prefixLift 3819975
  have htrace : WordTrace (prefixWord ++ tailWord_3819975) baseStart_3819975 baseEnd_3819975 := by
    simpa [prefixWord, tailWord_3819975, baseEnd_3819975] using wordTrace_append hprefix tailTrace_3819975
  have hstable : (prefixWord ++ tailWord_3819975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819975).length < 2 ^ (prefixWord ++ tailWord_3819975).sum := by decide
  have hdescent : baseEnd_3819975 < baseStart_3819975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819988 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 6]
def baseStart_3819988 : Nat := 118140960795 + 3819988 * 2 ^ 59
def prefixEnd_3819988 : Nat := 4983230072969 + 3 ^ 40 * 3819988 * 2
def baseEnd_3819988 : Nat := 217943326489700612564689

theorem tailTrace_3819988 : CollatzResearch.WordTrace tailWord_3819988 prefixEnd_3819988 217943326489700612564689 := by
  unfold tailWord_3819988
  simp only [CollatzResearch.WordTrace]
  refine ⟨69663204242421676427566309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92884272323228901903421745 69663204242421676427566309)
  ·
    refine ⟨13061850795454064330168683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69663204242421676427566309 13061850795454064330168683)
    ·
      refine ⟨19592776193181096495253025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061850795454064330168683 19592776193181096495253025)
      ·
        refine ⟨14694582144885822371439769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19592776193181096495253025 14694582144885822371439769)
        ·
          refine ⟨11020936608664366778579827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14694582144885822371439769 11020936608664366778579827)
          ·
            refine ⟨16531404912996550167869741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11020936608664366778579827 16531404912996550167869741)
            ·
              refine ⟨6199276842373706312951153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16531404912996550167869741 6199276842373706312951153)
              ·
                refine ⟨4649457631780279734713365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6199276842373706312951153 4649457631780279734713365)
                ·
                  refine ⟨217943326489700612564689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4649457631780279734713365 217943326489700612564689)
                  ·
                    rfl

theorem cell23_3819988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_3819988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3819988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3819988 prefixEnd_3819988 := by exact prefixLift 3819988
  have htrace : WordTrace (prefixWord ++ tailWord_3819988) baseStart_3819988 baseEnd_3819988 := by
    simpa [prefixWord, tailWord_3819988, baseEnd_3819988] using wordTrace_append hprefix tailTrace_3819988
  have hstable : (prefixWord ++ tailWord_3819988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819988).length < 2 ^ (prefixWord ++ tailWord_3819988).sum := by decide
  have hdescent : baseEnd_3819988 < baseStart_3819988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820005 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 6]
def baseStart_3820005 : Nat := 118140960795 + 3820005 * 2 ^ 59
def prefixEnd_3820005 : Nat := 4983230072969 + 3 ^ 40 * 3820005 * 2
def baseEnd_3820005 : Nat := 217944296397603549618847

theorem tailTrace_3820005 : CollatzResearch.WordTrace tailWord_3820005 prefixEnd_3820005 217944296397603549618847 := by
  unfold tailWord_3820005
  simp only [CollatzResearch.WordTrace]
  refine ⟨139327028525781764758501469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92884685683854509839000979 139327028525781764758501469)
  ·
    refine ⟨52247635697168161784438051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139327028525781764758501469 52247635697168161784438051)
    ·
      refine ⟨78371453545752242676657077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52247635697168161784438051 78371453545752242676657077)
      ·
        refine ⟨7347323769914272750936601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78371453545752242676657077 7347323769914272750936601)
        ·
          refine ⟨5510492827435704563202451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7347323769914272750936601 5510492827435704563202451)
          ·
            refine ⟨8265739241153556844803677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510492827435704563202451 8265739241153556844803677)
            ·
              refine ⟨3099652215432583816801379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8265739241153556844803677 3099652215432583816801379)
              ·
                refine ⟨4649478323148875725202069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099652215432583816801379 4649478323148875725202069)
                ·
                  refine ⟨217944296397603549618847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4649478323148875725202069 217944296397603549618847)
                  ·
                    rfl

theorem cell23_3820005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_3820005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820005 prefixEnd_3820005 := by exact prefixLift 3820005
  have htrace : WordTrace (prefixWord ++ tailWord_3820005) baseStart_3820005 baseEnd_3820005 := by
    simpa [prefixWord, tailWord_3820005, baseEnd_3820005] using wordTrace_append hprefix tailTrace_3820005
  have hstable : (prefixWord ++ tailWord_3820005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820005).length < 2 ^ (prefixWord ++ tailWord_3820005).sum := by decide
  have hdescent : baseEnd_3820005 < baseStart_3820005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820008 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_3820008 : Nat := 118140960795 + 3820008 * 2 ^ 59
def prefixEnd_3820008 : Nat := 4983230072969 + 3 ^ 40 * 3820008 * 2
def baseEnd_3820008 : Nat := 1961500208020395434832109

theorem tailTrace_3820008 : CollatzResearch.WordTrace tailWord_3820008 prefixEnd_3820008 1961500208020395434832109 := by
  unfold tailWord_3820008
  simp only [CollatzResearch.WordTrace]
  refine ⟨69663568972385448135430339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92884758629847264180573785 69663568972385448135430339)
  ·
    refine ⟨104495353458578172203145509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69663568972385448135430339 104495353458578172203145509)
    ·
      refine ⟨19592878773483407288089783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104495353458578172203145509 19592878773483407288089783)
      ·
        refine ⟨29389318160225110932134675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592878773483407288089783 29389318160225110932134675)
        ·
          refine ⟨44083977240337666398202013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29389318160225110932134675 44083977240337666398202013)
          ·
            refine ⟨16531491465126624899325755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44083977240337666398202013 16531491465126624899325755)
            ·
              refine ⟨24797237197689937348988633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16531491465126624899325755 24797237197689937348988633)
              ·
                refine ⟨18597927898267453011741475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24797237197689937348988633 18597927898267453011741475)
                ·
                  refine ⟨27896891847401179517612213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18597927898267453011741475 27896891847401179517612213)
                  ·
                    refine ⟨2615333610693860579776145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27896891847401179517612213 2615333610693860579776145)
                    ·
                      refine ⟨1961500208020395434832109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615333610693860579776145 1961500208020395434832109)
                      ·
                        rfl

theorem cell23_3820008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_3820008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820008 prefixEnd_3820008 := by exact prefixLift 3820008
  have htrace : WordTrace (prefixWord ++ tailWord_3820008) baseStart_3820008 baseEnd_3820008 := by
    simpa [prefixWord, tailWord_3820008, baseEnd_3820008] using wordTrace_append hprefix tailTrace_3820008
  have hstable : (prefixWord ++ tailWord_3820008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820008).length < 2 ^ (prefixWord ++ tailWord_3820008).sum := by decide
  have hdescent : baseEnd_3820008 < baseStart_3820008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820031 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 6, 4]
def baseStart_3820031 : Nat := 118140960795 + 3820031 * 2 ^ 59
def prefixEnd_3820031 : Nat := 4983230072969 + 3 ^ 40 * 3820031 * 2
def baseEnd_3820031 : Nat := 653837339358482948281501

theorem tailTrace_3820031 : CollatzResearch.WordTrace tailWord_3820031 prefixEnd_3820031 653837339358482948281501 := by
  unfold tailWord_3820031
  simp only [CollatzResearch.WordTrace]
  refine ⟨139327976823687571198947947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92885317882458380799298631 139327976823687571198947947)
  ·
    refine ⟨208991965235531356798421921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139327976823687571198947947 208991965235531356798421921)
    ·
      refine ⟨156743973926648517598816441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208991965235531356798421921 156743973926648517598816441)
      ·
        refine ⟨117557980444986388199112331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156743973926648517598816441 117557980444986388199112331)
        ·
          refine ⟨176336970667479582298668497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117557980444986388199112331 176336970667479582298668497)
          ·
            refine ⟨132252728000609686724001373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176336970667479582298668497 132252728000609686724001373)
            ·
              refine ⟨49594773000228632521500515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132252728000609686724001373 49594773000228632521500515)
              ·
                refine ⟨74392159500342948782250773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49594773000228632521500515 74392159500342948782250773)
                ·
                  refine ⟨3487132476578575724168005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74392159500342948782250773 3487132476578575724168005)
                  ·
                    refine ⟨653837339358482948281501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487132476578575724168005 653837339358482948281501)
                    ·
                      rfl

theorem cell23_3820031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 4].length) (baseStart_3820031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820031 prefixEnd_3820031 := by exact prefixLift 3820031
  have htrace : WordTrace (prefixWord ++ tailWord_3820031) baseStart_3820031 baseEnd_3820031 := by
    simpa [prefixWord, tailWord_3820031, baseEnd_3820031] using wordTrace_append hprefix tailTrace_3820031
  have hstable : (prefixWord ++ tailWord_3820031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820031).length < 2 ^ (prefixWord ++ tailWord_3820031).sum := by decide
  have hdescent : baseEnd_3820031 < baseStart_3820031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820061 : List Nat := [1, 4, 2, 2, 1, 2, 1, 10]
def baseStart_3820061 : Nat := 118140960795 + 3820061 * 2 ^ 59
def prefixEnd_3820061 : Nat := 4983230072969 + 3 ^ 40 * 3820061 * 2
def baseEnd_3820061 : Nat := 72649163796114212128495

theorem tailTrace_3820061 : CollatzResearch.WordTrace tailWord_3820061 prefixEnd_3820061 72649163796114212128495 := by
  unfold tailWord_3820061
  simp only [CollatzResearch.WordTrace]
  refine ⟨139329071013578886322540037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92886047342385924215026691 139329071013578886322540037)
  ·
    refine ⟨26124200815046041185476257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139329071013578886322540037 26124200815046041185476257)
    ·
      refine ⟨19593150611284530889107193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26124200815046041185476257 19593150611284530889107193)
      ·
        refine ⟨14694862958463398166830395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19593150611284530889107193 14694862958463398166830395)
        ·
          refine ⟨22042294437695097250245593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14694862958463398166830395 22042294437695097250245593)
          ·
            refine ⟨16531720828271322937684195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22042294437695097250245593 16531720828271322937684195)
            ·
              refine ⟨24797581242406984406526293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16531720828271322937684195 24797581242406984406526293)
              ·
                refine ⟨72649163796114212128495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24797581242406984406526293 72649163796114212128495)
                ·
                  rfl

theorem cell23_3820061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 10].length) (baseStart_3820061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820061 prefixEnd_3820061 := by exact prefixLift 3820061
  have htrace : WordTrace (prefixWord ++ tailWord_3820061) baseStart_3820061 baseEnd_3820061 := by
    simpa [prefixWord, tailWord_3820061, baseEnd_3820061] using wordTrace_append hprefix tailTrace_3820061
  have hstable : (prefixWord ++ tailWord_3820061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820061).length < 2 ^ (prefixWord ++ tailWord_3820061).sum := by decide
  have hdescent : baseEnd_3820061 < baseStart_3820061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820072 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3820072 : Nat := 118140960795 + 3820072 * 2 ^ 59
def prefixEnd_3820072 : Nat := 4983230072969 + 3 ^ 40 * 3820072 * 2
def baseEnd_3820072 : Nat := 1961533070782283184431815

theorem tailTrace_3820072 : CollatzResearch.WordTrace tailWord_3820072 prefixEnd_3820072 1961533070782283184431815 := by
  unfold tailWord_3820072
  simp only [CollatzResearch.WordTrace]
  refine ⟨69664736108269517600595235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92886314811026023467460313 69664736108269517600595235)
  ·
    refine ⟨104497104162404276400892853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69664736108269517600595235 104497104162404276400892853)
    ·
      refine ⟨9796603515225400912583705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104497104162404276400892853 9796603515225400912583705)
      ·
        refine ⟨7347452636419050684437779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9796603515225400912583705 7347452636419050684437779)
        ·
          refine ⟨11021178954628576026656669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347452636419050684437779 11021178954628576026656669)
          ·
            refine ⟨4132942107985716009996251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11021178954628576026656669 4132942107985716009996251)
            ·
              refine ⟨6199413161978574014994377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4132942107985716009996251 6199413161978574014994377)
              ·
                refine ⟨4649559871483930511245783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6199413161978574014994377 4649559871483930511245783)
                ·
                  refine ⟨6974339807225895766868675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649559871483930511245783 6974339807225895766868675)
                  ·
                    refine ⟨10461509710838843650303013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6974339807225895766868675 10461509710838843650303013)
                    ·
                      refine ⟨1961533070782283184431815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10461509710838843650303013 1961533070782283184431815)
                      ·
                        rfl

theorem cell23_3820072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3820072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820072 prefixEnd_3820072 := by exact prefixLift 3820072
  have htrace : WordTrace (prefixWord ++ tailWord_3820072) baseStart_3820072 baseEnd_3820072 := by
    simpa [prefixWord, tailWord_3820072, baseEnd_3820072] using wordTrace_append hprefix tailTrace_3820072
  have hstable : (prefixWord ++ tailWord_3820072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820072).length < 2 ^ (prefixWord ++ tailWord_3820072).sum := by decide
  have hdescent : baseEnd_3820072 < baseStart_3820072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820088 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_3820088 : Nat := 118140960795 + 3820088 * 2 ^ 59
def prefixEnd_3820088 : Nat := 4983230072969 + 3 ^ 40 * 3820088 * 2
def baseEnd_3820088 : Nat := 1961541286472755121831741

theorem tailTrace_3820088 : CollatzResearch.WordTrace tailWord_3820088 prefixEnd_3820088 1961541286472755121831741 := by
  unfold tailWord_3820088
  simp only [CollatzResearch.WordTrace]
  refine ⟨69665027892240534966886459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92886703856320713289181945 69665027892240534966886459)
  ·
    refine ⟨104497541838360802450329689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69665027892240534966886459 104497541838360802450329689)
    ·
      refine ⟨78373156378770601837747267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104497541838360802450329689 78373156378770601837747267)
      ·
        refine ⟨117559734568155902756620901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78373156378770601837747267 117559734568155902756620901)
        ·
          refine ⟨22042450231529231766866419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117559734568155902756620901 22042450231529231766866419)
          ·
            refine ⟨33063675347293847650299629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22042450231529231766866419 33063675347293847650299629)
            ·
              refine ⟨12398878255235192868862361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33063675347293847650299629 12398878255235192868862361)
              ·
                refine ⟨9299158691426394651646771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12398878255235192868862361 9299158691426394651646771)
                ·
                  refine ⟨13948738037139591977470157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9299158691426394651646771 13948738037139591977470157)
                  ·
                    refine ⟨5230776763927346991551309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13948738037139591977470157 5230776763927346991551309)
                    ·
                      refine ⟨1961541286472755121831741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5230776763927346991551309 1961541286472755121831741)
                      ·
                        rfl

theorem cell23_3820088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_3820088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820088 prefixEnd_3820088 := by exact prefixLift 3820088
  have htrace : WordTrace (prefixWord ++ tailWord_3820088) baseStart_3820088 baseEnd_3820088 := by
    simpa [prefixWord, tailWord_3820088, baseEnd_3820088] using wordTrace_append hprefix tailTrace_3820088
  have hstable : (prefixWord ++ tailWord_3820088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820088).length < 2 ^ (prefixWord ++ tailWord_3820088).sum := by decide
  have hdescent : baseEnd_3820088 < baseStart_3820088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820092 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_3820092 : Nat := 118140960795 + 3820092 * 2 ^ 59
def prefixEnd_3820092 : Nat := 4983230072969 + 3 ^ 40 * 3820092 * 2
def baseEnd_3820092 : Nat := 1961543340395373106181723

theorem tailTrace_3820092 : CollatzResearch.WordTrace tailWord_3820092 prefixEnd_3820092 1961543340395373106181723 := by
  unfold tailWord_3820092
  simp only [CollatzResearch.WordTrace]
  refine ⟨69665100838233289308459265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92886801117644385744612353 69665100838233289308459265)
  ·
    refine ⟨52248825628674966981344449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69665100838233289308459265 52248825628674966981344449)
    ·
      refine ⟨39186619221506225236008337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52248825628674966981344449 39186619221506225236008337)
      ·
        refine ⟨29389964416129668927006253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39186619221506225236008337 29389964416129668927006253)
        ·
          refine ⟨11021236656048625847627345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29389964416129668927006253 11021236656048625847627345)
          ·
            refine ⟨8265927492036469385720509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11021236656048625847627345 8265927492036469385720509)
            ·
              refine ⟨3099722809513676019645191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8265927492036469385720509 3099722809513676019645191)
              ·
                refine ⟨4649584214270514029467787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099722809513676019645191 4649584214270514029467787)
                ·
                  refine ⟨6974376321405771044201681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649584214270514029467787 6974376321405771044201681)
                  ·
                    refine ⟨5230782241054328283151261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6974376321405771044201681 5230782241054328283151261)
                    ·
                      refine ⟨1961543340395373106181723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5230782241054328283151261 1961543340395373106181723)
                      ·
                        rfl

theorem cell23_3820092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_3820092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820092 prefixEnd_3820092 := by exact prefixLift 3820092
  have htrace : WordTrace (prefixWord ++ tailWord_3820092) baseStart_3820092 baseEnd_3820092 := by
    simpa [prefixWord, tailWord_3820092, baseEnd_3820092] using wordTrace_append hprefix tailTrace_3820092
  have hstable : (prefixWord ++ tailWord_3820092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820092).length < 2 ^ (prefixWord ++ tailWord_3820092).sum := by decide
  have hdescent : baseEnd_3820092 < baseStart_3820092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820100 : List Nat := [2, 3, 5, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3820100 : Nat := 118140960795 + 3820100 * 2 ^ 59
def prefixEnd_3820100 : Nat := 4983230072969 + 3 ^ 40 * 3820100 * 2
def baseEnd_3820100 : Nat := 1961547448240609074881687

theorem tailTrace_3820100 : CollatzResearch.WordTrace tailWord_3820100 prefixEnd_3820100 1961547448240609074881687 := by
  unfold tailWord_3820100
  simp only [CollatzResearch.WordTrace]
  refine ⟨69665246730218797991604877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92886995640291730655473169 69665246730218797991604877)
  ·
    refine ⟨26124467523832049246851829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69665246730218797991604877 26124467523832049246851829)
    ·
      refine ⟨2449168830359254616892359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26124467523832049246851829 2449168830359254616892359)
      ·
        refine ⟨3673753245538881925338539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449168830359254616892359 3673753245538881925338539)
        ·
          refine ⟨5510629868308322888007809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673753245538881925338539 5510629868308322888007809)
          ·
            refine ⟨4132972401231242166005857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5510629868308322888007809 4132972401231242166005857)
            ·
              refine ⟨3099729300923431624504393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132972401231242166005857 3099729300923431624504393)
              ·
                refine ⟨2324796975692573718378295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099729300923431624504393 2324796975692573718378295)
                ·
                  refine ⟨3487195463538860577567443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324796975692573718378295 3487195463538860577567443)
                  ·
                    refine ⟨5230793195308290866351165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3487195463538860577567443 5230793195308290866351165)
                    ·
                      refine ⟨1961547448240609074881687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5230793195308290866351165 1961547448240609074881687)
                      ·
                        rfl

theorem cell23_3820100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3820100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820100 prefixEnd_3820100 := by exact prefixLift 3820100
  have htrace : WordTrace (prefixWord ++ tailWord_3820100) baseStart_3820100 baseEnd_3820100 := by
    simpa [prefixWord, tailWord_3820100, baseEnd_3820100] using wordTrace_append hprefix tailTrace_3820100
  have hstable : (prefixWord ++ tailWord_3820100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820100).length < 2 ^ (prefixWord ++ tailWord_3820100).sum := by decide
  have hdescent : baseEnd_3820100 < baseStart_3820100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820106 : List Nat := [3, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_3820106 : Nat := 118140960795 + 3820106 * 2 ^ 59
def prefixEnd_3820106 : Nat := 4983230072969 + 3 ^ 40 * 3820106 * 2
def baseEnd_3820106 : Nat := 1961550529124536051406659

theorem tailTrace_3820106 : CollatzResearch.WordTrace tailWord_3820106 prefixEnd_3820106 1961550529124536051406659 := by
  unfold tailWord_3820106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34832678074603964751982043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92887141532277239338618781 34832678074603964751982043)
  ·
    refine ⟨52249017111905947127973065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34832678074603964751982043 52249017111905947127973065)
    ·
      refine ⟨39186762833929460345979799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52249017111905947127973065 39186762833929460345979799)
      ·
        refine ⟨58780144250894190518969699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39186762833929460345979799 58780144250894190518969699)
        ·
          refine ⟨88170216376341285778454549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58780144250894190518969699 88170216376341285778454549)
          ·
            refine ⟨4132978892640997770865057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88170216376341285778454549 4132978892640997770865057)
            ·
              refine ⟨3099734169480748328148793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132978892640997770865057 3099734169480748328148793)
              ·
                refine ⟨2324800627110561246111595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099734169480748328148793 2324800627110561246111595)
                ·
                  refine ⟨3487200940665841869167393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324800627110561246111595 3487200940665841869167393)
                  ·
                    refine ⟨2615400705499381401875545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3487200940665841869167393 2615400705499381401875545)
                    ·
                      refine ⟨1961550529124536051406659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615400705499381401875545 1961550529124536051406659)
                      ·
                        rfl

theorem cell23_3820106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_3820106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820106 prefixEnd_3820106 := by exact prefixLift 3820106
  have htrace : WordTrace (prefixWord ++ tailWord_3820106) baseStart_3820106 baseEnd_3820106 := by
    simpa [prefixWord, tailWord_3820106, baseEnd_3820106] using wordTrace_append hprefix tailTrace_3820106
  have hstable : (prefixWord ++ tailWord_3820106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820106).length < 2 ^ (prefixWord ++ tailWord_3820106).sum := by decide
  have hdescent : baseEnd_3820106 < baseStart_3820106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820111 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_3820111 : Nat := 118140960795 + 3820111 * 2 ^ 59
def prefixEnd_3820111 : Nat := 4983230072969 + 3 ^ 40 * 3820111 * 2
def baseEnd_3820111 : Nat := 1961553096527808531844135

theorem tailTrace_3820111 : CollatzResearch.WordTrace tailWord_3820111 prefixEnd_3820111 1961553096527808531844135 := by
  unfold tailWord_3820111
  simp only [CollatzResearch.WordTrace]
  refine ⟨139330894663397744861860187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92887263108931829907906791 139330894663397744861860187)
  ·
    refine ⟨208996341995096617292790281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139330894663397744861860187 208996341995096617292790281)
    ·
      refine ⟨156747256496322462969592711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208996341995096617292790281 156747256496322462969592711)
      ·
        refine ⟨235120884744483694454389067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156747256496322462969592711 235120884744483694454389067)
        ·
          refine ⟨352681327116725541681583601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235120884744483694454389067 352681327116725541681583601)
          ·
            refine ⟨264510995337544156261187701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352681327116725541681583601 264510995337544156261187701)
            ·
              refine ⟨24797905812894764649486347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264510995337544156261187701 24797905812894764649486347)
              ·
                refine ⟨37196858719342146974229521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24797905812894764649486347 37196858719342146974229521)
                ·
                  refine ⟨27897644039506610230672141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37196858719342146974229521 27897644039506610230672141)
                  ·
                    refine ⟨10461616514814978836502053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27897644039506610230672141 10461616514814978836502053)
                    ·
                      refine ⟨1961553096527808531844135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10461616514814978836502053 1961553096527808531844135)
                      ·
                        rfl

theorem cell23_3820111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_3820111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820111 prefixEnd_3820111 := by exact prefixLift 3820111
  have htrace : WordTrace (prefixWord ++ tailWord_3820111) baseStart_3820111 baseEnd_3820111 := by
    simpa [prefixWord, tailWord_3820111, baseEnd_3820111] using wordTrace_append hprefix tailTrace_3820111
  have hstable : (prefixWord ++ tailWord_3820111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820111).length < 2 ^ (prefixWord ++ tailWord_3820111).sum := by decide
  have hdescent : baseEnd_3820111 < baseStart_3820111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820149 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3820149 : Nat := 118140960795 + 3820149 * 2 ^ 59
def prefixEnd_3820149 : Nat := 4983230072969 + 3 ^ 40 * 3820149 * 2
def baseEnd_3820149 : Nat := 1961572608792679383168961

theorem tailTrace_3820149 : CollatzResearch.WordTrace tailWord_3820149 prefixEnd_3820149 1961572608792679383168961 := by
  unfold tailWord_3820149
  simp only [CollatzResearch.WordTrace]
  refine ⟨139332280637260077351743501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92888187091506718234495667 139332280637260077351743501)
  ·
    refine ⟨52249605238972529006903813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139332280637260077351743501 52249605238972529006903813)
    ·
      refine ⟨9796800982307349188794465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52249605238972529006903813 9796800982307349188794465)
      ·
        refine ⟨7347600736730511891595849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9796800982307349188794465 7347600736730511891595849)
        ·
          refine ⟨5510700552547883918696887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7347600736730511891595849 5510700552547883918696887)
          ·
            refine ⟨8266050828821825878045331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510700552547883918696887 8266050828821825878045331)
            ·
              refine ⟨12399076243232738817067997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8266050828821825878045331 12399076243232738817067997)
              ·
                refine ⟨4649653591212277056400499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12399076243232738817067997 4649653591212277056400499)
                ·
                  refine ⟨6974480386818415584600749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649653591212277056400499 6974480386818415584600749)
                  ·
                    refine ⟨2615430145056905844225281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6974480386818415584600749 2615430145056905844225281)
                    ·
                      refine ⟨1961572608792679383168961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615430145056905844225281 1961572608792679383168961)
                      ·
                        rfl

theorem cell23_3820149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3820149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820149 prefixEnd_3820149 := by exact prefixLift 3820149
  have htrace : WordTrace (prefixWord ++ tailWord_3820149) baseStart_3820149 baseEnd_3820149 := by
    simpa [prefixWord, tailWord_3820149, baseEnd_3820149] using wordTrace_append hprefix tailTrace_3820149
  have hstable : (prefixWord ++ tailWord_3820149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820149).length < 2 ^ (prefixWord ++ tailWord_3820149).sum := by decide
  have hdescent : baseEnd_3820149 < baseStart_3820149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820215 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 2, 5]
def baseStart_3820215 : Nat := 118140960795 + 3820215 * 2 ^ 59
def prefixEnd_3820215 : Nat := 4983230072969 + 3 ^ 40 * 3820215 * 2
def baseEnd_3820215 : Nat := 653868832838625374981219

theorem tailTrace_3820215 : CollatzResearch.WordTrace tailWord_3820215 prefixEnd_3820215 653868832838625374981219 := by
  unfold tailWord_3820215
  simp only [CollatzResearch.WordTrace]
  refine ⟨139334687855020970623646099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92889791903347313749097399 139334687855020970623646099)
  ·
    refine ⟨209002031782531455935469149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139334687855020970623646099 209002031782531455935469149)
    ·
      refine ⟨78375761918449295975800931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209002031782531455935469149 78375761918449295975800931)
      ·
        refine ⟨117563642877673943963701397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78375761918449295975800931 117563642877673943963701397)
        ·
          refine ⟨5510795759890966123298503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117563642877673943963701397 5510795759890966123298503)
          ·
            refine ⟨8266193639836449184947755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510795759890966123298503 8266193639836449184947755)
            ·
              refine ⟨12399290459754673777421633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8266193639836449184947755 12399290459754673777421633)
              ·
                refine ⟨9299467844816005333066225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12399290459754673777421633 9299467844816005333066225)
                ·
                  refine ⟨6974600883612003999799669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299467844816005333066225 6974600883612003999799669)
                  ·
                    refine ⟨653868832838625374981219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6974600883612003999799669 653868832838625374981219)
                    ·
                      rfl

theorem cell23_3820215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_3820215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820215 prefixEnd_3820215 := by exact prefixLift 3820215
  have htrace : WordTrace (prefixWord ++ tailWord_3820215) baseStart_3820215 baseEnd_3820215 := by
    simpa [prefixWord, tailWord_3820215, baseEnd_3820215] using wordTrace_append hprefix tailTrace_3820215
  have hstable : (prefixWord ++ tailWord_3820215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820215).length < 2 ^ (prefixWord ++ tailWord_3820215).sum := by decide
  have hdescent : baseEnd_3820215 < baseStart_3820215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820252 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3820252 : Nat := 118140960795 + 3820252 * 2 ^ 59
def prefixEnd_3820252 : Nat := 4983230072969 + 3 ^ 40 * 3820252 * 2
def baseEnd_3820252 : Nat := 1961625497300092480180987

theorem tailTrace_3820252 : CollatzResearch.WordTrace tailWord_3820252 prefixEnd_3820252 1961625497300092480180987 := by
  unfold tailWord_3820252
  simp only [CollatzResearch.WordTrace]
  refine ⟨69668018677943462971371505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92890691570591283961828673 69668018677943462971371505)
  ·
    refine ⟨52251014008457597228528629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69668018677943462971371505 52251014008457597228528629)
    ·
      refine ⟨4898532563292899740174559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52251014008457597228528629 4898532563292899740174559)
      ·
        refine ⟨7347798844939349610261839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898532563292899740174559 7347798844939349610261839)
        ·
          refine ⟨11021698267409024415392759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347798844939349610261839 11021698267409024415392759)
          ·
            refine ⟨16532547401113536623089139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021698267409024415392759 16532547401113536623089139)
            ·
              refine ⟨24798821101670304934633709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16532547401113536623089139 24798821101670304934633709)
              ·
                refine ⟨9299557913126364350487641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24798821101670304934633709 9299557913126364350487641)
                ·
                  refine ⟨6974668434844773262865731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299557913126364350487641 6974668434844773262865731)
                  ·
                    refine ⟨10462002652267159894298597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6974668434844773262865731 10462002652267159894298597)
                    ·
                      refine ⟨1961625497300092480180987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10462002652267159894298597 1961625497300092480180987)
                      ·
                        rfl

theorem cell23_3820252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3820252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820252 prefixEnd_3820252 := by exact prefixLift 3820252
  have htrace : WordTrace (prefixWord ++ tailWord_3820252) baseStart_3820252 baseEnd_3820252 := by
    simpa [prefixWord, tailWord_3820252, baseEnd_3820252] using wordTrace_append hprefix tailTrace_3820252
  have hstable : (prefixWord ++ tailWord_3820252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820252).length < 2 ^ (prefixWord ++ tailWord_3820252).sum := by decide
  have hdescent : baseEnd_3820252 < baseStart_3820252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820255 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 3]
def baseStart_3820255 : Nat := 118140960795 + 3820255 * 2 ^ 59
def prefixEnd_3820255 : Nat := 4983230072969 + 3 ^ 40 * 3820255 * 2
def baseEnd_3820255 : Nat := 1961627037742055968443473

theorem tailTrace_3820255 : CollatzResearch.WordTrace tailWord_3820255 prefixEnd_3820255 1961627037742055968443473 := by
  unfold tailWord_3820255
  simp only [CollatzResearch.WordTrace]
  refine ⟨139336146774876057455102219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92890764516584038303401479 139336146774876057455102219)
  ·
    refine ⟨209004220162314086182653329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139336146774876057455102219 209004220162314086182653329)
    ·
      refine ⟨156753165121735564636989997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209004220162314086182653329 156753165121735564636989997)
      ·
        refine ⟨58782436920650836738871249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156753165121735564636989997 58782436920650836738871249)
        ·
          refine ⟨44086827690488127554153437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58782436920650836738871249 44086827690488127554153437)
          ·
            refine ⟨16532560383933047832807539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44086827690488127554153437 16532560383933047832807539)
            ·
              refine ⟨24798840575899571749211309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16532560383933047832807539 24798840575899571749211309)
              ·
                refine ⟨9299565215962339405954241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24798840575899571749211309 9299565215962339405954241)
                ·
                  refine ⟨6974673911971754554465681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299565215962339405954241 6974673911971754554465681)
                  ·
                    refine ⟨5231005433978815915849261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6974673911971754554465681 5231005433978815915849261)
                    ·
                      refine ⟨1961627037742055968443473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5231005433978815915849261 1961627037742055968443473)
                      ·
                        rfl

theorem cell23_3820255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_3820255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820255 prefixEnd_3820255 := by exact prefixLift 3820255
  have htrace : WordTrace (prefixWord ++ tailWord_3820255) baseStart_3820255 baseEnd_3820255 := by
    simpa [prefixWord, tailWord_3820255, baseEnd_3820255] using wordTrace_append hprefix tailTrace_3820255
  have hstable : (prefixWord ++ tailWord_3820255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820255).length < 2 ^ (prefixWord ++ tailWord_3820255).sum := by decide
  have hdescent : baseEnd_3820255 < baseStart_3820255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820298 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3820298 : Nat := 118140960795 + 3820298 * 2 ^ 59
def prefixEnd_3820298 : Nat := 4983230072969 + 3 ^ 40 * 3820298 * 2
def baseEnd_3820298 : Nat := 1961649117410199300205775

theorem tailTrace_3820298 : CollatzResearch.WordTrace tailWord_3820298 prefixEnd_3820298 1961649117410199300205775 := by
  unfold tailWord_3820298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34834428778430068949729387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92891810075813517199278365 34834428778430068949729387)
  ·
    refine ⟨52251643167645103424594081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34834428778430068949729387 52251643167645103424594081)
    ·
      refine ⟨39188732375733827568445561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52251643167645103424594081 39188732375733827568445561)
      ·
        refine ⟨29391549281800370676334171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39188732375733827568445561 29391549281800370676334171)
        ·
          refine ⟨44087323922700556014501257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29391549281800370676334171 44087323922700556014501257)
          ·
            refine ⟨33065492942025417010875943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44087323922700556014501257 33065492942025417010875943)
            ·
              refine ⟨49598239413038125516313915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33065492942025417010875943 49598239413038125516313915)
              ·
                refine ⟨74397359119557188274470873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49598239413038125516313915 74397359119557188274470873)
                ·
                  refine ⟨55798019339667891205853155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74397359119557188274470873 55798019339667891205853155)
                  ·
                    refine ⟨83697029009501836808779733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55798019339667891205853155 83697029009501836808779733)
                    ·
                      refine ⟨1961649117410199300205775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83697029009501836808779733 1961649117410199300205775)
                      ·
                        rfl

theorem cell23_3820298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3820298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820298 prefixEnd_3820298 := by exact prefixLift 3820298
  have htrace : WordTrace (prefixWord ++ tailWord_3820298) baseStart_3820298 baseEnd_3820298 := by
    simpa [prefixWord, tailWord_3820298, baseEnd_3820298] using wordTrace_append hprefix tailTrace_3820298
  have hstable : (prefixWord ++ tailWord_3820298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820298).length < 2 ^ (prefixWord ++ tailWord_3820298).sum := by decide
  have hdescent : baseEnd_3820298 < baseStart_3820298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820306 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3820306 : Nat := 118140960795 + 3820306 * 2 ^ 59
def prefixEnd_3820306 : Nat := 4983230072969 + 3 ^ 40 * 3820306 * 2
def baseEnd_3820306 : Nat := 1961653225255435268905739

theorem tailTrace_3820306 : CollatzResearch.WordTrace tailWord_3820306 prefixEnd_3820306 1961653225255435268905739 := by
  unfold tailWord_3820306
  simp only [CollatzResearch.WordTrace]
  refine ⟨34834501724422823291302193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92892004598460862110139181 34834501724422823291302193)
  ·
    refine ⟨26125876293317117468476645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34834501724422823291302193 26125876293317117468476645)
    ·
      refine ⟨4898601804996959525339371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26125876293317117468476645 4898601804996959525339371)
      ·
        refine ⟨7347902707495439288009057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898601804996959525339371 7347902707495439288009057)
        ·
          refine ⟨5510927030621579466006793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7347902707495439288009057 5510927030621579466006793)
          ·
            refine ⟨4133195272966184599505095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5510927030621579466006793 4133195272966184599505095)
            ·
              refine ⟨6199792909449276899257643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133195272966184599505095 6199792909449276899257643)
              ·
                refine ⟨9299689364173915348886465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6199792909449276899257643 9299689364173915348886465)
                ·
                  refine ⟨6974767023130436511664849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299689364173915348886465 6974767023130436511664849)
                  ·
                    refine ⟨5231075267347827383748637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6974767023130436511664849 5231075267347827383748637)
                    ·
                      refine ⟨1961653225255435268905739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5231075267347827383748637 1961653225255435268905739)
                      ·
                        rfl

theorem cell23_3820306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3820306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820306 prefixEnd_3820306 := by exact prefixLift 3820306
  have htrace : WordTrace (prefixWord ++ tailWord_3820306) baseStart_3820306 baseEnd_3820306 := by
    simpa [prefixWord, tailWord_3820306, baseEnd_3820306] using wordTrace_append hprefix tailTrace_3820306
  have hstable : (prefixWord ++ tailWord_3820306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820306).length < 2 ^ (prefixWord ++ tailWord_3820306).sum := by decide
  have hdescent : baseEnd_3820306 < baseStart_3820306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820319 : List Nat := [1, 1, 2, 4, 2, 2, 1, 5, 1, 1, 3]
def baseStart_3820319 : Nat := 118140960795 + 3820319 * 2 ^ 59
def prefixEnd_3820319 : Nat := 4983230072969 + 3 ^ 40 * 3820319 * 2
def baseEnd_3820319 : Nat := 1961659900503943718043179

theorem tailTrace_3820319 : CollatzResearch.WordTrace tailWord_3820319 prefixEnd_3820319 1961659900503943718043179 := by
  unfold tailWord_3820319
  simp only [CollatzResearch.WordTrace]
  refine ⟨139338481046644196385432011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92892320697762797590288007 139338481046644196385432011)
  ·
    refine ⟨209007721569966294578148017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139338481046644196385432011 209007721569966294578148017)
    ·
      refine ⟨156755791177474720933611013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209007721569966294578148017 156755791177474720933611013)
      ·
        refine ⟨29391710845776510175052065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156755791177474720933611013 29391710845776510175052065)
        ·
          refine ⟨22043783134332382631289049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29391710845776510175052065 22043783134332382631289049)
          ·
            refine ⟨16532837350749286973466787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22043783134332382631289049 16532837350749286973466787)
            ·
              refine ⟨24799256026123930460200181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16532837350749286973466787 24799256026123930460200181)
              ·
                refine ⟨2324930252449118480643767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24799256026123930460200181 2324930252449118480643767)
                ·
                  refine ⟨3487395378673677720965651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324930252449118480643767 3487395378673677720965651)
                  ·
                    refine ⟨5231093068010516581448477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3487395378673677720965651 5231093068010516581448477)
                    ·
                      refine ⟨1961659900503943718043179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5231093068010516581448477 1961659900503943718043179)
                      ·
                        rfl

theorem cell23_3820319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_3820319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820319 prefixEnd_3820319 := by exact prefixLift 3820319
  have htrace : WordTrace (prefixWord ++ tailWord_3820319) baseStart_3820319 baseEnd_3820319 := by
    simpa [prefixWord, tailWord_3820319, baseEnd_3820319] using wordTrace_append hprefix tailTrace_3820319
  have hstable : (prefixWord ++ tailWord_3820319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820319).length < 2 ^ (prefixWord ++ tailWord_3820319).sum := by decide
  have hdescent : baseEnd_3820319 < baseStart_3820319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820322 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3820322 : Nat := 118140960795 + 3820322 * 2 ^ 59
def prefixEnd_3820322 : Nat := 4983230072969 + 3 ^ 40 * 3820322 * 2
def baseEnd_3820322 : Nat := 653887146981969068768555

theorem tailTrace_3820322 : CollatzResearch.WordTrace tailWord_3820322 prefixEnd_3820322 653887146981969068768555 := by
  unfold tailWord_3820322
  simp only [CollatzResearch.WordTrace]
  refine ⟨34834647616408331974447805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92892393643755551931860813 34834647616408331974447805)
  ·
    refine ⟨13062992856153124490417927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34834647616408331974447805 13062992856153124490417927)
    ·
      refine ⟨19594489284229686735626891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13062992856153124490417927 19594489284229686735626891)
      ·
        refine ⟨29391733926344530103440337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19594489284229686735626891 29391733926344530103440337)
        ·
          refine ⟨22043800444758397577580253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29391733926344530103440337 22043800444758397577580253)
          ·
            refine ⟨8266425166784399091592595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22043800444758397577580253 8266425166784399091592595)
            ·
              refine ⟨12399637750176598637388893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8266425166784399091592595 12399637750176598637388893)
              ·
                refine ⟨4649864156316224489020835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12399637750176598637388893 4649864156316224489020835)
                ·
                  refine ⟨6974796234474336733531253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649864156316224489020835 6974796234474336733531253)
                  ·
                    refine ⟨653887146981969068768555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6974796234474336733531253 653887146981969068768555)
                    ·
                      rfl

theorem cell23_3820322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3820322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820322 prefixEnd_3820322 := by exact prefixLift 3820322
  have htrace : WordTrace (prefixWord ++ tailWord_3820322) baseStart_3820322 baseEnd_3820322 := by
    simpa [prefixWord, tailWord_3820322, baseEnd_3820322] using wordTrace_append hprefix tailTrace_3820322
  have hstable : (prefixWord ++ tailWord_3820322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820322).length < 2 ^ (prefixWord ++ tailWord_3820322).sum := by decide
  have hdescent : baseEnd_3820322 < baseStart_3820322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820348 : List Nat := [2, 2, 2, 2, 1, 1, 1, 12]
def baseStart_3820348 : Nat := 118140960795 + 3820348 * 2 ^ 59
def prefixEnd_3820348 : Nat := 4983230072969 + 3 ^ 40 * 3820348 * 2
def baseEnd_3820348 : Nat := 72654621905293485354835

theorem tailTrace_3820348 : CollatzResearch.WordTrace tailWord_3820348 prefixEnd_3820348 72654621905293485354835 := by
  unfold tailWord_3820348
  simp only [CollatzResearch.WordTrace]
  refine ⟨69669769381769567169118849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92893025842359422892158465 69669769381769567169118849)
  ·
    refine ⟨52252327036327175376839137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69669769381769567169118849 52252327036327175376839137)
    ·
      refine ⟨39189245277245381532629353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52252327036327175376839137 39189245277245381532629353)
      ·
        refine ⟨29391933957934036149472015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39189245277245381532629353 29391933957934036149472015)
        ·
          refine ⟨44087900936901054224208023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29391933957934036149472015 44087900936901054224208023)
          ·
            refine ⟨66131851405351581336312035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44087900936901054224208023 66131851405351581336312035)
            ·
              refine ⟨99197777108027372004468053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66131851405351581336312035 99197777108027372004468053)
              ·
                refine ⟨72654621905293485354835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 99197777108027372004468053 72654621905293485354835)
                ·
                  rfl

theorem cell23_3820348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 12].length) (baseStart_3820348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820348 prefixEnd_3820348 := by exact prefixLift 3820348
  have htrace : WordTrace (prefixWord ++ tailWord_3820348) baseStart_3820348 baseEnd_3820348 := by
    simpa [prefixWord, tailWord_3820348, baseEnd_3820348] using wordTrace_append hprefix tailTrace_3820348
  have hstable : (prefixWord ++ tailWord_3820348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820348).length < 2 ^ (prefixWord ++ tailWord_3820348).sum := by decide
  have hdescent : baseEnd_3820348 < baseStart_3820348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820356 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3820356 : Nat := 118140960795 + 3820356 * 2 ^ 59
def prefixEnd_3820356 : Nat := 4983230072969 + 3 ^ 40 * 3820356 * 2
def baseEnd_3820356 : Nat := 653892966429386691093503

theorem tailTrace_3820356 : CollatzResearch.WordTrace tailWord_3820356 prefixEnd_3820356 653892966429386691093503 := by
  unfold tailWord_3820356
  simp only [CollatzResearch.WordTrace]
  refine ⟨69669915273755075852264461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92893220365006767803019281 69669915273755075852264461)
  ·
    refine ⟨26126218227658153444599173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69669915273755075852264461 26126218227658153444599173)
    ·
      refine ⟨4898665917685903770862345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26126218227658153444599173 4898665917685903770862345)
      ·
        refine ⟨3673999438264427828146759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4898665917685903770862345 3673999438264427828146759)
        ·
          refine ⟨5510999157396641742220139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673999438264427828146759 5510999157396641742220139)
          ·
            refine ⟨8266498736094962613330209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510999157396641742220139 8266498736094962613330209)
            ·
              refine ⟨6199874052071221959997657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8266498736094962613330209 6199874052071221959997657)
              ·
                refine ⟨4649905539053416469998243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6199874052071221959997657 4649905539053416469998243)
                ·
                  refine ⟨6974858308580124704997365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649905539053416469998243 6974858308580124704997365)
                  ·
                    refine ⟨653892966429386691093503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6974858308580124704997365 653892966429386691093503)
                    ·
                      rfl

theorem cell23_3820356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3820356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820356 prefixEnd_3820356 := by exact prefixLift 3820356
  have htrace : WordTrace (prefixWord ++ tailWord_3820356) baseStart_3820356 baseEnd_3820356 := by
    simpa [prefixWord, tailWord_3820356, baseEnd_3820356] using wordTrace_append hprefix tailTrace_3820356
  have hstable : (prefixWord ++ tailWord_3820356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820356).length < 2 ^ (prefixWord ++ tailWord_3820356).sum := by decide
  have hdescent : baseEnd_3820356 < baseStart_3820356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820409 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 3]
def baseStart_3820409 : Nat := 118140960795 + 3820409 * 2 ^ 59
def prefixEnd_3820409 : Nat := 4983230072969 + 3 ^ 40 * 3820409 * 2
def baseEnd_3820409 : Nat := 1961706113762848365917765

theorem tailTrace_3820409 : CollatzResearch.WordTrace tailWord_3820409 prefixEnd_3820409 1961706113762848365917765 := by
  unfold tailWord_3820409
  simp only [CollatzResearch.WordTrace]
  refine ⟨139341763616318141756208281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92894509077545427837472187 139341763616318141756208281)
  ·
    refine ⟨104506322712238606317156211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139341763616318141756208281 104506322712238606317156211)
    ·
      refine ⟨156759484068357909475734317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104506322712238606317156211 156759484068357909475734317)
      ·
        refine ⟨58784806525634216053400369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156759484068357909475734317 58784806525634216053400369)
        ·
          refine ⟨44088604894225662040050277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58784806525634216053400369 44088604894225662040050277)
          ·
            refine ⟨8266613417667311632509427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44088604894225662040050277 8266613417667311632509427)
            ·
              refine ⟨12399920126500967448764141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8266613417667311632509427 12399920126500967448764141)
              ·
                refine ⟨4649970047437862793286553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12399920126500967448764141 4649970047437862793286553)
                ·
                  refine ⟨3487477535578397094964915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4649970047437862793286553 3487477535578397094964915)
                  ·
                    refine ⟨5231216303367595642447373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3487477535578397094964915 5231216303367595642447373)
                    ·
                      refine ⟨1961706113762848365917765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5231216303367595642447373 1961706113762848365917765)
                      ·
                        rfl

theorem cell23_3820409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_3820409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820409 prefixEnd_3820409 := by exact prefixLift 3820409
  have htrace : WordTrace (prefixWord ++ tailWord_3820409) baseStart_3820409 baseEnd_3820409 := by
    simpa [prefixWord, tailWord_3820409, baseEnd_3820409] using wordTrace_append hprefix tailTrace_3820409
  have hstable : (prefixWord ++ tailWord_3820409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820409).length < 2 ^ (prefixWord ++ tailWord_3820409).sum := by decide
  have hdescent : baseEnd_3820409 < baseStart_3820409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820522 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_3820522 : Nat := 118140960795 + 3820522 * 2 ^ 59
def prefixEnd_3820522 : Nat := 4983230072969 + 3 ^ 40 * 3820522 * 2
def baseEnd_3820522 : Nat := 1961764137076806423804745

theorem tailTrace_3820522 : CollatzResearch.WordTrace tailWord_3820522 prefixEnd_3820522 1961764137076806423804745 := by
  unfold tailWord_3820522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34836471266227190513767955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92897256709939174703381213 34836471266227190513767955)
  ·
    refine ⟨52254706899340785770651933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34836471266227190513767955 52254706899340785770651933)
    ·
      refine ⟨19595515087252794663994475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52254706899340785770651933 19595515087252794663994475)
      ·
        refine ⟨29393272630879191995991713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19595515087252794663994475 29393272630879191995991713)
        ·
          refine ⟨22044954473159393996993785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29393272630879191995991713 22044954473159393996993785)
          ·
            refine ⟨16533715854869545497745339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22044954473159393996993785 16533715854869545497745339)
            ·
              refine ⟨24800573782304318246618009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16533715854869545497745339 24800573782304318246618009)
              ·
                refine ⟨18600430336728238684963507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24800573782304318246618009 18600430336728238684963507)
                ·
                  refine ⟨27900645505092358027445261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18600430336728238684963507 27900645505092358027445261)
                  ·
                    refine ⟨10462742064409634260291973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27900645505092358027445261 10462742064409634260291973)
                    ·
                      refine ⟨1961764137076806423804745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10462742064409634260291973 1961764137076806423804745)
                      ·
                        rfl

theorem cell23_3820522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_3820522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820522 prefixEnd_3820522 := by exact prefixLift 3820522
  have htrace : WordTrace (prefixWord ++ tailWord_3820522) baseStart_3820522 baseEnd_3820522 := by
    simpa [prefixWord, tailWord_3820522, baseEnd_3820522] using wordTrace_append hprefix tailTrace_3820522
  have hstable : (prefixWord ++ tailWord_3820522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820522).length < 2 ^ (prefixWord ++ tailWord_3820522).sum := by decide
  have hdescent : baseEnd_3820522 < baseStart_3820522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820579 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 6]
def baseStart_3820579 : Nat := 118140960795 + 3820579 * 2 ^ 59
def prefixEnd_3820579 : Nat := 4983230072969 + 3 ^ 40 * 3820579 * 2
def baseEnd_3820579 : Nat := 217977045052679188976887

theorem tailTrace_3820579 : CollatzResearch.WordTrace tailWord_3820579 prefixEnd_3820579 217977045052679188976887 := by
  unfold tailWord_3820579
  simp only [CollatzResearch.WordTrace]
  refine ⟨139347964025702260789896791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92898642683801507193264527 139347964025702260789896791)
  ·
    refine ⟨209021946038553391184845187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139347964025702260789896791 209021946038553391184845187)
    ·
      refine ⟨313532919057830086777267781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209021946038553391184845187 313532919057830086777267781)
      ·
        refine ⟨58787422323343141270737709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313532919057830086777267781 58787422323343141270737709)
        ·
          refine ⟨22045283371253677976526641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58787422323343141270737709 22045283371253677976526641)
          ·
            refine ⟨16533962528440258482394981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22045283371253677976526641 16533962528440258482394981)
            ·
              refine ⟨3100117974082548465449059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16533962528440258482394981 3100117974082548465449059)
              ·
                refine ⟨4650176961123822698173589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100117974082548465449059 4650176961123822698173589)
                ·
                  refine ⟨217977045052679188976887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4650176961123822698173589 217977045052679188976887)
                  ·
                    rfl

theorem cell23_3820579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 6].length) (baseStart_3820579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820579 prefixEnd_3820579 := by exact prefixLift 3820579
  have htrace : WordTrace (prefixWord ++ tailWord_3820579) baseStart_3820579 baseEnd_3820579 := by
    simpa [prefixWord, tailWord_3820579, baseEnd_3820579] using wordTrace_append hprefix tailTrace_3820579
  have hstable : (prefixWord ++ tailWord_3820579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820579).length < 2 ^ (prefixWord ++ tailWord_3820579).sum := by decide
  have hdescent : baseEnd_3820579 < baseStart_3820579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820592 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 3, 5]
def baseStart_3820592 : Nat := 118140960795 + 3820592 * 2 ^ 59
def prefixEnd_3820592 : Nat := 4983230072969 + 3 ^ 40 * 3820592 * 2
def baseEnd_3820592 : Nat := 653933360240873716643141

theorem tailTrace_3820592 : CollatzResearch.WordTrace tailWord_3820592 prefixEnd_3820592 653933360240873716643141 := by
  unfold tailWord_3820592
  simp only [CollatzResearch.WordTrace]
  refine ⟨69674219087327582005060015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92898958783103442673413353 69674219087327582005060015)
  ·
    refine ⟨104511328630991373007590023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69674219087327582005060015 104511328630991373007590023)
    ·
      refine ⟨156766992946487059511385035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104511328630991373007590023 156766992946487059511385035)
      ·
        refine ⟨235150489419730589267077553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156766992946487059511385035 235150489419730589267077553)
        ·
          refine ⟨176362867064797941950308165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235150489419730589267077553 176362867064797941950308165)
          ·
            refine ⟨33068037574649614115682781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176362867064797941950308165 33068037574649614115682781)
            ·
              refine ⟨12400514090493605293381043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33068037574649614115682781 12400514090493605293381043)
              ·
                refine ⟨18600771135740407940071565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12400514090493605293381043 18600771135740407940071565)
                ·
                  refine ⟨6975289175902652977526837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18600771135740407940071565 6975289175902652977526837)
                  ·
                    refine ⟨653933360240873716643141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6975289175902652977526837 653933360240873716643141)
                    ·
                      rfl

theorem cell23_3820592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_3820592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820592 prefixEnd_3820592 := by exact prefixLift 3820592
  have htrace : WordTrace (prefixWord ++ tailWord_3820592) baseStart_3820592 baseEnd_3820592 := by
    simpa [prefixWord, tailWord_3820592, baseEnd_3820592] using wordTrace_append hprefix tailTrace_3820592
  have hstable : (prefixWord ++ tailWord_3820592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820592).length < 2 ^ (prefixWord ++ tailWord_3820592).sum := by decide
  have hdescent : baseEnd_3820592 < baseStart_3820592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820622 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_3820622 : Nat := 118140960795 + 3820622 * 2 ^ 59
def prefixEnd_3820622 : Nat := 4983230072969 + 3 ^ 40 * 3820622 * 2
def baseEnd_3820622 : Nat := 653938495047418677518095

theorem tailTrace_3820622 : CollatzResearch.WordTrace tailWord_3820622 prefixEnd_3820622 653938495047418677518095 := by
  unfold tailWord_3820622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17418691545568309891714015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92899688243030986089141413 17418691545568309891714015)
  ·
    refine ⟨26128037318352464837571023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17418691545568309891714015 26128037318352464837571023)
    ·
      refine ⟨39192055977528697256356535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26128037318352464837571023 39192055977528697256356535)
      ·
        refine ⟨58788083966293045884534803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39192055977528697256356535 58788083966293045884534803)
        ·
          refine ⟨88182125949439568826802205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58788083966293045884534803 88182125949439568826802205)
          ·
            refine ⟨33068297231039838310050827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88182125949439568826802205 33068297231039838310050827)
            ·
              refine ⟨49602445846559757465076241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33068297231039838310050827 49602445846559757465076241)
              ·
                refine ⟨37201834384919818098807181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49602445846559757465076241 37201834384919818098807181)
                ·
                  refine ⟨13950687894344931787052693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37201834384919818098807181 13950687894344931787052693)
                  ·
                    refine ⟨653938495047418677518095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13950687894344931787052693 653938495047418677518095)
                    ·
                      rfl

theorem cell23_3820622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_3820622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820622 prefixEnd_3820622 := by exact prefixLift 3820622
  have htrace : WordTrace (prefixWord ++ tailWord_3820622) baseStart_3820622 baseEnd_3820622 := by
    simpa [prefixWord, tailWord_3820622, baseEnd_3820622] using wordTrace_append hprefix tailTrace_3820622
  have hstable : (prefixWord ++ tailWord_3820622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820622).length < 2 ^ (prefixWord ++ tailWord_3820622).sum := by decide
  have hdescent : baseEnd_3820622 < baseStart_3820622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820632 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_3820632 : Nat := 118140960795 + 3820632 * 2 ^ 59
def prefixEnd_3820632 : Nat := 4983230072969 + 3 ^ 40 * 3820632 * 2
def baseEnd_3820632 : Nat := 1961820619948800993429239

theorem tailTrace_3820632 : CollatzResearch.WordTrace tailWord_3820632 prefixEnd_3820632 1961820619948800993429239 := by
  unfold tailWord_3820632
  simp only [CollatzResearch.WordTrace]
  refine ⟨69674948547255125420788075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92899931396340167227717433 69674948547255125420788075)
  ·
    refine ⟨104512422820882688131182113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69674948547255125420788075 104512422820882688131182113)
    ·
      refine ⟨78384317115662016098386585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104512422820882688131182113 78384317115662016098386585)
      ·
        refine ⟨58788237836746512073789939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78384317115662016098386585 58788237836746512073789939)
        ·
          refine ⟨88182356755119768110684909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58788237836746512073789939 88182356755119768110684909)
          ·
            refine ⟨33068383783169913041506841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88182356755119768110684909 33068383783169913041506841)
            ·
              refine ⟨24801287837377434781130131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33068383783169913041506841 24801287837377434781130131)
              ·
                refine ⟨37201931756066152171695197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24801287837377434781130131 37201931756066152171695197)
                ·
                  refine ⟨13950724408524807064385699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37201931756066152171695197 13950724408524807064385699)
                  ·
                    refine ⟨20926086612787210596578549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13950724408524807064385699 20926086612787210596578549)
                    ·
                      refine ⟨1961820619948800993429239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20926086612787210596578549 1961820619948800993429239)
                      ·
                        rfl

theorem cell23_3820632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_3820632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820632 prefixEnd_3820632 := by exact prefixLift 3820632
  have htrace : WordTrace (prefixWord ++ tailWord_3820632) baseStart_3820632 baseEnd_3820632 := by
    simpa [prefixWord, tailWord_3820632, baseEnd_3820632] using wordTrace_append hprefix tailTrace_3820632
  have hstable : (prefixWord ++ tailWord_3820632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820632).length < 2 ^ (prefixWord ++ tailWord_3820632).sum := by decide
  have hdescent : baseEnd_3820632 < baseStart_3820632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820639 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 2, 4]
def baseStart_3820639 : Nat := 118140960795 + 3820639 * 2 ^ 59
def prefixEnd_3820639 : Nat := 4983230072969 + 3 ^ 40 * 3820639 * 2
def baseEnd_3820639 : Nat := 653941404771127488680569

theorem tailTrace_3820639 : CollatzResearch.WordTrace tailWord_3820639 prefixEnd_3820639 653941404771127488680569 := by
  unfold tailWord_3820639
  simp only [CollatzResearch.WordTrace]
  refine ⟨139350152405484891037080971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92900101603656594024720647 139350152405484891037080971)
  ·
    refine ⟨209025228608227336555621457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139350152405484891037080971 209025228608227336555621457)
    ·
      refine ⟨156768921456170502416716093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209025228608227336555621457 156768921456170502416716093)
      ·
        refine ⟨58788345546063938406268535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156768921456170502416716093 58788345546063938406268535)
        ·
          refine ⟨88182518319095907609402803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58788345546063938406268535 88182518319095907609402803)
          ·
            refine ⟨132273777478643861414104205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88182518319095907609402803 132273777478643861414104205)
            ·
              refine ⟨49602666554491448030289077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132273777478643861414104205 49602666554491448030289077)
              ·
                refine ⟨4650249989483573252839601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49602666554491448030289077 4650249989483573252839601)
                ·
                  refine ⟨3487687492112679939629701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650249989483573252839601 3487687492112679939629701)
                  ·
                    refine ⟨653941404771127488680569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487687492112679939629701 653941404771127488680569)
                    ·
                      rfl

theorem cell23_3820639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 4].length) (baseStart_3820639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820639 prefixEnd_3820639 := by exact prefixLift 3820639
  have htrace : WordTrace (prefixWord ++ tailWord_3820639) baseStart_3820639 baseEnd_3820639 := by
    simpa [prefixWord, tailWord_3820639, baseEnd_3820639] using wordTrace_append hprefix tailTrace_3820639
  have hstable : (prefixWord ++ tailWord_3820639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820639).length < 2 ^ (prefixWord ++ tailWord_3820639).sum := by decide
  have hdescent : baseEnd_3820639 < baseStart_3820639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820649 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 3]
def baseStart_3820649 : Nat := 118140960795 + 3820649 * 2 ^ 59
def prefixEnd_3820649 : Nat := 4983230072969 + 3 ^ 40 * 3820649 * 2
def baseEnd_3820649 : Nat := 1961829349119927426916661

theorem tailTrace_3820649 : CollatzResearch.WordTrace tailWord_3820649 prefixEnd_3820649 1961829349119927426916661 := by
  unfold tailWord_3820649
  simp only [CollatzResearch.WordTrace]
  refine ⟨139350517135448662744945001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92900344756965775163296667 139350517135448662744945001)
  ·
    refine ⟨104512887851586497058708751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139350517135448662744945001 104512887851586497058708751)
    ·
      refine ⟨156769331777379745588063127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104512887851586497058708751 156769331777379745588063127)
      ·
        refine ⟨235153997666069618382094691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156769331777379745588063127 235153997666069618382094691)
        ·
          refine ⟨352730996499104427573142037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235153997666069618382094691 352730996499104427573142037)
          ·
            refine ⟨16534265460895520042491033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 352730996499104427573142037 16534265460895520042491033)
            ·
              refine ⟨12400699095671640031868275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16534265460895520042491033 12400699095671640031868275)
              ·
                refine ⟨18601048643507460047802413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12400699095671640031868275 18601048643507460047802413)
                ·
                  refine ⟨6975393241315297517925905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18601048643507460047802413 6975393241315297517925905)
                  ·
                    refine ⟨5231544930986473138444429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6975393241315297517925905 5231544930986473138444429)
                    ·
                      refine ⟨1961829349119927426916661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5231544930986473138444429 1961829349119927426916661)
                      ·
                        rfl

theorem cell23_3820649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 3].length) (baseStart_3820649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820649 prefixEnd_3820649 := by exact prefixLift 3820649
  have htrace : WordTrace (prefixWord ++ tailWord_3820649) baseStart_3820649 baseEnd_3820649 := by
    simpa [prefixWord, tailWord_3820649, baseEnd_3820649] using wordTrace_append hprefix tailTrace_3820649
  have hstable : (prefixWord ++ tailWord_3820649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820649).length < 2 ^ (prefixWord ++ tailWord_3820649).sum := by decide
  have hdescent : baseEnd_3820649 < baseStart_3820649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820673 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3820673 : Nat := 118140960795 + 3820673 * 2 ^ 59
def prefixEnd_3820673 : Nat := 4983230072969 + 3 ^ 40 * 3820673 * 2
def baseEnd_3820673 : Nat := 653947224218545111005517

theorem tailTrace_3820673 : CollatzResearch.WordTrace tailWord_3820673 prefixEnd_3820673 653947224218545111005517 := by
  unfold tailWord_3820673
  simp only [CollatzResearch.WordTrace]
  refine ⟨139351392487361714843818673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92900928324907809895879115 139351392487361714843818673)
  ·
    refine ⟨104513544365521286132864005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139351392487361714843818673 104513544365521286132864005)
    ·
      refine ⟨19596289568535241149912001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104513544365521286132864005 19596289568535241149912001)
      ·
        refine ⟨14697217176401430862434001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19596289568535241149912001 14697217176401430862434001)
        ·
          refine ⟨11022912882301073146825501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14697217176401430862434001 11022912882301073146825501)
          ·
            refine ⟨4133592330862902430059563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11022912882301073146825501 4133592330862902430059563)
            ·
              refine ⟨6200388496294353645089345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133592330862902430059563 6200388496294353645089345)
              ·
                refine ⟨4650291372220765233817009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200388496294353645089345 4650291372220765233817009)
                ·
                  refine ⟨3487718529165573925362757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650291372220765233817009 3487718529165573925362757)
                  ·
                    refine ⟨653947224218545111005517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487718529165573925362757 653947224218545111005517)
                    ·
                      rfl

theorem cell23_3820673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3820673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820673 prefixEnd_3820673 := by exact prefixLift 3820673
  have htrace : WordTrace (prefixWord ++ tailWord_3820673) baseStart_3820673 baseEnd_3820673 := by
    simpa [prefixWord, tailWord_3820673, baseEnd_3820673] using wordTrace_append hprefix tailTrace_3820673
  have hstable : (prefixWord ++ tailWord_3820673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820673).length < 2 ^ (prefixWord ++ tailWord_3820673).sum := by decide
  have hdescent : baseEnd_3820673 < baseStart_3820673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820680 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3820680 : Nat := 118140960795 + 3820680 * 2 ^ 59
def prefixEnd_3820680 : Nat := 4983230072969 + 3 ^ 40 * 3820680 * 2
def baseEnd_3820680 : Nat := 1961845267020216805629019

theorem tailTrace_3820680 : CollatzResearch.WordTrace tailWord_3820680 prefixEnd_3820680 1961845267020216805629019 := by
  unfold tailWord_3820680
  simp only [CollatzResearch.WordTrace]
  refine ⟨69675823899168177519661747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92901098532224236692882329 69675823899168177519661747)
  ·
    refine ⟨104513735848752266279492621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69675823899168177519661747 104513735848752266279492621)
    ·
      refine ⟨39192650943282099854809733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104513735848752266279492621 39192650943282099854809733)
      ·
        refine ⟨7348622051865393722776825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39192650943282099854809733 7348622051865393722776825)
        ·
          refine ⟨5511466538899045292082619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7348622051865393722776825 5511466538899045292082619)
          ·
            refine ⟨8267199808348567938123929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511466538899045292082619 8267199808348567938123929)
            ·
              refine ⟨6200399856261425953592947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8267199808348567938123929 6200399856261425953592947)
              ·
                refine ⟨9300599784392138930389421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200399856261425953592947 9300599784392138930389421)
                ·
                  refine ⟨3487724919147052098896033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9300599784392138930389421 3487724919147052098896033)
                  ·
                    refine ⟨2615793689360289074172025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3487724919147052098896033 2615793689360289074172025)
                    ·
                      refine ⟨1961845267020216805629019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615793689360289074172025 1961845267020216805629019)
                      ·
                        rfl

theorem cell23_3820680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3820680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820680 prefixEnd_3820680 := by exact prefixLift 3820680
  have htrace : WordTrace (prefixWord ++ tailWord_3820680) baseStart_3820680 baseEnd_3820680 := by
    simpa [prefixWord, tailWord_3820680, baseEnd_3820680] using wordTrace_append hprefix tailTrace_3820680
  have hstable : (prefixWord ++ tailWord_3820680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820680).length < 2 ^ (prefixWord ++ tailWord_3820680).sum := by decide
  have hdescent : baseEnd_3820680 < baseStart_3820680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820696 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3820696 : Nat := 118140960795 + 3820696 * 2 ^ 59
def prefixEnd_3820696 : Nat := 4983230072969 + 3 ^ 40 * 3820696 * 2
def baseEnd_3820696 : Nat := 1961853482710688743028945

theorem tailTrace_3820696 : CollatzResearch.WordTrace tailWord_3820696 prefixEnd_3820696 1961853482710688743028945 := by
  unfold tailWord_3820696
  simp only [CollatzResearch.WordTrace]
  refine ⟨69676115683139194885952971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92901487577518926514603961 69676115683139194885952971)
  ·
    refine ⟨104514173524708792328929457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69676115683139194885952971 104514173524708792328929457)
    ·
      refine ⟨78385630143531594246697093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104514173524708792328929457 78385630143531594246697093)
      ·
        refine ⟨14697305651912173921255705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78385630143531594246697093 14697305651912173921255705)
        ·
          refine ⟨11022979238934130440941779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14697305651912173921255705 11022979238934130440941779)
          ·
            refine ⟨16534468858401195661412669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11022979238934130440941779 16534468858401195661412669)
            ·
              refine ⟨6200425821900448373029751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16534468858401195661412669 6200425821900448373029751)
              ·
                refine ⟨9300638732850672559544627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200425821900448373029751 9300638732850672559544627)
                ·
                  refine ⟨13950958099276008839316941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9300638732850672559544627 13950958099276008839316941)
                  ·
                    refine ⟨5231609287228503314743853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13950958099276008839316941 5231609287228503314743853)
                    ·
                      refine ⟨1961853482710688743028945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5231609287228503314743853 1961853482710688743028945)
                      ·
                        rfl

theorem cell23_3820696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3820696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820696 prefixEnd_3820696 := by exact prefixLift 3820696
  have htrace : WordTrace (prefixWord ++ tailWord_3820696) baseStart_3820696 baseEnd_3820696 := by
    simpa [prefixWord, tailWord_3820696, baseEnd_3820696] using wordTrace_append hprefix tailTrace_3820696
  have hstable : (prefixWord ++ tailWord_3820696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820696).length < 2 ^ (prefixWord ++ tailWord_3820696).sum := by decide
  have hdescent : baseEnd_3820696 < baseStart_3820696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820703 : List Nat := [1, 1, 2, 6, 3, 1, 2, 7]
def baseStart_3820703 : Nat := 118140960795 + 3820703 * 2 ^ 59
def prefixEnd_3820703 : Nat := 4983230072969 + 3 ^ 40 * 3820703 * 2
def baseEnd_3820703 : Nat := 72661373225010007986719

theorem tailTrace_3820703 : CollatzResearch.WordTrace tailWord_3820703 prefixEnd_3820703 72661373225010007986719 := by
  unfold tailWord_3820703
  simp only [CollatzResearch.WordTrace]
  refine ⟨139352486677253029967410763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92901657784835353311607175 139352486677253029967410763)
  ·
    refine ⟨209028730015879544951116145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139352486677253029967410763 209028730015879544951116145)
    ·
      refine ⟨156771547511909658713337109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209028730015879544951116145 156771547511909658713337109)
      ·
        refine ⟨7348666289620765252187677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 156771547511909658713337109 7348666289620765252187677)
        ·
          refine ⟨2755749858607786969570379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7348666289620765252187677 2755749858607786969570379)
          ·
            refine ⟨4133624787911680454355569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755749858607786969570379 4133624787911680454355569)
            ·
              refine ⟨3100218590933760340766677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4133624787911680454355569 3100218590933760340766677)
              ·
                refine ⟨72661373225010007986719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3100218590933760340766677 72661373225010007986719)
                ·
                  rfl

theorem cell23_3820703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 7].length) (baseStart_3820703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820703 prefixEnd_3820703 := by exact prefixLift 3820703
  have htrace : WordTrace (prefixWord ++ tailWord_3820703) baseStart_3820703 baseEnd_3820703 := by
    simpa [prefixWord, tailWord_3820703, baseEnd_3820703] using wordTrace_append hprefix tailTrace_3820703
  have hstable : (prefixWord ++ tailWord_3820703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820703).length < 2 ^ (prefixWord ++ tailWord_3820703).sum := by decide
  have hdescent : baseEnd_3820703 < baseStart_3820703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820714 : List Nat := [3, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3820714 : Nat := 118140960795 + 3820714 * 2 ^ 59
def prefixEnd_3820714 : Nat := 4983230072969 + 3 ^ 40 * 3820714 * 2
def baseEnd_3820714 : Nat := 1961862725362469672603863

theorem tailTrace_3820714 : CollatzResearch.WordTrace tailWord_3820714 prefixEnd_3820714 1961862725362469672603863 := by
  unfold tailWord_3820714
  simp only [CollatzResearch.WordTrace]
  refine ⟨34838221970053294711515299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92901925253475452564040797 34838221970053294711515299)
  ·
    refine ⟨52257332955079942067272949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34838221970053294711515299 52257332955079942067272949)
    ·
      refine ⟨4899124964538744568806839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52257332955079942067272949 4899124964538744568806839)
      ·
        refine ⟨7348687446808116853210259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899124964538744568806839 7348687446808116853210259)
        ·
          refine ⟨11023031170212175279815389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7348687446808116853210259 11023031170212175279815389)
          ·
            refine ⟨4133636688829565729930771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11023031170212175279815389 4133636688829565729930771)
            ·
              refine ⟨6200455033244348594896157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133636688829565729930771 6200455033244348594896157)
              ·
                refine ⟨2325170637466630723086059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6200455033244348594896157 2325170637466630723086059)
                ·
                  refine ⟨3487755956199946084629089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325170637466630723086059 3487755956199946084629089)
                  ·
                    refine ⟨2615816967149959563471817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3487755956199946084629089 2615816967149959563471817)
                    ·
                      refine ⟨1961862725362469672603863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2615816967149959563471817 1961862725362469672603863)
                      ·
                        rfl

theorem cell23_3820714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3820714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820714 prefixEnd_3820714 := by exact prefixLift 3820714
  have htrace : WordTrace (prefixWord ++ tailWord_3820714) baseStart_3820714 baseEnd_3820714 := by
    simpa [prefixWord, tailWord_3820714, baseEnd_3820714] using wordTrace_append hprefix tailTrace_3820714
  have hstable : (prefixWord ++ tailWord_3820714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820714).length < 2 ^ (prefixWord ++ tailWord_3820714).sum := by decide
  have hdescent : baseEnd_3820714 < baseStart_3820714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820776 : List Nat := [2, 1, 4, 1, 2, 1, 2, 5, 5]
def baseStart_3820776 : Nat := 118140960795 + 3820776 * 2 ^ 59
def prefixEnd_3820776 : Nat := 4983230072969 + 3 ^ 40 * 3820776 * 2
def baseEnd_3820776 : Nat := 217988284573672047780953

theorem tailTrace_3820776 : CollatzResearch.WordTrace tailWord_3820776 prefixEnd_3820776 217988284573672047780953 := by
  unfold tailWord_3820776
  simp only [CollatzResearch.WordTrace]
  refine ⟨69677574602994281717409091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92903432803992375623212121 69677574602994281717409091)
  ·
    refine ⟨104516361904491422576113637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69677574602994281717409091 104516361904491422576113637)
    ·
      refine ⟨19596817857092141733021307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104516361904491422576113637 19596817857092141733021307)
      ·
        refine ⟨29395226785638212599531961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19596817857092141733021307 29395226785638212599531961)
        ·
          refine ⟨22046420089228659449648971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29395226785638212599531961 22046420089228659449648971)
          ·
            refine ⟨33069630133842989174473457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22046420089228659449648971 33069630133842989174473457)
            ·
              refine ⟨24802222600382241880855093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33069630133842989174473457 24802222600382241880855093)
              ·
                refine ⟨2325208368785835176330165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24802222600382241880855093 2325208368785835176330165)
                ·
                  refine ⟨217988284573672047780953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2325208368785835176330165 217988284573672047780953)
                  ·
                    rfl

theorem cell23_3820776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 5].length) (baseStart_3820776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820776 prefixEnd_3820776 := by exact prefixLift 3820776
  have htrace : WordTrace (prefixWord ++ tailWord_3820776) baseStart_3820776 baseEnd_3820776 := by
    simpa [prefixWord, tailWord_3820776, baseEnd_3820776] using wordTrace_append hprefix tailTrace_3820776
  have hstable : (prefixWord ++ tailWord_3820776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820776).length < 2 ^ (prefixWord ++ tailWord_3820776).sum := by decide
  have hdescent : baseEnd_3820776 < baseStart_3820776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820799 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_3820799 : Nat := 118140960795 + 3820799 * 2 ^ 59
def prefixEnd_3820799 : Nat := 4983230072969 + 3 ^ 40 * 3820799 * 2
def baseEnd_3820799 : Nat := 1961906371218101840040971

theorem tailTrace_3820799 : CollatzResearch.WordTrace tailWord_3820799 prefixEnd_3820799 1961906371218101840040971 := by
  unfold tailWord_3820799
  simp only [CollatzResearch.WordTrace]
  refine ⟨139355988084905238362905451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92903992056603492241936967 139355988084905238362905451)
  ·
    refine ⟨209033982127357857544358177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139355988084905238362905451 209033982127357857544358177)
    ·
      refine ⟨156775486595518393158268633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209033982127357857544358177 156775486595518393158268633)
      ·
        refine ⟨117581614946638794868701475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156775486595518393158268633 117581614946638794868701475)
        ·
          refine ⟨176372422419958192303052213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117581614946638794868701475 176372422419958192303052213)
          ·
            refine ⟨16534914601871080528411145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176372422419958192303052213 16534914601871080528411145)
            ·
              refine ⟨12401185951403310396308359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16534914601871080528411145 12401185951403310396308359)
              ·
                refine ⟨18601778927104965594462539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12401185951403310396308359 18601778927104965594462539)
                ·
                  refine ⟨27902668390657448391693809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18601778927104965594462539 27902668390657448391693809)
                  ·
                    refine ⟨20927001292993086293770357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27902668390657448391693809 20927001292993086293770357)
                    ·
                      refine ⟨1961906371218101840040971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20927001292993086293770357 1961906371218101840040971)
                      ·
                        rfl

theorem cell23_3820799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_3820799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820799 prefixEnd_3820799 := by exact prefixLift 3820799
  have htrace : WordTrace (prefixWord ++ tailWord_3820799) baseStart_3820799 baseEnd_3820799 := by
    simpa [prefixWord, tailWord_3820799, baseEnd_3820799] using wordTrace_append hprefix tailTrace_3820799
  have hstable : (prefixWord ++ tailWord_3820799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820799).length < 2 ^ (prefixWord ++ tailWord_3820799).sum := by decide
  have hdescent : baseEnd_3820799 < baseStart_3820799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820809 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_3820809 : Nat := 118140960795 + 3820809 * 2 ^ 59
def prefixEnd_3820809 : Nat := 4983230072969 + 3 ^ 40 * 3820809 * 2
def baseEnd_3820809 : Nat := 1961911506024646800915925

theorem tailTrace_3820809 : CollatzResearch.WordTrace tailWord_3820809 prefixEnd_3820809 1961911506024646800915925 := by
  unfold tailWord_3820809
  simp only [CollatzResearch.WordTrace]
  refine ⟨139356352814869010070769481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92904235209912673380512987 139356352814869010070769481)
  ·
    refine ⟨104517264611151757553077111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139356352814869010070769481 104517264611151757553077111)
    ·
      refine ⟨156775896916727636329615667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104517264611151757553077111 156775896916727636329615667)
      ·
        refine ⟨235163845375091454494423501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156775896916727636329615667 235163845375091454494423501)
        ·
          refine ⟨88186442015659295435408813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235163845375091454494423501 88186442015659295435408813)
          ·
            refine ⟨33069915755872235788278305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88186442015659295435408813 33069915755872235788278305)
            ·
              refine ⟨24802436816904176841208729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33069915755872235788278305 24802436816904176841208729)
              ·
                refine ⟨18601827612678132630906547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24802436816904176841208729 18601827612678132630906547)
                ·
                  refine ⟨27902741419017198946359821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18601827612678132630906547 27902741419017198946359821)
                  ·
                    refine ⟨10463528032131449604884933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27902741419017198946359821 10463528032131449604884933)
                    ·
                      refine ⟨1961911506024646800915925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10463528032131449604884933 1961911506024646800915925)
                      ·
                        rfl

theorem cell23_3820809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_3820809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820809 prefixEnd_3820809 := by exact prefixLift 3820809
  have htrace : WordTrace (prefixWord ++ tailWord_3820809) baseStart_3820809 baseEnd_3820809 := by
    simpa [prefixWord, tailWord_3820809, baseEnd_3820809] using wordTrace_append hprefix tailTrace_3820809
  have hstable : (prefixWord ++ tailWord_3820809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820809).length < 2 ^ (prefixWord ++ tailWord_3820809).sum := by decide
  have hdescent : baseEnd_3820809 < baseStart_3820809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820826 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_3820826 : Nat := 118140960795 + 3820826 * 2 ^ 59
def prefixEnd_3820826 : Nat := 4983230072969 + 3 ^ 40 * 3820826 * 2
def baseEnd_3820826 : Nat := 1961920235195773234403347

theorem tailTrace_3820826 : CollatzResearch.WordTrace tailWord_3820826 prefixEnd_3820826 1961920235195773234403347 := by
  unfold tailWord_3820826
  simp only [CollatzResearch.WordTrace]
  refine ⟨34839243213951855493534583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92904648570538281316092221 34839243213951855493534583)
  ·
    refine ⟨52258864820927783240301875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34839243213951855493534583 52258864820927783240301875)
    ·
      refine ⟨78388297231391674860452813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52258864820927783240301875 78388297231391674860452813)
      ·
        refine ⟨29395611461771878072669805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78388297231391674860452813 29395611461771878072669805)
        ·
          refine ⟨11023354298164454277251177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29395611461771878072669805 11023354298164454277251177)
          ·
            refine ⟨8267515723623340707938383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11023354298164454277251177 8267515723623340707938383)
            ·
              refine ⟨12401273585435011061907575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267515723623340707938383 12401273585435011061907575)
              ·
                refine ⟨18601910378152516592861363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12401273585435011061907575 18601910378152516592861363)
                ·
                  refine ⟨27902865567228774889292045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18601910378152516592861363 27902865567228774889292045)
                  ·
                    refine ⟨10463574587710790583484517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27902865567228774889292045 10463574587710790583484517)
                    ·
                      refine ⟨1961920235195773234403347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10463574587710790583484517 1961920235195773234403347)
                      ·
                        rfl

theorem cell23_3820826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_3820826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820826 prefixEnd_3820826 := by exact prefixLift 3820826
  have htrace : WordTrace (prefixWord ++ tailWord_3820826) baseStart_3820826 baseEnd_3820826 := by
    simpa [prefixWord, tailWord_3820826, baseEnd_3820826] using wordTrace_append hprefix tailTrace_3820826
  have hstable : (prefixWord ++ tailWord_3820826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820826).length < 2 ^ (prefixWord ++ tailWord_3820826).sum := by decide
  have hdescent : baseEnd_3820826 < baseStart_3820826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820836 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_3820836 : Nat := 118140960795 + 3820836 * 2 ^ 59
def prefixEnd_3820836 : Nat := 4983230072969 + 3 ^ 40 * 3820836 * 2
def baseEnd_3820836 : Nat := 653975123334106065092767

theorem tailTrace_3820836 : CollatzResearch.WordTrace tailWord_3820836 prefixEnd_3820836 653975123334106065092767 := by
  unfold tailWord_3820836
  simp only [CollatzResearch.WordTrace]
  refine ⟨69678668792885596841001181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92904891723847462454668241 69678668792885596841001181)
  ·
    refine ⟨26129500797332098815375443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69678668792885596841001181 26129500797332098815375443)
    ·
      refine ⟨39194251195998148223063165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26129500797332098815375443 39194251195998148223063165)
      ·
        refine ⟨14697844198499305583648687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39194251195998148223063165 14697844198499305583648687)
        ·
          refine ⟨22046766297748958375473031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14697844198499305583648687 22046766297748958375473031)
          ·
            refine ⟨33070149446623437563209547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22046766297748958375473031 33070149446623437563209547)
            ·
              refine ⟨49605224169935156344814321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33070149446623437563209547 49605224169935156344814321)
              ·
                refine ⟨37203918127451367258610741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49605224169935156344814321 37203918127451367258610741)
                ·
                  refine ⟨3487867324448565680494757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37203918127451367258610741 3487867324448565680494757)
                  ·
                    refine ⟨653975123334106065092767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487867324448565680494757 653975123334106065092767)
                    ·
                      rfl

theorem cell23_3820836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_3820836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820836 prefixEnd_3820836 := by exact prefixLift 3820836
  have htrace : WordTrace (prefixWord ++ tailWord_3820836) baseStart_3820836 baseEnd_3820836 := by
    simpa [prefixWord, tailWord_3820836, baseEnd_3820836] using wordTrace_append hprefix tailTrace_3820836
  have hstable : (prefixWord ++ tailWord_3820836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820836).length < 2 ^ (prefixWord ++ tailWord_3820836).sum := by decide
  have hdescent : baseEnd_3820836 < baseStart_3820836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820853 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3820853 : Nat := 118140960795 + 3820853 * 2 ^ 59
def prefixEnd_3820853 : Nat := 4983230072969 + 3 ^ 40 * 3820853 * 2
def baseEnd_3820853 : Nat := 653978033057814876255241

theorem tailTrace_3820853 : CollatzResearch.WordTrace tailWord_3820853 prefixEnd_3820853 653978033057814876255241 := by
  unfold tailWord_3820853
  simp only [CollatzResearch.WordTrace]
  refine ⟨139357957626709605585371213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92905305084473070390247475 139357957626709605585371213)
  ·
    refine ⟨52259234110016102094514205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139357957626709605585371213 52259234110016102094514205)
    ·
      refine ⟨19597212791256038285442827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52259234110016102094514205 19597212791256038285442827)
      ·
        refine ⟨29395819186884057428164241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19597212791256038285442827 29395819186884057428164241)
        ·
          refine ⟨22046864390163043071123181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29395819186884057428164241 22046864390163043071123181)
          ·
            refine ⟨8267574146311141151671193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22046864390163043071123181 8267574146311141151671193)
            ·
              refine ⟨6200680609733355863753395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8267574146311141151671193 6200680609733355863753395)
              ·
                refine ⟨9301020914600033795630093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200680609733355863753395 9301020914600033795630093)
                ·
                  refine ⟨3487882842975012673361285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9301020914600033795630093 3487882842975012673361285)
                  ·
                    refine ⟨653978033057814876255241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487882842975012673361285 653978033057814876255241)
                    ·
                      rfl

theorem cell23_3820853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3820853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820853 prefixEnd_3820853 := by exact prefixLift 3820853
  have htrace : WordTrace (prefixWord ++ tailWord_3820853) baseStart_3820853 baseEnd_3820853 := by
    simpa [prefixWord, tailWord_3820853, baseEnd_3820853] using wordTrace_append hprefix tailTrace_3820853
  have hstable : (prefixWord ++ tailWord_3820853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820853).length < 2 ^ (prefixWord ++ tailWord_3820853).sum := by decide
  have hdescent : baseEnd_3820853 < baseStart_3820853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820879 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 7, 5]
def baseStart_3820879 : Nat := 118140960795 + 3820879 * 2 ^ 59
def prefixEnd_3820879 : Nat := 4983230072969 + 3 ^ 40 * 3820879 * 2
def baseEnd_3820879 : Nat := 653982483223487175680201

theorem tailTrace_3820879 : CollatzResearch.WordTrace tailWord_3820879 prefixEnd_3820879 653982483223487175680201 := by
  unfold tailWord_3820879
  simp only [CollatzResearch.WordTrace]
  refine ⟨139358905924615412025817691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92905937283076941350545127 139358905924615412025817691)
  ·
    refine ⟨209038358886923118038726537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139358905924615412025817691 209038358886923118038726537)
    ·
      refine ⟨156778769165192338529044903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209038358886923118038726537 156778769165192338529044903)
      ·
        refine ⟨235168153747788507793567355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156778769165192338529044903 235168153747788507793567355)
        ·
          refine ⟨352752230621682761690351033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235168153747788507793567355 352752230621682761690351033)
          ·
            refine ⟨264564172966262071267763275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352752230621682761690351033 264564172966262071267763275)
            ·
              refine ⟨396846259449393106901644913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264564172966262071267763275 396846259449393106901644913)
              ·
                refine ⟨297634694587044830176233685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396846259449393106901644913 297634694587044830176233685)
                ·
                  refine ⟨6975813154383863207255477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297634694587044830176233685 6975813154383863207255477)
                  ·
                    refine ⟨653982483223487175680201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6975813154383863207255477 653982483223487175680201)
                    ·
                      rfl

theorem cell23_3820879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_3820879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820879 prefixEnd_3820879 := by exact prefixLift 3820879
  have htrace : WordTrace (prefixWord ++ tailWord_3820879) baseStart_3820879 baseEnd_3820879 := by
    simpa [prefixWord, tailWord_3820879, baseEnd_3820879] using wordTrace_append hprefix tailTrace_3820879
  have hstable : (prefixWord ++ tailWord_3820879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820879).length < 2 ^ (prefixWord ++ tailWord_3820879).sum := by decide
  have hdescent : baseEnd_3820879 < baseStart_3820879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820917 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 6]
def baseStart_3820917 : Nat := 118140960795 + 3820917 * 2 ^ 59
def prefixEnd_3820917 : Nat := 4983230072969 + 3 ^ 40 * 3820917 * 2
def baseEnd_3820917 : Nat := 217996329103925819818381

theorem tailTrace_3820917 : CollatzResearch.WordTrace tailWord_3820917 prefixEnd_3820917 217996329103925819818381 := by
  unfold tailWord_3820917
  simp only [CollatzResearch.WordTrace]
  refine ⟨139360291898477744515701005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92906861265651829677134003 139360291898477744515701005)
  ·
    refine ⟨52260109461929154193387877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139360291898477744515701005 52260109461929154193387877)
    ·
      refine ⟨9798770524111716411260227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52260109461929154193387877 9798770524111716411260227)
      ·
        refine ⟨14698155786167574616890341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9798770524111716411260227 14698155786167574616890341)
        ·
          refine ⟨2755904209906420240666939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14698155786167574616890341 2755904209906420240666939)
          ·
            refine ⟨4133856314859630361000409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755904209906420240666939 4133856314859630361000409)
            ·
              refine ⟨3100392236144722770750307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4133856314859630361000409 3100392236144722770750307)
              ·
                refine ⟨4650588354217084156125461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100392236144722770750307 4650588354217084156125461)
                ·
                  refine ⟨217996329103925819818381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4650588354217084156125461 217996329103925819818381)
                  ·
                    rfl

theorem cell23_3820917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_3820917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820917 prefixEnd_3820917 := by exact prefixLift 3820917
  have htrace : WordTrace (prefixWord ++ tailWord_3820917) baseStart_3820917 baseEnd_3820917 := by
    simpa [prefixWord, tailWord_3820917, baseEnd_3820917] using wordTrace_append hprefix tailTrace_3820917
  have hstable : (prefixWord ++ tailWord_3820917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820917).length < 2 ^ (prefixWord ++ tailWord_3820917).sum := by decide
  have hdescent : baseEnd_3820917 < baseStart_3820917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820930 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3820930 : Nat := 118140960795 + 3820930 * 2 ^ 59
def prefixEnd_3820930 : Nat := 4983230072969 + 3 ^ 40 * 3820930 * 2
def baseEnd_3820930 : Nat := 653991212394613609167623

theorem tailTrace_3820930 : CollatzResearch.WordTrace tailWord_3820930 prefixEnd_3820930 653991212394613609167623 := by
  unfold tailWord_3820930
  simp only [CollatzResearch.WordTrace]
  refine ⟨34840191511857661933981061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92907177364953765157282829 34840191511857661933981061)
  ·
    refine ⟨6532535908473311612621449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34840191511857661933981061 6532535908473311612621449)
    ·
      refine ⟨4899401931354983709466087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6532535908473311612621449 4899401931354983709466087)
      ·
        refine ⟨7349102897032475564199131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899401931354983709466087 7349102897032475564199131)
        ·
          refine ⟨11023654345548713346298697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7349102897032475564199131 11023654345548713346298697)
          ·
            refine ⟨8267740759161535009724023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11023654345548713346298697 8267740759161535009724023)
            ·
              refine ⟨12401611138742302514586035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267740759161535009724023 12401611138742302514586035)
              ·
                refine ⟨18602416708113453771879053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12401611138742302514586035 18602416708113453771879053)
                ·
                  refine ⟨6975906265542545164454645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18602416708113453771879053 6975906265542545164454645)
                  ·
                    refine ⟨653991212394613609167623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6975906265542545164454645 653991212394613609167623)
                    ·
                      rfl

theorem cell23_3820930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3820930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820930 prefixEnd_3820930 := by exact prefixLift 3820930
  have htrace : WordTrace (prefixWord ++ tailWord_3820930) baseStart_3820930 baseEnd_3820930 := by
    simpa [prefixWord, tailWord_3820930, baseEnd_3820930] using wordTrace_append hprefix tailTrace_3820930
  have hstable : (prefixWord ++ tailWord_3820930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820930).length < 2 ^ (prefixWord ++ tailWord_3820930).sum := by decide
  have hdescent : baseEnd_3820930 < baseStart_3820930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820933 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_3820933 : Nat := 118140960795 + 3820933 * 2 ^ 59
def prefixEnd_3820933 : Nat := 4983230072969 + 3 ^ 40 * 3820933 * 2
def baseEnd_3820933 : Nat := 1961975177625804315765355

theorem tailTrace_3820933 : CollatzResearch.WordTrace tailWord_3820933 prefixEnd_3820933 1961975177625804315765355 := by
  unfold tailWord_3820933
  simp only [CollatzResearch.WordTrace]
  refine ⟨139360875466419779248283453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92907250310946519498855635 139360875466419779248283453)
  ·
    refine ⟨52260328299907417218106295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139360875466419779248283453 52260328299907417218106295)
    ·
      refine ⟨78390492449861125827159443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52260328299907417218106295 78390492449861125827159443)
      ·
        refine ⟨117585738674791688740739165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78390492449861125827159443 117585738674791688740739165)
        ·
          refine ⟨44094652003046883277777187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117585738674791688740739165 44094652003046883277777187)
          ·
            refine ⟨66141978004570324916665781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44094652003046883277777187 66141978004570324916665781)
            ·
              refine ⟨6200810437928467960937417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66141978004570324916665781 6200810437928467960937417)
              ·
                refine ⟨4650607828446350970703063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200810437928467960937417 4650607828446350970703063)
                ·
                  refine ⟨6975911742669526456054595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650607828446350970703063 6975911742669526456054595)
                  ·
                    refine ⟨10463867614004289684081893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6975911742669526456054595 10463867614004289684081893)
                    ·
                      refine ⟨1961975177625804315765355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10463867614004289684081893 1961975177625804315765355)
                      ·
                        rfl

theorem cell23_3820933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_3820933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820933 prefixEnd_3820933 := by exact prefixLift 3820933
  have htrace : WordTrace (prefixWord ++ tailWord_3820933) baseStart_3820933 baseEnd_3820933 := by
    simpa [prefixWord, tailWord_3820933, baseEnd_3820933] using wordTrace_append hprefix tailTrace_3820933
  have hstable : (prefixWord ++ tailWord_3820933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820933).length < 2 ^ (prefixWord ++ tailWord_3820933).sum := by decide
  have hdescent : baseEnd_3820933 < baseStart_3820933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820939 : List Nat := [1, 1, 1, 1, 4, 3, 1, 11]
def baseStart_3820939 : Nat := 118140960795 + 3820939 * 2 ^ 59
def prefixEnd_3820939 : Nat := 4983230072969 + 3 ^ 40 * 3820939 * 2
def baseEnd_3820939 : Nat := 72665861426286344158901

theorem tailTrace_3820939 : CollatzResearch.WordTrace tailWord_3820939 prefixEnd_3820939 72665861426286344158901 := by
  unfold tailWord_3820939
  simp only [CollatzResearch.WordTrace]
  refine ⟨139361094304398042273001871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92907396202932028182001247 139361094304398042273001871)
  ·
    refine ⟨209041641456597063409502807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139361094304398042273001871 209041641456597063409502807)
    ·
      refine ⟨313562462184895595114254211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209041641456597063409502807 313562462184895595114254211)
      ·
        refine ⟨470343693277343392671381317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313562462184895595114254211 470343693277343392671381317)
        ·
          refine ⟨88189442489501886125883997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470343693277343392671381317 88189442489501886125883997)
          ·
            refine ⟨33071040933563207297206499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88189442489501886125883997 33071040933563207297206499)
            ·
              refine ⟨49606561400344810945809749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33071040933563207297206499 49606561400344810945809749)
              ·
                refine ⟨72665861426286344158901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 49606561400344810945809749 72665861426286344158901)
                ·
                  rfl

theorem cell23_3820939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 11].length) (baseStart_3820939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820939 prefixEnd_3820939 := by exact prefixLift 3820939
  have htrace : WordTrace (prefixWord ++ tailWord_3820939) baseStart_3820939 baseEnd_3820939 := by
    simpa [prefixWord, tailWord_3820939, baseEnd_3820939] using wordTrace_append hprefix tailTrace_3820939
  have hstable : (prefixWord ++ tailWord_3820939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820939).length < 2 ^ (prefixWord ++ tailWord_3820939).sum := by decide
  have hdescent : baseEnd_3820939 < baseStart_3820939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820953 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 5]
def baseStart_3820953 : Nat := 118140960795 + 3820953 * 2 ^ 59
def prefixEnd_3820953 : Nat := 4983230072969 + 3 ^ 40 * 3820953 * 2
def baseEnd_3820953 : Nat := 1961985447238894237515263

theorem tailTrace_3820953 : CollatzResearch.WordTrace tailWord_3820953 prefixEnd_3820953 1961985447238894237515263 := by
  unfold tailWord_3820953
  simp only [CollatzResearch.WordTrace]
  refine ⟨139361604926347322664011513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92907736617564881776007675 139361604926347322664011513)
  ·
    refine ⟨104521203694760491998008635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139361604926347322664011513 104521203694760491998008635)
    ·
      refine ⟨156781805542140737997012953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104521203694760491998008635 156781805542140737997012953)
      ·
        refine ⟨117586354156605553497759715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156781805542140737997012953 117586354156605553497759715)
        ·
          refine ⟨176379531234908330246639573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117586354156605553497759715 176379531234908330246639573)
          ·
            refine ⟨4133895263318163990155615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 176379531234908330246639573 4133895263318163990155615)
            ·
              refine ⟨6200842894977245985233423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133895263318163990155615 6200842894977245985233423)
              ·
                refine ⟨9301264342465868977850135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200842894977245985233423 9301264342465868977850135)
                ·
                  refine ⟨13951896513698803466775203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9301264342465868977850135 13951896513698803466775203)
                  ·
                    refine ⟨20927844770548205200162805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13951896513698803466775203 20927844770548205200162805)
                    ·
                      refine ⟨1961985447238894237515263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20927844770548205200162805 1961985447238894237515263)
                      ·
                        rfl

theorem cell23_3820953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_3820953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820953 prefixEnd_3820953 := by exact prefixLift 3820953
  have htrace : WordTrace (prefixWord ++ tailWord_3820953) baseStart_3820953 baseEnd_3820953 := by
    simpa [prefixWord, tailWord_3820953, baseEnd_3820953] using wordTrace_append hprefix tailTrace_3820953
  have hstable : (prefixWord ++ tailWord_3820953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820953).length < 2 ^ (prefixWord ++ tailWord_3820953).sum := by decide
  have hdescent : baseEnd_3820953 < baseStart_3820953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820956 : List Nat := [2, 2, 3, 4, 12]
def baseStart_3820956 : Nat := 118140960795 + 3820956 * 2 ^ 59
def prefixEnd_3820956 : Nat := 4983230072969 + 3 ^ 40 * 3820956 * 2
def baseEnd_3820956 : Nat := 2691340175145209500381

theorem tailTrace_3820956 : CollatzResearch.WordTrace tailWord_3820956 prefixEnd_3820956 2691340175145209500381 := by
  unfold tailWord_3820956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69680857172668227088185361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92907809563557636117580481 69680857172668227088185361)
  ·
    refine ⟨52260642879501170316139021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69680857172668227088185361 52260642879501170316139021)
    ·
      refine ⟨19597741079812938868552133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52260642879501170316139021 19597741079812938868552133)
      ·
        refine ⟨3674576452464926037853525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19597741079812938868552133 3674576452464926037853525)
        ·
          refine ⟨2691340175145209500381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3674576452464926037853525 2691340175145209500381)
          ·
            rfl

theorem cell23_3820956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 12].length) (baseStart_3820956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820956 prefixEnd_3820956 := by exact prefixLift 3820956
  have htrace : WordTrace (prefixWord ++ tailWord_3820956) baseStart_3820956 baseEnd_3820956 := by
    simpa [prefixWord, tailWord_3820956, baseEnd_3820956] using wordTrace_append hprefix tailTrace_3820956
  have hstable : (prefixWord ++ tailWord_3820956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820956).length < 2 ^ (prefixWord ++ tailWord_3820956).sum := by decide
  have hdescent : baseEnd_3820956 < baseStart_3820956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820973 : List Nat := [1, 5, 2, 2, 1, 1, 3, 8]
def baseStart_3820973 : Nat := 118140960795 + 3820973 * 2 ^ 59
def prefixEnd_3820973 : Nat := 4983230072969 + 3 ^ 40 * 3820973 * 2
def baseEnd_3820973 : Nat := 72666508031554968861673

theorem tailTrace_3820973 : CollatzResearch.WordTrace tailWord_3820973 prefixEnd_3820973 72666508031554968861673 := by
  unfold tailWord_3820973
  simp only [CollatzResearch.WordTrace]
  refine ⟨139362334386274866079739573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92908222924183244053159715 139362334386274866079739573)
  ·
    refine ⟨13065218848713268694975585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139362334386274866079739573 13065218848713268694975585)
    ·
      refine ⟨9798914136534951521231689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13065218848713268694975585 9798914136534951521231689)
      ·
        refine ⟨7349185602401213640923767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9798914136534951521231689 7349185602401213640923767)
        ·
          refine ⟨11023778403601820461385651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7349185602401213640923767 11023778403601820461385651)
          ·
            refine ⟨16535667605402730692078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11023778403601820461385651 16535667605402730692078477)
            ·
              refine ⟨6200875352026024009529429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16535667605402730692078477 6200875352026024009529429)
              ·
                refine ⟨72666508031554968861673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6200875352026024009529429 72666508031554968861673)
                ·
                  rfl

theorem cell23_3820973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 8].length) (baseStart_3820973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820973 prefixEnd_3820973 := by exact prefixLift 3820973
  have htrace : WordTrace (prefixWord ++ tailWord_3820973) baseStart_3820973 baseEnd_3820973 := by
    simpa [prefixWord, tailWord_3820973, baseEnd_3820973] using wordTrace_append hprefix tailTrace_3820973
  have hstable : (prefixWord ++ tailWord_3820973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820973).length < 2 ^ (prefixWord ++ tailWord_3820973).sum := by decide
  have hdescent : baseEnd_3820973 < baseStart_3820973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820983 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_3820983 : Nat := 118140960795 + 3820983 * 2 ^ 59
def prefixEnd_3820983 : Nat := 4983230072969 + 3 ^ 40 * 3820983 * 2
def baseEnd_3820983 : Nat := 1962000851658529120140125

theorem tailTrace_3820983 : CollatzResearch.WordTrace tailWord_3820983 prefixEnd_3820983 1962000851658529120140125 := by
  unfold tailWord_3820983
  simp only [CollatzResearch.WordTrace]
  refine ⟨139362699116238637787603603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92908466077492425191735735 139362699116238637787603603)
  ·
    refine ⟨209044048674357956681405405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139362699116238637787603603 209044048674357956681405405)
    ·
      refine ⟨78391518252884233755527027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209044048674357956681405405 78391518252884233755527027)
      ·
        refine ⟨117587277379326350633290541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78391518252884233755527027 117587277379326350633290541)
        ·
          refine ⟨44095229017247381487483953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117587277379326350633290541 44095229017247381487483953)
          ·
            refine ⟨33071421762935536115612965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44095229017247381487483953 33071421762935536115612965)
            ·
              refine ⟨6200891580550413021677431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33071421762935536115612965 6200891580550413021677431)
              ·
                refine ⟨9301337370825619532516147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200891580550413021677431 9301337370825619532516147)
                ·
                  refine ⟨13952006056238429298774221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9301337370825619532516147 13952006056238429298774221)
                  ·
                    refine ⟨5232002271089410987040333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13952006056238429298774221 5232002271089410987040333)
                    ·
                      refine ⟨1962000851658529120140125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232002271089410987040333 1962000851658529120140125)
                      ·
                        rfl

theorem cell23_3820983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_3820983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3820983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3820983 prefixEnd_3820983 := by exact prefixLift 3820983
  have htrace : WordTrace (prefixWord ++ tailWord_3820983) baseStart_3820983 baseEnd_3820983 := by
    simpa [prefixWord, tailWord_3820983, baseEnd_3820983] using wordTrace_append hprefix tailTrace_3820983
  have hstable : (prefixWord ++ tailWord_3820983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820983).length < 2 ^ (prefixWord ++ tailWord_3820983).sum := by decide
  have hdescent : baseEnd_3820983 < baseStart_3820983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821016 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 2, 6]
def baseStart_3821016 : Nat := 118140960795 + 3821016 * 2 ^ 59
def prefixEnd_3821016 : Nat := 4983230072969 + 3 ^ 40 * 3821016 * 2
def baseEnd_3821016 : Nat := 654005932173375830342491

theorem tailTrace_3821016 : CollatzResearch.WordTrace tailWord_3821016 prefixEnd_3821016 654005932173375830342491 := by
  unfold tailWord_3821016
  simp only [CollatzResearch.WordTrace]
  refine ⟨69681951362559542211777451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92909268483412722949036601 69681951362559542211777451)
  ·
    refine ⟨104522927043839313317666177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69681951362559542211777451 104522927043839313317666177)
    ·
      refine ⟨78392195282879484988249633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104522927043839313317666177 78392195282879484988249633)
      ·
        refine ⟨58794146462159613741187225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78392195282879484988249633 58794146462159613741187225)
        ·
          refine ⟨44095609846619710305890419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58794146462159613741187225 44095609846619710305890419)
          ·
            refine ⟨66143414769929565458835629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44095609846619710305890419 66143414769929565458835629)
            ·
              refine ⟨24803780538723587047063361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66143414769929565458835629 24803780538723587047063361)
              ·
                refine ⟨18602835404042690285297521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24803780538723587047063361 18602835404042690285297521)
                ·
                  refine ⟨13952126553032017713973141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18602835404042690285297521 13952126553032017713973141)
                  ·
                    refine ⟨654005932173375830342491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13952126553032017713973141 654005932173375830342491)
                    ·
                      rfl

theorem cell23_3821016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_3821016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821016 prefixEnd_3821016 := by exact prefixLift 3821016
  have htrace : WordTrace (prefixWord ++ tailWord_3821016) baseStart_3821016 baseEnd_3821016 := by
    simpa [prefixWord, tailWord_3821016, baseEnd_3821016] using wordTrace_append hprefix tailTrace_3821016
  have hstable : (prefixWord ++ tailWord_3821016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821016).length < 2 ^ (prefixWord ++ tailWord_3821016).sum := by decide
  have hdescent : baseEnd_3821016 < baseStart_3821016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821017 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 3]
def baseStart_3821017 : Nat := 118140960795 + 3821017 * 2 ^ 59
def prefixEnd_3821017 : Nat := 4983230072969 + 3 ^ 40 * 3821017 * 2
def baseEnd_3821017 : Nat := 1962018310000781987114969

theorem tailTrace_3821017 : CollatzResearch.WordTrace tailWord_3821017 prefixEnd_3821017 1962018310000781987114969 := by
  unfold tailWord_3821017
  simp only [CollatzResearch.WordTrace]
  refine ⟨139363939198115461594341305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92909292798743641062894203 139363939198115461594341305)
  ·
    refine ⟨104522954398586596195755979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139363939198115461594341305 104522954398586596195755979)
    ·
      refine ⟨156784431597879894293633969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104522954398586596195755979 156784431597879894293633969)
      ·
        refine ⟨117588323698409920720225477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156784431597879894293633969 117588323698409920720225477)
        ·
          refine ⟨22047810693451860135042277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117588323698409920720225477 22047810693451860135042277)
          ·
            refine ⟨4133964505022223775320427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22047810693451860135042277 4133964505022223775320427)
            ·
              refine ⟨6200946757533335662980641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133964505022223775320427 6200946757533335662980641)
              ·
                refine ⟨4650710068150001747235481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200946757533335662980641 4650710068150001747235481)
                ·
                  refine ⟨3488032551112501310426611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650710068150001747235481 3488032551112501310426611)
                  ·
                    refine ⟨5232048826668751965639917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488032551112501310426611 5232048826668751965639917)
                    ·
                      refine ⟨1962018310000781987114969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232048826668751965639917 1962018310000781987114969)
                      ·
                        rfl

theorem cell23_3821017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_3821017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821017 prefixEnd_3821017 := by exact prefixLift 3821017
  have htrace : WordTrace (prefixWord ++ tailWord_3821017) baseStart_3821017 baseEnd_3821017 := by
    simpa [prefixWord, tailWord_3821017, baseEnd_3821017] using wordTrace_append hprefix tailTrace_3821017
  have hstable : (prefixWord ++ tailWord_3821017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821017).length < 2 ^ (prefixWord ++ tailWord_3821017).sum := by decide
  have hdescent : baseEnd_3821017 < baseStart_3821017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821034 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_3821034 : Nat := 118140960795 + 3821034 * 2 ^ 59
def prefixEnd_3821034 : Nat := 4983230072969 + 3 ^ 40 * 3821034 * 2
def baseEnd_3821034 : Nat := 1962027039171908420602391

theorem tailTrace_3821034 : CollatzResearch.WordTrace tailWord_3821034 prefixEnd_3821034 1962027039171908420602391 := by
  unfold tailWord_3821034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34841139809763468374427539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92909706159369248998473437 34841139809763468374427539)
  ·
    refine ⟨52261709714645202561641309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34841139809763468374427539 52261709714645202561641309)
    ·
      refine ⟨19598141142991950960615491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52261709714645202561641309 19598141142991950960615491)
      ·
        refine ⟨29397211714487926440923237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19598141142991950960615491 29397211714487926440923237)
        ·
          refine ⟨5511977196466486207673107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29397211714487926440923237 5511977196466486207673107)
          ·
            refine ⟨8267965794699729311509661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511977196466486207673107 8267965794699729311509661)
            ·
              refine ⟨3100487173012398491816123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8267965794699729311509661 3100487173012398491816123)
              ·
                refine ⟨4650730759518597737724185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100487173012398491816123 4650730759518597737724185)
                ·
                  refine ⟨3488048069638948303293139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650730759518597737724185 3488048069638948303293139)
                  ·
                    refine ⟨5232072104458422454939709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488048069638948303293139 5232072104458422454939709)
                    ·
                      refine ⟨1962027039171908420602391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232072104458422454939709 1962027039171908420602391)
                      ·
                        rfl

theorem cell23_3821034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_3821034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821034 prefixEnd_3821034 := by exact prefixLift 3821034
  have htrace : WordTrace (prefixWord ++ tailWord_3821034) baseStart_3821034 baseEnd_3821034 := by
    simpa [prefixWord, tailWord_3821034, baseEnd_3821034] using wordTrace_append hprefix tailTrace_3821034
  have hstable : (prefixWord ++ tailWord_3821034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821034).length < 2 ^ (prefixWord ++ tailWord_3821034).sum := by decide
  have hdescent : baseEnd_3821034 < baseStart_3821034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821036 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_3821036 : Nat := 118140960795 + 3821036 * 2 ^ 59
def prefixEnd_3821036 : Nat := 4983230072969 + 3 ^ 40 * 3821036 * 2
def baseEnd_3821036 : Nat := 1962028066133217412777381

theorem tailTrace_3821036 : CollatzResearch.WordTrace tailWord_3821036 prefixEnd_3821036 1962028066133217412777381 := by
  unfold tailWord_3821036
  simp only [CollatzResearch.WordTrace]
  refine ⟨69682316092523313919641481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92909754790031085226188641 69682316092523313919641481)
  ·
    refine ⟨52261737069392485439731111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69682316092523313919641481 52261737069392485439731111)
    ·
      refine ⟨78392605604088728159596667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52261737069392485439731111 78392605604088728159596667)
      ·
        refine ⟨117588908406133092239395001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78392605604088728159596667 117588908406133092239395001)
        ·
          refine ⟨88191681304599819179546251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117588908406133092239395001 88191681304599819179546251)
          ·
            refine ⟨132287521956899728769319377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88191681304599819179546251 132287521956899728769319377)
            ·
              refine ⟨99215641467674796576989533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132287521956899728769319377 99215641467674796576989533)
              ·
                refine ⟨37205865550378048716371075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99215641467674796576989533 37205865550378048716371075)
                ·
                  refine ⟨55808798325567073074556613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37205865550378048716371075 55808798325567073074556613)
                  ·
                    refine ⟨10464149686043826201479365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55808798325567073074556613 10464149686043826201479365)
                    ·
                      refine ⟨1962028066133217412777381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10464149686043826201479365 1962028066133217412777381)
                      ·
                        rfl

theorem cell23_3821036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_3821036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821036 prefixEnd_3821036 := by exact prefixLift 3821036
  have htrace : WordTrace (prefixWord ++ tailWord_3821036) baseStart_3821036 baseEnd_3821036 := by
    simpa [prefixWord, tailWord_3821036, baseEnd_3821036] using wordTrace_append hprefix tailTrace_3821036
  have hstable : (prefixWord ++ tailWord_3821036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821036).length < 2 ^ (prefixWord ++ tailWord_3821036).sum := by decide
  have hdescent : baseEnd_3821036 < baseStart_3821036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821040 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 1, 4, 2]
def baseStart_3821040 : Nat := 118140960795 + 3821040 * 2 ^ 59
def prefixEnd_3821040 : Nat := 4983230072969 + 3 ^ 40 * 3821040 * 2
def baseEnd_3821040 : Nat := 1962030120055835397127363

theorem tailTrace_3821040 : CollatzResearch.WordTrace tailWord_3821040 prefixEnd_3821040 1962030120055835397127363 := by
  unfold tailWord_3821040
  simp only [CollatzResearch.WordTrace]
  refine ⟨69682389038516068261214287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92909852051354757681619049 69682389038516068261214287)
  ·
    refine ⟨104523583557774102391821431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69682389038516068261214287 104523583557774102391821431)
    ·
      refine ⟨156785375336661153587732147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104523583557774102391821431 156785375336661153587732147)
      ·
        refine ⟨235178063004991730381598221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156785375336661153587732147 235178063004991730381598221)
        ·
          refine ⟨88191773626871898893099333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235178063004991730381598221 88191773626871898893099333)
          ·
            refine ⟨16535957555038481042456125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88191773626871898893099333 16535957555038481042456125)
            ·
              refine ⟨6200984083139430390921047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16535957555038481042456125 6200984083139430390921047)
              ·
                refine ⟨9301476124709145586381571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200984083139430390921047 9301476124709145586381571)
                ·
                  refine ⟨13952214187063718379572357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9301476124709145586381571 13952214187063718379572357)
                  ·
                    refine ⟨2616040160074447196169817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13952214187063718379572357 2616040160074447196169817)
                    ·
                      refine ⟨1962030120055835397127363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616040160074447196169817 1962030120055835397127363)
                      ·
                        rfl

theorem cell23_3821040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 4, 2].length) (baseStart_3821040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821040 prefixEnd_3821040 := by exact prefixLift 3821040
  have htrace : WordTrace (prefixWord ++ tailWord_3821040) baseStart_3821040 baseEnd_3821040 := by
    simpa [prefixWord, tailWord_3821040, baseEnd_3821040] using wordTrace_append hprefix tailTrace_3821040
  have hstable : (prefixWord ++ tailWord_3821040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821040).length < 2 ^ (prefixWord ++ tailWord_3821040).sum := by decide
  have hdescent : baseEnd_3821040 < baseStart_3821040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821060 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3821060 : Nat := 118140960795 + 3821060 * 2 ^ 59
def prefixEnd_3821060 : Nat := 4983230072969 + 3 ^ 40 * 3821060 * 2
def baseEnd_3821060 : Nat := 1962040389668925318877271

theorem tailTrace_3821060 : CollatzResearch.WordTrace tailWord_3821060 prefixEnd_3821060 1962040389668925318877271 := by
  unfold tailWord_3821060
  simp only [CollatzResearch.WordTrace]
  refine ⟨69682753768479839969078317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92910338357973119958771089 69682753768479839969078317)
  ·
    refine ⟨26131032663179939988404369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69682753768479839969078317 26131032663179939988404369)
    ·
      refine ⟨19598274497384954991303277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26131032663179939988404369 19598274497384954991303277)
      ·
        refine ⟨7349352936519358121738729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19598274497384954991303277 7349352936519358121738729)
        ·
          refine ⟨5512014702389518591304047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7349352936519358121738729 5512014702389518591304047)
          ·
            refine ⟨8268022053584277886956071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512014702389518591304047 8268022053584277886956071)
            ·
              refine ⟨12402033080376416830434107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268022053584277886956071 12402033080376416830434107)
              ·
                refine ⟨18603049620564625245651161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12402033080376416830434107 18603049620564625245651161)
                ·
                  refine ⟨13952287215423468934238371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18603049620564625245651161 13952287215423468934238371)
                  ·
                    refine ⟨20928430823135203401357557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13952287215423468934238371 20928430823135203401357557)
                    ·
                      refine ⟨1962040389668925318877271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20928430823135203401357557 1962040389668925318877271)
                      ·
                        rfl

theorem cell23_3821060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3821060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821060 prefixEnd_3821060 := by exact prefixLift 3821060
  have htrace : WordTrace (prefixWord ++ tailWord_3821060) baseStart_3821060 baseEnd_3821060 := by
    simpa [prefixWord, tailWord_3821060, baseEnd_3821060] using wordTrace_append hprefix tailTrace_3821060
  have hstable : (prefixWord ++ tailWord_3821060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821060).length < 2 ^ (prefixWord ++ tailWord_3821060).sum := by decide
  have hdescent : baseEnd_3821060 < baseStart_3821060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821080 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 7]
def baseStart_3821080 : Nat := 118140960795 + 3821080 * 2 ^ 59
def prefixEnd_3821080 : Nat := 4983230072969 + 3 ^ 40 * 3821080 * 2
def baseEnd_3821080 : Nat := 218005628809112804514131

theorem tailTrace_3821080 : CollatzResearch.WordTrace tailWord_3821080 prefixEnd_3821080 218005628809112804514131 := by
  unfold tailWord_3821080
  simp only [CollatzResearch.WordTrace]
  refine ⟨69683118498443611676942347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92910824664591482235923129 69683118498443611676942347)
  ·
    refine ⟨104524677747665417515413521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69683118498443611676942347 104524677747665417515413521)
    ·
      refine ⟨78393508310749063136560141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104524677747665417515413521 78393508310749063136560141)
      ·
        refine ⟨29397565616530898676210053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78393508310749063136560141 29397565616530898676210053)
        ·
          refine ⟨5512043553099543501789385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29397565616530898676210053 5512043553099543501789385)
          ·
            refine ⟨4134032664824657626342039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5512043553099543501789385 4134032664824657626342039)
            ·
              refine ⟨6201048997236986439513059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134032664824657626342039 6201048997236986439513059)
              ·
                refine ⟨9301573495855479659269589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201048997236986439513059 9301573495855479659269589)
                ·
                  refine ⟨218005628809112804514131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9301573495855479659269589 218005628809112804514131)
                  ·
                    rfl

theorem cell23_3821080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 7].length) (baseStart_3821080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821080 prefixEnd_3821080 := by exact prefixLift 3821080
  have htrace : WordTrace (prefixWord ++ tailWord_3821080) baseStart_3821080 baseEnd_3821080 := by
    simpa [prefixWord, tailWord_3821080, baseEnd_3821080] using wordTrace_append hprefix tailTrace_3821080
  have hstable : (prefixWord ++ tailWord_3821080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821080).length < 2 ^ (prefixWord ++ tailWord_3821080).sum := by decide
  have hdescent : baseEnd_3821080 < baseStart_3821080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821091 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 2, 2, 2]
def baseStart_3821091 : Nat := 118140960795 + 3821091 * 2 ^ 59
def prefixEnd_3821091 : Nat := 4983230072969 + 3 ^ 40 * 3821091 * 2
def baseEnd_3821091 : Nat := 1962056307569214697589629

theorem tailTrace_3821091 : CollatzResearch.WordTrace tailWord_3821091 prefixEnd_3821091 1962056307569214697589629 := by
  unfold tailWord_3821091
  simp only [CollatzResearch.WordTrace]
  refine ⟨139366638199847372232535127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92911092133231581488356751 139366638199847372232535127)
  ·
    refine ⟨209049957299771058348802691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139366638199847372232535127 209049957299771058348802691)
    ·
      refine ⟨313574935949656587523204037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209049957299771058348802691 313574935949656587523204037)
      ·
        refine ⟨58795300490560610160600757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313574935949656587523204037 58795300490560610160600757)
        ·
          refine ⟨5512059420990057202556321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58795300490560610160600757 5512059420990057202556321)
          ·
            refine ⟨4134044565742542901917241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5512059420990057202556321 4134044565742542901917241)
            ·
              refine ⟨3100533424306907176437931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4134044565742542901917241 3100533424306907176437931)
              ·
                refine ⟨4650800136460360764656897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100533424306907176437931 4650800136460360764656897)
                ·
                  refine ⟨3488100102345270573492673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650800136460360764656897 3488100102345270573492673)
                  ·
                    refine ⟨2616075076758952930119505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3488100102345270573492673 2616075076758952930119505)
                    ·
                      refine ⟨1962056307569214697589629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616075076758952930119505 1962056307569214697589629)
                      ·
                        rfl

theorem cell23_3821091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_3821091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821091 prefixEnd_3821091 := by exact prefixLift 3821091
  have htrace : WordTrace (prefixWord ++ tailWord_3821091) baseStart_3821091 baseEnd_3821091 := by
    simpa [prefixWord, tailWord_3821091, baseEnd_3821091] using wordTrace_append hprefix tailTrace_3821091
  have hstable : (prefixWord ++ tailWord_3821091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821091).length < 2 ^ (prefixWord ++ tailWord_3821091).sum := by decide
  have hdescent : baseEnd_3821091 < baseStart_3821091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821130 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_3821130 : Nat := 118140960795 + 3821130 * 2 ^ 59
def prefixEnd_3821130 : Nat := 4983230072969 + 3 ^ 40 * 3821130 * 2
def baseEnd_3821130 : Nat := 1962076333314740045001949

theorem tailTrace_3821130 : CollatzResearch.WordTrace tailWord_3821130 prefixEnd_3821130 1962076333314740045001949 := by
  unfold tailWord_3821130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34842015161676520473301211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92912040431137387928803229 34842015161676520473301211)
  ·
    refine ⟨52263022742514780709951817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34842015161676520473301211 52263022742514780709951817)
    ·
      refine ⟨39197267056886085532463863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52263022742514780709951817 39197267056886085532463863)
      ·
        refine ⟨58795900585329128298695795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39197267056886085532463863 58795900585329128298695795)
        ·
          refine ⟨88193850877993692448043693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58795900585329128298695795 88193850877993692448043693)
          ·
            refine ⟨33072694079247634668016385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88193850877993692448043693 33072694079247634668016385)
            ·
              refine ⟨24804520559435726001012289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33072694079247634668016385 24804520559435726001012289)
              ·
                refine ⟨18603390419576794500759217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24804520559435726001012289 18603390419576794500759217)
                ·
                  refine ⟨13952542814682595875569413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18603390419576794500759217 13952542814682595875569413)
                  ·
                    refine ⟨2616101777752986726669265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13952542814682595875569413 2616101777752986726669265)
                    ·
                      refine ⟨1962076333314740045001949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616101777752986726669265 1962076333314740045001949)
                      ·
                        rfl

theorem cell23_3821130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_3821130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821130 prefixEnd_3821130 := by exact prefixLift 3821130
  have htrace : WordTrace (prefixWord ++ tailWord_3821130) baseStart_3821130 baseEnd_3821130 := by
    simpa [prefixWord, tailWord_3821130, baseEnd_3821130] using wordTrace_append hprefix tailTrace_3821130
  have hstable : (prefixWord ++ tailWord_3821130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821130).length < 2 ^ (prefixWord ++ tailWord_3821130).sum := by decide
  have hdescent : baseEnd_3821130 < baseStart_3821130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821140 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_3821140 : Nat := 118140960795 + 3821140 * 2 ^ 59
def prefixEnd_3821140 : Nat := 4983230072969 + 3 ^ 40 * 3821140 * 2
def baseEnd_3821140 : Nat := 654027156040428335292301

theorem tailTrace_3821140 : CollatzResearch.WordTrace tailWord_3821140 prefixEnd_3821140 654027156040428335292301 := by
  unfold tailWord_3821140
  simp only [CollatzResearch.WordTrace]
  refine ⟨69684212688334926800534437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92912283584446569067379249 69684212688334926800534437)
  ·
    refine ⟨13065789879062798775100207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69684212688334926800534437 13065789879062798775100207)
    ·
      refine ⟨19598684818594198162650311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065789879062798775100207 19598684818594198162650311)
      ·
        refine ⟨29398027227891297243975467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19598684818594198162650311 29398027227891297243975467)
        ·
          refine ⟨44097040841836945865963201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29398027227891297243975467 44097040841836945865963201)
          ·
            refine ⟨33072780631377709399472401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44097040841836945865963201 33072780631377709399472401)
            ·
              refine ⟨24804585473533282049604301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33072780631377709399472401 24804585473533282049604301)
              ·
                refine ⟨9301719552574980768601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24804585473533282049604301 9301719552574980768601613)
                ·
                  refine ⟨3488144832215617788225605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9301719552574980768601613 3488144832215617788225605)
                  ·
                    refine ⟨654027156040428335292301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488144832215617788225605 654027156040428335292301)
                    ·
                      rfl

theorem cell23_3821140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_3821140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821140 prefixEnd_3821140 := by exact prefixLift 3821140
  have htrace : WordTrace (prefixWord ++ tailWord_3821140) baseStart_3821140 baseEnd_3821140 := by
    simpa [prefixWord, tailWord_3821140, baseEnd_3821140] using wordTrace_append hprefix tailTrace_3821140
  have hstable : (prefixWord ++ tailWord_3821140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821140).length < 2 ^ (prefixWord ++ tailWord_3821140).sum := by decide
  have hdescent : baseEnd_3821140 < baseStart_3821140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821153 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 6]
def baseStart_3821153 : Nat := 118140960795 + 3821153 * 2 ^ 59
def prefixEnd_3821153 : Nat := 4983230072969 + 3 ^ 40 * 3821153 * 2
def baseEnd_3821153 : Nat := 218009793707754828334927

theorem tailTrace_3821153 : CollatzResearch.WordTrace tailWord_3821153 prefixEnd_3821153 218009793707754828334927 := by
  unfold tailWord_3821153
  simp only [CollatzResearch.WordTrace]
  refine ⟨139368899525622756821292113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92912599683748504547528075 139368899525622756821292113)
  ·
    refine ⟨104526674644217067615969085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139368899525622756821292113 104526674644217067615969085)
    ·
      refine ⟨39197502991581400355988407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104526674644217067615969085 39197502991581400355988407)
      ·
        refine ⟨58796254487372100533982611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39197502991581400355988407 58796254487372100533982611)
        ·
          refine ⟨88194381731058150800973917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58796254487372100533982611 88194381731058150800973917)
          ·
            refine ⟨33072893149146806550365219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88194381731058150800973917 33072893149146806550365219)
            ·
              refine ⟨49609339723720209825547829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33072893149146806550365219 49609339723720209825547829)
              ·
                refine ⟨4650875599098769671145109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49609339723720209825547829 4650875599098769671145109)
                ·
                  refine ⟨218009793707754828334927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4650875599098769671145109 218009793707754828334927)
                  ·
                    rfl

theorem cell23_3821153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 6].length) (baseStart_3821153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821153 prefixEnd_3821153 := by exact prefixLift 3821153
  have htrace : WordTrace (prefixWord ++ tailWord_3821153) baseStart_3821153 baseEnd_3821153 := by
    simpa [prefixWord, tailWord_3821153, baseEnd_3821153] using wordTrace_append hprefix tailTrace_3821153
  have hstable : (prefixWord ++ tailWord_3821153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821153).length < 2 ^ (prefixWord ++ tailWord_3821153).sum := by decide
  have hdescent : baseEnd_3821153 < baseStart_3821153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821174 : List Nat := [5, 1, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_3821174 : Nat := 118140960795 + 3821174 * 2 ^ 59
def prefixEnd_3821174 : Nat := 4983230072969 + 3 ^ 40 * 3821174 * 2
def baseEnd_3821174 : Nat := 654032975487845957617249

theorem tailTrace_3821174 : CollatzResearch.WordTrace tailWord_3821174 prefixEnd_3821174 654032975487845957617249 := by
  unfold tailWord_3821174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8710604091159167337987911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92913110305697784938537717 8710604091159167337987911)
  ·
    refine ⟨13065906136738751006981867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8710604091159167337987911 13065906136738751006981867)
    ·
      refine ⟨19598859205108126510472801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065906136738751006981867 19598859205108126510472801)
      ·
        refine ⟨14699144403831094882854601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19598859205108126510472801 14699144403831094882854601)
        ·
          refine ⟨11024358302873321162140951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14699144403831094882854601 11024358302873321162140951)
          ·
            refine ⟨16536537454309981743211427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11024358302873321162140951 16536537454309981743211427)
            ·
              refine ⟨24804806181464972614817141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16536537454309981743211427 24804806181464972614817141)
              ·
                refine ⟨2325450579512341182639107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24804806181464972614817141 2325450579512341182639107)
                ·
                  refine ⟨3488175869268511773958661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325450579512341182639107 3488175869268511773958661)
                  ·
                    refine ⟨654032975487845957617249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488175869268511773958661 654032975487845957617249)
                    ·
                      rfl

theorem cell23_3821174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_3821174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821174 prefixEnd_3821174 := by exact prefixLift 3821174
  have htrace : WordTrace (prefixWord ++ tailWord_3821174) baseStart_3821174 baseEnd_3821174 := by
    simpa [prefixWord, tailWord_3821174, baseEnd_3821174] using wordTrace_append hprefix tailTrace_3821174
  have hstable : (prefixWord ++ tailWord_3821174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821174).length < 2 ^ (prefixWord ++ tailWord_3821174).sum := by decide
  have hdescent : baseEnd_3821174 < baseStart_3821174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821180 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_3821180 : Nat := 118140960795 + 3821180 * 2 ^ 59
def prefixEnd_3821180 : Nat := 4983230072969 + 3 ^ 40 * 3821180 * 2
def baseEnd_3821180 : Nat := 1962102007347464849376719

theorem tailTrace_3821180 : CollatzResearch.WordTrace tailWord_3821180 prefixEnd_3821180 1962102007347464849376719 := by
  unfold tailWord_3821180
  simp only [CollatzResearch.WordTrace]
  refine ⟨69684942148262470216262497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92913256197683293621683329 69684942148262470216262497)
  ·
    refine ⟨52263706611196852662196873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69684942148262470216262497 52263706611196852662196873)
    ·
      refine ⟨39197779958397639496647655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52263706611196852662196873 39197779958397639496647655)
      ·
        refine ⟨58796669937596459244971483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39197779958397639496647655 58796669937596459244971483)
        ·
          refine ⟨88195004906394688867457225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58796669937596459244971483 88195004906394688867457225)
          ·
            refine ⟨66146253679796016650592919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88195004906394688867457225 66146253679796016650592919)
            ·
              refine ⟨99219380519694024975889379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66146253679796016650592919 99219380519694024975889379)
              ·
                refine ⟨148829070779541037463834069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99219380519694024975889379 148829070779541037463834069)
                ·
                  refine ⟨3488181346395493065558611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 148829070779541037463834069 3488181346395493065558611)
                  ·
                    refine ⟨5232272019593239598337917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488181346395493065558611 5232272019593239598337917)
                    ·
                      refine ⟨1962102007347464849376719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232272019593239598337917 1962102007347464849376719)
                      ·
                        rfl

theorem cell23_3821180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_3821180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821180 prefixEnd_3821180 := by exact prefixLift 3821180
  have htrace : WordTrace (prefixWord ++ tailWord_3821180) baseStart_3821180 baseEnd_3821180 := by
    simpa [prefixWord, tailWord_3821180, baseEnd_3821180] using wordTrace_append hprefix tailTrace_3821180
  have hstable : (prefixWord ++ tailWord_3821180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821180).length < 2 ^ (prefixWord ++ tailWord_3821180).sum := by decide
  have hdescent : baseEnd_3821180 < baseStart_3821180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821204 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 6]
def baseStart_3821204 : Nat := 118140960795 + 3821204 * 2 ^ 59
def prefixEnd_3821204 : Nat := 4983230072969 + 3 ^ 40 * 3821204 * 2
def baseEnd_3821204 : Nat := 218012703431463639497401

theorem tailTrace_3821204 : CollatzResearch.WordTrace tailWord_3821204 prefixEnd_3821204 218012703431463639497401 := by
  unfold tailWord_3821204
  simp only [CollatzResearch.WordTrace]
  refine ⟨69685379824218996265699333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92913839765625328354265777 69685379824218996265699333)
  ·
    refine ⟨13066008717041061799818625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69685379824218996265699333 13066008717041061799818625)
    ·
      refine ⟨9799506537780796349863969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13066008717041061799818625 9799506537780796349863969)
      ·
        refine ⟨7349629903335597262397977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9799506537780796349863969 7349629903335597262397977)
        ·
          refine ⟨5512222427501697946798483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7349629903335597262397977 5512222427501697946798483)
          ·
            refine ⟨8268333641252546920197725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512222427501697946798483 8268333641252546920197725)
            ·
              refine ⟨3100625115469705095074147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8268333641252546920197725 3100625115469705095074147)
              ·
                refine ⟨4650937673204557642611221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100625115469705095074147 4650937673204557642611221)
                ·
                  refine ⟨218012703431463639497401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4650937673204557642611221 218012703431463639497401)
                  ·
                    rfl

theorem cell23_3821204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_3821204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821204 prefixEnd_3821204 := by exact prefixLift 3821204
  have htrace : WordTrace (prefixWord ++ tailWord_3821204) baseStart_3821204 baseEnd_3821204 := by
    simpa [prefixWord, tailWord_3821204, baseEnd_3821204] using wordTrace_append hprefix tailTrace_3821204
  have hstable : (prefixWord ++ tailWord_3821204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821204).length < 2 ^ (prefixWord ++ tailWord_3821204).sum := by decide
  have hdescent : baseEnd_3821204 < baseStart_3821204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821214 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3821214 : Nat := 118140960795 + 3821214 * 2 ^ 59
def prefixEnd_3821214 : Nat := 4983230072969 + 3 ^ 40 * 3821214 * 2
def baseEnd_3821214 : Nat := 1962119465689717716351563

theorem tailTrace_3821214 : CollatzResearch.WordTrace tailWord_3821214 prefixEnd_3821214 1962119465689717716351563 := by
  unfold tailWord_3821214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17421390547300220529907837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92914082918934509492841797 17421390547300220529907837)
  ·
    refine ⟨6533021455237582698715439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17421390547300220529907837 6533021455237582698715439)
    ·
      refine ⟨9799532182856374048073159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533021455237582698715439 9799532182856374048073159)
      ·
        refine ⟨14699298274284561072109739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9799532182856374048073159 14699298274284561072109739)
        ·
          refine ⟨22048947411426841608164609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14699298274284561072109739 22048947411426841608164609)
          ·
            refine ⟨16536710558570131206123457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22048947411426841608164609 16536710558570131206123457)
            ·
              refine ⟨12402532918927598404592593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16536710558570131206123457 12402532918927598404592593)
              ·
                refine ⟨9301899689195698803444445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12402532918927598404592593 9301899689195698803444445)
                ·
                  refine ⟨3488212383448387051291667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9301899689195698803444445 3488212383448387051291667)
                  ·
                    refine ⟨5232318575172580576937501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488212383448387051291667 5232318575172580576937501)
                    ·
                      refine ⟨1962119465689717716351563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232318575172580576937501 1962119465689717716351563)
                      ·
                        rfl

theorem cell23_3821214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3821214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821214 prefixEnd_3821214 := by exact prefixLift 3821214
  have htrace : WordTrace (prefixWord ++ tailWord_3821214) baseStart_3821214 baseEnd_3821214 := by
    simpa [prefixWord, tailWord_3821214, baseEnd_3821214] using wordTrace_append hprefix tailTrace_3821214
  have hstable : (prefixWord ++ tailWord_3821214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821214).length < 2 ^ (prefixWord ++ tailWord_3821214).sum := by decide
  have hdescent : baseEnd_3821214 < baseStart_3821214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821217 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 1, 5]
def baseStart_3821217 : Nat := 118140960795 + 3821217 * 2 ^ 59
def prefixEnd_3821217 : Nat := 4983230072969 + 3 ^ 40 * 3821217 * 2
def baseEnd_3821217 : Nat := 654040335377227068204683

theorem tailTrace_3821217 : CollatzResearch.WordTrace tailWord_3821217 prefixEnd_3821217 654040335377227068204683 := by
  unfold tailWord_3821217
  simp only [CollatzResearch.WordTrace]
  refine ⟨139371233797390895751621905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92914155864927263834414603 139371233797390895751621905)
  ·
    refine ⟨104528425348043171813716429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139371233797390895751621905 104528425348043171813716429)
    ·
      refine ⟨39198159505516189430143661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104528425348043171813716429 39198159505516189430143661)
      ·
        refine ⟨14699309814568571036303873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39198159505516189430143661 14699309814568571036303873)
        ·
          refine ⟨11024482360926428277227905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14699309814568571036303873 11024482360926428277227905)
          ·
            refine ⟨8268361770694821207920929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11024482360926428277227905 8268361770694821207920929)
            ·
              refine ⟨6201271328021115905940697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268361770694821207920929 6201271328021115905940697)
              ·
                refine ⟨4650953496015836929455523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201271328021115905940697 4650953496015836929455523)
                ·
                  refine ⟨6976430244023755394183285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650953496015836929455523 6976430244023755394183285)
                  ·
                    refine ⟨654040335377227068204683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6976430244023755394183285 654040335377227068204683)
                    ·
                      rfl

theorem cell23_3821217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_3821217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821217 prefixEnd_3821217 := by exact prefixLift 3821217
  have htrace : WordTrace (prefixWord ++ tailWord_3821217) baseStart_3821217 baseEnd_3821217 := by
    simpa [prefixWord, tailWord_3821217, baseEnd_3821217] using wordTrace_append hprefix tailTrace_3821217
  have hstable : (prefixWord ++ tailWord_3821217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821217).length < 2 ^ (prefixWord ++ tailWord_3821217).sum := by decide
  have hdescent : baseEnd_3821217 < baseStart_3821217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821274 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_3821274 : Nat := 118140960795 + 3821274 * 2 ^ 59
def prefixEnd_3821274 : Nat := 4983230072969 + 3 ^ 40 * 3821274 * 2
def baseEnd_3821274 : Nat := 1962150274528987481601287

theorem tailTrace_3821274 : CollatzResearch.WordTrace tailWord_3821274 prefixEnd_3821274 1962150274528987481601287 := by
  unfold tailWord_3821274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34843328189546098621611719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92915541838789596324297917 34843328189546098621611719)
  ·
    refine ⟨52264992284319147932417579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34843328189546098621611719 52264992284319147932417579)
    ·
      refine ⟨78397488426478721898626369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52264992284319147932417579 78397488426478721898626369)
      ·
        refine ⟨58798116319859041423969777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78397488426478721898626369 58798116319859041423969777)
        ·
          refine ⟨44098587239894281067977333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58798116319859041423969777 44098587239894281067977333)
          ·
            refine ⟨4134242553740088850122875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44098587239894281067977333 4134242553740088850122875)
            ·
              refine ⟨6201363830610133275184313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134242553740088850122875 6201363830610133275184313)
              ·
                refine ⟨4651022872957599956388235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201363830610133275184313 4651022872957599956388235)
                ·
                  refine ⟨6976534309436399934582353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651022872957599956388235 6976534309436399934582353)
                  ·
                    refine ⟨5232400732077299950936765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6976534309436399934582353 5232400732077299950936765)
                    ·
                      refine ⟨1962150274528987481601287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232400732077299950936765 1962150274528987481601287)
                      ·
                        rfl

theorem cell23_3821274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_3821274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821274 prefixEnd_3821274 := by exact prefixLift 3821274
  have htrace : WordTrace (prefixWord ++ tailWord_3821274) baseStart_3821274 baseEnd_3821274 := by
    simpa [prefixWord, tailWord_3821274, baseEnd_3821274] using wordTrace_append hprefix tailTrace_3821274
  have hstable : (prefixWord ++ tailWord_3821274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821274).length < 2 ^ (prefixWord ++ tailWord_3821274).sum := by decide
  have hdescent : baseEnd_3821274 < baseStart_3821274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821314 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_3821314 : Nat := 118140960795 + 3821314 * 2 ^ 59
def prefixEnd_3821314 : Nat := 4983230072969 + 3 ^ 40 * 3821314 * 2
def baseEnd_3821314 : Nat := 1962170813755167325101103

theorem tailTrace_3821314 : CollatzResearch.WordTrace tailWord_3821314 prefixEnd_3821314 1962170813755167325101103 := by
  unfold tailWord_3821314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34843692919509870329475749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92916514452026320878601997 34843692919509870329475749)
  ·
    refine ⟨6533192422408100686776703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34843692919509870329475749 6533192422408100686776703)
    ·
      refine ⟨9799788633612151030165055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533192422408100686776703 9799788633612151030165055)
      ·
        refine ⟨14699682950418226545247583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9799788633612151030165055 14699682950418226545247583)
        ·
          refine ⟨22049524425627339817871375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14699682950418226545247583 22049524425627339817871375)
          ·
            refine ⟨33074286638441009726807063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22049524425627339817871375 33074286638441009726807063)
            ·
              refine ⟨49611429957661514590210595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33074286638441009726807063 49611429957661514590210595)
              ·
                refine ⟨74417144936492271885315893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49611429957661514590210595 74417144936492271885315893)
                ·
                  refine ⟨6976607337796150489248365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74417144936492271885315893 6976607337796150489248365)
                  ·
                    refine ⟨2616227751673556433468137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6976607337796150489248365 2616227751673556433468137)
                    ·
                      refine ⟨1962170813755167325101103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616227751673556433468137 1962170813755167325101103)
                      ·
                        rfl

theorem cell23_3821314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_3821314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821314 prefixEnd_3821314 := by exact prefixLift 3821314
  have htrace : WordTrace (prefixWord ++ tailWord_3821314) baseStart_3821314 baseEnd_3821314 := by
    simpa [prefixWord, tailWord_3821314, baseEnd_3821314] using wordTrace_append hprefix tailTrace_3821314
  have hstable : (prefixWord ++ tailWord_3821314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821314).length < 2 ^ (prefixWord ++ tailWord_3821314).sum := by decide
  have hdescent : baseEnd_3821314 < baseStart_3821314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821320 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 2, 6]
def baseStart_3821320 : Nat := 118140960795 + 3821320 * 2 ^ 59
def prefixEnd_3821320 : Nat := 4983230072969 + 3 ^ 40 * 3821320 * 2
def baseEnd_3821320 : Nat := 654057964879698100542025

theorem tailTrace_3821320 : CollatzResearch.WordTrace tailWord_3821320 prefixEnd_3821320 654057964879698100542025 := by
  unfold tailWord_3821320
  simp only [CollatzResearch.WordTrace]
  refine ⟨69687495258008872171310707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92916660344011829561747609 69687495258008872171310707)
  ·
    refine ⟨104531242887013308256966061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69687495258008872171310707 104531242887013308256966061)
    ·
      refine ⟨39199216082629990596362273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104531242887013308256966061 39199216082629990596362273)
      ·
        refine ⟨29399412061972492947271705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39199216082629990596362273 29399412061972492947271705)
        ·
          refine ⟨22049559046479369710453779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29399412061972492947271705 22049559046479369710453779)
          ·
            refine ⟨33074338569719054565680669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22049559046479369710453779 33074338569719054565680669)
            ·
              refine ⟨12402876963644645462130251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33074338569719054565680669 12402876963644645462130251)
              ·
                refine ⟨18604315445466968193195377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12402876963644645462130251 18604315445466968193195377)
                ·
                  refine ⟨13953236584100226144896533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18604315445466968193195377 13953236584100226144896533)
                  ·
                    refine ⟨654057964879698100542025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13953236584100226144896533 654057964879698100542025)
                    ·
                      rfl

theorem cell23_3821320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_3821320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821320 prefixEnd_3821320 := by exact prefixLift 3821320
  have htrace : WordTrace (prefixWord ++ tailWord_3821320) baseStart_3821320 baseEnd_3821320 := by
    simpa [prefixWord, tailWord_3821320, baseEnd_3821320] using wordTrace_append hprefix tailTrace_3821320
  have hstable : (prefixWord ++ tailWord_3821320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821320).length < 2 ^ (prefixWord ++ tailWord_3821320).sum := by decide
  have hdescent : baseEnd_3821320 < baseStart_3821320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821340 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3821340 : Nat := 118140960795 + 3821340 * 2 ^ 59
def prefixEnd_3821340 : Nat := 4983230072969 + 3 ^ 40 * 3821340 * 2
def baseEnd_3821340 : Nat := 1962184164252184223375983

theorem tailTrace_3821340 : CollatzResearch.WordTrace tailWord_3821340 prefixEnd_3821340 1962184164252184223375983 := by
  unfold tailWord_3821340
  simp only [CollatzResearch.WordTrace]
  refine ⟨69687859987972643879174737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92917146650630191838899649 69687859987972643879174737)
  ·
    refine ⟨52265894990979482909381053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69687859987972643879174737 52265894990979482909381053)
    ·
      refine ⟨19599710621617306091017895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52265894990979482909381053 19599710621617306091017895)
      ·
        refine ⟨29399565932425959136526843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19599710621617306091017895 29399565932425959136526843)
        ·
          refine ⟨44099348898638938704790265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29399565932425959136526843 44099348898638938704790265)
          ·
            refine ⟨33074511673979204028592699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44099348898638938704790265 33074511673979204028592699)
            ·
              refine ⟨49611767510968806042889049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33074511673979204028592699 49611767510968806042889049)
              ·
                refine ⟨37208825633226604532166787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49611767510968806042889049 37208825633226604532166787)
                ·
                  refine ⟨55813238449839906798250181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37208825633226604532166787 55813238449839906798250181)
                  ·
                    refine ⟨10464982209344982524671909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55813238449839906798250181 10464982209344982524671909)
                    ·
                      refine ⟨1962184164252184223375983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10464982209344982524671909 1962184164252184223375983)
                      ·
                        rfl

theorem cell23_3821340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3821340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821340 prefixEnd_3821340 := by exact prefixLift 3821340
  have htrace : WordTrace (prefixWord ++ tailWord_3821340) baseStart_3821340 baseEnd_3821340 := by
    simpa [prefixWord, tailWord_3821340, baseEnd_3821340] using wordTrace_append hprefix tailTrace_3821340
  have hstable : (prefixWord ++ tailWord_3821340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821340).length < 2 ^ (prefixWord ++ tailWord_3821340).sum := by decide
  have hdescent : baseEnd_3821340 < baseStart_3821340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821342 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3821342 : Nat := 118140960795 + 3821342 * 2 ^ 59
def prefixEnd_3821342 : Nat := 4983230072969 + 3 ^ 40 * 3821342 * 2
def baseEnd_3821342 : Nat := 1962185191213493215550975

theorem tailTrace_3821342 : CollatzResearch.WordTrace tailWord_3821342 prefixEnd_3821342 1962185191213493215550975 := by
  unfold tailWord_3821342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17421974115242255262490285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92917195281292028066614853 17421974115242255262490285)
  ·
    refine ⟨6533240293215845723433857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17421974115242255262490285 6533240293215845723433857)
    ·
      refine ⟨4899930219911884292575393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6533240293215845723433857 4899930219911884292575393)
      ·
        refine ⟨3674947664933913219431545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4899930219911884292575393 3674947664933913219431545)
        ·
          refine ⟨2756210748700434914573659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3674947664933913219431545 2756210748700434914573659)
          ·
            refine ⟨4134316123050652371860489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756210748700434914573659 4134316123050652371860489)
            ·
              refine ⟨3100737092287989278895367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4134316123050652371860489 3100737092287989278895367)
              ·
                refine ⟨4651105638431983918343051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100737092287989278895367 4651105638431983918343051)
                ·
                  refine ⟨6976658457647975877514577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651105638431983918343051 6976658457647975877514577)
                  ·
                    refine ⟨5232493843235981908135933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6976658457647975877514577 5232493843235981908135933)
                    ·
                      refine ⟨1962185191213493215550975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232493843235981908135933 1962185191213493215550975)
                      ·
                        rfl

theorem cell23_3821342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3821342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821342 prefixEnd_3821342 := by exact prefixLift 3821342
  have htrace : WordTrace (prefixWord ++ tailWord_3821342) baseStart_3821342 baseEnd_3821342 := by
    simpa [prefixWord, tailWord_3821342, baseEnd_3821342] using wordTrace_append hprefix tailTrace_3821342
  have hstable : (prefixWord ++ tailWord_3821342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821342).length < 2 ^ (prefixWord ++ tailWord_3821342).sum := by decide
  have hdescent : baseEnd_3821342 < baseStart_3821342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821344 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 4, 2, 2]
def baseStart_3821344 : Nat := 118140960795 + 3821344 * 2 ^ 59
def prefixEnd_3821344 : Nat := 4983230072969 + 3 ^ 40 * 3821344 * 2
def baseEnd_3821344 : Nat := 1962186218174802207725965

theorem tailTrace_3821344 : CollatzResearch.WordTrace tailWord_3821344 prefixEnd_3821344 1962186218174802207725965 := by
  unfold tailWord_3821344
  simp only [CollatzResearch.WordTrace]
  refine ⟨69687932933965398220747543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92917243911953864294330057 69687932933965398220747543)
  ·
    refine ⟨104531899400948097331121315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69687932933965398220747543 104531899400948097331121315)
    ·
      refine ⟨156797849101422145996681973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104531899400948097331121315 156797849101422145996681973)
      ·
        refine ⟨14699798353258326187188935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156797849101422145996681973 14699798353258326187188935)
        ·
          refine ⟨22049697529887489280783403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14699798353258326187188935 22049697529887489280783403)
          ·
            refine ⟨33074546294831233921175105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22049697529887489280783403 33074546294831233921175105)
            ·
              refine ⟨24805909721123425440881329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33074546294831233921175105 24805909721123425440881329)
              ·
                refine ⟨18604432290842569080660997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24805909721123425440881329 18604432290842569080660997)
                ·
                  refine ⟨3488331054532981702623937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18604432290842569080660997 3488331054532981702623937)
                  ·
                    refine ⟨2616248290899736276967953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3488331054532981702623937 2616248290899736276967953)
                    ·
                      refine ⟨1962186218174802207725965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616248290899736276967953 1962186218174802207725965)
                      ·
                        rfl

theorem cell23_3821344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_3821344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821344 prefixEnd_3821344 := by exact prefixLift 3821344
  have htrace : WordTrace (prefixWord ++ tailWord_3821344) baseStart_3821344 baseEnd_3821344 := by
    simpa [prefixWord, tailWord_3821344, baseEnd_3821344] using wordTrace_append hprefix tailTrace_3821344
  have hstable : (prefixWord ++ tailWord_3821344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821344).length < 2 ^ (prefixWord ++ tailWord_3821344).sum := by decide
  have hdescent : baseEnd_3821344 < baseStart_3821344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821348 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_3821348 : Nat := 118140960795 + 3821348 * 2 ^ 59
def prefixEnd_3821348 : Nat := 4983230072969 + 3 ^ 40 * 3821348 * 2
def baseEnd_3821348 : Nat := 1962188272097420192075947

theorem tailTrace_3821348 : CollatzResearch.WordTrace tailWord_3821348 prefixEnd_3821348 1962188272097420192075947 := by
  unfold tailWord_3821348
  simp only [CollatzResearch.WordTrace]
  refine ⟨69688005879958152562320349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92917341173277536749760465 69688005879958152562320349)
  ·
    refine ⟨26133002204984307210870131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69688005879958152562320349 26133002204984307210870131)
    ·
      refine ⟨39199503307476460816305197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26133002204984307210870131 39199503307476460816305197)
      ·
        refine ⟨14699813740303672806114449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39199503307476460816305197 14699813740303672806114449)
        ·
          refine ⟨11024860305227754604585837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14699813740303672806114449 11024860305227754604585837)
          ·
            refine ⟨4134322614460407976719689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11024860305227754604585837 4134322614460407976719689)
            ·
              refine ⟨3100741960845305982539767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4134322614460407976719689 3100741960845305982539767)
              ·
                refine ⟨4651112941267958973809651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100741960845305982539767 4651112941267958973809651)
                ·
                  refine ⟨6976669411901938460714477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651112941267958973809651 6976669411901938460714477)
                  ·
                    refine ⟨2616251029463226922767929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6976669411901938460714477 2616251029463226922767929)
                    ·
                      refine ⟨1962188272097420192075947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616251029463226922767929 1962188272097420192075947)
                      ·
                        rfl

theorem cell23_3821348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_3821348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821348 prefixEnd_3821348 := by exact prefixLift 3821348
  have htrace : WordTrace (prefixWord ++ tailWord_3821348) baseStart_3821348 baseEnd_3821348 := by
    simpa [prefixWord, tailWord_3821348, baseEnd_3821348] using wordTrace_append hprefix tailTrace_3821348
  have hstable : (prefixWord ++ tailWord_3821348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821348).length < 2 ^ (prefixWord ++ tailWord_3821348).sum := by decide
  have hdescent : baseEnd_3821348 < baseStart_3821348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821361 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 2, 2, 2]
def baseStart_3821361 : Nat := 118140960795 + 3821361 * 2 ^ 59
def prefixEnd_3821361 : Nat := 4983230072969 + 3 ^ 40 * 3821361 * 2
def baseEnd_3821361 : Nat := 1962194947345928641213387

theorem tailTrace_3821361 : CollatzResearch.WordTrace tailWord_3821361 prefixEnd_3821361 1962194947345928641213387 := by
  unfold tailWord_3821361
  simp only [CollatzResearch.WordTrace]
  refine ⟨139376485908869208344863937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92917657272579472229909291 139376485908869208344863937)
  ·
    refine ⟨104532364431651906258647953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139376485908869208344863937 104532364431651906258647953)
    ·
      refine ⟨78399273323738929693985965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104532364431651906258647953 78399273323738929693985965)
      ·
        refine ⟨29399727496402098635244737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78399273323738929693985965 29399727496402098635244737)
        ·
          refine ⟨22049795622301573976433553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29399727496402098635244737 22049795622301573976433553)
          ·
            refine ⟨16537346716726180482325165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22049795622301573976433553 16537346716726180482325165)
            ·
              refine ⟨6201505018772317680871937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16537346716726180482325165 6201505018772317680871937)
              ·
                refine ⟨4651128764079238260653953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201505018772317680871937 4651128764079238260653953)
                ·
                  refine ⟨3488346573059428695490465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4651128764079238260653953 3488346573059428695490465)
                  ·
                    refine ⟨2616259929794571521617849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3488346573059428695490465 2616259929794571521617849)
                    ·
                      refine ⟨1962194947345928641213387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616259929794571521617849 1962194947345928641213387)
                      ·
                        rfl

theorem cell23_3821361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_3821361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821361 prefixEnd_3821361 := by exact prefixLift 3821361
  have htrace : WordTrace (prefixWord ++ tailWord_3821361) baseStart_3821361 baseEnd_3821361 := by
    simpa [prefixWord, tailWord_3821361, baseEnd_3821361] using wordTrace_append hprefix tailTrace_3821361
  have hstable : (prefixWord ++ tailWord_3821361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821361).length < 2 ^ (prefixWord ++ tailWord_3821361).sum := by decide
  have hdescent : baseEnd_3821361 < baseStart_3821361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821390 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3821390 : Nat := 118140960795 + 3821390 * 2 ^ 59
def prefixEnd_3821390 : Nat := 4983230072969 + 3 ^ 40 * 3821390 * 2
def baseEnd_3821390 : Nat := 1962209838284909027750753

theorem tailTrace_3821390 : CollatzResearch.WordTrace tailWord_3821390 prefixEnd_3821390 1962209838284909027750753 := by
  unfold tailWord_3821390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17422192953220518287208703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92918362417176097531779749 17422192953220518287208703)
  ·
    refine ⟨26133289429830777430813055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17422192953220518287208703 26133289429830777430813055)
    ·
      refine ⟨39199934144746166146219583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26133289429830777430813055 39199934144746166146219583)
      ·
        refine ⟨58799901217119249219329375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39199934144746166146219583 58799901217119249219329375)
        ·
          refine ⟨88199851825678873828994063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58799901217119249219329375 88199851825678873828994063)
          ·
            refine ⟨132299777738518310743491095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88199851825678873828994063 132299777738518310743491095)
            ·
              refine ⟨198449666607777466115236643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132299777738518310743491095 198449666607777466115236643)
              ·
                refine ⟨297674499911666199172854965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198449666607777466115236643 297674499911666199172854965)
                ·
                  refine ⟨27906984366718706172455153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 297674499911666199172854965 27906984366718706172455153)
                  ·
                    refine ⟨20930238275039029629341365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27906984366718706172455153 20930238275039029629341365)
                    ·
                      refine ⟨1962209838284909027750753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20930238275039029629341365 1962209838284909027750753)
                      ·
                        rfl

theorem cell23_3821390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3821390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821390 prefixEnd_3821390 := by exact prefixLift 3821390
  have htrace : WordTrace (prefixWord ++ tailWord_3821390) baseStart_3821390 baseEnd_3821390 := by
    simpa [prefixWord, tailWord_3821390, baseEnd_3821390] using wordTrace_append hprefix tailTrace_3821390
  have hstable : (prefixWord ++ tailWord_3821390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821390).length < 2 ^ (prefixWord ++ tailWord_3821390).sum := by decide
  have hdescent : baseEnd_3821390 < baseStart_3821390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821417 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 4, 4, 2]
def baseStart_3821417 : Nat := 118140960795 + 3821417 * 2 ^ 59
def prefixEnd_3821417 : Nat := 4983230072969 + 3 ^ 40 * 3821417 * 2
def baseEnd_3821417 : Nat := 1962223702262580422113129

theorem tailTrace_3821417 : CollatzResearch.WordTrace tailWord_3821417 prefixEnd_3821417 1962223702262580422113129 := by
  unfold tailWord_3821417
  simp only [CollatzResearch.WordTrace]
  refine ⟨139378528396666329908902505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92919018931110886605935003 139378528396666329908902505)
  ·
    refine ⟨104533896297499747431676879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139378528396666329908902505 104533896297499747431676879)
    ·
      refine ⟨156800844446249621147515319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104533896297499747431676879 156800844446249621147515319)
      ·
        refine ⟨235201266669374431721272979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156800844446249621147515319 235201266669374431721272979)
        ·
          refine ⟨352801900004061647581909469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235201266669374431721272979 352801900004061647581909469)
          ·
            refine ⟨132300712501523117843216051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352801900004061647581909469 132300712501523117843216051)
            ·
              refine ⟨198451068752284676764824077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132300712501523117843216051 198451068752284676764824077)
              ·
                refine ⟨74419150782106753786809029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198451068752284676764824077 74419150782106753786809029)
                ·
                  refine ⟨13953590771645016335026693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74419150782106753786809029 13953590771645016335026693)
                  ·
                    refine ⟨2616298269683440562817505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13953590771645016335026693 2616298269683440562817505)
                    ·
                      refine ⟨1962223702262580422113129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616298269683440562817505 1962223702262580422113129)
                      ·
                        rfl

theorem cell23_3821417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 4, 2].length) (baseStart_3821417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821417 prefixEnd_3821417 := by exact prefixLift 3821417
  have htrace : WordTrace (prefixWord ++ tailWord_3821417) baseStart_3821417 baseEnd_3821417 := by
    simpa [prefixWord, tailWord_3821417, baseEnd_3821417] using wordTrace_append hprefix tailTrace_3821417
  have hstable : (prefixWord ++ tailWord_3821417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821417).length < 2 ^ (prefixWord ++ tailWord_3821417).sum := by decide
  have hdescent : baseEnd_3821417 < baseStart_3821417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821418 : List Nat := [3, 1, 3, 4, 1, 1, 3, 2, 5]
def baseStart_3821418 : Nat := 118140960795 + 3821418 * 2 ^ 59
def prefixEnd_3821418 : Nat := 4983230072969 + 3 ^ 40 * 3821418 * 2
def baseEnd_3821418 : Nat := 218024912860359435355625

theorem tailTrace_3821418 : CollatzResearch.WordTrace tailWord_3821418 prefixEnd_3821418 218024912860359435355625 := by
  unfold tailWord_3821418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34844641217415676769922227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92919043246441804719792605 34844641217415676769922227)
  ·
    refine ⟨52266961826123515154883341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34844641217415676769922227 52266961826123515154883341)
    ·
      refine ⟨19600110684796318183081253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52266961826123515154883341 19600110684796318183081253)
      ·
        refine ⟨3675020753399309659327735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19600110684796318183081253 3675020753399309659327735)
        ·
          refine ⟨5512531130098964488991603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675020753399309659327735 5512531130098964488991603)
          ·
            refine ⟨8268796695148446733487405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512531130098964488991603 8268796695148446733487405)
            ·
              refine ⟨3100798760680667525057777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8268796695148446733487405 3100798760680667525057777)
              ·
                refine ⟨2325599070510500643793333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100798760680667525057777 2325599070510500643793333)
                ·
                  refine ⟨218024912860359435355625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2325599070510500643793333 218024912860359435355625)
                  ·
                    rfl

theorem cell23_3821418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_3821418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821418 prefixEnd_3821418 := by exact prefixLift 3821418
  have htrace : WordTrace (prefixWord ++ tailWord_3821418) baseStart_3821418 baseEnd_3821418 := by
    simpa [prefixWord, tailWord_3821418, baseEnd_3821418] using wordTrace_append hprefix tailTrace_3821418
  have hstable : (prefixWord ++ tailWord_3821418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821418).length < 2 ^ (prefixWord ++ tailWord_3821418).sum := by decide
  have hdescent : baseEnd_3821418 < baseStart_3821418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821437 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_3821437 : Nat := 118140960795 + 3821437 * 2 ^ 59
def prefixEnd_3821437 : Nat := 4983230072969 + 3 ^ 40 * 3821437 * 2
def baseEnd_3821437 : Nat := 1962233971875670343863037

theorem tailTrace_3821437 : CollatzResearch.WordTrace tailWord_3821437 prefixEnd_3821437 1962233971875670343863037 := by
  unfold tailWord_3821437
  simp only [CollatzResearch.WordTrace]
  refine ⟨139379257856593873324630565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92919505237729248883087043 139379257856593873324630565)
  ·
    refine ⟨26133610848111351248368231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139379257856593873324630565 26133610848111351248368231)
    ·
      refine ⟨39200416272167026872552347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26133610848111351248368231 39200416272167026872552347)
      ·
        refine ⟨58800624408250540308828521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39200416272167026872552347 58800624408250540308828521)
        ·
          refine ⟨44100468306187905231621391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58800624408250540308828521 44100468306187905231621391)
          ·
            refine ⟨66150702459281857847432087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44100468306187905231621391 66150702459281857847432087)
            ·
              refine ⟨99226053688922786771148131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66150702459281857847432087 99226053688922786771148131)
              ·
                refine ⟨148839080533384180156722197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99226053688922786771148131 148839080533384180156722197)
                ·
                  refine ⟨6976831900002383444846353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148839080533384180156722197 6976831900002383444846353)
                  ·
                    refine ⟨5232623925001787583634765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6976831900002383444846353 5232623925001787583634765)
                    ·
                      refine ⟨1962233971875670343863037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232623925001787583634765 1962233971875670343863037)
                      ·
                        rfl

theorem cell23_3821437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_3821437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821437 prefixEnd_3821437 := by exact prefixLift 3821437
  have htrace : WordTrace (prefixWord ++ tailWord_3821437) baseStart_3821437 baseEnd_3821437 := by
    simpa [prefixWord, tailWord_3821437, baseEnd_3821437] using wordTrace_append hprefix tailTrace_3821437
  have hstable : (prefixWord ++ tailWord_3821437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821437).length < 2 ^ (prefixWord ++ tailWord_3821437).sum := by decide
  have hdescent : baseEnd_3821437 < baseStart_3821437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821501 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3821501 : Nat := 118140960795 + 3821501 * 2 ^ 59
def prefixEnd_3821501 : Nat := 4983230072969 + 3 ^ 40 * 3821501 * 2
def baseEnd_3821501 : Nat := 1962266834637558093462743

theorem tailTrace_3821501 : CollatzResearch.WordTrace tailWord_3821501 prefixEnd_3821501 1962266834637558093462743 := by
  unfold tailWord_3821501
  simp only [CollatzResearch.WordTrace]
  refine ⟨139381592128362012254960357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92921061418908008169973571 139381592128362012254960357)
  ·
    refine ⟨26134048524067877297805067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139381592128362012254960357 26134048524067877297805067)
    ·
      refine ⟨39201072786101815946707601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26134048524067877297805067 39201072786101815946707601)
      ·
        refine ⟨29400804589576361960030701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39201072786101815946707601 29400804589576361960030701)
        ·
          refine ⟨11025301721091135735011513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29400804589576361960030701 11025301721091135735011513)
          ·
            refine ⟨8268976290818351801258635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11025301721091135735011513 8268976290818351801258635)
            ·
              refine ⟨12403464436227527701887953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268976290818351801258635 12403464436227527701887953)
              ·
                refine ⟨9302598327170645776415965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12403464436227527701887953 9302598327170645776415965)
                ·
                  refine ⟨3488474372688992166155987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9302598327170645776415965 3488474372688992166155987)
                  ·
                    refine ⟨5232711559033488249233981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488474372688992166155987 5232711559033488249233981)
                    ·
                      refine ⟨1962266834637558093462743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232711559033488249233981 1962266834637558093462743)
                      ·
                        rfl

theorem cell23_3821501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3821501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821501 prefixEnd_3821501 := by exact prefixLift 3821501
  have htrace : WordTrace (prefixWord ++ tailWord_3821501) baseStart_3821501 baseEnd_3821501 := by
    simpa [prefixWord, tailWord_3821501, baseEnd_3821501] using wordTrace_append hprefix tailTrace_3821501
  have hstable : (prefixWord ++ tailWord_3821501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821501).length < 2 ^ (prefixWord ++ tailWord_3821501).sum := by decide
  have hdescent : baseEnd_3821501 < baseStart_3821501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821518 : List Nat := [4, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_3821518 : Nat := 118140960795 + 3821518 * 2 ^ 59
def prefixEnd_3821518 : Nat := 4983230072969 + 3 ^ 40 * 3821518 * 2
def baseEnd_3821518 : Nat := 1962275563808684526950165

theorem tailTrace_3821518 : CollatzResearch.WordTrace tailWord_3821518 prefixEnd_3821518 1962275563808684526950165 := by
  unfold tailWord_3821518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17422776521162553019791151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92921474779533616105552805 17422776521162553019791151)
  ·
    refine ⟨26134164781743829529686727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17422776521162553019791151 26134164781743829529686727)
    ·
      refine ⟨39201247172615744294530091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26134164781743829529686727 39201247172615744294530091)
      ·
        refine ⟨58801870758923616441795137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39201247172615744294530091 58801870758923616441795137)
        ·
          refine ⟨44101403069192712331346353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58801870758923616441795137 44101403069192712331346353)
          ·
            refine ⟨33076052301894534248509765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44101403069192712331346353 33076052301894534248509765)
            ·
              refine ⟨6201759806605225171595581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33076052301894534248509765 6201759806605225171595581)
              ·
                refine ⟨2325659927476959439348343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6201759806605225171595581 2325659927476959439348343)
                ·
                  refine ⟨3488489891215439159022515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325659927476959439348343 3488489891215439159022515)
                  ·
                    refine ⟨5232734836823158738533773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488489891215439159022515 5232734836823158738533773)
                    ·
                      refine ⟨1962275563808684526950165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232734836823158738533773 1962275563808684526950165)
                      ·
                        rfl

theorem cell23_3821518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_3821518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821518 prefixEnd_3821518 := by exact prefixLift 3821518
  have htrace : WordTrace (prefixWord ++ tailWord_3821518) baseStart_3821518 baseEnd_3821518 := by
    simpa [prefixWord, tailWord_3821518, baseEnd_3821518] using wordTrace_append hprefix tailTrace_3821518
  have hstable : (prefixWord ++ tailWord_3821518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821518).length < 2 ^ (prefixWord ++ tailWord_3821518).sum := by decide
  have hdescent : baseEnd_3821518 < baseStart_3821518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821527 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_3821527 : Nat := 118140960795 + 3821527 * 2 ^ 59
def prefixEnd_3821527 : Nat := 4983230072969 + 3 ^ 40 * 3821527 * 2
def baseEnd_3821527 : Nat := 1962280185134574991737623

theorem tailTrace_3821527 : CollatzResearch.WordTrace tailWord_3821527 prefixEnd_3821527 1962280185134574991737623 := by
  unfold tailWord_3821527
  simp only [CollatzResearch.WordTrace]
  refine ⟨139382540426267818695406835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92921693617511879130271223 139382540426267818695406835)
  ·
    refine ⟨209073810639401728043110253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139382540426267818695406835 209073810639401728043110253)
    ·
      refine ⟨78402678989775648016166345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209073810639401728043110253 78402678989775648016166345)
      ·
        refine ⟨58802009242331736012124759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78402678989775648016166345 58802009242331736012124759)
        ·
          refine ⟨88203013863497604018187139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58802009242331736012124759 88203013863497604018187139)
          ·
            refine ⟨132304520795246406027280709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88203013863497604018187139 132304520795246406027280709)
            ·
              refine ⟨24807097649108701130115133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132304520795246406027280709 24807097649108701130115133)
              ·
                refine ⟨9302661618415762923793175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24807097649108701130115133 9302661618415762923793175)
                ·
                  refine ⟨13953992427623644385689763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9302661618415762923793175 13953992427623644385689763)
                  ·
                    refine ⟨20930988641435466578534645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13953992427623644385689763 20930988641435466578534645)
                    ·
                      refine ⟨1962280185134574991737623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20930988641435466578534645 1962280185134574991737623)
                      ·
                        rfl

theorem cell23_3821527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_3821527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821527 prefixEnd_3821527 := by exact prefixLift 3821527
  have htrace : WordTrace (prefixWord ++ tailWord_3821527) baseStart_3821527 baseEnd_3821527 := by
    simpa [prefixWord, tailWord_3821527, baseEnd_3821527] using wordTrace_append hprefix tailTrace_3821527
  have hstable : (prefixWord ++ tailWord_3821527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821527).length < 2 ^ (prefixWord ++ tailWord_3821527).sum := by decide
  have hdescent : baseEnd_3821527 < baseStart_3821527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821537 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3821537 : Nat := 118140960795 + 3821537 * 2 ^ 59
def prefixEnd_3821537 : Nat := 4983230072969 + 3 ^ 40 * 3821537 * 2
def baseEnd_3821537 : Nat := 1962285319941119952612577

theorem tailTrace_3821537 : CollatzResearch.WordTrace tailWord_3821537 prefixEnd_3821537 1962285319941119952612577 := by
  unfold tailWord_3821537
  simp only [CollatzResearch.WordTrace]
  refine ⟨139382905156231590403270865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92921936770821060268847243 139382905156231590403270865)
  ·
    refine ⟨104537178867173692802453149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139382905156231590403270865 104537178867173692802453149)
    ·
      refine ⟨39201442075190134800919931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104537178867173692802453149 39201442075190134800919931)
      ·
        refine ⟨58802163112785202201379897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39201442075190134800919931 58802163112785202201379897)
        ·
          refine ⟨44101622334588901651034923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58802163112785202201379897 44101622334588901651034923)
          ·
            refine ⟨66152433501883352476552385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44101622334588901651034923 66152433501883352476552385)
            ·
              refine ⟨49614325126412514357414289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66152433501883352476552385 49614325126412514357414289)
              ·
                refine ⟨37210743844809385768060717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49614325126412514357414289 37210743844809385768060717)
                ·
                  refine ⟨13954028941803519663022769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37210743844809385768060717 13954028941803519663022769)
                  ·
                    refine ⟨10465521706352639747267077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13954028941803519663022769 10465521706352639747267077)
                    ·
                      refine ⟨1962285319941119952612577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10465521706352639747267077 1962285319941119952612577)
                      ·
                        rfl

theorem cell23_3821537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3821537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821537 prefixEnd_3821537 := by exact prefixLift 3821537
  have htrace : WordTrace (prefixWord ++ tailWord_3821537) baseStart_3821537 baseEnd_3821537 := by
    simpa [prefixWord, tailWord_3821537, baseEnd_3821537] using wordTrace_append hprefix tailTrace_3821537
  have hstable : (prefixWord ++ tailWord_3821537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821537).length < 2 ^ (prefixWord ++ tailWord_3821537).sum := by decide
  have hdescent : baseEnd_3821537 < baseStart_3821537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821551 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 2, 4]
def baseStart_3821551 : Nat := 118140960795 + 3821551 * 2 ^ 59
def prefixEnd_3821551 : Nat := 4983230072969 + 3 ^ 40 * 3821551 * 2
def baseEnd_3821551 : Nat := 654097502890094299279171

theorem tailTrace_3821551 : CollatzResearch.WordTrace tailWord_3821551 prefixEnd_3821551 654097502890094299279171 := by
  unfold tailWord_3821551
  simp only [CollatzResearch.WordTrace]
  refine ⟨139383415778180870794280507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92922277185453913862853671 139383415778180870794280507)
  ·
    refine ⟨209075123667271306191420761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139383415778180870794280507 209075123667271306191420761)
    ·
      refine ⟨156806342750453479643565571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209075123667271306191420761 156806342750453479643565571)
      ·
        refine ⟨235209514125680219465348357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156806342750453479643565571 235209514125680219465348357)
        ·
          refine ⟨44101783898565041149752817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235209514125680219465348357 44101783898565041149752817)
          ·
            refine ⟨33076337923923780862314613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44101783898565041149752817 33076337923923780862314613)
            ·
              refine ⟨3100906680367854455841995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33076337923923780862314613 3100906680367854455841995)
              ·
                refine ⟨4651360020551781683762993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100906680367854455841995 4651360020551781683762993)
                ·
                  refine ⟨3488520015413836262822245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4651360020551781683762993 3488520015413836262822245)
                  ·
                    refine ⟨654097502890094299279171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488520015413836262822245 654097502890094299279171)
                    ·
                      rfl

theorem cell23_3821551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 4].length) (baseStart_3821551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821551 prefixEnd_3821551 := by exact prefixLift 3821551
  have htrace : WordTrace (prefixWord ++ tailWord_3821551) baseStart_3821551 baseEnd_3821551 := by
    simpa [prefixWord, tailWord_3821551, baseEnd_3821551] using wordTrace_append hprefix tailTrace_3821551
  have hstable : (prefixWord ++ tailWord_3821551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821551).length < 2 ^ (prefixWord ++ tailWord_3821551).sum := by decide
  have hdescent : baseEnd_3821551 < baseStart_3821551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821558 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3821558 : Nat := 118140960795 + 3821558 * 2 ^ 59
def prefixEnd_3821558 : Nat := 4983230072969 + 3 ^ 40 * 3821558 * 2
def baseEnd_3821558 : Nat := 1962296103034864370449981

theorem tailTrace_3821558 : CollatzResearch.WordTrace tailWord_3821558 prefixEnd_3821558 1962296103034864370449981 := by
  unfold tailWord_3821558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8711479443072219436861583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92922447392770340659856885 8711479443072219436861583)
  ·
    refine ⟨13067219164608329155292375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8711479443072219436861583 13067219164608329155292375)
    ·
      refine ⟨19600828746912493732938563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13067219164608329155292375 19600828746912493732938563)
      ·
        refine ⟨29401243120368740599407845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19600828746912493732938563 29401243120368740599407845)
        ·
          refine ⟨5512733085069138862388971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29401243120368740599407845 5512733085069138862388971)
          ·
            refine ⟨8269099627603708293583457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512733085069138862388971 8269099627603708293583457)
            ·
              refine ⟨6201824720702781220187593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8269099627603708293583457 6201824720702781220187593)
              ·
                refine ⟨4651368540527085915140695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201824720702781220187593 4651368540527085915140695)
                ·
                  refine ⟨6977052810790628872711043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651368540527085915140695 6977052810790628872711043)
                  ·
                    refine ⟨10465579216185943309066565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6977052810790628872711043 10465579216185943309066565)
                    ·
                      refine ⟨1962296103034864370449981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10465579216185943309066565 1962296103034864370449981)
                      ·
                        rfl

theorem cell23_3821558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3821558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821558 prefixEnd_3821558 := by exact prefixLift 3821558
  have htrace : WordTrace (prefixWord ++ tailWord_3821558) baseStart_3821558 baseEnd_3821558 := by
    simpa [prefixWord, tailWord_3821558, baseEnd_3821558] using wordTrace_append hprefix tailTrace_3821558
  have hstable : (prefixWord ++ tailWord_3821558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821558).length < 2 ^ (prefixWord ++ tailWord_3821558).sum := by decide
  have hdescent : baseEnd_3821558 < baseStart_3821558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821561 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 3]
def baseStart_3821561 : Nat := 118140960795 + 3821561 * 2 ^ 59
def prefixEnd_3821561 : Nat := 4983230072969 + 3 ^ 40 * 3821561 * 2
def baseEnd_3821561 : Nat := 1962297643476827858712467

theorem tailTrace_3821561 : CollatzResearch.WordTrace tailWord_3821561 prefixEnd_3821561 1962297643476827858712467 := by
  unfold tailWord_3821561
  simp only [CollatzResearch.WordTrace]
  refine ⟨139383780508144642502144537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92922520338763095001429691 139383780508144642502144537)
  ·
    refine ⟨104537835381108481876608403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139383780508144642502144537 104537835381108481876608403)
    ·
      refine ⟨156806753071662722814912605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104537835381108481876608403 156806753071662722814912605)
      ·
        refine ⟨58802532401873521055592227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156806753071662722814912605 58802532401873521055592227)
        ·
          refine ⟨88203798602810281583388341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58802532401873521055592227 88203798602810281583388341)
          ·
            refine ⟨8269106119013463898442657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88203798602810281583388341 8269106119013463898442657)
            ·
              refine ⟨6201829589260097923831993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8269106119013463898442657 6201829589260097923831993)
              ·
                refine ⟨4651372191945073442873995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201829589260097923831993 4651372191945073442873995)
                ·
                  refine ⟨6977058287917610164310993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651372191945073442873995 6977058287917610164310993)
                  ·
                    refine ⟨5232793715938207623233245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6977058287917610164310993 5232793715938207623233245)
                    ·
                      refine ⟨1962297643476827858712467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232793715938207623233245 1962297643476827858712467)
                      ·
                        rfl

theorem cell23_3821561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_3821561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821561 prefixEnd_3821561 := by exact prefixLift 3821561
  have htrace : WordTrace (prefixWord ++ tailWord_3821561) baseStart_3821561 baseEnd_3821561 := by
    simpa [prefixWord, tailWord_3821561, baseEnd_3821561] using wordTrace_append hprefix tailTrace_3821561
  have hstable : (prefixWord ++ tailWord_3821561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821561).length < 2 ^ (prefixWord ++ tailWord_3821561).sum := by decide
  have hdescent : baseEnd_3821561 < baseStart_3821561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821575 : List Nat := [1, 1, 4, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_3821575 : Nat := 118140960795 + 3821575 * 2 ^ 59
def prefixEnd_3821575 : Nat := 4983230072969 + 3 ^ 40 * 3821575 * 2
def baseEnd_3821575 : Nat := 1962304832205990803937403

theorem tailTrace_3821575 : CollatzResearch.WordTrace tailWord_3821575 prefixEnd_3821575 1962304832205990803937403 := by
  unfold tailWord_3821575
  simp only [CollatzResearch.WordTrace]
  refine ⟨139384291130093922893154179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92922860753395948595436119 139384291130093922893154179)
  ·
    refine ⟨209076436695140884339731269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139384291130093922893154179 209076436695140884339731269)
    ·
      refine ⟨39201831880338915813699613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209076436695140884339731269 39201831880338915813699613)
      ·
        refine ⟨14700686955127093430137355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39201831880338915813699613 14700686955127093430137355)
        ·
          refine ⟨22051030432690640145206033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14700686955127093430137355 22051030432690640145206033)
          ·
            refine ⟨16538272824517980108904525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22051030432690640145206033 16538272824517980108904525)
            ·
              refine ⟨6201852309194242540839197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16538272824517980108904525 6201852309194242540839197)
              ·
                refine ⟨2325694615947840952814699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6201852309194242540839197 2325694615947840952814699)
                ·
                  refine ⟨3488541923921761429222049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325694615947840952814699 3488541923921761429222049)
                  ·
                    refine ⟨2616406442941321071916537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3488541923921761429222049 2616406442941321071916537)
                    ·
                      refine ⟨1962304832205990803937403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616406442941321071916537 1962304832205990803937403)
                      ·
                        rfl

theorem cell23_3821575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_3821575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821575 prefixEnd_3821575 := by exact prefixLift 3821575
  have htrace : WordTrace (prefixWord ++ tailWord_3821575) baseStart_3821575 baseEnd_3821575 := by
    simpa [prefixWord, tailWord_3821575, baseEnd_3821575] using wordTrace_append hprefix tailTrace_3821575
  have hstable : (prefixWord ++ tailWord_3821575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821575).length < 2 ^ (prefixWord ++ tailWord_3821575).sum := by decide
  have hdescent : baseEnd_3821575 < baseStart_3821575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821618 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_3821618 : Nat := 118140960795 + 3821618 * 2 ^ 59
def prefixEnd_3821618 : Nat := 4983230072969 + 3 ^ 40 * 3821618 * 2
def baseEnd_3821618 : Nat := 1962326911874134135699705

theorem tailTrace_3821618 : CollatzResearch.WordTrace tailWord_3821618 prefixEnd_3821618 1962326911874134135699705 := by
  unfold tailWord_3821618
  simp only [CollatzResearch.WordTrace]
  refine ⟨34846464867234535309242377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92923906312625427491313005 34846464867234535309242377)
  ·
    refine ⟨26134848650425901481931783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34846464867234535309242377 26134848650425901481931783)
    ·
      refine ⟨39202272975638852222897675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26134848650425901481931783 39202272975638852222897675)
      ·
        refine ⟨58803409463458278334346513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39202272975638852222897675 58803409463458278334346513)
        ·
          refine ⟨44102557097593708750759885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58803409463458278334346513 44102557097593708750759885)
          ·
            refine ⟨16538458911597640781534957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44102557097593708750759885 16538458911597640781534957)
            ·
              refine ⟨6201922091849115293075609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16538458911597640781534957 6201922091849115293075609)
              ·
                refine ⟨4651441568886836469806707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201922091849115293075609 4651441568886836469806707)
                ·
                  refine ⟨6977162353330254704710061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651441568886836469806707 6977162353330254704710061)
                  ·
                    refine ⟨2616435882498845514266273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6977162353330254704710061 2616435882498845514266273)
                    ·
                      refine ⟨1962326911874134135699705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616435882498845514266273 1962326911874134135699705)
                      ·
                        rfl

theorem cell23_3821618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_3821618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821618 prefixEnd_3821618 := by exact prefixLift 3821618
  have htrace : WordTrace (prefixWord ++ tailWord_3821618) baseStart_3821618 baseEnd_3821618 := by
    simpa [prefixWord, tailWord_3821618, baseEnd_3821618] using wordTrace_append hprefix tailTrace_3821618
  have hstable : (prefixWord ++ tailWord_3821618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821618).length < 2 ^ (prefixWord ++ tailWord_3821618).sum := by decide
  have hdescent : baseEnd_3821618 < baseStart_3821618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821627 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4]
def baseStart_3821627 : Nat := 118140960795 + 3821627 * 2 ^ 59
def prefixEnd_3821627 : Nat := 4983230072969 + 3 ^ 40 * 3821627 * 2
def baseEnd_3821627 : Nat := 1962331533200024600487163

theorem tailTrace_3821627 : CollatzResearch.WordTrace tailWord_3821627 prefixEnd_3821627 1962331533200024600487163 := by
  unfold tailWord_3821627
  simp only [CollatzResearch.WordTrace]
  refine ⟨139386187725905535774047135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92924125150603690516031423 139386187725905535774047135)
  ·
    refine ⟨209079281588858303661070703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139386187725905535774047135 209079281588858303661070703)
    ·
      refine ⟨313618922383287455491606055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209079281588858303661070703 313618922383287455491606055)
      ·
        refine ⟨470428383574931183237409083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313618922383287455491606055 470428383574931183237409083)
        ·
          refine ⟨705642575362396774856113625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470428383574931183237409083 705642575362396774856113625)
          ·
            refine ⟨529231931521797581142085219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705642575362396774856113625 529231931521797581142085219)
            ·
              refine ⟨793847897282696371713127829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529231931521797581142085219 793847897282696371713127829)
              ·
                refine ⟨37211620185126392424052867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 793847897282696371713127829 37211620185126392424052867)
                ·
                  refine ⟨55817430277689588636079301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37211620185126392424052867 55817430277689588636079301)
                  ·
                    refine ⟨10465768177066797869264869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55817430277689588636079301 10465768177066797869264869)
                    ·
                      refine ⟨1962331533200024600487163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10465768177066797869264869 1962331533200024600487163)
                      ·
                        rfl

theorem cell23_3821627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_3821627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821627 prefixEnd_3821627 := by exact prefixLift 3821627
  have htrace : WordTrace (prefixWord ++ tailWord_3821627) baseStart_3821627 baseEnd_3821627 := by
    simpa [prefixWord, tailWord_3821627, baseEnd_3821627] using wordTrace_append hprefix tailTrace_3821627
  have hstable : (prefixWord ++ tailWord_3821627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821627).length < 2 ^ (prefixWord ++ tailWord_3821627).sum := by decide
  have hdescent : baseEnd_3821627 < baseStart_3821627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821631 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 6, 2, 2]
def baseStart_3821631 : Nat := 118140960795 + 3821631 * 2 ^ 59
def prefixEnd_3821631 : Nat := 4983230072969 + 3 ^ 40 * 3821631 * 2
def baseEnd_3821631 : Nat := 1962333587122642584837145

theorem tailTrace_3821631 : CollatzResearch.WordTrace tailWord_3821631 prefixEnd_3821631 1962333587122642584837145 := by
  unfold tailWord_3821631
  simp only [CollatzResearch.WordTrace]
  refine ⟨139386333617891044457192747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92924222411927362971461831 139386333617891044457192747)
  ·
    refine ⟨209079500426836566685789121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139386333617891044457192747 209079500426836566685789121)
    ·
      refine ⟨156809625320127425014341841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209079500426836566685789121 156809625320127425014341841)
      ·
        refine ⟨117607218990095568760756381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156809625320127425014341841 117607218990095568760756381)
        ·
          refine ⟨44102707121285838285283643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117607218990095568760756381 44102707121285838285283643)
          ·
            refine ⟨66154060681928757427925465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44102707121285838285283643 66154060681928757427925465)
            ·
              refine ⟨49615545511446568070944099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66154060681928757427925465 49615545511446568070944099)
              ·
                refine ⟨74423318267169852106416149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49615545511446568070944099 74423318267169852106416149)
                ·
                  refine ⟨3488593043773586817488257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74423318267169852106416149 3488593043773586817488257)
                  ·
                    refine ⟨2616444782830190113116193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3488593043773586817488257 2616444782830190113116193)
                    ·
                      refine ⟨1962333587122642584837145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616444782830190113116193 1962333587122642584837145)
                      ·
                        rfl

theorem cell23_3821631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_3821631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821631 prefixEnd_3821631 := by exact prefixLift 3821631
  have htrace : WordTrace (prefixWord ++ tailWord_3821631) baseStart_3821631 baseEnd_3821631 := by
    simpa [prefixWord, tailWord_3821631, baseEnd_3821631] using wordTrace_append hprefix tailTrace_3821631
  have hstable : (prefixWord ++ tailWord_3821631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821631).length < 2 ^ (prefixWord ++ tailWord_3821631).sum := by decide
  have hdescent : baseEnd_3821631 < baseStart_3821631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821661 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3821661 : Nat := 118140960795 + 3821661 * 2 ^ 59
def prefixEnd_3821661 : Nat := 4983230072969 + 3 ^ 40 * 3821661 * 2
def baseEnd_3821661 : Nat := 1962348991542277467462007

theorem tailTrace_3821661 : CollatzResearch.WordTrace tailWord_3821661 prefixEnd_3821661 1962348991542277467462007 := by
  unfold tailWord_3821661
  simp only [CollatzResearch.WordTrace]
  refine ⟨139387427807782359580784837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92924951871854906387189891 139387427807782359580784837)
  ·
    refine ⟨26135142713959192421397157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139387427807782359580784837 26135142713959192421397157)
    ·
      refine ⟨4900339258867348579011967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26135142713959192421397157 4900339258867348579011967)
      ·
        refine ⟨7350508888301022868517951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900339258867348579011967 7350508888301022868517951)
        ·
          refine ⟨11025763332451534302776927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7350508888301022868517951 11025763332451534302776927)
          ·
            refine ⟨16538644998677301454165391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11025763332451534302776927 16538644998677301454165391)
            ·
              refine ⟨24807967498015952181248087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16538644998677301454165391 24807967498015952181248087)
              ·
                refine ⟨37211951247023928271872131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24807967498015952181248087 37211951247023928271872131)
                ·
                  refine ⟨55817926870535892407808197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37211951247023928271872131 55817926870535892407808197)
                  ·
                    refine ⟨10465861288225479826464037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55817926870535892407808197 10465861288225479826464037)
                    ·
                      refine ⟨1962348991542277467462007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10465861288225479826464037 1962348991542277467462007)
                      ·
                        rfl

theorem cell23_3821661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3821661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821661 prefixEnd_3821661 := by exact prefixLift 3821661
  have htrace : WordTrace (prefixWord ++ tailWord_3821661) baseStart_3821661 baseEnd_3821661 := by
    simpa [prefixWord, tailWord_3821661, baseEnd_3821661] using wordTrace_append hprefix tailTrace_3821661
  have hstable : (prefixWord ++ tailWord_3821661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821661).length < 2 ^ (prefixWord ++ tailWord_3821661).sum := by decide
  have hdescent : baseEnd_3821661 < baseStart_3821661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821664 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3]
def baseStart_3821664 : Nat := 118140960795 + 3821664 * 2 ^ 59
def prefixEnd_3821664 : Nat := 4983230072969 + 3 ^ 40 * 3821664 * 2
def baseEnd_3821664 : Nat := 1962350531984240955724493

theorem tailTrace_3821664 : CollatzResearch.WordTrace tailWord_3821664 prefixEnd_3821664 1962350531984240955724493 := by
  unfold tailWord_3821664
  simp only [CollatzResearch.WordTrace]
  refine ⟨69693768613385745546572023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92925024817847660728762697 69693768613385745546572023)
  ·
    refine ⟨104540652920078618319858035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69693768613385745546572023 104540652920078618319858035)
    ·
      refine ⟨156810979380117927479787053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104540652920078618319858035 156810979380117927479787053)
      ·
        refine ⟨58804117267544222804920145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156810979380117927479787053 58804117267544222804920145)
        ·
          refine ⟨44103087950658167103690109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58804117267544222804920145 44103087950658167103690109)
          ·
            refine ⟨16538657981496812663883791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44103087950658167103690109 16538657981496812663883791)
            ·
              refine ⟨24807986972245218995825687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16538657981496812663883791 24807986972245218995825687)
              ·
                refine ⟨37211980458367828493738531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24807986972245218995825687 37211980458367828493738531)
                ·
                  refine ⟨55817970687551742740607797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37211980458367828493738531 55817970687551742740607797)
                  ·
                    refine ⟨5232934751957975881931981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55817970687551742740607797 5232934751957975881931981)
                    ·
                      refine ⟨1962350531984240955724493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5232934751957975881931981 1962350531984240955724493)
                      ·
                        rfl

theorem cell23_3821664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_3821664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821664 prefixEnd_3821664 := by exact prefixLift 3821664
  have htrace : WordTrace (prefixWord ++ tailWord_3821664) baseStart_3821664 baseEnd_3821664 := by
    simpa [prefixWord, tailWord_3821664, baseEnd_3821664] using wordTrace_append hprefix tailTrace_3821664
  have hstable : (prefixWord ++ tailWord_3821664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821664).length < 2 ^ (prefixWord ++ tailWord_3821664).sum := by decide
  have hdescent : baseEnd_3821664 < baseStart_3821664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821778 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 6]
def baseStart_3821778 : Nat := 118140960795 + 3821778 * 2 ^ 59
def prefixEnd_3821778 : Nat := 4983230072969 + 3 ^ 40 * 3821778 * 2
def baseEnd_3821778 : Nat := 218045452086539278855441

theorem tailTrace_3821778 : CollatzResearch.WordTrace tailWord_3821778 prefixEnd_3821778 218045452086539278855441 := by
  unfold tailWord_3821778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34847923787089622140698497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92927796765572325708529325 34847923787089622140698497)
  ·
    refine ⟨26135942840317216605523873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34847923787089622140698497 26135942840317216605523873)
    ·
      refine ⟨19601957130237912454142905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26135942840317216605523873 19601957130237912454142905)
      ·
        refine ⟨14701467847678434340607179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19601957130237912454142905 14701467847678434340607179)
        ·
          refine ⟨22052201771517651510910769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14701467847678434340607179 22052201771517651510910769)
          ·
            refine ⟨16539151328638238633183077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22052201771517651510910769 16539151328638238633183077)
            ·
              refine ⟨3101090874119669743721827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16539151328638238633183077 3101090874119669743721827)
              ·
                refine ⟨4651636311179504615582741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101090874119669743721827 4651636311179504615582741)
                ·
                  refine ⟨218045452086539278855441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4651636311179504615582741 218045452086539278855441)
                  ·
                    rfl

theorem cell23_3821778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_3821778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821778 prefixEnd_3821778 := by exact prefixLift 3821778
  have htrace : WordTrace (prefixWord ++ tailWord_3821778) baseStart_3821778 baseEnd_3821778 := by
    simpa [prefixWord, tailWord_3821778, baseEnd_3821778] using wordTrace_append hprefix tailTrace_3821778
  have hstable : (prefixWord ++ tailWord_3821778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821778).length < 2 ^ (prefixWord ++ tailWord_3821778).sum := by decide
  have hdescent : baseEnd_3821778 < baseStart_3821778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821821 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_3821821 : Nat := 118140960795 + 3821821 * 2 ^ 59
def prefixEnd_3821821 : Nat := 4983230072969 + 3 ^ 40 * 3821821 * 2
def baseEnd_3821821 : Nat := 654143716148998947153757

theorem tailTrace_3821821 : CollatzResearch.WordTrace tailWord_3821821 prefixEnd_3821821 654143716148998947153757 := by
  unfold tailWord_3821821
  simp only [CollatzResearch.WordTrace]
  refine ⟨139393263487202706906609317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92928842324801804604406211 139393263487202706906609317)
  ·
    refine ⟨26136236903850507544989247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139393263487202706906609317 26136236903850507544989247)
    ·
      refine ⟨39204355355775761317483871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26136236903850507544989247 39204355355775761317483871)
      ·
        refine ⟨58806533033663641976225807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39204355355775761317483871 58806533033663641976225807)
        ·
          refine ⟨88209799550495462964338711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58806533033663641976225807 88209799550495462964338711)
          ·
            refine ⟨132314699325743194446508067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88209799550495462964338711 132314699325743194446508067)
            ·
              refine ⟨198472048988614791669762101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132314699325743194446508067 198472048988614791669762101)
              ·
                refine ⟨18606754592682636719040197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198472048988614791669762101 18606754592682636719040197)
                ·
                  refine ⟨3488766486127994384820037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18606754592682636719040197 3488766486127994384820037)
                  ·
                    refine ⟨654143716148998947153757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488766486127994384820037 654143716148998947153757)
                    ·
                      rfl

theorem cell23_3821821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_3821821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821821 prefixEnd_3821821 := by exact prefixLift 3821821
  have htrace : WordTrace (prefixWord ++ tailWord_3821821) baseStart_3821821 baseEnd_3821821 := by
    simpa [prefixWord, tailWord_3821821, baseEnd_3821821] using wordTrace_append hprefix tailTrace_3821821
  have hstable : (prefixWord ++ tailWord_3821821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821821).length < 2 ^ (prefixWord ++ tailWord_3821821).sum := by decide
  have hdescent : baseEnd_3821821 < baseStart_3821821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821822 : List Nat := [4, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3821822 : Nat := 118140960795 + 3821822 * 2 ^ 59
def prefixEnd_3821822 : Nat := 4983230072969 + 3 ^ 40 * 3821822 * 2
def baseEnd_3821822 : Nat := 1962431661927651337548767

theorem tailTrace_3821822 : CollatzResearch.WordTrace tailWord_3821822 prefixEnd_3821822 1962431661927651337548767 := by
  unfold tailWord_3821822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424162495024885509674465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92928866640132722718263813 17424162495024885509674465)
  ·
    refine ⟨13068121871268664132255849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17424162495024885509674465 13068121871268664132255849)
    ·
      refine ⟨9801091403451498099191887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13068121871268664132255849 9801091403451498099191887)
      ·
        refine ⟨14701637105177247148787831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801091403451498099191887 14701637105177247148787831)
        ·
          refine ⟨22052455657765870723181747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14701637105177247148787831 22052455657765870723181747)
          ·
            refine ⟨33078683486648806084772621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22052455657765870723181747 33078683486648806084772621)
            ·
              refine ⟨12404506307493302281789733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33078683486648806084772621 12404506307493302281789733)
              ·
                refine ⟨2325844932654994177835575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12404506307493302281789733 2325844932654994177835575)
                ·
                  refine ⟨3488767398982491266753363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325844932654994177835575 3488767398982491266753363)
                  ·
                    refine ⟨5233151098473736900130045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3488767398982491266753363 5233151098473736900130045)
                    ·
                      refine ⟨1962431661927651337548767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5233151098473736900130045 1962431661927651337548767)
                      ·
                        rfl

theorem cell23_3821822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3821822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821822 prefixEnd_3821822 := by exact prefixLift 3821822
  have htrace : WordTrace (prefixWord ++ tailWord_3821822) baseStart_3821822 baseEnd_3821822 := by
    simpa [prefixWord, tailWord_3821822, baseEnd_3821822] using wordTrace_append hprefix tailTrace_3821822
  have hstable : (prefixWord ++ tailWord_3821822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821822).length < 2 ^ (prefixWord ++ tailWord_3821822).sum := by decide
  have hdescent : baseEnd_3821822 < baseStart_3821822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821824 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_3821824 : Nat := 118140960795 + 3821824 * 2 ^ 59
def prefixEnd_3821824 : Nat := 4983230072969 + 3 ^ 40 * 3821824 * 2
def baseEnd_3821824 : Nat := 1962432688888960329723757

theorem tailTrace_3821824 : CollatzResearch.WordTrace tailWord_3821824 prefixEnd_3821824 1962432688888960329723757 := by
  unfold tailWord_3821824
  simp only [CollatzResearch.WordTrace]
  refine ⟨69696686453095919209484263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92928915270794558945979017 69696686453095919209484263)
  ·
    refine ⟨104545029679643878814226395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69696686453095919209484263 104545029679643878814226395)
    ·
      refine ⟨156817544519465818221339593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104545029679643878814226395 156817544519465818221339593)
      ·
        refine ⟨117613158389599363666004695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156817544519465818221339593 117613158389599363666004695)
        ·
          refine ⟨176419737584399045499007043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117613158389599363666004695 176419737584399045499007043)
          ·
            refine ⟨264629606376598568248510565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176419737584399045499007043 264629606376598568248510565)
            ·
              refine ⟨49618051195612231546595731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264629606376598568248510565 49618051195612231546595731)
              ·
                refine ⟨74427076793418347319893597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49618051195612231546595731 74427076793418347319893597)
                ·
                  refine ⟨27910153797531880244960099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74427076793418347319893597 27910153797531880244960099)
                  ·
                    refine ⟨41865230696297820367440149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27910153797531880244960099 41865230696297820367440149)
                    ·
                      refine ⟨1962432688888960329723757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41865230696297820367440149 1962432688888960329723757)
                      ·
                        rfl

theorem cell23_3821824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_3821824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821824 prefixEnd_3821824 := by exact prefixLift 3821824
  have htrace : WordTrace (prefixWord ++ tailWord_3821824) baseStart_3821824 baseEnd_3821824 := by
    simpa [prefixWord, tailWord_3821824, baseEnd_3821824] using wordTrace_append hprefix tailTrace_3821824
  have hstable : (prefixWord ++ tailWord_3821824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821824).length < 2 ^ (prefixWord ++ tailWord_3821824).sum := by decide
  have hdescent : baseEnd_3821824 < baseStart_3821824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821838 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3821838 : Nat := 118140960795 + 3821838 * 2 ^ 59
def prefixEnd_3821838 : Nat := 4983230072969 + 3 ^ 40 * 3821838 * 2
def baseEnd_3821838 : Nat := 654146625872707758316231

theorem tailTrace_3821838 : CollatzResearch.WordTrace tailWord_3821838 prefixEnd_3821838 654146625872707758316231 := by
  unfold tailWord_3821838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424235441017639851247271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92929255685427412539985445 17424235441017639851247271)
  ·
    refine ⟨26136353161526459776870907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17424235441017639851247271 26136353161526459776870907)
    ·
      refine ⟨39204529742289689665306361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26136353161526459776870907 39204529742289689665306361)
      ·
        refine ⟨29403397306717267248979771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39204529742289689665306361 29403397306717267248979771)
        ·
          refine ⟨44105095960075900873469657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29403397306717267248979771 44105095960075900873469657)
          ·
            refine ⟨33078821970056925655102243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44105095960075900873469657 33078821970056925655102243)
            ·
              refine ⟨49618232955085388482653365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33078821970056925655102243 49618232955085388482653365)
              ·
                refine ⟨4651709339539255170248753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49618232955085388482653365 4651709339539255170248753)
                ·
                  refine ⟨3488782004654441377686565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4651709339539255170248753 3488782004654441377686565)
                  ·
                    refine ⟨654146625872707758316231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488782004654441377686565 654146625872707758316231)
                    ·
                      rfl

theorem cell23_3821838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3821838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821838 prefixEnd_3821838 := by exact prefixLift 3821838
  have htrace : WordTrace (prefixWord ++ tailWord_3821838) baseStart_3821838 baseEnd_3821838 := by
    simpa [prefixWord, tailWord_3821838, baseEnd_3821838] using wordTrace_append hprefix tailTrace_3821838
  have hstable : (prefixWord ++ tailWord_3821838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821838).length < 2 ^ (prefixWord ++ tailWord_3821838).sum := by decide
  have hdescent : baseEnd_3821838 < baseStart_3821838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821841 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_3821841 : Nat := 118140960795 + 3821841 * 2 ^ 59
def prefixEnd_3821841 : Nat := 4983230072969 + 3 ^ 40 * 3821841 * 2
def baseEnd_3821841 : Nat := 1962441418060086763211179

theorem tailTrace_3821841 : CollatzResearch.WordTrace tailWord_3821841 prefixEnd_3821841 1962441418060086763211179 := by
  unfold tailWord_3821841
  simp only [CollatzResearch.WordTrace]
  refine ⟨139393992947130250322337377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92929328631420166881558251 139393992947130250322337377)
  ·
    refine ⟨104545494710347687741753033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139393992947130250322337377 104545494710347687741753033)
    ·
      refine ⟨78409121032760765806314775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104545494710347687741753033 78409121032760765806314775)
      ·
        refine ⟨117613681549141148709472163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78409121032760765806314775 117613681549141148709472163)
        ·
          refine ⟨176420522323711723064208245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117613681549141148709472163 176420522323711723064208245)
          ·
            refine ⟨16539423967847974037269523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176420522323711723064208245 16539423967847974037269523)
            ·
              refine ⟨24809135951771961055904285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16539423967847974037269523 24809135951771961055904285)
              ·
                refine ⟨9303425981914485395964107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24809135951771961055904285 9303425981914485395964107)
                ·
                  refine ⟨13955138972871728093946161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9303425981914485395964107 13955138972871728093946161)
                  ·
                    refine ⟨10466354229653796070459621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13955138972871728093946161 10466354229653796070459621)
                    ·
                      refine ⟨1962441418060086763211179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10466354229653796070459621 1962441418060086763211179)
                      ·
                        rfl

theorem cell23_3821841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_3821841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821841 prefixEnd_3821841 := by exact prefixLift 3821841
  have htrace : WordTrace (prefixWord ++ tailWord_3821841) baseStart_3821841 baseEnd_3821841 := by
    simpa [prefixWord, tailWord_3821841, baseEnd_3821841] using wordTrace_append hprefix tailTrace_3821841
  have hstable : (prefixWord ++ tailWord_3821841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821841).length < 2 ^ (prefixWord ++ tailWord_3821841).sum := by decide
  have hdescent : baseEnd_3821841 < baseStart_3821841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821848 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_3821848 : Nat := 118140960795 + 3821848 * 2 ^ 59
def prefixEnd_3821848 : Nat := 4983230072969 + 3 ^ 40 * 3821848 * 2
def baseEnd_3821848 : Nat := 1962445012424668235823647

theorem tailTrace_3821848 : CollatzResearch.WordTrace tailWord_3821848 prefixEnd_3821848 1962445012424668235823647 := by
  unfold tailWord_3821848
  simp only [CollatzResearch.WordTrace]
  refine ⟨69697124129052445258921099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92929498838736593678561465 69697124129052445258921099)
  ·
    refine ⟨104545686193578667888381649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69697124129052445258921099 104545686193578667888381649)
    ·
      refine ⟨78409264645184000916286237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104545686193578667888381649 78409264645184000916286237)
      ·
        refine ⟨29403474241944000343607339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78409264645184000916286237 29403474241944000343607339)
        ·
          refine ⟨44105211362916000515411009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29403474241944000343607339 44105211362916000515411009)
          ·
            refine ⟨33078908522187000386558257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44105211362916000515411009 33078908522187000386558257)
            ·
              refine ⟨24809181391640250289918693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33078908522187000386558257 24809181391640250289918693)
              ·
                refine ⟨4651721510932546929359755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24809181391640250289918693 4651721510932546929359755)
                ·
                  refine ⟨6977582266398820394039633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651721510932546929359755 6977582266398820394039633)
                  ·
                    refine ⟨5233186699799115295529725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6977582266398820394039633 5233186699799115295529725)
                    ·
                      refine ⟨1962445012424668235823647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5233186699799115295529725 1962445012424668235823647)
                      ·
                        rfl

theorem cell23_3821848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_3821848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821848 prefixEnd_3821848 := by exact prefixLift 3821848
  have htrace : WordTrace (prefixWord ++ tailWord_3821848) baseStart_3821848 baseEnd_3821848 := by
    simpa [prefixWord, tailWord_3821848, baseEnd_3821848] using wordTrace_append hprefix tailTrace_3821848
  have hstable : (prefixWord ++ tailWord_3821848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821848).length < 2 ^ (prefixWord ++ tailWord_3821848).sum := by decide
  have hdescent : baseEnd_3821848 < baseStart_3821848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821858 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3821858 : Nat := 118140960795 + 3821858 * 2 ^ 59
def prefixEnd_3821858 : Nat := 4983230072969 + 3 ^ 40 * 3821858 * 2
def baseEnd_3821858 : Nat := 1962450147231213196698601

theorem tailTrace_3821858 : CollatzResearch.WordTrace tailWord_3821858 prefixEnd_3821858 1962450147231213196698601 := by
  unfold tailWord_3821858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34848653247017165556426557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92929741992045774817137485 34848653247017165556426557)
  ·
    refine ⟨13068244967631437083659959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34848653247017165556426557 13068244967631437083659959)
    ·
      refine ⟨19602367451447155625489939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13068244967631437083659959 19602367451447155625489939)
      ·
        refine ⟨29403551177170733438234909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19602367451447155625489939 29403551177170733438234909)
        ·
          refine ⟨11026331691439025039338091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29403551177170733438234909 11026331691439025039338091)
          ·
            refine ⟨16539497537158537559007137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11026331691439025039338091 16539497537158537559007137)
            ·
              refine ⟨12404623152868903169255353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16539497537158537559007137 12404623152868903169255353)
              ·
                refine ⟨9303467364651677376941515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12404623152868903169255353 9303467364651677376941515)
                ·
                  refine ⟨13955201046977516065412273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9303467364651677376941515 13955201046977516065412273)
                  ·
                    refine ⟨10466400785233137049059205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13955201046977516065412273 10466400785233137049059205)
                    ·
                      refine ⟨1962450147231213196698601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10466400785233137049059205 1962450147231213196698601)
                      ·
                        rfl

theorem cell23_3821858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3821858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821858 prefixEnd_3821858 := by exact prefixLift 3821858
  have htrace : WordTrace (prefixWord ++ tailWord_3821858) baseStart_3821858 baseEnd_3821858 := by
    simpa [prefixWord, tailWord_3821858, baseEnd_3821858] using wordTrace_append hprefix tailTrace_3821858
  have hstable : (prefixWord ++ tailWord_3821858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821858).length < 2 ^ (prefixWord ++ tailWord_3821858).sum := by decide
  have hdescent : baseEnd_3821858 < baseStart_3821858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821888 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 3, 3, 2]
def baseStart_3821888 : Nat := 118140960795 + 3821888 * 2 ^ 59
def prefixEnd_3821888 : Nat := 4983230072969 + 3 ^ 40 * 3821888 * 2
def baseEnd_3821888 : Nat := 1962465551650848079323463

theorem tailTrace_3821888 : CollatzResearch.WordTrace tailWord_3821888 prefixEnd_3821888 1962465551650848079323463 := by
  unfold tailWord_3821888
  simp only [CollatzResearch.WordTrace]
  refine ⟨69697853588979988674649159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92930471451973318232865545 69697853588979988674649159)
  ·
    refine ⟨104546780383469983011973739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69697853588979988674649159 104546780383469983011973739)
    ·
      refine ⟨156820170575204974517960609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104546780383469983011973739 156820170575204974517960609)
      ·
        refine ⟨117615127931403730888470457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156820170575204974517960609 117615127931403730888470457)
        ·
          refine ⟨88211345948552798166352843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117615127931403730888470457 88211345948552798166352843)
          ·
            refine ⟨132317018922829197249529265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88211345948552798166352843 132317018922829197249529265)
            ·
              refine ⟨99237764192121897937146949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132317018922829197249529265 99237764192121897937146949)
              ·
                refine ⟨18607080786022855863215053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99237764192121897937146949 18607080786022855863215053)
                ·
                  refine ⟨6977655294758570948705645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18607080786022855863215053 6977655294758570948705645)
                  ·
                    refine ⟨2616620735534464105764617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6977655294758570948705645 2616620735534464105764617)
                    ·
                      refine ⟨1962465551650848079323463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616620735534464105764617 1962465551650848079323463)
                      ·
                        rfl

theorem cell23_3821888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_3821888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821888 prefixEnd_3821888 := by exact prefixLift 3821888
  have htrace : WordTrace (prefixWord ++ tailWord_3821888) baseStart_3821888 baseEnd_3821888 := by
    simpa [prefixWord, tailWord_3821888, baseEnd_3821888] using wordTrace_append hprefix tailTrace_3821888
  have hstable : (prefixWord ++ tailWord_3821888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821888).length < 2 ^ (prefixWord ++ tailWord_3821888).sum := by decide
  have hdescent : baseEnd_3821888 < baseStart_3821888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821892 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3821892 : Nat := 118140960795 + 3821892 * 2 ^ 59
def prefixEnd_3821892 : Nat := 4983230072969 + 3 ^ 40 * 3821892 * 2
def baseEnd_3821892 : Nat := 1962467605573466063673445

theorem tailTrace_3821892 : CollatzResearch.WordTrace tailWord_3821892 prefixEnd_3821892 1962467605573466063673445 := by
  unfold tailWord_3821892
  simp only [CollatzResearch.WordTrace]
  refine ⟨69697926534972743016221965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92930568713296990688295953 69697926534972743016221965)
  ·
    refine ⟨26136722450614778631083237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69697926534972743016221965 26136722450614778631083237)
    ·
      refine ⟨4900635459490270993328107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26136722450614778631083237 4900635459490270993328107)
      ·
        refine ⟨7350953189235406489992161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900635459490270993328107 7350953189235406489992161)
        ·
          refine ⟨5513214891926554867494121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7350953189235406489992161 5513214891926554867494121)
          ·
            refine ⟨4134911168944916150620591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5513214891926554867494121 4134911168944916150620591)
            ·
              refine ⟨6202366753417374225930887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134911168944916150620591 6202366753417374225930887)
              ·
                refine ⟨9303550130126061338896331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6202366753417374225930887 9303550130126061338896331)
                ·
                  refine ⟨13955325195189092008344497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9303550130126061338896331 13955325195189092008344497)
                  ·
                    refine ⟨10466493896391819006258373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13955325195189092008344497 10466493896391819006258373)
                    ·
                      refine ⟨1962467605573466063673445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10466493896391819006258373 1962467605573466063673445)
                      ·
                        rfl

theorem cell23_3821892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3821892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821892 prefixEnd_3821892 := by exact prefixLift 3821892
  have htrace : WordTrace (prefixWord ++ tailWord_3821892) baseStart_3821892 baseEnd_3821892 := by
    simpa [prefixWord, tailWord_3821892, baseEnd_3821892] using wordTrace_append hprefix tailTrace_3821892
  have hstable : (prefixWord ++ tailWord_3821892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821892).length < 2 ^ (prefixWord ++ tailWord_3821892).sum := by decide
  have hdescent : baseEnd_3821892 < baseStart_3821892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821905 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 1, 3, 2]
def baseStart_3821905 : Nat := 118140960795 + 3821905 * 2 ^ 59
def prefixEnd_3821905 : Nat := 4983230072969 + 3 ^ 40 * 3821905 * 2
def baseEnd_3821905 : Nat := 1962474280821974512810885

theorem tailTrace_3821905 : CollatzResearch.WordTrace tailWord_3821905 prefixEnd_3821905 1962474280821974512810885 := by
  unfold tailWord_3821905
  simp only [CollatzResearch.WordTrace]
  refine ⟨139396327218898389252667169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92930884812598926168444779 139396327218898389252667169)
  ·
    refine ⟨104547245414173791939500377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139396327218898389252667169 104547245414173791939500377)
    ·
      refine ⟨78410434060630343954625283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104547245414173791939500377 78410434060630343954625283)
      ·
        refine ⟨117615651090945515931937925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78410434060630343954625283 117615651090945515931937925)
        ·
          refine ⟨22052934579552284237238361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117615651090945515931937925 22052934579552284237238361)
          ·
            refine ⟨16539700934664213177928771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22052934579552284237238361 16539700934664213177928771)
            ·
              refine ⟨24809551401996319766893157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16539700934664213177928771 24809551401996319766893157)
              ·
                refine ⟨4651790887874309956292467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24809551401996319766893157 4651790887874309956292467)
                ·
                  refine ⟨6977686331811464934438701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651790887874309956292467 6977686331811464934438701)
                  ·
                    refine ⟨2616632374429299350414513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6977686331811464934438701 2616632374429299350414513)
                    ·
                      refine ⟨1962474280821974512810885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616632374429299350414513 1962474280821974512810885)
                      ·
                        rfl

theorem cell23_3821905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_3821905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821905 prefixEnd_3821905 := by exact prefixLift 3821905
  have htrace : WordTrace (prefixWord ++ tailWord_3821905) baseStart_3821905 baseEnd_3821905 := by
    simpa [prefixWord, tailWord_3821905, baseEnd_3821905] using wordTrace_append hprefix tailTrace_3821905
  have hstable : (prefixWord ++ tailWord_3821905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821905).length < 2 ^ (prefixWord ++ tailWord_3821905).sum := by decide
  have hdescent : baseEnd_3821905 < baseStart_3821905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821921 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_3821921 : Nat := 118140960795 + 3821921 * 2 ^ 59
def prefixEnd_3821921 : Nat := 4983230072969 + 3 ^ 40 * 3821921 * 2
def baseEnd_3821921 : Nat := 1962482496512446450210811

theorem tailTrace_3821921 : CollatzResearch.WordTrace tailWord_3821921 prefixEnd_3821921 1962482496512446450210811 := by
  unfold tailWord_3821921
  simp only [CollatzResearch.WordTrace]
  refine ⟨139396910786840423985249617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92931273857893615990166411 139396910786840423985249617)
  ·
    refine ⟨104547683090130317988937213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139396910786840423985249617 104547683090130317988937213)
    ·
      refine ⟨39205381158798869245851455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104547683090130317988937213 39205381158798869245851455)
      ·
        refine ⟨58808071738198303868777183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39205381158798869245851455 58808071738198303868777183)
        ·
          refine ⟨88212107607297455803165775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58808071738198303868777183 88212107607297455803165775)
          ·
            refine ⟨132318161410946183704748663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88212107607297455803165775 132318161410946183704748663)
            ·
              refine ⟨198477242116419275557122995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132318161410946183704748663 198477242116419275557122995)
              ·
                refine ⟨297715863174628913335684493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198477242116419275557122995 297715863174628913335684493)
                ·
                  refine ⟨111643448690485842500881685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297715863174628913335684493 111643448690485842500881685)
                  ·
                    refine ⟨5233286657366523867228829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111643448690485842500881685 5233286657366523867228829)
                    ·
                      refine ⟨1962482496512446450210811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5233286657366523867228829 1962482496512446450210811)
                      ·
                        rfl

theorem cell23_3821921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_3821921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821921 prefixEnd_3821921 := by exact prefixLift 3821921
  have htrace : WordTrace (prefixWord ++ tailWord_3821921) baseStart_3821921 baseEnd_3821921 := by
    simpa [prefixWord, tailWord_3821921, baseEnd_3821921] using wordTrace_append hprefix tailTrace_3821921
  have hstable : (prefixWord ++ tailWord_3821921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821921).length < 2 ^ (prefixWord ++ tailWord_3821921).sum := by decide
  have hdescent : baseEnd_3821921 < baseStart_3821921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821922 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_3821922 : Nat := 118140960795 + 3821922 * 2 ^ 59
def prefixEnd_3821922 : Nat := 4983230072969 + 3 ^ 40 * 3821922 * 2
def baseEnd_3821922 : Nat := 1962483009993100946298307

theorem tailTrace_3821922 : CollatzResearch.WordTrace tailWord_3821922 prefixEnd_3821922 1962483009993100946298307 := by
  unfold tailWord_3821922
  simp only [CollatzResearch.WordTrace]
  refine ⟨34849236814959200289009005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92931298173224534104024013 34849236814959200289009005)
  ·
    refine ⟨13068463805609700108378377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34849236814959200289009005 13068463805609700108378377)
    ·
      refine ⟨9801347854207275081283783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13068463805609700108378377 9801347854207275081283783)
      ·
        refine ⟨14702021781310912621925675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801347854207275081283783 14702021781310912621925675)
        ·
          refine ⟨22053032671966368932888513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14702021781310912621925675 22053032671966368932888513)
          ·
            refine ⟨16539774503974776699666385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22053032671966368932888513 16539774503974776699666385)
            ·
              refine ⟨12404830877981082524749789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16539774503974776699666385 12404830877981082524749789)
              ·
                refine ⟨4651811579242905946781171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12404830877981082524749789 4651811579242905946781171)
                ·
                  refine ⟨6977717368864358920171757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651811579242905946781171 6977717368864358920171757)
                  ·
                    refine ⟨2616644013324134595064409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6977717368864358920171757 2616644013324134595064409)
                    ·
                      refine ⟨1962483009993100946298307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616644013324134595064409 1962483009993100946298307)
                      ·
                        rfl

theorem cell23_3821922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_3821922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821922 prefixEnd_3821922 := by exact prefixLift 3821922
  have htrace : WordTrace (prefixWord ++ tailWord_3821922) baseStart_3821922 baseEnd_3821922 := by
    simpa [prefixWord, tailWord_3821922, baseEnd_3821922] using wordTrace_append hprefix tailTrace_3821922
  have hstable : (prefixWord ++ tailWord_3821922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821922).length < 2 ^ (prefixWord ++ tailWord_3821922).sum := by decide
  have hdescent : baseEnd_3821922 < baseStart_3821922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821988 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_3821988 : Nat := 118140960795 + 3821988 * 2 ^ 59
def prefixEnd_3821988 : Nat := 4983230072969 + 3 ^ 40 * 3821988 * 2
def baseEnd_3821988 : Nat := 654172299905432562691001

theorem tailTrace_3821988 : CollatzResearch.WordTrace tailWord_3821988 prefixEnd_3821988 654172299905432562691001 := by
  unfold tailWord_3821988
  simp only [CollatzResearch.WordTrace]
  refine ⟨69699677238798847213969309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92932902985065129618625745 69699677238798847213969309)
  ·
    refine ⟨26137378964549567705238491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69699677238798847213969309 26137378964549567705238491)
    ·
      refine ⟨39206068446824351557857737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26137378964549567705238491 39206068446824351557857737)
      ·
        refine ⟨29404551335118263668393303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39206068446824351557857737 29404551335118263668393303)
        ·
          refine ⟨44106827002677395502589955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29404551335118263668393303 44106827002677395502589955)
          ·
            refine ⟨66160240504016093253884933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44106827002677395502589955 66160240504016093253884933)
            ·
              refine ⟨12405045094503017485103425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66160240504016093253884933 12405045094503017485103425)
              ·
                refine ⟨9303783820877263113827569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12405045094503017485103425 9303783820877263113827569)
                ·
                  refine ⟨6977837865657947335370677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9303783820877263113827569 6977837865657947335370677)
                  ·
                    refine ⟨654172299905432562691001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6977837865657947335370677 654172299905432562691001)
                    ·
                      rfl

theorem cell23_3821988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_3821988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821988 prefixEnd_3821988 := by exact prefixLift 3821988
  have htrace : WordTrace (prefixWord ++ tailWord_3821988) baseStart_3821988 baseEnd_3821988 := by
    simpa [prefixWord, tailWord_3821988, baseEnd_3821988] using wordTrace_append hprefix tailTrace_3821988
  have hstable : (prefixWord ++ tailWord_3821988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821988).length < 2 ^ (prefixWord ++ tailWord_3821988).sum := by decide
  have hdescent : baseEnd_3821988 < baseStart_3821988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821992 : List Nat := [2, 1, 6, 1, 1, 2, 1, 4, 5]
def baseStart_3821992 : Nat := 118140960795 + 3821992 * 2 ^ 59
def prefixEnd_3821992 : Nat := 4983230072969 + 3 ^ 40 * 3821992 * 2
def baseEnd_3821992 : Nat := 218057661515435074713665

theorem tailTrace_3821992 : CollatzResearch.WordTrace tailWord_3821992 prefixEnd_3821992 218057661515435074713665 := by
  unfold tailWord_3821992
  simp only [CollatzResearch.WordTrace]
  refine ⟨69699750184791601555542115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92933000246388802074056153 69699750184791601555542115)
  ·
    refine ⟨104549625277187402333313173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69699750184791601555542115 104549625277187402333313173)
    ·
      refine ⟨4900763684868159484374055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104549625277187402333313173 4900763684868159484374055)
      ·
        refine ⟨7351145527302239226561083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900763684868159484374055 7351145527302239226561083)
        ·
          refine ⟨11026718290953358839841625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7351145527302239226561083 11026718290953358839841625)
          ·
            refine ⟨8270038718215019129881219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11026718290953358839841625 8270038718215019129881219)
            ·
              refine ⟨12405058077322528694821829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8270038718215019129881219 12405058077322528694821829)
              ·
                refine ⟨2325948389497974130279093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12405058077322528694821829 2325948389497974130279093)
                ·
                  refine ⟨218057661515435074713665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2325948389497974130279093 218057661515435074713665)
                  ·
                    rfl

theorem cell23_3821992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 5].length) (baseStart_3821992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3821992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3821992 prefixEnd_3821992 := by exact prefixLift 3821992
  have htrace : WordTrace (prefixWord ++ tailWord_3821992) baseStart_3821992 baseEnd_3821992 := by
    simpa [prefixWord, tailWord_3821992, baseEnd_3821992] using wordTrace_append hprefix tailTrace_3821992
  have hstable : (prefixWord ++ tailWord_3821992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821992).length < 2 ^ (prefixWord ++ tailWord_3821992).sum := by decide
  have hdescent : baseEnd_3821992 < baseStart_3821992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822021 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3822021 : Nat := 118140960795 + 3822021 * 2 ^ 59
def prefixEnd_3822021 : Nat := 4983230072969 + 3 ^ 40 * 3822021 * 2
def baseEnd_3822021 : Nat := 1962533844577896058960351

theorem tailTrace_3822021 : CollatzResearch.WordTrace tailWord_3822021 prefixEnd_3822021 1962533844577896058960351 := by
  unfold tailWord_3822021
  simp only [CollatzResearch.WordTrace]
  refine ⟨139400558086478141063889917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92933705390985427375926611 139400558086478141063889917)
  ·
    refine ⟨52275209282429302898958719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139400558086478141063889917 52275209282429302898958719)
    ·
      refine ⟨78412813923643954348438079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52275209282429302898958719 78412813923643954348438079)
      ·
        refine ⟨117619220885465931522657119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78412813923643954348438079 117619220885465931522657119)
        ·
          refine ⟨176428831328198897283985679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117619220885465931522657119 176428831328198897283985679)
          ·
            refine ⟨264643246992298345925978519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176428831328198897283985679 264643246992298345925978519)
            ·
              refine ⟨396964870488447518888967779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264643246992298345925978519 396964870488447518888967779)
              ·
                refine ⟨595447305732671278333451669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396964870488447518888967779 595447305732671278333451669)
                ·
                  refine ⟨27911592456218966171880547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 595447305732671278333451669 27911592456218966171880547)
                  ·
                    refine ⟨41867388684328449257820821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27911592456218966171880547 41867388684328449257820821)
                    ·
                      refine ⟨1962533844577896058960351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41867388684328449257820821 1962533844577896058960351)
                      ·
                        rfl

theorem cell23_3822021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3822021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822021 prefixEnd_3822021 := by exact prefixLift 3822021
  have htrace : WordTrace (prefixWord ++ tailWord_3822021) baseStart_3822021 baseEnd_3822021 := by
    simpa [prefixWord, tailWord_3822021, baseEnd_3822021] using wordTrace_append hprefix tailTrace_3822021
  have hstable : (prefixWord ++ tailWord_3822021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822021).length < 2 ^ (prefixWord ++ tailWord_3822021).sum := by decide
  have hdescent : baseEnd_3822021 < baseStart_3822021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822031 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 8]
def baseStart_3822031 : Nat := 118140960795 + 3822031 * 2 ^ 59
def prefixEnd_3822031 : Nat := 4983230072969 + 3 ^ 40 * 3822031 * 2
def baseEnd_3822031 : Nat := 218059886598271224426145

theorem tailTrace_3822031 : CollatzResearch.WordTrace tailWord_3822031 prefixEnd_3822031 218059886598271224426145 := by
  unfold tailWord_3822031
  simp only [CollatzResearch.WordTrace]
  refine ⟨139400922816441912771753947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92933948544294608514502631 139400922816441912771753947)
  ·
    refine ⟨209101384224662869157630921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139400922816441912771753947 209101384224662869157630921)
    ·
      refine ⟨156826038168497151868223191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209101384224662869157630921 156826038168497151868223191)
      ·
        refine ⟨235239057252745727802334787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156826038168497151868223191 235239057252745727802334787)
        ·
          refine ⟨352858585879118591703502181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235239057252745727802334787 352858585879118591703502181)
          ·
            refine ⟨66160984852334735944406659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352858585879118591703502181 66160984852334735944406659)
            ·
              refine ⟨99241477278502103916609989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66160984852334735944406659 99241477278502103916609989)
              ·
                refine ⟨18607776989719144484364373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99241477278502103916609989 18607776989719144484364373)
                ·
                  refine ⟨218059886598271224426145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18607776989719144484364373 218059886598271224426145)
                  ·
                    rfl

theorem cell23_3822031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 8].length) (baseStart_3822031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822031 prefixEnd_3822031 := by exact prefixLift 3822031
  have htrace : WordTrace (prefixWord ++ tailWord_3822031) baseStart_3822031 baseEnd_3822031 := by
    simpa [prefixWord, tailWord_3822031, baseEnd_3822031] using wordTrace_append hprefix tailTrace_3822031
  have hstable : (prefixWord ++ tailWord_3822031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822031).length < 2 ^ (prefixWord ++ tailWord_3822031).sum := by decide
  have hdescent : baseEnd_3822031 < baseStart_3822031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822045 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3822045 : Nat := 118140960795 + 3822045 * 2 ^ 59
def prefixEnd_3822045 : Nat := 4983230072969 + 3 ^ 40 * 3822045 * 2
def baseEnd_3822045 : Nat := 1962546168113603965060241

theorem tailTrace_3822045 : CollatzResearch.WordTrace tailWord_3822045 prefixEnd_3822045 1962546168113603965060241 := by
  unfold tailWord_3822045
  simp only [CollatzResearch.WordTrace]
  refine ⟨139401433438391193162763589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92934288958927462108509059 139401433438391193162763589)
  ·
    refine ⟨26137768769698348718018173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139401433438391193162763589 26137768769698348718018173)
    ·
      refine ⟨9801663288636880769256815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26137768769698348718018173 9801663288636880769256815)
      ·
        refine ⟨14702494932955321153885223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801663288636880769256815 14702494932955321153885223)
        ·
          refine ⟨22053742399432981730827835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14702494932955321153885223 22053742399432981730827835)
          ·
            refine ⟨33080613599149472596241753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22053742399432981730827835 33080613599149472596241753)
            ·
              refine ⟨24810460199362104447181315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33080613599149472596241753 24810460199362104447181315)
              ·
                refine ⟨37215690299043156670771973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24810460199362104447181315 37215690299043156670771973)
                ·
                  refine ⟨6977941931070591875769745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37215690299043156670771973 6977941931070591875769745)
                  ·
                    refine ⟨5233456448302943906827309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6977941931070591875769745 5233456448302943906827309)
                    ·
                      refine ⟨1962546168113603965060241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5233456448302943906827309 1962546168113603965060241)
                      ·
                        rfl

theorem cell23_3822045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3822045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822045 prefixEnd_3822045 := by exact prefixLift 3822045
  have htrace : WordTrace (prefixWord ++ tailWord_3822045) baseStart_3822045 baseEnd_3822045 := by
    simpa [prefixWord, tailWord_3822045, baseEnd_3822045] using wordTrace_append hprefix tailTrace_3822045
  have hstable : (prefixWord ++ tailWord_3822045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822045).length < 2 ^ (prefixWord ++ tailWord_3822045).sum := by decide
  have hdescent : baseEnd_3822045 < baseStart_3822045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822065 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 6]
def baseStart_3822065 : Nat := 118140960795 + 3822065 * 2 ^ 59
def prefixEnd_3822065 : Nat := 4983230072969 + 3 ^ 40 * 3822065 * 2
def baseEnd_3822065 : Nat := 218061826414077098534461

theorem tailTrace_3822065 : CollatzResearch.WordTrace tailWord_3822065 prefixEnd_3822065 218061826414077098534461 := by
  unfold tailWord_3822065
  simp only [CollatzResearch.WordTrace]
  refine ⟨139402162898318736578491649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92934775265545824385661099 139402162898318736578491649)
  ·
    refine ⟨104551622173739052433868737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139402162898318736578491649 104551622173739052433868737)
    ·
      refine ⟨78413716630304289325401553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104551622173739052433868737 78413716630304289325401553)
      ·
        refine ⟨58810287472728216994051165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78413716630304289325401553 58810287472728216994051165)
        ·
          refine ⟨22053857802273081372769187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58810287472728216994051165 22053857802273081372769187)
          ·
            refine ⟨33080786703409622059153781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22053857802273081372769187 33080786703409622059153781)
            ·
              refine ⟨3101323753444652068045667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33080786703409622059153781 3101323753444652068045667)
              ·
                refine ⟨4651985630166978102068501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101323753444652068045667 4651985630166978102068501)
                ·
                  refine ⟨218061826414077098534461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4651985630166978102068501 218061826414077098534461)
                  ·
                    rfl

theorem cell23_3822065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 6].length) (baseStart_3822065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822065 prefixEnd_3822065 := by exact prefixLift 3822065
  have htrace : WordTrace (prefixWord ++ tailWord_3822065) baseStart_3822065 baseEnd_3822065 := by
    simpa [prefixWord, tailWord_3822065, baseEnd_3822065] using wordTrace_append hprefix tailTrace_3822065
  have hstable : (prefixWord ++ tailWord_3822065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822065).length < 2 ^ (prefixWord ++ tailWord_3822065).sum := by decide
  have hdescent : baseEnd_3822065 < baseStart_3822065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822085 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 1, 5, 2]
def baseStart_3822085 : Nat := 118140960795 + 3822085 * 2 ^ 59
def prefixEnd_3822085 : Nat := 4983230072969 + 3 ^ 40 * 3822085 * 2
def baseEnd_3822085 : Nat := 1962566707339783808560057

theorem tailTrace_3822085 : CollatzResearch.WordTrace tailWord_3822085 prefixEnd_3822085 1962566707339783808560057 := by
  unfold tailWord_3822085
  simp only [CollatzResearch.WordTrace]
  refine ⟨139402892358246279994219709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92935261572164186662813139 139402892358246279994219709)
  ·
    refine ⟨52276084634342354997832391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139402892358246279994219709 52276084634342354997832391)
    ·
      refine ⟨78414126951513532496748587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52276084634342354997832391 78414126951513532496748587)
      ·
        refine ⟨117621190427270298745122881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78414126951513532496748587 117621190427270298745122881)
        ·
          refine ⟨88215892820452724058842161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117621190427270298745122881 88215892820452724058842161)
          ·
            refine ⟨66161919615339543044131621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88215892820452724058842161 66161919615339543044131621)
            ·
              refine ⟨12405359927876164320774679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66161919615339543044131621 12405359927876164320774679)
              ·
                refine ⟨18608039891814246481162019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405359927876164320774679 18608039891814246481162019)
                ·
                  refine ⟨27912059837721369721743029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18608039891814246481162019 27912059837721369721743029)
                  ·
                    refine ⟨2616755609786378411413409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27912059837721369721743029 2616755609786378411413409)
                    ·
                      refine ⟨1962566707339783808560057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616755609786378411413409 1962566707339783808560057)
                      ·
                        rfl

theorem cell23_3822085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_3822085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822085 prefixEnd_3822085 := by exact prefixLift 3822085
  have htrace : WordTrace (prefixWord ++ tailWord_3822085) baseStart_3822085 baseEnd_3822085 := by
    simpa [prefixWord, tailWord_3822085, baseEnd_3822085] using wordTrace_append hprefix tailTrace_3822085
  have hstable : (prefixWord ++ tailWord_3822085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822085).length < 2 ^ (prefixWord ++ tailWord_3822085).sum := by decide
  have hdescent : baseEnd_3822085 < baseStart_3822085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822109 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3822109 : Nat := 118140960795 + 3822109 * 2 ^ 59
def prefixEnd_3822109 : Nat := 4983230072969 + 3 ^ 40 * 3822109 * 2
def baseEnd_3822109 : Nat := 1962579030875491714659947

theorem tailTrace_3822109 : CollatzResearch.WordTrace tailWord_3822109 prefixEnd_3822109 1962579030875491714659947 := by
  unfold tailWord_3822109
  simp only [CollatzResearch.WordTrace]
  refine ⟨139403767710159332093093381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92935845140106221395395587 139403767710159332093093381)
  ·
    refine ⟨26138206445654874767455009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139403767710159332093093381 26138206445654874767455009)
    ·
      refine ⟨19603654834241156075591257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26138206445654874767455009 19603654834241156075591257)
      ·
        refine ⟨14702741125680867056693443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19603654834241156075591257 14702741125680867056693443)
        ·
          refine ⟨22054111688521300585040165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14702741125680867056693443 22054111688521300585040165)
          ·
            refine ⟨4135145941597743859695031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22054111688521300585040165 4135145941597743859695031)
            ·
              refine ⟨6202718912396615789542547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135145941597743859695031 6202718912396615789542547)
              ·
                refine ⟨9304078368594923684313821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6202718912396615789542547 9304078368594923684313821)
                ·
                  refine ⟨3489029388223096381617683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9304078368594923684313821 3489029388223096381617683)
                  ·
                    refine ⟨5233544082334644572426525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3489029388223096381617683 5233544082334644572426525)
                    ·
                      refine ⟨1962579030875491714659947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5233544082334644572426525 1962579030875491714659947)
                      ·
                        rfl

theorem cell23_3822109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3822109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822109 prefixEnd_3822109 := by exact prefixLift 3822109
  have htrace : WordTrace (prefixWord ++ tailWord_3822109) baseStart_3822109 baseEnd_3822109 := by
    simpa [prefixWord, tailWord_3822109, baseEnd_3822109] using wordTrace_append hprefix tailTrace_3822109
  have hstable : (prefixWord ++ tailWord_3822109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822109).length < 2 ^ (prefixWord ++ tailWord_3822109).sum := by decide
  have hdescent : baseEnd_3822109 < baseStart_3822109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822116 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 6]
def baseStart_3822116 : Nat := 118140960795 + 3822116 * 2 ^ 59
def prefixEnd_3822116 : Nat := 4983230072969 + 3 ^ 40 * 3822116 * 2
def baseEnd_3822116 : Nat := 218064736137785909696935

theorem tailTrace_3822116 : CollatzResearch.WordTrace tailWord_3822116 prefixEnd_3822116 218064736137785909696935 := by
  unfold tailWord_3822116
  simp only [CollatzResearch.WordTrace]
  refine ⟨69702011510566986144299101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92936015347422648192398801 69702011510566986144299101)
  ·
    refine ⟨26138254316462619804112163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69702011510566986144299101 26138254316462619804112163)
    ·
      refine ⟨39207381474693929706168245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26138254316462619804112163 39207381474693929706168245)
      ·
        refine ⟨3675692013252555909953273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39207381474693929706168245 3675692013252555909953273)
        ·
          refine ⟨2756769009939416932464955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675692013252555909953273 2756769009939416932464955)
          ·
            refine ⟨4135153514909125398697433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756769009939416932464955 4135153514909125398697433)
            ·
              refine ⟨3101365136181844049023075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135153514909125398697433 3101365136181844049023075)
              ·
                refine ⟨4652047704272766073534613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101365136181844049023075 4652047704272766073534613)
                ·
                  refine ⟨218064736137785909696935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4652047704272766073534613 218064736137785909696935)
                  ·
                    rfl

theorem cell23_3822116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_3822116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822116 prefixEnd_3822116 := by exact prefixLift 3822116
  have htrace : WordTrace (prefixWord ++ tailWord_3822116) baseStart_3822116 baseEnd_3822116 := by
    simpa [prefixWord, tailWord_3822116, baseEnd_3822116] using wordTrace_append hprefix tailTrace_3822116
  have hstable : (prefixWord ++ tailWord_3822116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822116).length < 2 ^ (prefixWord ++ tailWord_3822116).sum := by decide
  have hdescent : baseEnd_3822116 < baseStart_3822116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822128 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_3822128 : Nat := 118140960795 + 3822128 * 2 ^ 59
def prefixEnd_3822128 : Nat := 4983230072969 + 3 ^ 40 * 3822128 * 2
def baseEnd_3822128 : Nat := 1962588787007927140322359

theorem tailTrace_3822128 : CollatzResearch.WordTrace tailWord_3822128 prefixEnd_3822128 1962588787007927140322359 := by
  unfold tailWord_3822128
  simp only [CollatzResearch.WordTrace]
  refine ⟨69702230348545249169017519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92936307131393665558690025 69702230348545249169017519)
  ·
    refine ⟨104553345522817873753526279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69702230348545249169017519 104553345522817873753526279)
    ·
      refine ⟨156830018284226810630289419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104553345522817873753526279 156830018284226810630289419)
      ·
        refine ⟨235245027426340215945434129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156830018284226810630289419 235245027426340215945434129)
        ·
          refine ⟨176433770569755161959075597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235245027426340215945434129 176433770569755161959075597)
          ·
            refine ⟨66162663963658185734653349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176433770569755161959075597 66162663963658185734653349)
            ·
              refine ⟨12405499493185909825247503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66162663963658185734653349 12405499493185909825247503)
              ·
                refine ⟨18608249239778864737871255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405499493185909825247503 18608249239778864737871255)
                ·
                  refine ⟨27912373859668297106806883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18608249239778864737871255 27912373859668297106806883)
                  ·
                    refine ⟨41868560789502445660210325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27912373859668297106806883 41868560789502445660210325)
                    ·
                      refine ⟨1962588787007927140322359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41868560789502445660210325 1962588787007927140322359)
                      ·
                        rfl

theorem cell23_3822128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_3822128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822128 prefixEnd_3822128 := by exact prefixLift 3822128
  have htrace : WordTrace (prefixWord ++ tailWord_3822128) baseStart_3822128 baseEnd_3822128 := by
    simpa [prefixWord, tailWord_3822128, baseEnd_3822128] using wordTrace_append hprefix tailTrace_3822128
  have hstable : (prefixWord ++ tailWord_3822128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822128).length < 2 ^ (prefixWord ++ tailWord_3822128).sum := by decide
  have hdescent : baseEnd_3822128 < baseStart_3822128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822135 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_3822135 : Nat := 118140960795 + 3822135 * 2 ^ 59
def prefixEnd_3822135 : Nat := 4983230072969 + 3 ^ 40 * 3822135 * 2
def baseEnd_3822135 : Nat := 1962592381372508612934827

theorem tailTrace_3822135 : CollatzResearch.WordTrace tailWord_3822135 prefixEnd_3822135 1962592381372508612934827 := by
  unfold tailWord_3822135
  simp only [CollatzResearch.WordTrace]
  refine ⟨139404716008065138533539859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92936477338710092355693239 139404716008065138533539859)
  ·
    refine ⟨209107074012097707800309789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139404716008065138533539859 209107074012097707800309789)
    ·
      refine ⟨78415152754536640425116171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209107074012097707800309789 78415152754536640425116171)
      ·
        refine ⟨117622729131804960637674257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78415152754536640425116171 117622729131804960637674257)
        ·
          refine ⟨88217046848853720478255693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117622729131804960637674257 88217046848853720478255693)
          ·
            refine ⟨33081392568320145179345885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88217046848853720478255693 33081392568320145179345885)
            ·
              refine ⟨12405522213120054442254707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33081392568320145179345885 12405522213120054442254707)
              ·
                refine ⟨18608283319680081663382061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405522213120054442254707 18608283319680081663382061)
                ·
                  refine ⟨6978106244880030623768273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18608283319680081663382061 6978106244880030623768273)
                  ·
                    refine ⟨5233579683660022967826205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978106244880030623768273 5233579683660022967826205)
                    ·
                      refine ⟨1962592381372508612934827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5233579683660022967826205 1962592381372508612934827)
                      ·
                        rfl

theorem cell23_3822135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_3822135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822135 prefixEnd_3822135 := by exact prefixLift 3822135
  have htrace : WordTrace (prefixWord ++ tailWord_3822135) baseStart_3822135 baseEnd_3822135 := by
    simpa [prefixWord, tailWord_3822135, baseEnd_3822135] using wordTrace_append hprefix tailTrace_3822135
  have hstable : (prefixWord ++ tailWord_3822135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822135).length < 2 ^ (prefixWord ++ tailWord_3822135).sum := by decide
  have hdescent : baseEnd_3822135 < baseStart_3822135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822138 : List Nat := [3, 1, 1, 1, 3, 3, 2, 9]
def baseStart_3822138 : Nat := 118140960795 + 3822138 * 2 ^ 59
def prefixEnd_3822138 : Nat := 4983230072969 + 3 ^ 40 * 3822138 * 2
def baseEnd_3822138 : Nat := 72688663770906374118419

theorem tailTrace_3822138 : CollatzResearch.WordTrace tailWord_3822138 prefixEnd_3822138 72688663770906374118419 := by
  unfold tailWord_3822138
  simp only [CollatzResearch.WordTrace]
  refine ⟨34851206356763567511474767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92936550284702846697266045 34851206356763567511474767)
  ·
    refine ⟨52276809535145351267212151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34851206356763567511474767 52276809535145351267212151)
    ·
      refine ⟨78415214302718026900818227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52276809535145351267212151 78415214302718026900818227)
      ·
        refine ⟨117622821454077040351227341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78415214302718026900818227 117622821454077040351227341)
        ·
          refine ⟨44108558045278890131710253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117622821454077040351227341 44108558045278890131710253)
          ·
            refine ⟨16540709266979583799391345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44108558045278890131710253 16540709266979583799391345)
            ·
              refine ⟨12405531950234687849543509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16540709266979583799391345 12405531950234687849543509)
              ·
                refine ⟨72688663770906374118419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12405531950234687849543509 72688663770906374118419)
                ·
                  rfl

theorem cell23_3822138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_3822138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822138 prefixEnd_3822138 := by exact prefixLift 3822138
  have htrace : WordTrace (prefixWord ++ tailWord_3822138) baseStart_3822138 baseEnd_3822138 := by
    simpa [prefixWord, tailWord_3822138, baseEnd_3822138] using wordTrace_append hprefix tailTrace_3822138
  have hstable : (prefixWord ++ tailWord_3822138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822138).length < 2 ^ (prefixWord ++ tailWord_3822138).sum := by decide
  have hdescent : baseEnd_3822138 < baseStart_3822138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822145 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3822145 : Nat := 118140960795 + 3822145 * 2 ^ 59
def prefixEnd_3822145 : Nat := 4983230072969 + 3 ^ 40 * 3822145 * 2
def baseEnd_3822145 : Nat := 1962597516179053573809781

theorem tailTrace_3822145 : CollatzResearch.WordTrace tailWord_3822145 prefixEnd_3822145 1962597516179053573809781 := by
  unfold tailWord_3822145
  simp only [CollatzResearch.WordTrace]
  refine ⟨139405080738028910241403889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92936720492019273494269259 139405080738028910241403889)
  ·
    refine ⟨104553810553521682681052917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139405080738028910241403889 104553810553521682681052917)
    ·
      refine ⟨9801919739392657751348711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104553810553521682681052917 9801919739392657751348711)
      ·
        refine ⟨14702879609088986627023067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801919739392657751348711 14702879609088986627023067)
        ·
          refine ⟨22054319413633479940534601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14702879609088986627023067 22054319413633479940534601)
          ·
            refine ⟨16540739560225109955400951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22054319413633479940534601 16540739560225109955400951)
            ·
              refine ⟨24811109340337664933101427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16540739560225109955400951 24811109340337664933101427)
              ·
                refine ⟨37216664010506497399652141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24811109340337664933101427 37216664010506497399652141)
                ·
                  refine ⟨13956249003939936524869553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37216664010506497399652141 13956249003939936524869553)
                  ·
                    refine ⟨10467186752954952393652165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13956249003939936524869553 10467186752954952393652165)
                    ·
                      refine ⟨1962597516179053573809781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10467186752954952393652165 1962597516179053573809781)
                      ·
                        rfl

theorem cell23_3822145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3822145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822145 prefixEnd_3822145 := by exact prefixLift 3822145
  have htrace : WordTrace (prefixWord ++ tailWord_3822145) baseStart_3822145 baseEnd_3822145 := by
    simpa [prefixWord, tailWord_3822145, baseEnd_3822145] using wordTrace_append hprefix tailTrace_3822145
  have hstable : (prefixWord ++ tailWord_3822145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822145).length < 2 ^ (prefixWord ++ tailWord_3822145).sum := by decide
  have hdescent : baseEnd_3822145 < baseStart_3822145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822168 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 2, 7]
def baseStart_3822168 : Nat := 118140960795 + 3822168 * 2 ^ 59
def prefixEnd_3822168 : Nat := 4983230072969 + 3 ^ 40 * 3822168 * 2
def baseEnd_3822168 : Nat := 654203108744702327940725

theorem tailTrace_3822168 : CollatzResearch.WordTrace tailWord_3822168 prefixEnd_3822168 654203108744702327940725 := by
  unfold tailWord_3822168
  simp only [CollatzResearch.WordTrace]
  refine ⟨69702959808472792584745579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92937279744630390112994105 69702959808472792584745579)
  ·
    refine ⟨104554439712709188877118369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69702959808472792584745579 104554439712709188877118369)
    ·
      refine ⟨78415829784531891657838777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104554439712709188877118369 78415829784531891657838777)
      ·
        refine ⟨58811872338398918743379083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78415829784531891657838777 58811872338398918743379083)
        ·
          refine ⟨88217808507598378115068625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58811872338398918743379083 88217808507598378115068625)
          ·
            refine ⟨66163356380698783586301469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88217808507598378115068625 66163356380698783586301469)
            ·
              refine ⟨24811258642762043844863051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66163356380698783586301469 24811258642762043844863051)
              ·
                refine ⟨37216887964143065767294577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24811258642762043844863051 37216887964143065767294577)
                ·
                  refine ⟨27912665973107299325470933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37216887964143065767294577 27912665973107299325470933)
                  ·
                    refine ⟨654203108744702327940725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27912665973107299325470933 654203108744702327940725)
                    ·
                      rfl

theorem cell23_3822168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_3822168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822168 prefixEnd_3822168 := by exact prefixLift 3822168
  have htrace : WordTrace (prefixWord ++ tailWord_3822168) baseStart_3822168 baseEnd_3822168 := by
    simpa [prefixWord, tailWord_3822168, baseEnd_3822168] using wordTrace_append hprefix tailTrace_3822168
  have hstable : (prefixWord ++ tailWord_3822168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822168).length < 2 ^ (prefixWord ++ tailWord_3822168).sum := by decide
  have hdescent : baseEnd_3822168 < baseStart_3822168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822172 : List Nat := [2, 2, 4, 1, 3, 2, 1, 8]
def baseStart_3822172 : Nat := 118140960795 + 3822172 * 2 ^ 59
def prefixEnd_3822172 : Nat := 4983230072969 + 3 ^ 40 * 3822172 * 2
def baseEnd_3822172 : Nat := 72689310376174998821191

theorem tailTrace_3822172 : CollatzResearch.WordTrace tailWord_3822172 prefixEnd_3822172 72689310376174998821191 := by
  unfold tailWord_3822172
  simp only [CollatzResearch.WordTrace]
  refine ⟨69703032754465546926318385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92937377005954062568424513 69703032754465546926318385)
  ·
    refine ⟨52277274565849160194738789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69703032754465546926318385 52277274565849160194738789)
    ·
      refine ⟨9801988981096717536513523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52277274565849160194738789 9801988981096717536513523)
      ·
        refine ⟨14702983471645076304770285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801988981096717536513523 14702983471645076304770285)
        ·
          refine ⟨5513618801866903614288857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14702983471645076304770285 5513618801866903614288857)
          ·
            refine ⟨4135214101400177710716643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5513618801866903614288857 4135214101400177710716643)
            ·
              refine ⟨6202821152100266566074965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135214101400177710716643 6202821152100266566074965)
              ·
                refine ⟨72689310376174998821191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6202821152100266566074965 72689310376174998821191)
                ·
                  rfl

theorem cell23_3822172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 8].length) (baseStart_3822172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822172 prefixEnd_3822172 := by exact prefixLift 3822172
  have htrace : WordTrace (prefixWord ++ tailWord_3822172) baseStart_3822172 baseEnd_3822172 := by
    simpa [prefixWord, tailWord_3822172, baseEnd_3822172] using wordTrace_append hprefix tailTrace_3822172
  have hstable : (prefixWord ++ tailWord_3822172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822172).length < 2 ^ (prefixWord ++ tailWord_3822172).sum := by decide
  have hdescent : baseEnd_3822172 < baseStart_3822172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822209 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_3822209 : Nat := 118140960795 + 3822209 * 2 ^ 59
def prefixEnd_3822209 : Nat := 4983230072969 + 3 ^ 40 * 3822209 * 2
def baseEnd_3822209 : Nat := 1962630378940941323409487

theorem tailTrace_3822209 : CollatzResearch.WordTrace tailWord_3822209 prefixEnd_3822209 1962630378940941323409487 := by
  unfold tailWord_3822209
  simp only [CollatzResearch.WordTrace]
  refine ⟨139407415009797049171733681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92938276673198032781155787 139407415009797049171733681)
  ·
    refine ⟨104555561257347786878800261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139407415009797049171733681 104555561257347786878800261)
    ·
      refine ⟨19604167735752710039775049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104555561257347786878800261 19604167735752710039775049)
      ·
        refine ⟨14703125801814532529831287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19604167735752710039775049 14703125801814532529831287)
        ·
          refine ⟨22054688702721798794746931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14703125801814532529831287 22054688702721798794746931)
          ·
            refine ⟨33082033054082698192120397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22054688702721798794746931 33082033054082698192120397)
            ·
              refine ⟨12405762395281011822045149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33082033054082698192120397 12405762395281011822045149)
              ·
                refine ⟨4652160898230379433266931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12405762395281011822045149 4652160898230379433266931)
                ·
                  refine ⟨6978241347345569149900397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652160898230379433266931 6978241347345569149900397)
                  ·
                    refine ⟨2616840505254588431212649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6978241347345569149900397 2616840505254588431212649)
                    ·
                      refine ⟨1962630378940941323409487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616840505254588431212649 1962630378940941323409487)
                      ·
                        rfl

theorem cell23_3822209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_3822209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822209 prefixEnd_3822209 := by exact prefixLift 3822209
  have htrace : WordTrace (prefixWord ++ tailWord_3822209) baseStart_3822209 baseEnd_3822209 := by
    simpa [prefixWord, tailWord_3822209, baseEnd_3822209] using wordTrace_append hprefix tailTrace_3822209
  have hstable : (prefixWord ++ tailWord_3822209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822209).length < 2 ^ (prefixWord ++ tailWord_3822209).sum := by decide
  have hdescent : baseEnd_3822209 < baseStart_3822209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822210 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3822210 : Nat := 118140960795 + 3822210 * 2 ^ 59
def prefixEnd_3822210 : Nat := 4983230072969 + 3 ^ 40 * 3822210 * 2
def baseEnd_3822210 : Nat := 654210297473865273165661

theorem tailTrace_3822210 : CollatzResearch.WordTrace tailWord_3822210 prefixEnd_3822210 654210297473865273165661 := by
  unfold tailWord_3822210
  simp only [CollatzResearch.WordTrace]
  refine ⟨34851862870698356585630021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92938300988528950895013389 34851862870698356585630021)
  ·
    refine ⟨6534724288255941859805629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34851862870698356585630021 6534724288255941859805629)
    ·
      refine ⟨2450521608095978197427111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6534724288255941859805629 2450521608095978197427111)
      ·
        refine ⟨3675782412143967296140667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450521608095978197427111 3675782412143967296140667)
        ·
          refine ⟨5513673618215950944211001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675782412143967296140667 5513673618215950944211001)
          ·
            refine ⟨4135255213661963208158251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5513673618215950944211001 4135255213661963208158251)
            ·
              refine ⟨6202882820492944812237377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135255213661963208158251 6202882820492944812237377)
              ·
                refine ⟨4652162115369708609178033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6202882820492944812237377 4652162115369708609178033)
                ·
                  refine ⟨3489121586527281456883525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4652162115369708609178033 3489121586527281456883525)
                  ·
                    refine ⟨654210297473865273165661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3489121586527281456883525 654210297473865273165661)
                    ·
                      rfl

theorem cell23_3822210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3822210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822210 prefixEnd_3822210 := by exact prefixLift 3822210
  have htrace : WordTrace (prefixWord ++ tailWord_3822210) baseStart_3822210 baseEnd_3822210 := by
    simpa [prefixWord, tailWord_3822210, baseEnd_3822210] using wordTrace_append hprefix tailTrace_3822210
  have hstable : (prefixWord ++ tailWord_3822210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822210).length < 2 ^ (prefixWord ++ tailWord_3822210).sum := by decide
  have hdescent : baseEnd_3822210 < baseStart_3822210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822290 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_3822290 : Nat := 118140960795 + 3822290 * 2 ^ 59
def prefixEnd_3822290 : Nat := 4983230072969 + 3 ^ 40 * 3822290 * 2
def baseEnd_3822290 : Nat := 1962671970873955506496615

theorem tailTrace_3822290 : CollatzResearch.WordTrace tailWord_3822290 prefixEnd_3822290 1962671970873955506496615 := by
  unfold tailWord_3822290
  simp only [CollatzResearch.WordTrace]
  refine ⟨34852592330625900001358081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92940246215002400003621549 34852592330625900001358081)
  ·
    refine ⟨26139444247969425001018561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34852592330625900001358081 26139444247969425001018561)
    ·
      refine ⟨19604583185977068750763921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26139444247969425001018561 19604583185977068750763921)
      ·
        refine ⟨14703437389482801563072941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19604583185977068750763921 14703437389482801563072941)
        ·
          refine ⟨5513789021056050586152353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14703437389482801563072941 5513789021056050586152353)
          ·
            refine ⟨4135341765792037939614265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5513789021056050586152353 4135341765792037939614265)
            ·
              refine ⟨3101506324344028454710699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135341765792037939614265 3101506324344028454710699)
              ·
                refine ⟨4652259486516042682066049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101506324344028454710699 4652259486516042682066049)
                ·
                  refine ⟨3489194614887032011549537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4652259486516042682066049 3489194614887032011549537)
                  ·
                    refine ⟨2616895961165274008662153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3489194614887032011549537 2616895961165274008662153)
                    ·
                      refine ⟨1962671970873955506496615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2616895961165274008662153 1962671970873955506496615)
                      ·
                        rfl

theorem cell23_3822290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_3822290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822290 prefixEnd_3822290 := by exact prefixLift 3822290
  have htrace : WordTrace (prefixWord ++ tailWord_3822290) baseStart_3822290 baseEnd_3822290 := by
    simpa [prefixWord, tailWord_3822290, baseEnd_3822290] using wordTrace_append hprefix tailTrace_3822290
  have hstable : (prefixWord ++ tailWord_3822290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822290).length < 2 ^ (prefixWord ++ tailWord_3822290).sum := by decide
  have hdescent : baseEnd_3822290 < baseStart_3822290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822432 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_3822432 : Nat := 118140960795 + 3822432 * 2 ^ 59
def prefixEnd_3822432 : Nat := 4983230072969 + 3 ^ 40 * 3822432 * 2
def baseEnd_3822432 : Nat := 1962744885126893950920961

theorem tailTrace_3822432 : CollatzResearch.WordTrace tailWord_3822432 prefixEnd_3822432 1962744885126893950920961 := by
  unfold tailWord_3822432
  simp only [CollatzResearch.WordTrace]
  refine ⟨69707774243994579128550775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92943698991992772171401033 69707774243994579128550775)
  ·
    refine ⟨104561661365991868692826163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69707774243994579128550775 104561661365991868692826163)
    ·
      refine ⟨156842492048987803039239245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104561661365991868692826163 156842492048987803039239245)
      ·
        refine ⟨58815934518370426139714717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156842492048987803039239245 58815934518370426139714717)
        ·
          refine ⟨22055975444388909802393019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58815934518370426139714717 22055975444388909802393019)
          ·
            refine ⟨33083963166583364703589529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22055975444388909802393019 33083963166583364703589529)
            ·
              refine ⟨24812972374937523527692147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33083963166583364703589529 24812972374937523527692147)
              ·
                refine ⟨37219458562406285291538221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24812972374937523527692147 37219458562406285291538221)
                ·
                  refine ⟨13957296960902356984326833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37219458562406285291538221 13957296960902356984326833)
                  ·
                    refine ⟨10467972720676767738245125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13957296960902356984326833 10467972720676767738245125)
                    ·
                      refine ⟨1962744885126893950920961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10467972720676767738245125 1962744885126893950920961)
                      ·
                        rfl

theorem cell23_3822432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_3822432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822432 prefixEnd_3822432 := by exact prefixLift 3822432
  have htrace : WordTrace (prefixWord ++ tailWord_3822432) baseStart_3822432 baseEnd_3822432 := by
    simpa [prefixWord, tailWord_3822432, baseEnd_3822432] using wordTrace_append hprefix tailTrace_3822432
  have hstable : (prefixWord ++ tailWord_3822432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822432).length < 2 ^ (prefixWord ++ tailWord_3822432).sum := by decide
  have hdescent : baseEnd_3822432 < baseStart_3822432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822439 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_3822439 : Nat := 118140960795 + 3822439 * 2 ^ 59
def prefixEnd_3822439 : Nat := 4983230072969 + 3 ^ 40 * 3822439 * 2
def baseEnd_3822439 : Nat := 1962748479491475423533429

theorem tailTrace_3822439 : CollatzResearch.WordTrace tailWord_3822439 prefixEnd_3822439 1962748479491475423533429 := by
  unfold tailWord_3822439
  simp only [CollatzResearch.WordTrace]
  refine ⟨139415803798963798452606371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92943869199309198968404247 139415803798963798452606371)
  ·
    refine ⟨209123705698445697678909557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139415803798963798452606371 209123705698445697678909557)
    ·
      refine ⟨19605347409229284157397771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209123705698445697678909557 19605347409229284157397771)
      ·
        refine ⟨29408021113843926236096657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19605347409229284157397771 29408021113843926236096657)
        ·
          refine ⟨22056015835382944677072493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29408021113843926236096657 22056015835382944677072493)
          ·
            refine ⟨8271005938268604253902185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22056015835382944677072493 8271005938268604253902185)
            ·
              refine ⟨6203254453701453190426639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271005938268604253902185 6203254453701453190426639)
              ·
                refine ⟨9304881680552179785639959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203254453701453190426639 9304881680552179785639959)
                ·
                  refine ⟨13957322520828269678459939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9304881680552179785639959 13957322520828269678459939)
                  ·
                    refine ⟨20935983781242404517689909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13957322520828269678459939 20935983781242404517689909)
                    ·
                      refine ⟨1962748479491475423533429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20935983781242404517689909 1962748479491475423533429)
                      ·
                        rfl

theorem cell23_3822439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_3822439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822439 prefixEnd_3822439 := by exact prefixLift 3822439
  have htrace : WordTrace (prefixWord ++ tailWord_3822439) baseStart_3822439 baseEnd_3822439 := by
    simpa [prefixWord, tailWord_3822439, baseEnd_3822439] using wordTrace_append hprefix tailTrace_3822439
  have hstable : (prefixWord ++ tailWord_3822439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822439).length < 2 ^ (prefixWord ++ tailWord_3822439).sum := by decide
  have hdescent : baseEnd_3822439 < baseStart_3822439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822453 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_3822453 : Nat := 118140960795 + 3822453 * 2 ^ 59
def prefixEnd_3822453 : Nat := 4983230072969 + 3 ^ 40 * 3822453 * 2
def baseEnd_3822453 : Nat := 1962755668220638368758365

theorem tailTrace_3822453 : CollatzResearch.WordTrace tailWord_3822453 prefixEnd_3822453 1962755668220638368758365 := by
  unfold tailWord_3822453
  simp only [CollatzResearch.WordTrace]
  refine ⟨139416314420913078843616013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92944209613942052562410675 139416314420913078843616013)
  ·
    refine ⟨52281117907842404566356005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139416314420913078843616013 52281117907842404566356005)
    ·
      refine ⟨9802709607720450856191751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52281117907842404566356005 9802709607720450856191751)
      ·
        refine ⟨14704064411580676284287627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9802709607720450856191751 14704064411580676284287627)
        ·
          refine ⟨22056096617371014426431441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14704064411580676284287627 22056096617371014426431441)
          ·
            refine ⟨16542072463028260819823581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22056096617371014426431441 16542072463028260819823581)
            ·
              refine ⟨6203277173635597807433843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16542072463028260819823581 6203277173635597807433843)
              ·
                refine ⟨9304915760453396711150765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203277173635597807433843 9304915760453396711150765)
                ·
                  refine ⟨3489343410170023766681537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9304915760453396711150765 3489343410170023766681537)
                  ·
                    refine ⟨2617007557627517825011153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3489343410170023766681537 2617007557627517825011153)
                    ·
                      refine ⟨1962755668220638368758365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617007557627517825011153 1962755668220638368758365)
                      ·
                        rfl

theorem cell23_3822453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_3822453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822453 prefixEnd_3822453 := by exact prefixLift 3822453
  have htrace : WordTrace (prefixWord ++ tailWord_3822453) baseStart_3822453 baseEnd_3822453 := by
    simpa [prefixWord, tailWord_3822453, baseEnd_3822453] using wordTrace_append hprefix tailTrace_3822453
  have hstable : (prefixWord ++ tailWord_3822453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822453).length < 2 ^ (prefixWord ++ tailWord_3822453).sum := by decide
  have hdescent : baseEnd_3822453 < baseStart_3822453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822496 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 1, 3, 2]
def baseStart_3822496 : Nat := 118140960795 + 3822496 * 2 ^ 59
def prefixEnd_3822496 : Nat := 4983230072969 + 3 ^ 40 * 3822496 * 2
def baseEnd_3822496 : Nat := 1962777747888781700520667

theorem tailTrace_3822496 : CollatzResearch.WordTrace tailWord_3822496 prefixEnd_3822496 1962777747888781700520667 := by
  unfold tailWord_3822496
  simp only [CollatzResearch.WordTrace]
  refine ⟨69708941379878648593715671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92945255173171531458287561 69708941379878648593715671)
  ·
    refine ⟨104563412069817972890573507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69708941379878648593715671 104563412069817972890573507)
    ·
      refine ⟨156845118104726959335860261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104563412069817972890573507 156845118104726959335860261)
      ·
        refine ⟨29408459644636304875473799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156845118104726959335860261 29408459644636304875473799)
        ·
          refine ⟨44112689466954457313210699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29408459644636304875473799 44112689466954457313210699)
          ·
            refine ⟨66169034200431685969816049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44112689466954457313210699 66169034200431685969816049)
            ·
              refine ⟨49626775650323764477362037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66169034200431685969816049 49626775650323764477362037)
              ·
                refine ⟨4652510217217852919752691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49626775650323764477362037 4652510217217852919752691)
                ·
                  refine ⟨6978765325826779379629037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652510217217852919752691 6978765325826779379629037)
                  ·
                    refine ⟨2617036997185042267360889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6978765325826779379629037 2617036997185042267360889)
                    ·
                      refine ⟨1962777747888781700520667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617036997185042267360889 1962777747888781700520667)
                      ·
                        rfl

theorem cell23_3822496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_3822496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822496 prefixEnd_3822496 := by exact prefixLift 3822496
  have htrace : WordTrace (prefixWord ++ tailWord_3822496) baseStart_3822496 baseEnd_3822496 := by
    simpa [prefixWord, tailWord_3822496, baseEnd_3822496] using wordTrace_append hprefix tailTrace_3822496
  have hstable : (prefixWord ++ tailWord_3822496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822496).length < 2 ^ (prefixWord ++ tailWord_3822496).sum := by decide
  have hdescent : baseEnd_3822496 < baseStart_3822496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822541 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3822541 : Nat := 118140960795 + 3822541 * 2 ^ 59
def prefixEnd_3822541 : Nat := 4983230072969 + 3 ^ 40 * 3822541 * 2
def baseEnd_3822541 : Nat := 1962800854518234024457961

theorem tailTrace_3822541 : CollatzResearch.WordTrace tailWord_3822541 prefixEnd_3822541 1962800854518234024457961 := by
  unfold tailWord_3822541
  simp only [CollatzResearch.WordTrace]
  refine ⟨139419524044594269872819477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92946349363062846581879651 139419524044594269872819477)
  ·
    refine ⟨6535290189590356400288413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139419524044594269872819477 6535290189590356400288413)
    ·
      refine ⟨2450733821096383650108155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6535290189590356400288413 2450733821096383650108155)
      ·
        refine ⟨3676100731644575475162233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450733821096383650108155 3676100731644575475162233)
        ·
          refine ⟨2757075548733431606371675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3676100731644575475162233 2757075548733431606371675)
          ·
            refine ⟨4135613323100147409557513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757075548733431606371675 4135613323100147409557513)
            ·
              refine ⟨3101709992325110557168135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135613323100147409557513 3101709992325110557168135)
              ·
                refine ⟨4652564988487665835752203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101709992325110557168135 4652564988487665835752203)
                ·
                  refine ⟨6978847482731498753628305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652564988487665835752203 6978847482731498753628305)
                  ·
                    refine ⟨5234135612048624065221229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978847482731498753628305 5234135612048624065221229)
                    ·
                      refine ⟨1962800854518234024457961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5234135612048624065221229 1962800854518234024457961)
                      ·
                        rfl

theorem cell23_3822541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3822541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822541 prefixEnd_3822541 := by exact prefixLift 3822541
  have htrace : WordTrace (prefixWord ++ tailWord_3822541) baseStart_3822541 baseEnd_3822541 := by
    simpa [prefixWord, tailWord_3822541, baseEnd_3822541] using wordTrace_append hprefix tailTrace_3822541
  have hstable : (prefixWord ++ tailWord_3822541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822541).length < 2 ^ (prefixWord ++ tailWord_3822541).sum := by decide
  have hdescent : baseEnd_3822541 < baseStart_3822541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822599 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3822599 : Nat := 118140960795 + 3822599 * 2 ^ 59
def prefixEnd_3822599 : Nat := 4983230072969 + 3 ^ 40 * 3822599 * 2
def baseEnd_3822599 : Nat := 1962830636396194797532693

theorem tailTrace_3822599 : CollatzResearch.WordTrace tailWord_3822599 prefixEnd_3822599 1962830636396194797532693 := by
  unfold tailWord_3822599
  simp only [CollatzResearch.WordTrace]
  refine ⟨139421639478384145778430851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92947759652256097185620567 139421639478384145778430851)
  ·
    refine ⟨209132459217576218667646277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139421639478384145778430851 209132459217576218667646277)
    ·
      refine ⟨39212336103295541000183677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209132459217576218667646277 39212336103295541000183677)
      ·
        refine ⟨14704626038735827875068879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39212336103295541000183677 14704626038735827875068879)
        ·
          refine ⟨22056939058103741812603319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14704626038735827875068879 22056939058103741812603319)
          ·
            refine ⟨33085408587155612718904979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22056939058103741812603319 33085408587155612718904979)
            ·
              refine ⟨49628112880733419078357469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33085408587155612718904979 49628112880733419078357469)
              ·
                refine ⟨18610542330275032154384051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49628112880733419078357469 18610542330275032154384051)
                ·
                  refine ⟨27915813495412548231576077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18610542330275032154384051 27915813495412548231576077)
                  ·
                    refine ⟨10468430060779705586841029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27915813495412548231576077 10468430060779705586841029)
                    ·
                      refine ⟨1962830636396194797532693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10468430060779705586841029 1962830636396194797532693)
                      ·
                        rfl

theorem cell23_3822599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3822599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822599 prefixEnd_3822599 := by exact prefixLift 3822599
  have htrace : WordTrace (prefixWord ++ tailWord_3822599) baseStart_3822599 baseEnd_3822599 := by
    simpa [prefixWord, tailWord_3822599, baseEnd_3822599] using wordTrace_append hprefix tailTrace_3822599
  have hstable : (prefixWord ++ tailWord_3822599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822599).length < 2 ^ (prefixWord ++ tailWord_3822599).sum := by decide
  have hdescent : baseEnd_3822599 < baseStart_3822599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822609 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 5, 4]
def baseStart_3822609 : Nat := 118140960795 + 3822609 * 2 ^ 59
def prefixEnd_3822609 : Nat := 4983230072969 + 3 ^ 40 * 3822609 * 2
def baseEnd_3822609 : Nat := 654278590400913252802549

theorem tailTrace_3822609 : CollatzResearch.WordTrace tailWord_3822609 prefixEnd_3822609 654278590400913252802549 := by
  unfold tailWord_3822609
  simp only [CollatzResearch.WordTrace]
  refine ⟨139422004208347917486294881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92948002805565278324196587 139422004208347917486294881)
  ·
    refine ⟨104566503156260938114721161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139422004208347917486294881 104566503156260938114721161)
    ·
      refine ⟨78424877367195703586040871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104566503156260938114721161 78424877367195703586040871)
      ·
        refine ⟨117637316050793555379061307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78424877367195703586040871 117637316050793555379061307)
        ·
          refine ⟨176455974076190333068591961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117637316050793555379061307 176455974076190333068591961)
          ·
            refine ⟨132341980557142749801443971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176455974076190333068591961 132341980557142749801443971)
            ·
              refine ⟨198512970835714124702165957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132341980557142749801443971 198512970835714124702165957)
              ·
                refine ⟨37221182031696398381656117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198512970835714124702165957 37221182031696398381656117)
                ·
                  refine ⟨3489485815471537348280261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37221182031696398381656117 3489485815471537348280261)
                  ·
                    refine ⟨654278590400913252802549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3489485815471537348280261 654278590400913252802549)
                    ·
                      rfl

theorem cell23_3822609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_3822609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822609 prefixEnd_3822609 := by exact prefixLift 3822609
  have htrace : WordTrace (prefixWord ++ tailWord_3822609) baseStart_3822609 baseEnd_3822609 := by
    simpa [prefixWord, tailWord_3822609, baseEnd_3822609] using wordTrace_append hprefix tailTrace_3822609
  have hstable : (prefixWord ++ tailWord_3822609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822609).length < 2 ^ (prefixWord ++ tailWord_3822609).sum := by decide
  have hdescent : baseEnd_3822609 < baseStart_3822609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822616 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3822616 : Nat := 118140960795 + 3822616 * 2 ^ 59
def prefixEnd_3822616 : Nat := 4983230072969 + 3 ^ 40 * 3822616 * 2
def baseEnd_3822616 : Nat := 1962839365567321231020115

theorem tailTrace_3822616 : CollatzResearch.WordTrace tailWord_3822616 prefixEnd_3822616 1962839365567321231020115 := by
  unfold tailWord_3822616
  simp only [CollatzResearch.WordTrace]
  refine ⟨69711129759661278840899851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92948173012881705121199801 69711129759661278840899851)
  ·
    refine ⟨104566694639491918261349777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69711129759661278840899851 104566694639491918261349777)
    ·
      refine ⟨78425020979618938696012333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104566694639491918261349777 78425020979618938696012333)
      ·
        refine ⟨29409382867357102011004625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78425020979618938696012333 29409382867357102011004625)
        ·
          refine ⟨22057037150517826508253469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29409382867357102011004625 22057037150517826508253469)
          ·
            refine ⟨8271388931444184940595051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22057037150517826508253469 8271388931444184940595051)
            ·
              refine ⟨12407083397166277410892577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271388931444184940595051 12407083397166277410892577)
              ·
                refine ⟨9305312547874708058169433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12407083397166277410892577 9305312547874708058169433)
                ·
                  refine ⟨6978984410906031043627075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305312547874708058169433 6978984410906031043627075)
                  ·
                    refine ⟨10468476616359046565440613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6978984410906031043627075 10468476616359046565440613)
                    ·
                      refine ⟨1962839365567321231020115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10468476616359046565440613 1962839365567321231020115)
                      ·
                        rfl

theorem cell23_3822616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3822616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822616 prefixEnd_3822616 := by exact prefixLift 3822616
  have htrace : WordTrace (prefixWord ++ tailWord_3822616) baseStart_3822616 baseEnd_3822616 := by
    simpa [prefixWord, tailWord_3822616, baseEnd_3822616] using wordTrace_append hprefix tailTrace_3822616
  have hstable : (prefixWord ++ tailWord_3822616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822616).length < 2 ^ (prefixWord ++ tailWord_3822616).sum := by decide
  have hdescent : baseEnd_3822616 < baseStart_3822616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822653 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3822653 : Nat := 118140960795 + 3822653 * 2 ^ 59
def prefixEnd_3822653 : Nat := 4983230072969 + 3 ^ 40 * 3822653 * 2
def baseEnd_3822653 : Nat := 1962858364351537586257445

theorem tailTrace_3822653 : CollatzResearch.WordTrace tailWord_3822653 prefixEnd_3822653 1962858364351537586257445 := by
  unfold tailWord_3822653
  simp only [CollatzResearch.WordTrace]
  refine ⟨139423609020188513000896613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92949072680125675333931075 139423609020188513000896613)
  ·
    refine ⟨26141926691285346187668115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139423609020188513000896613 26141926691285346187668115)
    ·
      refine ⟨39212890036928019281502173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26141926691285346187668115 39212890036928019281502173)
      ·
        refine ⟨14704833763848007230563315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39212890036928019281502173 14704833763848007230563315)
        ·
          refine ⟨22057250645772010845844973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14704833763848007230563315 22057250645772010845844973)
          ·
            refine ⟨8271468992164504067191865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22057250645772010845844973 8271468992164504067191865)
            ·
              refine ⟨6203601744123378050393899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271468992164504067191865 6203601744123378050393899)
              ·
                refine ⟨9305402616185067075590849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203601744123378050393899 9305402616185067075590849)
                ·
                  refine ⟨6979051962138800306693137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305402616185067075590849 6979051962138800306693137)
                  ·
                    refine ⟨5234288971604100230019853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6979051962138800306693137 5234288971604100230019853)
                    ·
                      refine ⟨1962858364351537586257445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5234288971604100230019853 1962858364351537586257445)
                      ·
                        rfl

theorem cell23_3822653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3822653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822653 prefixEnd_3822653 := by exact prefixLift 3822653
  have htrace : WordTrace (prefixWord ++ tailWord_3822653) baseStart_3822653 baseEnd_3822653 := by
    simpa [prefixWord, tailWord_3822653, baseEnd_3822653] using wordTrace_append hprefix tailTrace_3822653
  have hstable : (prefixWord ++ tailWord_3822653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822653).length < 2 ^ (prefixWord ++ tailWord_3822653).sum := by decide
  have hdescent : baseEnd_3822653 < baseStart_3822653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822706 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3822706 : Nat := 118140960795 + 3822706 * 2 ^ 59
def prefixEnd_3822706 : Nat := 4983230072969 + 3 ^ 40 * 3822706 * 2
def baseEnd_3822706 : Nat := 1962885578826225878894701

theorem tailTrace_3822706 : CollatzResearch.WordTrace tailWord_3822706 prefixEnd_3822706 1962885578826225878894701 := by
  unfold tailWord_3822706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34856385522249125763143993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92950361392664335368383981 34856385522249125763143993)
  ·
    refine ⟨26142289141686844322357995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34856385522249125763143993 26142289141686844322357995)
    ·
      refine ⟨39213433712530266483536993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26142289141686844322357995 39213433712530266483536993)
      ·
        refine ⟨29410075284397699862652745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39213433712530266483536993 29410075284397699862652745)
        ·
          refine ⟨22057556463298274896989559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29410075284397699862652745 22057556463298274896989559)
          ·
            refine ⟨33086334694947412345484339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22057556463298274896989559 33086334694947412345484339)
            ·
              refine ⟨49629502042421118518226509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33086334694947412345484339 49629502042421118518226509)
              ·
                refine ⟨18611063265907919444334941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49629502042421118518226509 18611063265907919444334941)
                ·
                  refine ⟨6979148724715469791625603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18611063265907919444334941 6979148724715469791625603)
                  ·
                    refine ⟨10468723087073204687438405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979148724715469791625603 10468723087073204687438405)
                    ·
                      refine ⟨1962885578826225878894701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10468723087073204687438405 1962885578826225878894701)
                      ·
                        rfl

theorem cell23_3822706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3822706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822706 prefixEnd_3822706 := by exact prefixLift 3822706
  have htrace : WordTrace (prefixWord ++ tailWord_3822706) baseStart_3822706 baseEnd_3822706 := by
    simpa [prefixWord, tailWord_3822706, baseEnd_3822706] using wordTrace_append hprefix tailTrace_3822706
  have hstable : (prefixWord ++ tailWord_3822706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822706).length < 2 ^ (prefixWord ++ tailWord_3822706).sum := by decide
  have hdescent : baseEnd_3822706 < baseStart_3822706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822716 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_3822716 : Nat := 118140960795 + 3822716 * 2 ^ 59
def prefixEnd_3822716 : Nat := 4983230072969 + 3 ^ 40 * 3822716 * 2
def baseEnd_3822716 : Nat := 654296904544256946589885

theorem tailTrace_3822716 : CollatzResearch.WordTrace tailWord_3822716 prefixEnd_3822716 654296904544256946589885 := by
  unfold tailWord_3822716
  simp only [CollatzResearch.WordTrace]
  refine ⟨69712953409480137380220001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92950604545973516506960001 69712953409480137380220001)
  ·
    refine ⟨52284715057110103035165001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69712953409480137380220001 52284715057110103035165001)
    ·
      refine ⟨39213536292832577276373751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52284715057110103035165001 39213536292832577276373751)
      ·
        refine ⟨58820304439248865914560627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39213536292832577276373751 58820304439248865914560627)
        ·
          refine ⟨88230456658873298871840941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58820304439248865914560627 88230456658873298871840941)
          ·
            refine ⟨33086421247077487076940353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88230456658873298871840941 33086421247077487076940353)
            ·
              refine ⟨24814815935308115307705265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33086421247077487076940353 24814815935308115307705265)
              ·
                refine ⟨18611111951481086480778949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24814815935308115307705265 18611111951481086480778949)
                ·
                  refine ⟨3489583490902703715146053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18611111951481086480778949 3489583490902703715146053)
                  ·
                    refine ⟨654296904544256946589885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3489583490902703715146053 654296904544256946589885)
                    ·
                      rfl

theorem cell23_3822716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_3822716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822716 prefixEnd_3822716 := by exact prefixLift 3822716
  have htrace : WordTrace (prefixWord ++ tailWord_3822716) baseStart_3822716 baseEnd_3822716 := by
    simpa [prefixWord, tailWord_3822716, baseEnd_3822716] using wordTrace_append hprefix tailTrace_3822716
  have hstable : (prefixWord ++ tailWord_3822716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822716).length < 2 ^ (prefixWord ++ tailWord_3822716).sum := by decide
  have hdescent : baseEnd_3822716 < baseStart_3822716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822723 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 5, 2, 2]
def baseStart_3822723 : Nat := 118140960795 + 3822723 * 2 ^ 59
def prefixEnd_3822723 : Nat := 4983230072969 + 3 ^ 40 * 3822723 * 2
def baseEnd_3822723 : Nat := 1962894307997352312382123

theorem tailTrace_3822723 : CollatzResearch.WordTrace tailWord_3822723 prefixEnd_3822723 1962894307997352312382123 := by
  unfold tailWord_3822723
  simp only [CollatzResearch.WordTrace]
  refine ⟨139426162129934914955944823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92950774753289943303963215 139426162129934914955944823)
  ·
    refine ⟨209139243194902372433917235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139426162129934914955944823 209139243194902372433917235)
    ·
      refine ⟨313708864792353558650875853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209139243194902372433917235 313708864792353558650875853)
      ·
        refine ⟨117640824297132584494078445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313708864792353558650875853 117640824297132584494078445)
        ·
          refine ⟨44115309111424719185279417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117640824297132584494078445 44115309111424719185279417)
          ·
            refine ⟨33086481833568539388959563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44115309111424719185279417 33086481833568539388959563)
            ·
              refine ⟨49629722750352809083439345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33086481833568539388959563 49629722750352809083439345)
              ·
                refine ⟨37222292062764606812579509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49629722750352809083439345 37222292062764606812579509)
                ·
                  refine ⟨3489589880884181888679329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37222292062764606812579509 3489589880884181888679329)
                  ·
                    refine ⟨2617192410663136416509497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3489589880884181888679329 2617192410663136416509497)
                    ·
                      refine ⟨1962894307997352312382123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617192410663136416509497 1962894307997352312382123)
                      ·
                        rfl

theorem cell23_3822723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_3822723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822723 prefixEnd_3822723 := by exact prefixLift 3822723
  have htrace : WordTrace (prefixWord ++ tailWord_3822723) baseStart_3822723 baseEnd_3822723 := by
    simpa [prefixWord, tailWord_3822723, baseEnd_3822723] using wordTrace_append hprefix tailTrace_3822723
  have hstable : (prefixWord ++ tailWord_3822723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822723).length < 2 ^ (prefixWord ++ tailWord_3822723).sum := by decide
  have hdescent : baseEnd_3822723 < baseStart_3822723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822729 : List Nat := [1, 2, 1, 1, 4, 4, 10]
def baseStart_3822729 : Nat := 118140960795 + 3822729 * 2 ^ 59
def prefixEnd_3822729 : Nat := 4983230072969 + 3 ^ 40 * 3822729 * 2
def baseEnd_3822729 : Nat := 24233301097299744307495

theorem tailTrace_3822729 : CollatzResearch.WordTrace tailWord_3822729 prefixEnd_3822729 24233301097299744307495 := by
  unfold tailWord_3822729
  simp only [CollatzResearch.WordTrace]
  refine ⟨139426380967913177980663241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92950920645275451987108827 139426380967913177980663241)
  ·
    refine ⟨104569785725934883485497431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139426380967913177980663241 104569785725934883485497431)
    ·
      refine ⟨156854678588902325228246147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104569785725934883485497431 156854678588902325228246147)
      ·
        refine ⟨235282017883353487842369221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156854678588902325228246147 235282017883353487842369221)
        ·
          refine ⟨44115378353128778970444229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235282017883353487842369221 44115378353128778970444229)
          ·
            refine ⟨8271633441211646056958293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44115378353128778970444229 8271633441211646056958293)
            ·
              refine ⟨24233301097299744307495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8271633441211646056958293 24233301097299744307495)
              ·
                rfl

theorem cell23_3822729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 10].length) (baseStart_3822729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822729 prefixEnd_3822729 := by exact prefixLift 3822729
  have htrace : WordTrace (prefixWord ++ tailWord_3822729) baseStart_3822729 baseEnd_3822729 := by
    simpa [prefixWord, tailWord_3822729, baseEnd_3822729] using wordTrace_append hprefix tailTrace_3822729
  have hstable : (prefixWord ++ tailWord_3822729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822729).length < 2 ^ (prefixWord ++ tailWord_3822729).sum := by decide
  have hdescent : baseEnd_3822729 < baseStart_3822729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822750 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3822750 : Nat := 118140960795 + 3822750 * 2 ^ 59
def prefixEnd_3822750 : Nat := 4983230072969 + 3 ^ 40 * 3822750 * 2
def baseEnd_3822750 : Nat := 654302723991674568914833

theorem tailTrace_3822750 : CollatzResearch.WordTrace tailWord_3822750 prefixEnd_3822750 654302723991674568914833 := by
  unfold tailWord_3822750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17428393362604637320897213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92951431267224732378118469 17428393362604637320897213)
  ·
    refine ⟨6535647510976738995336455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17428393362604637320897213 6535647510976738995336455)
    ·
      refine ⟨9803471266465108493004683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6535647510976738995336455 9803471266465108493004683)
      ·
        refine ⟨14705206899697662739507025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9803471266465108493004683 14705206899697662739507025)
        ·
          refine ⟨11028905174773247054630269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14705206899697662739507025 11028905174773247054630269)
          ·
            refine ⟨4135839440539967645486351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11028905174773247054630269 4135839440539967645486351)
            ·
              refine ⟨6203759160809951468229527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135839440539967645486351 6203759160809951468229527)
              ·
                refine ⟨9305638741214927202344291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203759160809951468229527 9305638741214927202344291)
                ·
                  refine ⟨13958458111822390803516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9305638741214927202344291 13958458111822390803516437)
                  ·
                    refine ⟨654302723991674568914833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13958458111822390803516437 654302723991674568914833)
                    ·
                      rfl

theorem cell23_3822750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3822750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822750 prefixEnd_3822750 := by exact prefixLift 3822750
  have htrace : WordTrace (prefixWord ++ tailWord_3822750) baseStart_3822750 baseEnd_3822750 := by
    simpa [prefixWord, tailWord_3822750, baseEnd_3822750] using wordTrace_append hprefix tailTrace_3822750
  have hstable : (prefixWord ++ tailWord_3822750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822750).length < 2 ^ (prefixWord ++ tailWord_3822750).sum := by decide
  have hdescent : baseEnd_3822750 < baseStart_3822750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822816 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_3822816 : Nat := 118140960795 + 3822816 * 2 ^ 59
def prefixEnd_3822816 : Nat := 4983230072969 + 3 ^ 40 * 3822816 * 2
def baseEnd_3822816 : Nat := 1962942061698220448519195

theorem tailTrace_3822816 : CollatzResearch.WordTrace tailWord_3822816 prefixEnd_3822816 1962942061698220448519195 := by
  unfold tailWord_3822816
  simp only [CollatzResearch.WordTrace]
  refine ⟨69714777059298995919540151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92953036079065327892720201 69714777059298995919540151)
  ·
    refine ⟨104572165588948493879310227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69714777059298995919540151 104572165588948493879310227)
    ·
      refine ⟨156858248383422740818965341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104572165588948493879310227 156858248383422740818965341)
      ·
        refine ⟨58821843143783527807112003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156858248383422740818965341 58821843143783527807112003)
        ·
          refine ⟨88232764715675291710668005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58821843143783527807112003 88232764715675291710668005)
          ·
            refine ⟨16543643384189117195750251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88232764715675291710668005 16543643384189117195750251)
            ·
              refine ⟨24815465076283675793625377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16543643384189117195750251 24815465076283675793625377)
              ·
                refine ⟨18611598807212756845219033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24815465076283675793625377 18611598807212756845219033)
                ·
                  refine ⟨13958699105409567633914275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18611598807212756845219033 13958699105409567633914275)
                  ·
                    refine ⟨20938048658114351450871413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13958699105409567633914275 20938048658114351450871413)
                    ·
                      refine ⟨1962942061698220448519195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20938048658114351450871413 1962942061698220448519195)
                      ·
                        rfl

theorem cell23_3822816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_3822816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822816 prefixEnd_3822816 := by exact prefixLift 3822816
  have htrace : WordTrace (prefixWord ++ tailWord_3822816) baseStart_3822816 baseEnd_3822816 := by
    simpa [prefixWord, tailWord_3822816, baseEnd_3822816] using wordTrace_append hprefix tailTrace_3822816
  have hstable : (prefixWord ++ tailWord_3822816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822816).length < 2 ^ (prefixWord ++ tailWord_3822816).sum := by decide
  have hdescent : baseEnd_3822816 < baseStart_3822816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822817 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_3822817 : Nat := 118140960795 + 3822817 * 2 ^ 59
def prefixEnd_3822817 : Nat := 4983230072969 + 3 ^ 40 * 3822817 * 2
def baseEnd_3822817 : Nat := 1962942575178874944606691

theorem tailTrace_3822817 : CollatzResearch.WordTrace tailWord_3822817 prefixEnd_3822817 1962942575178874944606691 := by
  unfold tailWord_3822817
  simp only [CollatzResearch.WordTrace]
  refine ⟨139429590591594369009866705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92953060394396246006577803 139429590591594369009866705)
  ·
    refine ⟨104572192943695776757400029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139429590591594369009866705 104572192943695776757400029)
    ·
      refine ⟨39214572353885916284025011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104572192943695776757400029 39214572353885916284025011)
      ·
        refine ⟨58821858530828874426037517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39214572353885916284025011 58821858530828874426037517)
        ·
          refine ⟨22058196949060827909764069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58821858530828874426037517 22058196949060827909764069)
          ·
            refine ⟨4135911927948905233080763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22058196949060827909764069 4135911927948905233080763)
            ·
              refine ⟨6203867891923357849621145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135911927948905233080763 6203867891923357849621145)
              ·
                refine ⟨4652900918942518387215859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203867891923357849621145 4652900918942518387215859)
                ·
                  refine ⟨6979351378413777580823789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652900918942518387215859 6979351378413777580823789)
                  ·
                    refine ⟨2617256766905166592808921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6979351378413777580823789 2617256766905166592808921)
                    ·
                      refine ⟨1962942575178874944606691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617256766905166592808921 1962942575178874944606691)
                      ·
                        rfl

theorem cell23_3822817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_3822817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822817 prefixEnd_3822817 := by exact prefixLift 3822817
  have htrace : WordTrace (prefixWord ++ tailWord_3822817) baseStart_3822817 baseEnd_3822817 := by
    simpa [prefixWord, tailWord_3822817, baseEnd_3822817] using wordTrace_append hprefix tailTrace_3822817
  have hstable : (prefixWord ++ tailWord_3822817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822817).length < 2 ^ (prefixWord ++ tailWord_3822817).sum := by decide
  have hdescent : baseEnd_3822817 < baseStart_3822817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822830 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_3822830 : Nat := 118140960795 + 3822830 * 2 ^ 59
def prefixEnd_3822830 : Nat := 4983230072969 + 3 ^ 40 * 3822830 * 2
def baseEnd_3822830 : Nat := 1962949250427383393744131

theorem tailTrace_3822830 : CollatzResearch.WordTrace tailWord_3822830 prefixEnd_3822830 1962949250427383393744131 := by
  unfold tailWord_3822830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17428758092568409028761243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92953376493698181486726629 17428758092568409028761243)
  ·
    refine ⟨26143137138852613543141865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17428758092568409028761243 26143137138852613543141865)
    ·
      refine ⟨19607352854139460157356399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26143137138852613543141865 19607352854139460157356399)
      ·
        refine ⟨29411029281209190236034599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19607352854139460157356399 29411029281209190236034599)
        ·
          refine ⟨44116543921813785354051899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29411029281209190236034599 44116543921813785354051899)
          ·
            refine ⟨66174815882720678031077849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44116543921813785354051899 66174815882720678031077849)
            ·
              refine ⟨49631111912040508523308387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66174815882720678031077849 49631111912040508523308387)
              ·
                refine ⟨74446667868060762784962581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49631111912040508523308387 74446667868060762784962581)
                ·
                  refine ⟨3489687556315348255545121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74446667868060762784962581 3489687556315348255545121)
                  ·
                    refine ⟨2617265667236511191658841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3489687556315348255545121 2617265667236511191658841)
                    ·
                      refine ⟨1962949250427383393744131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617265667236511191658841 1962949250427383393744131)
                      ·
                        rfl

theorem cell23_3822830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_3822830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822830 prefixEnd_3822830 := by exact prefixLift 3822830
  have htrace : WordTrace (prefixWord ++ tailWord_3822830) baseStart_3822830 baseEnd_3822830 := by
    simpa [prefixWord, tailWord_3822830, baseEnd_3822830] using wordTrace_append hprefix tailTrace_3822830
  have hstable : (prefixWord ++ tailWord_3822830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822830).length < 2 ^ (prefixWord ++ tailWord_3822830).sum := by decide
  have hdescent : baseEnd_3822830 < baseStart_3822830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822834 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_3822834 : Nat := 118140960795 + 3822834 * 2 ^ 59
def prefixEnd_3822834 : Nat := 4983230072969 + 3 ^ 40 * 3822834 * 2
def baseEnd_3822834 : Nat := 1962951304350001378094113

theorem tailTrace_3822834 : CollatzResearch.WordTrace tailWord_3822834 prefixEnd_3822834 1962951304350001378094113 := by
  unfold tailWord_3822834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34857552658133195228308889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92953473755021853942157037 34857552658133195228308889)
  ·
    refine ⟨26143164493599896421231667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34857552658133195228308889 26143164493599896421231667)
    ·
      refine ⟨39214746740399844631847501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26143164493599896421231667 39214746740399844631847501)
      ·
        refine ⟨14705530027649941736942813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39214746740399844631847501 14705530027649941736942813)
        ·
          refine ⟨5514573760368728151353555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14705530027649941736942813 5514573760368728151353555)
          ·
            refine ⟨8271860640553092227030333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514573760368728151353555 8271860640553092227030333)
            ·
              refine ⟨3101947740207409585136375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8271860640553092227030333 3101947740207409585136375)
              ·
                refine ⟨4652921610311114377704563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101947740207409585136375 4652921610311114377704563)
                ·
                  refine ⟨6979382415466671566556845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652921610311114377704563 6979382415466671566556845)
                  ·
                    refine ⟨2617268405800001837458817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6979382415466671566556845 2617268405800001837458817)
                    ·
                      refine ⟨1962951304350001378094113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617268405800001837458817 1962951304350001378094113)
                      ·
                        rfl

theorem cell23_3822834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_3822834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822834 prefixEnd_3822834 := by exact prefixLift 3822834
  have htrace : WordTrace (prefixWord ++ tailWord_3822834) baseStart_3822834 baseEnd_3822834 := by
    simpa [prefixWord, tailWord_3822834, baseEnd_3822834] using wordTrace_append hprefix tailTrace_3822834
  have hstable : (prefixWord ++ tailWord_3822834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822834).length < 2 ^ (prefixWord ++ tailWord_3822834).sum := by decide
  have hdescent : baseEnd_3822834 < baseStart_3822834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822847 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 2, 2, 2]
def baseStart_3822847 : Nat := 118140960795 + 3822847 * 2 ^ 59
def prefixEnd_3822847 : Nat := 4983230072969 + 3 ^ 40 * 3822847 * 2
def baseEnd_3822847 : Nat := 1962957979598509827231553

theorem tailTrace_3822847 : CollatzResearch.WordTrace tailWord_3822847 prefixEnd_3822847 1962957979598509827231553 := by
  unfold tailWord_3822847
  simp only [CollatzResearch.WordTrace]
  refine ⟨139430684781485684133458795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92953789854323789422305863 139430684781485684133458795)
  ·
    refine ⟨209146027172228526200188193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139430684781485684133458795 209146027172228526200188193)
    ·
      refine ⟨156859520379171394650141145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209146027172228526200188193 156859520379171394650141145)
      ·
        refine ⟨117644640284378545987605859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156859520379171394650141145 117644640284378545987605859)
        ·
          refine ⟨176466960426567818981408789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117644640284378545987605859 176466960426567818981408789)
          ·
            refine ⟨8271888769995366514753537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176466960426567818981408789 8271888769995366514753537)
            ·
              refine ⟨6203916577496524886065153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271888769995366514753537 6203916577496524886065153)
              ·
                refine ⟨4652937433122393664548865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203916577496524886065153 4652937433122393664548865)
                ·
                  refine ⟨3489703074841795248411649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4652937433122393664548865 3489703074841795248411649)
                  ·
                    refine ⟨2617277306131346436308737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3489703074841795248411649 2617277306131346436308737)
                    ·
                      refine ⟨1962957979598509827231553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617277306131346436308737 1962957979598509827231553)
                      ·
                        rfl

theorem cell23_3822847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_3822847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822847 prefixEnd_3822847 := by exact prefixLift 3822847
  have htrace : WordTrace (prefixWord ++ tailWord_3822847) baseStart_3822847 baseEnd_3822847 := by
    simpa [prefixWord, tailWord_3822847, baseEnd_3822847] using wordTrace_append hprefix tailTrace_3822847
  have hstable : (prefixWord ++ tailWord_3822847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822847).length < 2 ^ (prefixWord ++ tailWord_3822847).sum := by decide
  have hdescent : baseEnd_3822847 < baseStart_3822847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822853 : List Nat := [1, 3, 1, 1, 2, 1, 5, 4, 5]
def baseStart_3822853 : Nat := 118140960795 + 3822853 * 2 ^ 59
def prefixEnd_3822853 : Nat := 4983230072969 + 3 ^ 40 * 3822853 * 2
def baseEnd_3822853 : Nat := 218106784498048533750725

theorem tailTrace_3822853 : CollatzResearch.WordTrace tailWord_3822853 prefixEnd_3822853 218106784498048533750725 := by
  unfold tailWord_3822853
  simp only [CollatzResearch.WordTrace]
  refine ⟨139430903619463947158177213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92953935746309298105451475 139430903619463947158177213)
  ·
    refine ⟨52286588857298980184316455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139430903619463947158177213 52286588857298980184316455)
    ·
      refine ⟨78429883285948470276474683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52286588857298980184316455 78429883285948470276474683)
      ·
        refine ⟨117644824928922705414712025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78429883285948470276474683 117644824928922705414712025)
        ·
          refine ⟨88233618696692029061034019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117644824928922705414712025 88233618696692029061034019)
          ·
            refine ⟨132350428045038043591551029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88233618696692029061034019 132350428045038043591551029)
            ·
              refine ⟨12407852629222316586707909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132350428045038043591551029 12407852629222316586707909)
              ·
                refine ⟨2326472367979184360007733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12407852629222316586707909 2326472367979184360007733)
                ·
                  refine ⟨218106784498048533750725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2326472367979184360007733 218106784498048533750725)
                  ·
                    rfl

theorem cell23_3822853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_3822853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822853 prefixEnd_3822853 := by exact prefixLift 3822853
  have htrace : WordTrace (prefixWord ++ tailWord_3822853) baseStart_3822853 baseEnd_3822853 := by
    simpa [prefixWord, tailWord_3822853, baseEnd_3822853] using wordTrace_append hprefix tailTrace_3822853
  have hstable : (prefixWord ++ tailWord_3822853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822853).length < 2 ^ (prefixWord ++ tailWord_3822853).sum := by decide
  have hdescent : baseEnd_3822853 < baseStart_3822853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822876 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3822876 : Nat := 118140960795 + 3822876 * 2 ^ 59
def prefixEnd_3822876 : Nat := 4983230072969 + 3 ^ 40 * 3822876 * 2
def baseEnd_3822876 : Nat := 1962972870537490213768919

theorem tailTrace_3822876 : CollatzResearch.WordTrace tailWord_3822876 prefixEnd_3822876 1962972870537490213768919 := by
  unfold tailWord_3822876
  simp only [CollatzResearch.WordTrace]
  refine ⟨69715871249190311043132241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92954494998920414724176321 69715871249190311043132241)
  ·
    refine ⟨52286903436892733282349181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69715871249190311043132241 52286903436892733282349181)
    ·
      refine ⟨19607588788834774980880943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52286903436892733282349181 19607588788834774980880943)
      ·
        refine ⟨29411383183252162471321415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19607588788834774980880943 29411383183252162471321415)
        ·
          refine ⟨44117074774878243706982123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29411383183252162471321415 44117074774878243706982123)
          ·
            refine ⟨66175612162317365560473185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44117074774878243706982123 66175612162317365560473185)
            ·
              refine ⟨49631709121738024170354889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66175612162317365560473185 49631709121738024170354889)
              ·
                refine ⟨37223781841303518127766167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49631709121738024170354889 37223781841303518127766167)
                ·
                  refine ⟨55835672761955277191649251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37223781841303518127766167 55835672761955277191649251)
                  ·
                    refine ⟨83753509142932915787473877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55835672761955277191649251 83753509142932915787473877)
                    ·
                      refine ⟨1962972870537490213768919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83753509142932915787473877 1962972870537490213768919)
                      ·
                        rfl

theorem cell23_3822876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3822876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822876 prefixEnd_3822876 := by exact prefixLift 3822876
  have htrace : WordTrace (prefixWord ++ tailWord_3822876) baseStart_3822876 baseEnd_3822876 := by
    simpa [prefixWord, tailWord_3822876, baseEnd_3822876] using wordTrace_append hprefix tailTrace_3822876
  have hstable : (prefixWord ++ tailWord_3822876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822876).length < 2 ^ (prefixWord ++ tailWord_3822876).sum := by decide
  have hdescent : baseEnd_3822876 < baseStart_3822876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822883 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 2, 5]
def baseStart_3822883 : Nat := 118140960795 + 3822883 * 2 ^ 59
def prefixEnd_3822883 : Nat := 4983230072969 + 3 ^ 40 * 3822883 * 2
def baseEnd_3822883 : Nat := 654325488300690562127129

theorem tailTrace_3822883 : CollatzResearch.WordTrace tailWord_3822883 prefixEnd_3822883 654325488300690562127129 := by
  unfold tailWord_3822883
  simp only [CollatzResearch.WordTrace]
  refine ⟨139431997809355262281769303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92954665206236841521179535 139431997809355262281769303)
  ·
    refine ⟨209147996714032893422653955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139431997809355262281769303 209147996714032893422653955)
    ·
      refine ⟨313721995071049340133980933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209147996714032893422653955 313721995071049340133980933)
      ·
        refine ⟨58822874075821751275121425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313721995071049340133980933 58822874075821751275121425)
        ·
          refine ⟨44117155556866313456341069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58822874075821751275121425 44117155556866313456341069)
          ·
            refine ⟨16543933333824867546127901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44117155556866313456341069 16543933333824867546127901)
            ·
              refine ⟨6203975000184325329797963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16543933333824867546127901 6203975000184325329797963)
              ·
                refine ⟨9305962500276487994696945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203975000184325329797963 9305962500276487994696945)
                ·
                  refine ⟨6979471875207365996022709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305962500276487994696945 6979471875207365996022709)
                  ·
                    refine ⟨654325488300690562127129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6979471875207365996022709 654325488300690562127129)
                    ·
                      rfl

theorem cell23_3822883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 5].length) (baseStart_3822883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822883 prefixEnd_3822883 := by exact prefixLift 3822883
  have htrace : WordTrace (prefixWord ++ tailWord_3822883) baseStart_3822883 baseEnd_3822883 := by
    simpa [prefixWord, tailWord_3822883, baseEnd_3822883] using wordTrace_append hprefix tailTrace_3822883
  have hstable : (prefixWord ++ tailWord_3822883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822883).length < 2 ^ (prefixWord ++ tailWord_3822883).sum := by decide
  have hdescent : baseEnd_3822883 < baseStart_3822883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822947 : List Nat := [1, 1, 1, 5, 2, 2, 3, 3, 1, 4]
def baseStart_3822947 : Nat := 118140960795 + 3822947 * 2 ^ 59
def prefixEnd_3822947 : Nat := 4983230072969 + 3 ^ 40 * 3822947 * 2
def baseEnd_3822947 : Nat := 654336442554653145327031

theorem tailTrace_3822947 : CollatzResearch.WordTrace tailWord_3822947 prefixEnd_3822947 654336442554653145327031 := by
  unfold tailWord_3822947
  simp only [CollatzResearch.WordTrace]
  refine ⟨139434332081123401212099095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92956221387415600808066063 139434332081123401212099095)
  ·
    refine ⟨209151498121685101818148643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139434332081123401212099095 209151498121685101818148643)
    ·
      refine ⟨313727247182527652727222965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209151498121685101818148643 313727247182527652727222965)
      ·
        refine ⟨29411929423361967443177153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313727247182527652727222965 29411929423361967443177153)
        ·
          refine ⟨22058947067521475582382865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29411929423361967443177153 22058947067521475582382865)
          ·
            refine ⟨16544210300641106686787149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22058947067521475582382865 16544210300641106686787149)
            ·
              refine ⟨6204078862740415007545181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16544210300641106686787149 6204078862740415007545181)
              ·
                refine ⟨2326529573527655627829443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6204078862740415007545181 2326529573527655627829443)
                ·
                  refine ⟨3489794360291483441744165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326529573527655627829443 3489794360291483441744165)
                  ·
                    refine ⟨654336442554653145327031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3489794360291483441744165 654336442554653145327031)
                    ·
                      rfl

theorem cell23_3822947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 4].length) (baseStart_3822947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822947 prefixEnd_3822947 := by exact prefixLift 3822947
  have htrace : WordTrace (prefixWord ++ tailWord_3822947) baseStart_3822947 baseEnd_3822947 := by
    simpa [prefixWord, tailWord_3822947, baseEnd_3822947] using wordTrace_append hprefix tailTrace_3822947
  have hstable : (prefixWord ++ tailWord_3822947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822947).length < 2 ^ (prefixWord ++ tailWord_3822947).sum := by decide
  have hdescent : baseEnd_3822947 < baseStart_3822947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822973 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_3822973 : Nat := 118140960795 + 3822973 * 2 ^ 59
def prefixEnd_3822973 : Nat := 4983230072969 + 3 ^ 40 * 3822973 * 2
def baseEnd_3822973 : Nat := 654340892720325444751991

theorem tailTrace_3822973 : CollatzResearch.WordTrace tailWord_3822973 prefixEnd_3822973 654340892720325444751991 := by
  unfold tailWord_3822973
  simp only [CollatzResearch.WordTrace]
  refine ⟨139435280379029207652545573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92956853586019471768363715 139435280379029207652545573)
  ·
    refine ⟨26144115071067976434852295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139435280379029207652545573 26144115071067976434852295)
    ·
      refine ⟨39216172606601964652278443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26144115071067976434852295 39216172606601964652278443)
      ·
        refine ⟨58824258909902946978417665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39216172606601964652278443 58824258909902946978417665)
        ·
          refine ⟨44118194182427210233813249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58824258909902946978417665 44118194182427210233813249)
          ·
            refine ⟨33088645636820407675359937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44118194182427210233813249 33088645636820407675359937)
            ·
              refine ⟨24816484227615305756519953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33088645636820407675359937 24816484227615305756519953)
              ·
                refine ⟨18612363170711479317389965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24816484227615305756519953 18612363170711479317389965)
                ·
                  refine ⟨6979636189016804744021237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18612363170711479317389965 6979636189016804744021237)
                  ·
                    refine ⟨654340892720325444751991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6979636189016804744021237 654340892720325444751991)
                    ·
                      rfl

theorem cell23_3822973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_3822973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822973 prefixEnd_3822973 := by exact prefixLift 3822973
  have htrace : WordTrace (prefixWord ++ tailWord_3822973) baseStart_3822973 baseEnd_3822973 := by
    simpa [prefixWord, tailWord_3822973, baseEnd_3822973] using wordTrace_append hprefix tailTrace_3822973
  have hstable : (prefixWord ++ tailWord_3822973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822973).length < 2 ^ (prefixWord ++ tailWord_3822973).sum := by decide
  have hdescent : baseEnd_3822973 < baseStart_3822973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822993 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_3822993 : Nat := 118140960795 + 3822993 * 2 ^ 59
def prefixEnd_3822993 : Nat := 4983230072969 + 3 ^ 40 * 3822993 * 2
def baseEnd_3822993 : Nat := 1963032947774066256005881

theorem tailTrace_3822993 : CollatzResearch.WordTrace tailWord_3822993 prefixEnd_3822993 1963032947774066256005881 := by
  unfold tailWord_3822993
  simp only [CollatzResearch.WordTrace]
  refine ⟨139436009838956751068273633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92957339892637834045515755 139436009838956751068273633)
  ·
    refine ⟨104577007379217563301205225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139436009838956751068273633 104577007379217563301205225)
    ·
      refine ⟨78432755534413172475903919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104577007379217563301205225 78432755534413172475903919)
      ·
        refine ⟨117649133301619758713855879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78432755534413172475903919 117649133301619758713855879)
        ·
          refine ⟨176473699952429638070783819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117649133301619758713855879 176473699952429638070783819)
          ·
            refine ⟨264710549928644457106175729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176473699952429638070783819 264710549928644457106175729)
            ·
              refine ⟨198532912446483342829631797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264710549928644457106175729 198532912446483342829631797)
              ·
                refine ⟨18612460541857813390277981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198532912446483342829631797 18612460541857813390277981)
                ·
                  refine ⟨6979672703196680021354243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18612460541857813390277981 6979672703196680021354243)
                  ·
                    refine ⟨10469509054795020032031365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979672703196680021354243 10469509054795020032031365)
                    ·
                      refine ⟨1963032947774066256005881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10469509054795020032031365 1963032947774066256005881)
                      ·
                        rfl

theorem cell23_3822993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_3822993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3822993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3822993 prefixEnd_3822993 := by exact prefixLift 3822993
  have htrace : WordTrace (prefixWord ++ tailWord_3822993) baseStart_3822993 baseEnd_3822993 := by
    simpa [prefixWord, tailWord_3822993, baseEnd_3822993] using wordTrace_append hprefix tailTrace_3822993
  have hstable : (prefixWord ++ tailWord_3822993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822993).length < 2 ^ (prefixWord ++ tailWord_3822993).sum := by decide
  have hdescent : baseEnd_3822993 < baseStart_3822993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823007 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 1, 5]
def baseStart_3823007 : Nat := 118140960795 + 3823007 * 2 ^ 59
def prefixEnd_3823007 : Nat := 4983230072969 + 3 ^ 40 * 3823007 * 2
def baseEnd_3823007 : Nat := 654346712167743067076939

theorem tailTrace_3823007 : CollatzResearch.WordTrace tailWord_3823007 prefixEnd_3823007 654346712167743067076939 := by
  unfold tailWord_3823007
  simp only [CollatzResearch.WordTrace]
  refine ⟨139436520460906031459283275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92957680307270687639522183 139436520460906031459283275)
  ·
    refine ⟨209154780691359047188924913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139436520460906031459283275 209154780691359047188924913)
    ·
      refine ⟨156866085518519285391693685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209154780691359047188924913 156866085518519285391693685)
      ·
        refine ⟨14706195517361183005471283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156866085518519285391693685 14706195517361183005471283)
        ·
          refine ⟨22059293276041774508206925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14706195517361183005471283 22059293276041774508206925)
          ·
            refine ⟨8272234978515665440577597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22059293276041774508206925 8272234978515665440577597)
            ·
              refine ⟨3102088116943374540216599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272234978515665440577597 3102088116943374540216599)
              ·
                refine ⟨4653132175415061810324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102088116943374540216599 4653132175415061810324899)
                ·
                  refine ⟨6979698263122592715487349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653132175415061810324899 6979698263122592715487349)
                  ·
                    refine ⟨654346712167743067076939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6979698263122592715487349 654346712167743067076939)
                    ·
                      rfl

theorem cell23_3823007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 5].length) (baseStart_3823007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823007 prefixEnd_3823007 := by exact prefixLift 3823007
  have htrace : WordTrace (prefixWord ++ tailWord_3823007) baseStart_3823007 baseEnd_3823007 := by
    simpa [prefixWord, tailWord_3823007, baseEnd_3823007] using wordTrace_append hprefix tailTrace_3823007
  have hstable : (prefixWord ++ tailWord_3823007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823007).length < 2 ^ (prefixWord ++ tailWord_3823007).sum := by decide
  have hdescent : baseEnd_3823007 < baseStart_3823007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823013 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_3823013 : Nat := 118140960795 + 3823013 * 2 ^ 59
def prefixEnd_3823013 : Nat := 4983230072969 + 3 ^ 40 * 3823013 * 2
def baseEnd_3823013 : Nat := 1963043217387156177755789

theorem tailTrace_3823013 : CollatzResearch.WordTrace tailWord_3823013 prefixEnd_3823013 1963043217387156177755789 := by
  unfold tailWord_3823013
  simp only [CollatzResearch.WordTrace]
  refine ⟨139436739298884294484001693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92957826199256196322667795 139436739298884294484001693)
  ·
    refine ⟨52288777237081610431500635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139436739298884294484001693 52288777237081610431500635)
    ·
      refine ⟨78433165855622415647250953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52288777237081610431500635 78433165855622415647250953)
      ·
        refine ⟨58824874391716811735438215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78433165855622415647250953 58824874391716811735438215)
        ·
          refine ⟨88237311587575217603157323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58824874391716811735438215 88237311587575217603157323)
          ·
            refine ⟨132355967381362826404735985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88237311587575217603157323 132355967381362826404735985)
            ·
              refine ⟨99266975536022119803551989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132355967381362826404735985 99266975536022119803551989)
              ·
                refine ⟨9306278956502073731582999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99266975536022119803551989 9306278956502073731582999)
                ·
                  refine ⟨13959418434753110597374499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9306278956502073731582999 13959418434753110597374499)
                  ·
                    refine ⟨20939127652129665896061749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13959418434753110597374499 20939127652129665896061749)
                    ·
                      refine ⟨1963043217387156177755789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20939127652129665896061749 1963043217387156177755789)
                      ·
                        rfl

theorem cell23_3823013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_3823013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823013 prefixEnd_3823013 := by exact prefixLift 3823013
  have htrace : WordTrace (prefixWord ++ tailWord_3823013) baseStart_3823013 baseEnd_3823013 := by
    simpa [prefixWord, tailWord_3823013, baseEnd_3823013] using wordTrace_append hprefix tailTrace_3823013
  have hstable : (prefixWord ++ tailWord_3823013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823013).length < 2 ^ (prefixWord ++ tailWord_3823013).sum := by decide
  have hdescent : baseEnd_3823013 < baseStart_3823013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823020 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_3823020 : Nat := 118140960795 + 3823020 * 2 ^ 59
def prefixEnd_3823020 : Nat := 4983230072969 + 3 ^ 40 * 3823020 * 2
def baseEnd_3823020 : Nat := 654348937250579216789419

theorem tailTrace_3823020 : CollatzResearch.WordTrace tailWord_3823020 prefixEnd_3823020 654348937250579216789419 := by
  unfold tailWord_3823020
  simp only [CollatzResearch.WordTrace]
  refine ⟨69718497304929467339753257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92957996406572623119671009 69718497304929467339753257)
  ·
    refine ⟨52288872978697100504814943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69718497304929467339753257 52288872978697100504814943)
    ·
      refine ⟨78433309468045650757222415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52288872978697100504814943 78433309468045650757222415)
      ·
        refine ⟨117649964202068476135833623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78433309468045650757222415 117649964202068476135833623)
        ·
          refine ⟨176474946303102714203750435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117649964202068476135833623 176474946303102714203750435)
          ·
            refine ⟨264712419454654071305625653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176474946303102714203750435 264712419454654071305625653)
            ·
              refine ⟨24816789323873819184902405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264712419454654071305625653 24816789323873819184902405)
              ·
                refine ⟨4653147998226341097169201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24816789323873819184902405 4653147998226341097169201)
                ·
                  refine ⟨3489860998669755822876901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653147998226341097169201 3489860998669755822876901)
                  ·
                    refine ⟨654348937250579216789419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3489860998669755822876901 654348937250579216789419)
                    ·
                      rfl

theorem cell23_3823020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_3823020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823020 prefixEnd_3823020 := by exact prefixLift 3823020
  have htrace : WordTrace (prefixWord ++ tailWord_3823020) baseStart_3823020 baseEnd_3823020 := by
    simpa [prefixWord, tailWord_3823020, baseEnd_3823020] using wordTrace_append hprefix tailTrace_3823020
  have hstable : (prefixWord ++ tailWord_3823020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823020).length < 2 ^ (prefixWord ++ tailWord_3823020).sum := by decide
  have hdescent : baseEnd_3823020 < baseStart_3823020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823021 : List Nat := [1, 5, 2, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_3823021 : Nat := 118140960795 + 3823021 * 2 ^ 59
def prefixEnd_3823021 : Nat := 4983230072969 + 3 ^ 40 * 3823021 * 2
def baseEnd_3823021 : Nat := 1963047325232392146455753

theorem tailTrace_3823021 : CollatzResearch.WordTrace tailWord_3823021 prefixEnd_3823021 1963047325232392146455753 := by
  unfold tailWord_3823021
  simp only [CollatzResearch.WordTrace]
  refine ⟨139437031082855311850292917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92958020721903541233528611 139437031082855311850292917)
  ·
    refine ⟨13072221664017685485964961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139437031082855311850292917 13072221664017685485964961)
    ·
      refine ⟨9804166248013264114473721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13072221664017685485964961 9804166248013264114473721)
      ·
        refine ⟨7353124686009948085855291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9804166248013264114473721 7353124686009948085855291)
        ·
          refine ⟨11029687029014922128782937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353124686009948085855291 11029687029014922128782937)
          ·
            refine ⟨8272265271761191596587203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11029687029014922128782937 8272265271761191596587203)
            ·
              refine ⟨12408397907641787394880805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272265271761191596587203 12408397907641787394880805)
              ·
                refine ⟨2326574607682835136540151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12408397907641787394880805 2326574607682835136540151)
                ·
                  refine ⟨3489861911524252704810227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326574607682835136540151 3489861911524252704810227)
                  ·
                    refine ⟨5234792867286379057215341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3489861911524252704810227 5234792867286379057215341)
                    ·
                      refine ⟨1963047325232392146455753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5234792867286379057215341 1963047325232392146455753)
                      ·
                        rfl

theorem cell23_3823021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_3823021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823021 prefixEnd_3823021 := by exact prefixLift 3823021
  have htrace : WordTrace (prefixWord ++ tailWord_3823021) baseStart_3823021 baseEnd_3823021 := by
    simpa [prefixWord, tailWord_3823021, baseEnd_3823021] using wordTrace_append hprefix tailTrace_3823021
  have hstable : (prefixWord ++ tailWord_3823021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823021).length < 2 ^ (prefixWord ++ tailWord_3823021).sum := by decide
  have hdescent : baseEnd_3823021 < baseStart_3823021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823044 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3823044 : Nat := 118140960795 + 3823044 * 2 ^ 59
def prefixEnd_3823044 : Nat := 4983230072969 + 3 ^ 40 * 3823044 * 2
def baseEnd_3823044 : Nat := 1963059135287445556468147

theorem tailTrace_3823044 : CollatzResearch.WordTrace tailWord_3823044 prefixEnd_3823044 1963059135287445556468147 := by
  unfold tailWord_3823044
  simp only [CollatzResearch.WordTrace]
  refine ⟨69718934980885993389190093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92958579974514657852253457 69718934980885993389190093)
  ·
    refine ⟨26144600617832247520946285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69718934980885993389190093 26144600617832247520946285)
    ·
      refine ⟨9804225231687092820354857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26144600617832247520946285 9804225231687092820354857)
      ·
        refine ⟨7353168923765319615266143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9804225231687092820354857 7353168923765319615266143)
        ·
          refine ⟨11029753385647979422899215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353168923765319615266143 11029753385647979422899215)
          ·
            refine ⟨16544630078471969134348823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029753385647979422899215 16544630078471969134348823)
            ·
              refine ⟨24816945117707953701523235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16544630078471969134348823 24816945117707953701523235)
              ·
                refine ⟨37225417676561930552284853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24816945117707953701523235 37225417676561930552284853)
                ·
                  refine ⟨3489882907177680989276705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37225417676561930552284853 3489882907177680989276705)
                  ·
                    refine ⟨2617412180383260741957529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3489882907177680989276705 2617412180383260741957529)
                    ·
                      refine ⟨1963059135287445556468147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617412180383260741957529 1963059135287445556468147)
                      ·
                        rfl

theorem cell23_3823044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3823044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823044 prefixEnd_3823044 := by exact prefixLift 3823044
  have htrace : WordTrace (prefixWord ++ tailWord_3823044) baseStart_3823044 baseEnd_3823044 := by
    simpa [prefixWord, tailWord_3823044, baseEnd_3823044] using wordTrace_append hprefix tailTrace_3823044
  have hstable : (prefixWord ++ tailWord_3823044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823044).length < 2 ^ (prefixWord ++ tailWord_3823044).sum := by decide
  have hdescent : baseEnd_3823044 < baseStart_3823044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823050 : List Nat := [3, 1, 2, 1, 2, 4, 3, 7]
def baseStart_3823050 : Nat := 118140960795 + 3823050 * 2 ^ 59
def prefixEnd_3823050 : Nat := 4983230072969 + 3 ^ 40 * 3823050 * 2
def baseEnd_3823050 : Nat := 72706008006347130851597

theorem tailTrace_3823050 : CollatzResearch.WordTrace tailWord_3823050 prefixEnd_3823050 72706008006347130851597 := by
  unfold tailWord_3823050
  simp only [CollatzResearch.WordTrace]
  refine ⟨34859522199937562450774651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92958725866500166535399069 34859522199937562450774651)
  ·
    refine ⟨52289283299906343676161977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34859522199937562450774651 52289283299906343676161977)
    ·
      refine ⟨39216962474929757757121483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52289283299906343676161977 39216962474929757757121483)
      ·
        refine ⟨58825443712394636635682225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39216962474929757757121483 58825443712394636635682225)
        ·
          refine ⟨44119082784295977476761669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58825443712394636635682225 44119082784295977476761669)
          ·
            refine ⟨8272328022055495776892813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44119082784295977476761669 8272328022055495776892813)
            ·
              refine ⟨3102123008270810916334805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272328022055495776892813 3102123008270810916334805)
              ·
                refine ⟨72706008006347130851597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3102123008270810916334805 72706008006347130851597)
                ·
                  rfl

theorem cell23_3823050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_3823050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823050 prefixEnd_3823050 := by exact prefixLift 3823050
  have htrace : WordTrace (prefixWord ++ tailWord_3823050) baseStart_3823050 baseEnd_3823050 := by
    simpa [prefixWord, tailWord_3823050, baseEnd_3823050] using wordTrace_append hprefix tailTrace_3823050
  have hstable : (prefixWord ++ tailWord_3823050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823050).length < 2 ^ (prefixWord ++ tailWord_3823050).sum := by decide
  have hdescent : baseEnd_3823050 < baseStart_3823050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823061 : List Nat := [1, 3, 2, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3823061 : Nat := 118140960795 + 3823061 * 2 ^ 59
def prefixEnd_3823061 : Nat := 4983230072969 + 3 ^ 40 * 3823061 * 2
def baseEnd_3823061 : Nat := 1963067864458571989955569

theorem tailTrace_3823061 : CollatzResearch.WordTrace tailWord_3823061 prefixEnd_3823061 1963067864458571989955569 := by
  unfold tailWord_3823061
  simp only [CollatzResearch.WordTrace]
  refine ⟨139438490002710398681749037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92958993335140265787832691 139438490002710398681749037)
  ·
    refine ⟨52289433751016399505655889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139438490002710398681749037 52289433751016399505655889)
    ·
      refine ⟨39217075313262299629241917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52289433751016399505655889 39217075313262299629241917)
      ·
        refine ⟨14706403242473362360965719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39217075313262299629241917 14706403242473362360965719)
        ·
          refine ⟨22059604863710043541448579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14706403242473362360965719 22059604863710043541448579)
          ·
            refine ⟨33089407295565065312172869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22059604863710043541448579 33089407295565065312172869)
            ·
              refine ⟨6204263867918449746032413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33089407295565065312172869 6204263867918449746032413)
              ·
                refine ⟨2326598950469418654762155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6204263867918449746032413 2326598950469418654762155)
                ·
                  refine ⟨3489898425704127982143233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326598950469418654762155 3489898425704127982143233)
                  ·
                    refine ⟨2617423819278095986607425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3489898425704127982143233 2617423819278095986607425)
                    ·
                      refine ⟨1963067864458571989955569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617423819278095986607425 1963067864458571989955569)
                      ·
                        rfl

theorem cell23_3823061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3823061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823061 prefixEnd_3823061 := by exact prefixLift 3823061
  have htrace : WordTrace (prefixWord ++ tailWord_3823061) baseStart_3823061 baseEnd_3823061 := by
    simpa [prefixWord, tailWord_3823061, baseEnd_3823061] using wordTrace_append hprefix tailTrace_3823061
  have hstable : (prefixWord ++ tailWord_3823061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823061).length < 2 ^ (prefixWord ++ tailWord_3823061).sum := by decide
  have hdescent : baseEnd_3823061 < baseStart_3823061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823083 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4]
def baseStart_3823083 : Nat := 118140960795 + 3823083 * 2 ^ 59
def prefixEnd_3823083 : Nat := 4983230072969 + 3 ^ 40 * 3823083 * 2
def baseEnd_3823083 : Nat := 1963079161032970903880467

theorem tailTrace_3823083 : CollatzResearch.WordTrace tailWord_3823083 prefixEnd_3823083 1963079161032970903880467 := by
  unfold tailWord_3823083
  simp only [CollatzResearch.WordTrace]
  refine ⟨139439292408630696439049903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92959528272420464292699935 139439292408630696439049903)
  ·
    refine ⟨209158938612946044658574855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139439292408630696439049903 209158938612946044658574855)
    ·
      refine ⟨313738407919419066987862283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209158938612946044658574855 313738407919419066987862283)
      ·
        refine ⟨470607611879128600481793425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313738407919419066987862283 470607611879128600481793425)
        ·
          refine ⟨352955708909346450361345069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470607611879128600481793425 352955708909346450361345069)
          ·
            refine ⟨132358390841004918885504401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352955708909346450361345069 132358390841004918885504401)
            ·
              refine ⟨99268793130753689164128301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132358390841004918885504401 99268793130753689164128301)
              ·
                refine ⟨37225797424032633436548113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99268793130753689164128301 37225797424032633436548113)
                ·
                  refine ⟨27919348068024475077411085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37225797424032633436548113 27919348068024475077411085)
                  ·
                    refine ⟨10469755525509178154029157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27919348068024475077411085 10469755525509178154029157)
                    ·
                      refine ⟨1963079161032970903880467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10469755525509178154029157 1963079161032970903880467)
                      ·
                        rfl

theorem cell23_3823083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_3823083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823083 prefixEnd_3823083 := by exact prefixLift 3823083
  have htrace : WordTrace (prefixWord ++ tailWord_3823083) baseStart_3823083 baseEnd_3823083 := by
    simpa [prefixWord, tailWord_3823083, baseEnd_3823083] using wordTrace_append hprefix tailTrace_3823083
  have hstable : (prefixWord ++ tailWord_3823083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823083).length < 2 ^ (prefixWord ++ tailWord_3823083).sum := by decide
  have hdescent : baseEnd_3823083 < baseStart_3823083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823094 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3823094 : Nat := 118140960795 + 3823094 * 2 ^ 59
def prefixEnd_3823094 : Nat := 4983230072969 + 3 ^ 40 * 3823094 * 2
def baseEnd_3823094 : Nat := 1963084809320170360842917

theorem tailTrace_3823094 : CollatzResearch.WordTrace tailWord_3823094 prefixEnd_3823094 1963084809320170360842917 := by
  unfold tailWord_3823094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714980850724427832356271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92959795741060563545133557 8714980850724427832356271)
  ·
    refine ⟨13072471276086641748534407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8714980850724427832356271 13072471276086641748534407)
    ·
      refine ⟨19608706914129962622801611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13072471276086641748534407 19608706914129962622801611)
      ·
        refine ⟨29413060371194943934202417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19608706914129962622801611 29413060371194943934202417)
        ·
          refine ⟨22059795278396207950651813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29413060371194943934202417 22059795278396207950651813)
          ·
            refine ⟨4136211614699288990747215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22059795278396207950651813 4136211614699288990747215)
            ·
              refine ⟨6204317422048933486120823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136211614699288990747215 6204317422048933486120823)
              ·
                refine ⟨9306476133073400229181235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204317422048933486120823 9306476133073400229181235)
                ·
                  refine ⟨13959714199610100343771853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9306476133073400229181235 13959714199610100343771853)
                  ·
                    refine ⟨5234892824853787628914445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13959714199610100343771853 5234892824853787628914445)
                    ·
                      refine ⟨1963084809320170360842917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5234892824853787628914445 1963084809320170360842917)
                      ·
                        rfl

theorem cell23_3823094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3823094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823094 prefixEnd_3823094 := by exact prefixLift 3823094
  have htrace : WordTrace (prefixWord ++ tailWord_3823094) baseStart_3823094 baseEnd_3823094 := by
    simpa [prefixWord, tailWord_3823094, baseEnd_3823094] using wordTrace_append hprefix tailTrace_3823094
  have hstable : (prefixWord ++ tailWord_3823094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823094).length < 2 ^ (prefixWord ++ tailWord_3823094).sum := by decide
  have hdescent : baseEnd_3823094 < baseStart_3823094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823180 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3823180 : Nat := 118140960795 + 3823180 * 2 ^ 59
def prefixEnd_3823180 : Nat := 4983230072969 + 3 ^ 40 * 3823180 * 2
def baseEnd_3823180 : Nat := 1963128968656457024367521

theorem tailTrace_3823180 : CollatzResearch.WordTrace tailWord_3823180 prefixEnd_3823180 1963128968656457024367521 := by
  unfold tailWord_3823180
  simp only [CollatzResearch.WordTrace]
  refine ⟨69721415144639641002665497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92961886859519521336887329 69721415144639641002665497)
  ·
    refine ⟨52291061358479730751999123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69721415144639641002665497 52291061358479730751999123)
    ·
      refine ⟨78436592037719596127998685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52291061358479730751999123 78436592037719596127998685)
      ·
        refine ⟨29413722014144848547999507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78436592037719596127998685 29413722014144848547999507)
        ·
          refine ⟨44120583021217272821999261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29413722014144848547999507 44120583021217272821999261)
          ·
            refine ⟨16545218632956477308249723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44120583021217272821999261 16545218632956477308249723)
            ·
              refine ⟨24817827949434715962374585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16545218632956477308249723 24817827949434715962374585)
              ·
                refine ⟨18613370962076036971780939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24817827949434715962374585 18613370962076036971780939)
                ·
                  refine ⟨27920056443114055457671409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18613370962076036971780939 27920056443114055457671409)
                  ·
                    refine ⟨20940042332335541593253557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27920056443114055457671409 20940042332335541593253557)
                    ·
                      refine ⟨1963128968656457024367521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20940042332335541593253557 1963128968656457024367521)
                      ·
                        rfl

theorem cell23_3823180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3823180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823180 prefixEnd_3823180 := by exact prefixLift 3823180
  have htrace : WordTrace (prefixWord ++ tailWord_3823180) baseStart_3823180 baseEnd_3823180 := by
    simpa [prefixWord, tailWord_3823180, baseEnd_3823180] using wordTrace_append hprefix tailTrace_3823180
  have hstable : (prefixWord ++ tailWord_3823180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823180).length < 2 ^ (prefixWord ++ tailWord_3823180).sum := by decide
  have hdescent : baseEnd_3823180 < baseStart_3823180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823207 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_3823207 : Nat := 118140960795 + 3823207 * 2 ^ 59
def prefixEnd_3823207 : Nat := 4983230072969 + 3 ^ 40 * 3823207 * 2
def baseEnd_3823207 : Nat := 1963142832634128418729897

theorem tailTrace_3823207 : CollatzResearch.WordTrace tailWord_3823207 prefixEnd_3823207 1963142832634128418729897 := by
  unfold tailWord_3823207
  simp only [CollatzResearch.WordTrace]
  refine ⟨139443815060181465616563875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92962543373454310411042583 139443815060181465616563875)
  ·
    refine ⟨209165722590272198424845813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139443815060181465616563875 209165722590272198424845813)
    ·
      refine ⟨19609286492838018602329295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209165722590272198424845813 19609286492838018602329295)
      ·
        refine ⟨29413929739257027903493943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19609286492838018602329295 29413929739257027903493943)
        ·
          refine ⟨44120894608885541855240915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29413929739257027903493943 44120894608885541855240915)
          ·
            refine ⟨66181341913328312782861373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44120894608885541855240915 66181341913328312782861373)
            ·
              refine ⟨24818003217498117293573015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66181341913328312782861373 24818003217498117293573015)
              ·
                refine ⟨37227004826247175940359523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24818003217498117293573015 37227004826247175940359523)
                ·
                  refine ⟨55840507239370763910539285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37227004826247175940359523 55840507239370763910539285)
                  ·
                    refine ⟨2617523776845504558306529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55840507239370763910539285 2617523776845504558306529)
                    ·
                      refine ⟨1963142832634128418729897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617523776845504558306529 1963142832634128418729897)
                      ·
                        rfl

theorem cell23_3823207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_3823207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823207 prefixEnd_3823207 := by exact prefixLift 3823207
  have htrace : WordTrace (prefixWord ++ tailWord_3823207) baseStart_3823207 baseEnd_3823207 := by
    simpa [prefixWord, tailWord_3823207, baseEnd_3823207] using wordTrace_append hprefix tailTrace_3823207
  have hstable : (prefixWord ++ tailWord_3823207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823207).length < 2 ^ (prefixWord ++ tailWord_3823207).sum := by decide
  have hdescent : baseEnd_3823207 < baseStart_3823207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823264 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 6]
def baseStart_3823264 : Nat := 118140960795 + 3823264 * 2 ^ 59
def prefixEnd_3823264 : Nat := 4983230072969 + 3 ^ 40 * 3823264 * 2
def baseEnd_3823264 : Nat := 218130233447937188413015

theorem tailTrace_3823264 : CollatzResearch.WordTrace tailWord_3823264 prefixEnd_3823264 218130233447937188413015 := by
  unfold tailWord_3823264
  simp only [CollatzResearch.WordTrace]
  refine ⟨69722947010487482175694423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92963929347316642900925897 69722947010487482175694423)
  ·
    refine ⟨104584420515731223263541635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69722947010487482175694423 104584420515731223263541635)
    ·
      refine ⟨156876630773596834895312453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104584420515731223263541635 156876630773596834895312453)
      ·
        refine ⟨29414368270049406542871085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156876630773596834895312453 29414368270049406542871085)
        ·
          refine ⟨11030388101268527453576657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29414368270049406542871085 11030388101268527453576657)
          ·
            refine ⟨8272791075951395590182493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11030388101268527453576657 8272791075951395590182493)
            ·
              refine ⟨3102296653481773346318435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272791075951395590182493 3102296653481773346318435)
              ·
                refine ⟨4653444980222660019477653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102296653481773346318435 4653444980222660019477653)
                ·
                  refine ⟨218130233447937188413015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4653444980222660019477653 218130233447937188413015)
                  ·
                    rfl

theorem cell23_3823264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 6].length) (baseStart_3823264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823264 prefixEnd_3823264 := by exact prefixLift 3823264
  have htrace : WordTrace (prefixWord ++ tailWord_3823264) baseStart_3823264 baseEnd_3823264 := by
    simpa [prefixWord, tailWord_3823264, baseEnd_3823264] using wordTrace_append hprefix tailTrace_3823264
  have hstable : (prefixWord ++ tailWord_3823264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823264).length < 2 ^ (prefixWord ++ tailWord_3823264).sum := by decide
  have hdescent : baseEnd_3823264 < baseStart_3823264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823267 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 3, 5, 2]
def baseStart_3823267 : Nat := 118140960795 + 3823267 * 2 ^ 59
def prefixEnd_3823267 : Nat := 4983230072969 + 3 ^ 40 * 3823267 * 2
def baseEnd_3823267 : Nat := 1963173641473398183979621

theorem tailTrace_3823267 : CollatzResearch.WordTrace tailWord_3823267 prefixEnd_3823267 1963173641473398183979621 := by
  unfold tailWord_3823267
  simp only [CollatzResearch.WordTrace]
  refine ⟨139446003439964095863748055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92964002293309397242498703 139446003439964095863748055)
  ·
    refine ⟨209169005159946143795622083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139446003439964095863748055 209169005159946143795622083)
    ·
      refine ⟨313753507739919215693433125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209169005159946143795622083 313753507739919215693433125)
      ·
        refine ⟨58828782701234852942518711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313753507739919215693433125 58828782701234852942518711)
        ·
          refine ⟨88243174051852279413778067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58828782701234852942518711 88243174051852279413778067)
          ·
            refine ⟨132364761077778419120667101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88243174051852279413778067 132364761077778419120667101)
            ·
              refine ⟨49636785404166907170250163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132364761077778419120667101 49636785404166907170250163)
              ·
                refine ⟨74455178106250360755375245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49636785404166907170250163 74455178106250360755375245)
                ·
                  refine ⟨27920691789843885283265717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74455178106250360755375245 27920691789843885283265717)
                  ·
                    refine ⟨2617564855297864245306161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27920691789843885283265717 2617564855297864245306161)
                    ·
                      refine ⟨1963173641473398183979621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617564855297864245306161 1963173641473398183979621)
                      ·
                        rfl

theorem cell23_3823267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_3823267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823267 prefixEnd_3823267 := by exact prefixLift 3823267
  have htrace : WordTrace (prefixWord ++ tailWord_3823267) baseStart_3823267 baseEnd_3823267 := by
    simpa [prefixWord, tailWord_3823267, baseEnd_3823267] using wordTrace_append hprefix tailTrace_3823267
  have hstable : (prefixWord ++ tailWord_3823267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823267).length < 2 ^ (prefixWord ++ tailWord_3823267).sum := by decide
  have hdescent : baseEnd_3823267 < baseStart_3823267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823285 : List Nat := [1, 3, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3823285 : Nat := 118140960795 + 3823285 * 2 ^ 59
def prefixEnd_3823285 : Nat := 4983230072969 + 3 ^ 40 * 3823285 * 2
def baseEnd_3823285 : Nat := 654394294708393037851513

theorem tailTrace_3823285 : CollatzResearch.WordTrace tailWord_3823285 prefixEnd_3823285 654394294708393037851513 := by
  unfold tailWord_3823285
  simp only [CollatzResearch.WordTrace]
  refine ⟨139446659953898884937903309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92964439969265923291935539 139446659953898884937903309)
  ·
    refine ⟨52292497482712081851713741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139446659953898884937903309 52292497482712081851713741)
    ·
      refine ⟨19609686556017030694392653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52292497482712081851713741 19609686556017030694392653)
      ·
        refine ⟨7353632458506386510397245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19609686556017030694392653 7353632458506386510397245)
        ·
          refine ⟨2757612171939894941398967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7353632458506386510397245 2757612171939894941398967)
          ·
            refine ⟨4136418257909842412098451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757612171939894941398967 4136418257909842412098451)
            ·
              refine ⟨6204627386864763618147677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136418257909842412098451 6204627386864763618147677)
              ·
                refine ⟨2326735270074286356805379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6204627386864763618147677 2326735270074286356805379)
                ·
                  refine ⟨3490102905111429535208069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326735270074286356805379 3490102905111429535208069)
                  ·
                    refine ⟨654394294708393037851513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490102905111429535208069 654394294708393037851513)
                    ·
                      rfl

theorem cell23_3823285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3823285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823285 prefixEnd_3823285 := by exact prefixLift 3823285
  have htrace : WordTrace (prefixWord ++ tailWord_3823285) baseStart_3823285 baseEnd_3823285 := by
    simpa [prefixWord, tailWord_3823285, baseEnd_3823285] using wordTrace_append hprefix tailTrace_3823285
  have hstable : (prefixWord ++ tailWord_3823285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823285).length < 2 ^ (prefixWord ++ tailWord_3823285).sum := by decide
  have hdescent : baseEnd_3823285 < baseStart_3823285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823294 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3823294 : Nat := 118140960795 + 3823294 * 2 ^ 59
def prefixEnd_3823294 : Nat := 4983230072969 + 3 ^ 40 * 3823294 * 2
def baseEnd_3823294 : Nat := 654395835150356526113999

theorem tailTrace_3823294 : CollatzResearch.WordTrace tailWord_3823294 prefixEnd_3823294 654395835150356526113999 := by
  unfold tailWord_3823294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430873526358284934372617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92964658807244186316653957 17430873526358284934372617)
  ·
    refine ⟨13073155144768713700779463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17430873526358284934372617 13073155144768713700779463)
    ·
      refine ⟨19609732717153070551169195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13073155144768713700779463 19609732717153070551169195)
      ·
        refine ⟨29414599075729605826753793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19609732717153070551169195 29414599075729605826753793)
        ·
          refine ⟨22060949306797204370065345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29414599075729605826753793 22060949306797204370065345)
          ·
            refine ⟨16545711980097903277549009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22060949306797204370065345 16545711980097903277549009)
            ·
              refine ⟨12409283985073427458161757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16545711980097903277549009 12409283985073427458161757)
              ·
                refine ⟨4653481494402535296810659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12409283985073427458161757 4653481494402535296810659)
                ·
                  refine ⟨6980222241603802945215989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653481494402535296810659 6980222241603802945215989)
                  ·
                    refine ⟨654395835150356526113999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6980222241603802945215989 654395835150356526113999)
                    ·
                      rfl

theorem cell23_3823294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3823294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823294 prefixEnd_3823294 := by exact prefixLift 3823294
  have htrace : WordTrace (prefixWord ++ tailWord_3823294) baseStart_3823294 baseEnd_3823294 := by
    simpa [prefixWord, tailWord_3823294, baseEnd_3823294] using wordTrace_append hprefix tailTrace_3823294
  have hstable : (prefixWord ++ tailWord_3823294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823294).length < 2 ^ (prefixWord ++ tailWord_3823294).sum := by decide
  have hdescent : baseEnd_3823294 < baseStart_3823294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823302 : List Nat := [6, 1, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3823302 : Nat := 118140960795 + 3823302 * 2 ^ 59
def prefixEnd_3823302 : Nat := 4983230072969 + 3 ^ 40 * 3823302 * 2
def baseEnd_3823302 : Nat := 654397204432101849013987

theorem tailTrace_3823302 : CollatzResearch.WordTrace tailWord_3823302 prefixEnd_3823302 654397204432101849013987 := by
  unfold tailWord_3823302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357727499838665526289755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92964853329891531227514773 4357727499838665526289755)
  ·
    refine ⟨6536591249757998289434633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4357727499838665526289755 6536591249757998289434633)
    ·
      refine ⟨4902443437318498717075975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6536591249757998289434633 4902443437318498717075975)
      ·
        refine ⟨7353665155977748075613963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902443437318498717075975 7353665155977748075613963)
        ·
          refine ⟨11030497733966622113420945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353665155977748075613963 11030497733966622113420945)
          ·
            refine ⟨8272873300474966585065709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11030497733966622113420945 8272873300474966585065709)
            ·
              refine ⟨3102327487678112469399641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272873300474966585065709 3102327487678112469399641)
              ·
                refine ⟨2326745615758584352049731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102327487678112469399641 2326745615758584352049731)
                ·
                  refine ⟨3490118423637876528074597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326745615758584352049731 3490118423637876528074597)
                  ·
                    refine ⟨654397204432101849013987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490118423637876528074597 654397204432101849013987)
                    ·
                      rfl

theorem cell23_3823302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3823302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823302 prefixEnd_3823302 := by exact prefixLift 3823302
  have htrace : WordTrace (prefixWord ++ tailWord_3823302) baseStart_3823302 baseEnd_3823302 := by
    simpa [prefixWord, tailWord_3823302, baseEnd_3823302] using wordTrace_append hprefix tailTrace_3823302
  have hstable : (prefixWord ++ tailWord_3823302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823302).length < 2 ^ (prefixWord ++ tailWord_3823302).sum := by decide
  have hdescent : baseEnd_3823302 < baseStart_3823302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823308 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3823308 : Nat := 118140960795 + 3823308 * 2 ^ 59
def prefixEnd_3823308 : Nat := 4983230072969 + 3 ^ 40 * 3823308 * 2
def baseEnd_3823308 : Nat := 1963194694180232523566933

theorem tailTrace_3823308 : CollatzResearch.WordTrace tailWord_3823308 prefixEnd_3823308 1963194694180232523566933 := by
  unfold tailWord_3823308
  simp only [CollatzResearch.WordTrace]
  refine ⟨69723749416407779932995289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92964999221877039910660385 69723749416407779932995289)
  ·
    refine ⟨52292812062305834949746467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69723749416407779932995289 52292812062305834949746467)
    ·
      refine ⟨78439218093458752424619701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52292812062305834949746467 78439218093458752424619701)
      ·
        refine ⟨7353676696261758039808097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78439218093458752424619701 7353676696261758039808097)
        ·
          refine ⟨5515257522196318529856073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7353676696261758039808097 5515257522196318529856073)
          ·
            refine ⟨4136443141647238897392055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515257522196318529856073 4136443141647238897392055)
            ·
              refine ⟨6204664712470858346088083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136443141647238897392055 6204664712470858346088083)
              ·
                refine ⟨9306997068706287519132125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204664712470858346088083 9306997068706287519132125)
                ·
                  refine ⟨3490123900764857819674547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9306997068706287519132125 3490123900764857819674547)
                  ·
                    refine ⟨5235185851147286729511821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3490123900764857819674547 5235185851147286729511821)
                    ·
                      refine ⟨1963194694180232523566933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5235185851147286729511821 1963194694180232523566933)
                      ·
                        rfl

theorem cell23_3823308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3823308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823308 prefixEnd_3823308 := by exact prefixLift 3823308
  have htrace : WordTrace (prefixWord ++ tailWord_3823308) baseStart_3823308 baseEnd_3823308 := by
    simpa [prefixWord, tailWord_3823308, baseEnd_3823308] using wordTrace_append hprefix tailTrace_3823308
  have hstable : (prefixWord ++ tailWord_3823308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823308).length < 2 ^ (prefixWord ++ tailWord_3823308).sum := by decide
  have hdescent : baseEnd_3823308 < baseStart_3823308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823327 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_3823327 : Nat := 118140960795 + 3823327 * 2 ^ 59
def prefixEnd_3823327 : Nat := 4983230072969 + 3 ^ 40 * 3823327 * 2
def baseEnd_3823327 : Nat := 1963204450312667949229345

theorem tailTrace_3823327 : CollatzResearch.WordTrace tailWord_3823327 prefixEnd_3823327 1963204450312667949229345 := by
  unfold tailWord_3823327
  simp only [CollatzResearch.WordTrace]
  refine ⟨139448191819746726110932235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92965461213164484073954823 139448191819746726110932235)
  ·
    refine ⟨209172287729620089166398353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139448191819746726110932235 209172287729620089166398353)
    ·
      refine ⟨156879215797215066874798765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209172287729620089166398353 156879215797215066874798765)
      ·
        refine ⟨58829705923955650078049537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156879215797215066874798765 58829705923955650078049537)
        ·
          refine ⟨44122279442966737558537153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58829705923955650078049537 44122279442966737558537153)
          ·
            refine ⟨33091709582225053168902865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44122279442966737558537153 33091709582225053168902865)
            ·
              refine ⟨24818782186668789876677149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33091709582225053168902865 24818782186668789876677149)
              ·
                refine ⟨9307043320000796203753931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24818782186668789876677149 9307043320000796203753931)
                ·
                  refine ⟨13960564980001194305630897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307043320000796203753931 13960564980001194305630897)
                  ·
                    refine ⟨10470423735000895729223173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13960564980001194305630897 10470423735000895729223173)
                    ·
                      refine ⟨1963204450312667949229345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10470423735000895729223173 1963204450312667949229345)
                      ·
                        rfl

theorem cell23_3823327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_3823327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823327 prefixEnd_3823327 := by exact prefixLift 3823327
  have htrace : WordTrace (prefixWord ++ tailWord_3823327) baseStart_3823327 baseEnd_3823327 := by
    simpa [prefixWord, tailWord_3823327, baseEnd_3823327] using wordTrace_append hprefix tailTrace_3823327
  have hstable : (prefixWord ++ tailWord_3823327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823327).length < 2 ^ (prefixWord ++ tailWord_3823327).sum := by decide
  have hdescent : baseEnd_3823327 < baseStart_3823327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823347 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 3]
def baseStart_3823347 : Nat := 118140960795 + 3823347 * 2 ^ 59
def prefixEnd_3823347 : Nat := 4983230072969 + 3 ^ 40 * 3823347 * 2
def baseEnd_3823347 : Nat := 1963214719925757870979253

theorem tailTrace_3823347 : CollatzResearch.WordTrace tailWord_3823347 prefixEnd_3823347 1963214719925757870979253 := by
  unfold tailWord_3823347
  simp only [CollatzResearch.WordTrace]
  refine ⟨139448921279674269526660295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92965947519782846351106863 139448921279674269526660295)
  ·
    refine ⟨209173381919511404289990443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139448921279674269526660295 209173381919511404289990443)
    ·
      refine ⟨313760072879267106434985665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209173381919511404289990443 313760072879267106434985665)
      ·
        refine ⟨235320054659450329826239249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313760072879267106434985665 235320054659450329826239249)
        ·
          refine ⟨176490040994587747369679437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235320054659450329826239249 176490040994587747369679437)
          ·
            refine ⟨66183765372970405263629789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176490040994587747369679437 66183765372970405263629789)
            ·
              refine ⟨24818912014863901973861171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66183765372970405263629789 24818912014863901973861171)
              ·
                refine ⟨37228368022295852960791757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24818912014863901973861171 37228368022295852960791757)
                ·
                  refine ⟨13960638008360944860296909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37228368022295852960791757 13960638008360944860296909)
                  ·
                    refine ⟨5235239253135354322611341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13960638008360944860296909 5235239253135354322611341)
                    ·
                      refine ⟨1963214719925757870979253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5235239253135354322611341 1963214719925757870979253)
                      ·
                        rfl

theorem cell23_3823347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_3823347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823347 prefixEnd_3823347 := by exact prefixLift 3823347
  have htrace : WordTrace (prefixWord ++ tailWord_3823347) baseStart_3823347 baseEnd_3823347 := by
    simpa [prefixWord, tailWord_3823347, baseEnd_3823347] using wordTrace_append hprefix tailTrace_3823347
  have hstable : (prefixWord ++ tailWord_3823347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823347).length < 2 ^ (prefixWord ++ tailWord_3823347).sum := by decide
  have hdescent : baseEnd_3823347 < baseStart_3823347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823358 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3823358 : Nat := 118140960795 + 3823358 * 2 ^ 59
def prefixEnd_3823358 : Nat := 4983230072969 + 3 ^ 40 * 3823358 * 2
def baseEnd_3823358 : Nat := 654406789404319109313901

theorem tailTrace_3823358 : CollatzResearch.WordTrace tailWord_3823358 prefixEnd_3823358 654406789404319109313901 := by
  unfold tailWord_3823358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17431165310329302300663841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92966214988422945603540485 17431165310329302300663841)
  ·
    refine ⟨13073373982746976725497881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17431165310329302300663841 13073373982746976725497881)
    ·
      refine ⟨9805030487060232544123411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13073373982746976725497881 9805030487060232544123411)
      ·
        refine ⟨14707545730590348816185117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805030487060232544123411 14707545730590348816185117)
        ·
          refine ⟨5515329648971380806069419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14707545730590348816185117 5515329648971380806069419)
          ·
            refine ⟨8272994473457071209104129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515329648971380806069419 8272994473457071209104129)
            ·
              refine ⟨6204745855092803406828097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8272994473457071209104129 6204745855092803406828097)
              ·
                refine ⟨4653559391319602555121073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204745855092803406828097 4653559391319602555121073)
                ·
                  refine ⟨3490169543489701916340805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653559391319602555121073 3490169543489701916340805)
                  ·
                    refine ⟨654406789404319109313901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490169543489701916340805 654406789404319109313901)
                    ·
                      rfl

theorem cell23_3823358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3823358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823358 prefixEnd_3823358 := by exact prefixLift 3823358
  have htrace : WordTrace (prefixWord ++ tailWord_3823358) baseStart_3823358 baseEnd_3823358 := by
    simpa [prefixWord, tailWord_3823358, baseEnd_3823358] using wordTrace_append hprefix tailTrace_3823358
  have hstable : (prefixWord ++ tailWord_3823358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823358).length < 2 ^ (prefixWord ++ tailWord_3823358).sum := by decide
  have hdescent : baseEnd_3823358 < baseStart_3823358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823381 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_3823381 : Nat := 118140960795 + 3823381 * 2 ^ 59
def prefixEnd_3823381 : Nat := 4983230072969 + 3 ^ 40 * 3823381 * 2
def baseEnd_3823381 : Nat := 1963232178268010737954097

theorem tailTrace_3823381 : CollatzResearch.WordTrace tailWord_3823381 prefixEnd_3823381 1963232178268010737954097 := by
  unfold tailWord_3823381
  simp only [CollatzResearch.WordTrace]
  refine ⟨139450161361551093333397997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92966774241034062222265331 139450161361551093333397997)
  ·
    refine ⟨52293810510581660000024249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139450161361551093333397997 52293810510581660000024249)
    ·
      refine ⟨39220357882936245000018187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52293810510581660000024249 39220357882936245000018187)
      ·
        refine ⟨58830536824404367500027281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39220357882936245000018187 58830536824404367500027281)
        ·
          refine ⟨44122902618303275625020461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58830536824404367500027281 44122902618303275625020461)
          ·
            refine ⟨16546088481863728359382673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44122902618303275625020461 16546088481863728359382673)
            ·
              refine ⟨12409566361397796269537005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16546088481863728359382673 12409566361397796269537005)
              ·
                refine ⟨4653587385524173601076377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12409566361397796269537005 4653587385524173601076377)
                ·
                  refine ⟨3490190539143130200807283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653587385524173601076377 3490190539143130200807283)
                  ·
                    refine ⟨5235285808714695301210925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3490190539143130200807283 5235285808714695301210925)
                    ·
                      refine ⟨1963232178268010737954097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5235285808714695301210925 1963232178268010737954097)
                      ·
                        rfl

theorem cell23_3823381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_3823381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823381 prefixEnd_3823381 := by exact prefixLift 3823381
  have htrace : WordTrace (prefixWord ++ tailWord_3823381) baseStart_3823381 baseEnd_3823381 := by
    simpa [prefixWord, tailWord_3823381, baseEnd_3823381] using wordTrace_append hprefix tailTrace_3823381
  have hstable : (prefixWord ++ tailWord_3823381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823381).length < 2 ^ (prefixWord ++ tailWord_3823381).sum := by decide
  have hdescent : baseEnd_3823381 < baseStart_3823381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823391 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 1, 3, 2]
def baseStart_3823391 : Nat := 118140960795 + 3823391 * 2 ^ 59
def prefixEnd_3823391 : Nat := 4983230072969 + 3 ^ 40 * 3823391 * 2
def baseEnd_3823391 : Nat := 1963237313074555698829051

theorem tailTrace_3823391 : CollatzResearch.WordTrace tailWord_3823391 prefixEnd_3823391 1963237313074555698829051 := by
  unfold tailWord_3823391
  simp only [CollatzResearch.WordTrace]
  refine ⟨139450526091514865041262027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92967017394343243360841351 139450526091514865041262027)
  ·
    refine ⟨209175789137272297561893041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139450526091514865041262027 209175789137272297561893041)
    ·
      refine ⟨156881841852954223171419781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209175789137272297561893041 156881841852954223171419781)
      ·
        refine ⟨29415345347428916844641209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156881841852954223171419781 29415345347428916844641209)
        ·
          refine ⟨22061509010571687633480907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29415345347428916844641209 22061509010571687633480907)
          ·
            refine ⟨33092263515857531450221361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22061509010571687633480907 33092263515857531450221361)
            ·
              refine ⟨24819197636893148587666021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33092263515857531450221361 24819197636893148587666021)
              ·
                refine ⟨4653599556917465360187379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24819197636893148587666021 4653599556917465360187379)
                ·
                  refine ⟨6980399335376198040281069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653599556917465360187379 6980399335376198040281069)
                  ·
                    refine ⟨2617649750766074265105401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6980399335376198040281069 2617649750766074265105401)
                    ·
                      refine ⟨1963237313074555698829051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617649750766074265105401 1963237313074555698829051)
                      ·
                        rfl

theorem cell23_3823391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_3823391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823391 prefixEnd_3823391 := by exact prefixLift 3823391
  have htrace : WordTrace (prefixWord ++ tailWord_3823391) baseStart_3823391 baseEnd_3823391 := by
    simpa [prefixWord, tailWord_3823391, baseEnd_3823391] using wordTrace_append hprefix tailTrace_3823391
  have hstable : (prefixWord ++ tailWord_3823391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823391).length < 2 ^ (prefixWord ++ tailWord_3823391).sum := by decide
  have hdescent : baseEnd_3823391 < baseStart_3823391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823407 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 3]
def baseStart_3823407 : Nat := 118140960795 + 3823407 * 2 ^ 59
def prefixEnd_3823407 : Nat := 4983230072969 + 3 ^ 40 * 3823407 * 2
def baseEnd_3823407 : Nat := 1963245528765027636228977

theorem tailTrace_3823407 : CollatzResearch.WordTrace tailWord_3823407 prefixEnd_3823407 1963245528765027636228977 := by
  unfold tailWord_3823407
  simp only [CollatzResearch.WordTrace]
  refine ⟨139451109659456899773844475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92967406439637933182562983 139451109659456899773844475)
  ·
    refine ⟨209176664489185349660766713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139451109659456899773844475 209176664489185349660766713)
    ·
      refine ⟨156882498366889012245575035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209176664489185349660766713 156882498366889012245575035)
      ·
        refine ⟨235323747550333518368362553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156882498366889012245575035 235323747550333518368362553)
        ·
          refine ⟨176492810662750138776271915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235323747550333518368362553 176492810662750138776271915)
          ·
            refine ⟨264739215994125208164407873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176492810662750138776271915 264739215994125208164407873)
            ·
              refine ⟨198554411995593906123305905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264739215994125208164407873 198554411995593906123305905)
              ·
                refine ⟨148915808996695429592479429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198554411995593906123305905 148915808996695429592479429)
                ·
                  refine ⟨27921714186880393048589893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148915808996695429592479429 27921714186880393048589893)
                  ·
                    refine ⟨5235321410040073696610605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27921714186880393048589893 5235321410040073696610605)
                    ·
                      refine ⟨1963245528765027636228977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5235321410040073696610605 1963245528765027636228977)
                      ·
                        rfl

theorem cell23_3823407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_3823407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823407 prefixEnd_3823407 := by exact prefixLift 3823407
  have htrace : WordTrace (prefixWord ++ tailWord_3823407) baseStart_3823407 baseEnd_3823407 := by
    simpa [prefixWord, tailWord_3823407, baseEnd_3823407] using wordTrace_append hprefix tailTrace_3823407
  have hstable : (prefixWord ++ tailWord_3823407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823407).length < 2 ^ (prefixWord ++ tailWord_3823407).sum := by decide
  have hdescent : baseEnd_3823407 < baseStart_3823407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823427 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 7]
def baseStart_3823427 : Nat := 118140960795 + 3823427 * 2 ^ 59
def prefixEnd_3823427 : Nat := 4983230072969 + 3 ^ 40 * 3823427 * 2
def baseEnd_3823427 : Nat := 218139533153124173108765

theorem tailTrace_3823427 : CollatzResearch.WordTrace tailWord_3823427 prefixEnd_3823427 218139533153124173108765 := by
  unfold tailWord_3823427
  simp only [CollatzResearch.WordTrace]
  refine ⟨139451839119384443189572535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92967892746256295459715023 139451839119384443189572535)
  ·
    refine ⟨209177758679076664784358803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139451839119384443189572535 209177758679076664784358803)
    ·
      refine ⟨313766638018614997176538205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209177758679076664784358803 313766638018614997176538205)
      ·
        refine ⟨117662489256980623941201827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313766638018614997176538205 117662489256980623941201827)
        ·
          refine ⟨176493733885470935911802741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117662489256980623941201827 176493733885470935911802741)
          ·
            refine ⟨16546287551762900241731507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176493733885470935911802741 16546287551762900241731507)
            ·
              refine ⟨24819431327644350362597261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16546287551762900241731507 24819431327644350362597261)
              ·
                refine ⟨9307286747866631385973973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24819431327644350362597261 9307286747866631385973973)
                ·
                  refine ⟨218139533153124173108765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9307286747866631385973973 218139533153124173108765)
                  ·
                    rfl

theorem cell23_3823427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 7].length) (baseStart_3823427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823427 prefixEnd_3823427 := by exact prefixLift 3823427
  have htrace : WordTrace (prefixWord ++ tailWord_3823427) baseStart_3823427 baseEnd_3823427 := by
    simpa [prefixWord, tailWord_3823427, baseEnd_3823427] using wordTrace_append hprefix tailTrace_3823427
  have hstable : (prefixWord ++ tailWord_3823427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823427).length < 2 ^ (prefixWord ++ tailWord_3823427).sum := by decide
  have hdescent : baseEnd_3823427 < baseStart_3823427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823444 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 7]
def baseStart_3823444 : Nat := 118140960795 + 3823444 * 2 ^ 59
def prefixEnd_3823444 : Nat := 4983230072969 + 3 ^ 40 * 3823444 * 2
def baseEnd_3823444 : Nat := 218140503061027110162923

theorem tailTrace_3823444 : CollatzResearch.WordTrace tailWord_3823444 prefixEnd_3823444 218140503061027110162923 := by
  unfold tailWord_3823444
  simp only [CollatzResearch.WordTrace]
  refine ⟨69726229580161427546470693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92968306106881903395294257 69726229580161427546470693)
  ·
    refine ⟨13073668046280267664963255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69726229580161427546470693 13073668046280267664963255)
    ·
      refine ⟨19610502069420401497444883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13073668046280267664963255 19610502069420401497444883)
      ·
        refine ⟨29415753104130602246167325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19610502069420401497444883 29415753104130602246167325)
        ·
          refine ⟨11030907414048975842312747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29415753104130602246167325 11030907414048975842312747)
          ·
            refine ⟨16546361121073463763469121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11030907414048975842312747 16546361121073463763469121)
            ·
              refine ⟨12409770840805097822601841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16546361121073463763469121 12409770840805097822601841)
              ·
                refine ⟨9307328130603823366951381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12409770840805097822601841 9307328130603823366951381)
                ·
                  refine ⟨218140503061027110162923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9307328130603823366951381 218140503061027110162923)
                  ·
                    rfl

theorem cell23_3823444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_3823444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823444 prefixEnd_3823444 := by exact prefixLift 3823444
  have htrace : WordTrace (prefixWord ++ tailWord_3823444) baseStart_3823444 baseEnd_3823444 := by
    simpa [prefixWord, tailWord_3823444, baseEnd_3823444] using wordTrace_append hprefix tailTrace_3823444
  have hstable : (prefixWord ++ tailWord_3823444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823444).length < 2 ^ (prefixWord ++ tailWord_3823444).sum := by decide
  have hdescent : baseEnd_3823444 < baseStart_3823444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823457 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3823457 : Nat := 118140960795 + 3823457 * 2 ^ 59
def prefixEnd_3823457 : Nat := 4983230072969 + 3 ^ 40 * 3823457 * 2
def baseEnd_3823457 : Nat := 654423734265917480201249

theorem tailTrace_3823457 : CollatzResearch.WordTrace tailWord_3823457 prefixEnd_3823457 654423734265917480201249 := by
  unfold tailWord_3823457
  simp only [CollatzResearch.WordTrace]
  refine ⟨139452933309275758313164625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92968622206183838875443083 139452933309275758313164625)
  ·
    refine ⟨104589699981956818734873469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139452933309275758313164625 104589699981956818734873469)
    ·
      refine ⟨39221137493233807025577551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104589699981956818734873469 39221137493233807025577551)
      ·
        refine ⟨58831706239850710538366327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39221137493233807025577551 58831706239850710538366327)
        ·
          refine ⟨88247559359776065807549491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58831706239850710538366327 88247559359776065807549491)
          ·
            refine ⟨132371339039664098711324237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88247559359776065807549491 132371339039664098711324237)
            ·
              refine ⟨49639252139874037016746589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132371339039664098711324237 49639252139874037016746589)
              ·
                refine ⟨18614719552452763881279971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49639252139874037016746589 18614719552452763881279971)
                ·
                  refine ⟨27922079328679145821919957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18614719552452763881279971 27922079328679145821919957)
                  ·
                    refine ⟨654423734265917480201249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27922079328679145821919957 654423734265917480201249)
                    ·
                      rfl

theorem cell23_3823457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3823457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823457 prefixEnd_3823457 := by exact prefixLift 3823457
  have htrace : WordTrace (prefixWord ++ tailWord_3823457) baseStart_3823457 baseEnd_3823457 := by
    simpa [prefixWord, tailWord_3823457, baseEnd_3823457] using wordTrace_append hprefix tailTrace_3823457
  have hstable : (prefixWord ++ tailWord_3823457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823457).length < 2 ^ (prefixWord ++ tailWord_3823457).sum := by decide
  have hdescent : baseEnd_3823457 < baseStart_3823457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823467 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5]
def baseStart_3823467 : Nat := 118140960795 + 3823467 * 2 ^ 59
def prefixEnd_3823467 : Nat := 4983230072969 + 3 ^ 40 * 3823467 * 2
def baseEnd_3823467 : Nat := 1963276337604297401478701

theorem tailTrace_3823467 : CollatzResearch.WordTrace tailWord_3823467 prefixEnd_3823467 1963276337604297401478701 := by
  unfold tailWord_3823467
  simp only [CollatzResearch.WordTrace]
  refine ⟨139453298039239530021028655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92968865359493020014019103 139453298039239530021028655)
  ·
    refine ⟨209179947058859295031542983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139453298039239530021028655 209179947058859295031542983)
    ·
      refine ⟨313769920588288942547314475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209179947058859295031542983 313769920588288942547314475)
      ·
        refine ⟨470654880882433413820971713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313769920588288942547314475 470654880882433413820971713)
        ·
          refine ⟨352991160661825060365728785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470654880882433413820971713 352991160661825060365728785)
          ·
            refine ⟨264743370496368795274296589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352991160661825060365728785 264743370496368795274296589)
            ·
              refine ⟨99278763936138298227861221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264743370496368795274296589 99278763936138298227861221)
              ·
                refine ⟨18614768238025930917723979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99278763936138298227861221 18614768238025930917723979)
                ·
                  refine ⟨27922152357038896376585969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18614768238025930917723979 27922152357038896376585969)
                  ·
                    refine ⟨20941614267779172282439477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27922152357038896376585969 20941614267779172282439477)
                    ·
                      refine ⟨1963276337604297401478701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20941614267779172282439477 1963276337604297401478701)
                      ·
                        rfl

theorem cell23_3823467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_3823467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823467 prefixEnd_3823467 := by exact prefixLift 3823467
  have htrace : WordTrace (prefixWord ++ tailWord_3823467) baseStart_3823467 baseEnd_3823467 := by
    simpa [prefixWord, tailWord_3823467, baseEnd_3823467] using wordTrace_append hprefix tailTrace_3823467
  have hstable : (prefixWord ++ tailWord_3823467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823467).length < 2 ^ (prefixWord ++ tailWord_3823467).sum := by decide
  have hdescent : baseEnd_3823467 < baseStart_3823467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823478 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_3823478 : Nat := 118140960795 + 3823478 * 2 ^ 59
def prefixEnd_3823478 : Nat := 4983230072969 + 3 ^ 40 * 3823478 * 2
def baseEnd_3823478 : Nat := 218142442876832984271239

theorem tailTrace_3823478 : CollatzResearch.WordTrace tailWord_3823478 prefixEnd_3823478 218142442876832984271239 := by
  unfold tailWord_3823478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8715856202637479931229943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92969132828133119266452725 8715856202637479931229943)
  ·
    refine ⟨13073784303956219896844915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8715856202637479931229943 13073784303956219896844915)
    ·
      refine ⟨19610676455934329845267373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13073784303956219896844915 19610676455934329845267373)
      ·
        refine ⟨7354003670975373691975265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19610676455934329845267373 7354003670975373691975265)
        ·
          refine ⟨5515502753231530268981449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7354003670975373691975265 5515502753231530268981449)
          ·
            refine ⟨4136627064923647701736087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515502753231530268981449 4136627064923647701736087)
            ·
              refine ⟨6204940597385471552604131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136627064923647701736087 6204940597385471552604131)
              ·
                refine ⟨9307410896078207328906197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204940597385471552604131 9307410896078207328906197)
                ·
                  refine ⟨218142442876832984271239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9307410896078207328906197 218142442876832984271239)
                  ·
                    rfl

theorem cell23_3823478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_3823478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823478 prefixEnd_3823478 := by exact prefixLift 3823478
  have htrace : WordTrace (prefixWord ++ tailWord_3823478) baseStart_3823478 baseEnd_3823478 := by
    simpa [prefixWord, tailWord_3823478, baseEnd_3823478] using wordTrace_append hprefix tailTrace_3823478
  have hstable : (prefixWord ++ tailWord_3823478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823478).length < 2 ^ (prefixWord ++ tailWord_3823478).sum := by decide
  have hdescent : baseEnd_3823478 < baseStart_3823478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823489 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3823489 : Nat := 118140960795 + 3823489 * 2 ^ 59
def prefixEnd_3823489 : Nat := 4983230072969 + 3 ^ 40 * 3823489 * 2
def baseEnd_3823489 : Nat := 1963287634178696315403601

theorem tailTrace_3823489 : CollatzResearch.WordTrace tailWord_3823489 prefixEnd_3823489 1963287634178696315403601 := by
  unfold tailWord_3823489
  simp only [CollatzResearch.WordTrace]
  refine ⟨139454100445159827778329521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92969400296773218518886347 139454100445159827778329521)
  ·
    refine ⟨104590575333869870833747141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139454100445159827778329521 104590575333869870833747141)
    ·
      refine ⟨19610732875100600781327589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104590575333869870833747141 19610732875100600781327589)
      ·
        refine ⟨3677012414081362646498923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19610732875100600781327589 3677012414081362646498923)
        ·
          refine ⟨5515518621122043969748385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677012414081362646498923 5515518621122043969748385)
          ·
            refine ⟨4136638965841532977311289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515518621122043969748385 4136638965841532977311289)
            ·
              refine ⟨3102479224381149732983467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136638965841532977311289 3102479224381149732983467)
              ·
                refine ⟨4653718836571724599475201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102479224381149732983467 4653718836571724599475201)
                ·
                  refine ⟨3490289127428793449606401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653718836571724599475201 3490289127428793449606401)
                  ·
                    refine ⟨2617716845571595087204801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3490289127428793449606401 2617716845571595087204801)
                    ·
                      refine ⟨1963287634178696315403601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617716845571595087204801 1963287634178696315403601)
                      ·
                        rfl

theorem cell23_3823489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3823489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823489 prefixEnd_3823489 := by exact prefixLift 3823489
  have htrace : WordTrace (prefixWord ++ tailWord_3823489) baseStart_3823489 baseEnd_3823489 := by
    simpa [prefixWord, tailWord_3823489, baseEnd_3823489] using wordTrace_append hprefix tailTrace_3823489
  have hstable : (prefixWord ++ tailWord_3823489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823489).length < 2 ^ (prefixWord ++ tailWord_3823489).sum := by decide
  have hdescent : baseEnd_3823489 < baseStart_3823489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823511 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_3823511 : Nat := 118140960795 + 3823511 * 2 ^ 59
def prefixEnd_3823511 : Nat := 4983230072969 + 3 ^ 40 * 3823511 * 2
def baseEnd_3823511 : Nat := 1963298930753095229328499

theorem tailTrace_3823511 : CollatzResearch.WordTrace tailWord_3823511 prefixEnd_3823511 1963298930753095229328499 := by
  unfold tailWord_3823511
  simp only [CollatzResearch.WordTrace]
  refine ⟨139454902851080125535630387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92969935234053417023753591 139454902851080125535630387)
  ·
    refine ⟨209182354276620188303445581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139454902851080125535630387 209182354276620188303445581)
    ·
      refine ⟨78443382853732570613792093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209182354276620188303445581 78443382853732570613792093)
      ·
        refine ⟨29416268570149713980172035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78443382853732570613792093 29416268570149713980172035)
        ·
          refine ⟨44124402855224570970258053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29416268570149713980172035 44124402855224570970258053)
          ·
            refine ⟨8273325535354607056923385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44124402855224570970258053 8273325535354607056923385)
            ·
              refine ⟨6204994151515955292692539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273325535354607056923385 6204994151515955292692539)
              ·
                refine ⟨9307491227273932939038809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204994151515955292692539 9307491227273932939038809)
                ·
                  refine ⟨6980618420455449704279107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9307491227273932939038809 6980618420455449704279107)
                  ·
                    refine ⟨10470927630683174556418661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6980618420455449704279107 10470927630683174556418661)
                    ·
                      refine ⟨1963298930753095229328499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10470927630683174556418661 1963298930753095229328499)
                      ·
                        rfl

theorem cell23_3823511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_3823511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823511 prefixEnd_3823511 := by exact prefixLift 3823511
  have htrace : WordTrace (prefixWord ++ tailWord_3823511) baseStart_3823511 baseEnd_3823511 := by
    simpa [prefixWord, tailWord_3823511, baseEnd_3823511] using wordTrace_append hprefix tailTrace_3823511
  have hstable : (prefixWord ++ tailWord_3823511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823511).length < 2 ^ (prefixWord ++ tailWord_3823511).sum := by decide
  have hdescent : baseEnd_3823511 < baseStart_3823511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823547 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 9]
def baseStart_3823547 : Nat := 118140960795 + 3823547 * 2 ^ 59
def prefixEnd_3823547 : Nat := 4983230072969 + 3 ^ 40 * 3823547 * 2
def baseEnd_3823547 : Nat := 654439138685552362826111

theorem tailTrace_3823547 : CollatzResearch.WordTrace tailWord_3823547 prefixEnd_3823547 654439138685552362826111 := by
  unfold tailWord_3823547
  simp only [CollatzResearch.WordTrace]
  refine ⟨139456215878949703683940895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92970810585966469122627263 139456215878949703683940895)
  ·
    refine ⟨209184323818424555525911343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139456215878949703683940895 209184323818424555525911343)
    ·
      refine ⟨313776485727636833288867015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209184323818424555525911343 313776485727636833288867015)
      ·
        refine ⟨470664728591455249933300523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313776485727636833288867015 470664728591455249933300523)
        ·
          refine ⟨705997092887182874899950785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470664728591455249933300523 705997092887182874899950785)
          ·
            refine ⟨529497819665387156174963089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705997092887182874899950785 529497819665387156174963089)
            ·
              refine ⟨397123364749040367131222317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529497819665387156174963089 397123364749040367131222317)
              ·
                refine ⟨148921261780890137674208369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 397123364749040367131222317 148921261780890137674208369)
                ·
                  refine ⟨111690946335667603255656277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148921261780890137674208369 111690946335667603255656277)
                  ·
                    refine ⟨654439138685552362826111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 111690946335667603255656277 654439138685552362826111)
                    ·
                      rfl

theorem cell23_3823547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_3823547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823547 prefixEnd_3823547 := by exact prefixLift 3823547
  have htrace : WordTrace (prefixWord ++ tailWord_3823547) baseStart_3823547 baseEnd_3823547 := by
    simpa [prefixWord, tailWord_3823547, baseEnd_3823547] using wordTrace_append hprefix tailTrace_3823547
  have hstable : (prefixWord ++ tailWord_3823547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823547).length < 2 ^ (prefixWord ++ tailWord_3823547).sum := by decide
  have hdescent : baseEnd_3823547 < baseStart_3823547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823561 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 3]
def baseStart_3823561 : Nat := 118140960795 + 3823561 * 2 ^ 59
def prefixEnd_3823561 : Nat := 4983230072969 + 3 ^ 40 * 3823561 * 2
def baseEnd_3823561 : Nat := 1963324604785820033703269

theorem tailTrace_3823561 : CollatzResearch.WordTrace tailWord_3823561 prefixEnd_3823561 1963324604785820033703269 := by
  unfold tailWord_3823561
  simp only [CollatzResearch.WordTrace]
  refine ⟨139456726500898984074950537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92971151000599322716633691 139456726500898984074950537)
  ·
    refine ⟨104592544875674238056212903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139456726500898984074950537 104592544875674238056212903)
    ·
      refine ⟨156888817313511357084319355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104592544875674238056212903 156888817313511357084319355)
      ·
        refine ⟨235333225970267035626479033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156888817313511357084319355 235333225970267035626479033)
        ·
          refine ⟨176499919477700276719859275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235333225970267035626479033 176499919477700276719859275)
          ·
            refine ⟨264749879216550415079788913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176499919477700276719859275 264749879216550415079788913)
            ·
              refine ⟨198562409412412811309841685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264749879216550415079788913 198562409412412811309841685)
              ·
                refine ⟨9307612941206850530148829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198562409412412811309841685 9307612941206850530148829)
                ·
                  refine ⟨3490354852952568948805811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9307612941206850530148829 3490354852952568948805811)
                  ·
                    refine ⟨5235532279428853423208717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3490354852952568948805811 5235532279428853423208717)
                    ·
                      refine ⟨1963324604785820033703269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5235532279428853423208717 1963324604785820033703269)
                      ·
                        rfl

theorem cell23_3823561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 3].length) (baseStart_3823561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823561 prefixEnd_3823561 := by exact prefixLift 3823561
  have htrace : WordTrace (prefixWord ++ tailWord_3823561) baseStart_3823561 baseEnd_3823561 := by
    simpa [prefixWord, tailWord_3823561, baseEnd_3823561] using wordTrace_append hprefix tailTrace_3823561
  have hstable : (prefixWord ++ tailWord_3823561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823561).length < 2 ^ (prefixWord ++ tailWord_3823561).sum := by decide
  have hdescent : baseEnd_3823561 < baseStart_3823561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823611 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 2, 4]
def baseStart_3823611 : Nat := 118140960795 + 3823611 * 2 ^ 59
def prefixEnd_3823611 : Nat := 4983230072969 + 3 ^ 40 * 3823611 * 2
def baseEnd_3823611 : Nat := 654450092939514946026013

theorem tailTrace_3823611 : CollatzResearch.WordTrace tailWord_3823611 prefixEnd_3823611 654450092939514946026013 := by
  unfold tailWord_3823611
  simp only [CollatzResearch.WordTrace]
  refine ⟨139458550150717842614270687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92972366767145228409513791 139458550150717842614270687)
  ·
    refine ⟨209187825226076763921406031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139458550150717842614270687 209187825226076763921406031)
    ·
      refine ⟨313781737839115145882109047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209187825226076763921406031 313781737839115145882109047)
      ·
        refine ⟨470672606758672718823163571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313781737839115145882109047 470672606758672718823163571)
        ·
          refine ⟨706008910138009078234745357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470672606758672718823163571 706008910138009078234745357)
          ·
            refine ⟨264753341301753404338029509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706008910138009078234745357 264753341301753404338029509)
            ·
              refine ⟨49641251494078763313380533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264753341301753404338029509 49641251494078763313380533)
              ·
                refine ⟨4653867327569884060629425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49641251494078763313380533 4653867327569884060629425)
                ·
                  refine ⟨3490400495677413045472069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653867327569884060629425 3490400495677413045472069)
                  ·
                    refine ⟨654450092939514946026013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490400495677413045472069 654450092939514946026013)
                    ·
                      rfl

theorem cell23_3823611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 4].length) (baseStart_3823611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823611 prefixEnd_3823611 := by exact prefixLift 3823611
  have htrace : WordTrace (prefixWord ++ tailWord_3823611) baseStart_3823611 baseEnd_3823611 := by
    simpa [prefixWord, tailWord_3823611, baseEnd_3823611] using wordTrace_append hprefix tailTrace_3823611
  have hstable : (prefixWord ++ tailWord_3823611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823611).length < 2 ^ (prefixWord ++ tailWord_3823611).sum := by decide
  have hdescent : baseEnd_3823611 < baseStart_3823611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823624 : List Nat := [2, 1, 3, 2, 1, 2, 3, 9]
def baseStart_3823624 : Nat := 118140960795 + 3823624 * 2 ^ 59
def prefixEnd_3823624 : Nat := 4983230072969 + 3 ^ 40 * 3823624 * 2
def baseEnd_3823624 : Nat := 72716924224705677304277

theorem tailTrace_3823624 : CollatzResearch.WordTrace tailWord_3823624 prefixEnd_3823624 72716924224705677304277 := by
  unfold tailWord_3823624
  simp only [CollatzResearch.WordTrace]
  refine ⟨69729512149835372917246963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92972682866447163889662617 69729512149835372917246963)
  ·
    refine ⟨104594268224753059375870445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69729512149835372917246963 104594268224753059375870445)
    ·
      refine ⟨39222850584282397265951417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104594268224753059375870445 39222850584282397265951417)
      ·
        refine ⟨29417137938211797949463563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39222850584282397265951417 29417137938211797949463563)
        ·
          refine ⟨44125706907317696924195345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29417137938211797949463563 44125706907317696924195345)
          ·
            refine ⟨33094280180488272693146509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44125706907317696924195345 33094280180488272693146509)
            ·
              refine ⟨12410355067683102259929941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33094280180488272693146509 12410355067683102259929941)
              ·
                refine ⟨72716924224705677304277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12410355067683102259929941 72716924224705677304277)
                ·
                  rfl

theorem cell23_3823624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 9].length) (baseStart_3823624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823624 prefixEnd_3823624 := by exact prefixLift 3823624
  have htrace : WordTrace (prefixWord ++ tailWord_3823624) baseStart_3823624 baseEnd_3823624 := by
    simpa [prefixWord, tailWord_3823624, baseEnd_3823624] using wordTrace_append hprefix tailTrace_3823624
  have hstable : (prefixWord ++ tailWord_3823624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823624).length < 2 ^ (prefixWord ++ tailWord_3823624).sum := by decide
  have hdescent : baseEnd_3823624 < baseStart_3823624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823662 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3823662 : Nat := 118140960795 + 3823662 * 2 ^ 59
def prefixEnd_3823662 : Nat := 4983230072969 + 3 ^ 40 * 3823662 * 2
def baseEnd_3823662 : Nat := 654458822110641379513435

theorem tailTrace_3823662 : CollatzResearch.WordTrace tailWord_3823662 prefixEnd_3823662 654458822110641379513435 := by
  unfold tailWord_3823662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432551284191634790547155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92973606849022052216251493 17432551284191634790547155)
  ·
    refine ⟨26148826926287452185820733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17432551284191634790547155 26148826926287452185820733)
    ·
      refine ⟨9805810097357794569682775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26148826926287452185820733 9805810097357794569682775)
      ·
        refine ⟨14708715146036691854524163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805810097357794569682775 14708715146036691854524163)
        ·
          refine ⟨22063072719055037781786245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14708715146036691854524163 22063072719055037781786245)
          ·
            refine ⟨4136826134822819584084921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22063072719055037781786245 4136826134822819584084921)
            ·
              refine ⟨3102619601117114688063691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136826134822819584084921 3102619601117114688063691)
              ·
                refine ⟨4653929401675672032095537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102619601117114688063691 4653929401675672032095537)
                ·
                  refine ⟨3490447051256754024071653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653929401675672032095537 3490447051256754024071653)
                  ·
                    refine ⟨654458822110641379513435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490447051256754024071653 654458822110641379513435)
                    ·
                      rfl

theorem cell23_3823662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3823662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823662 prefixEnd_3823662 := by exact prefixLift 3823662
  have htrace : WordTrace (prefixWord ++ tailWord_3823662) baseStart_3823662 baseEnd_3823662 := by
    simpa [prefixWord, tailWord_3823662, baseEnd_3823662] using wordTrace_append hprefix tailTrace_3823662
  have hstable : (prefixWord ++ tailWord_3823662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823662).length < 2 ^ (prefixWord ++ tailWord_3823662).sum := by decide
  have hdescent : baseEnd_3823662 < baseStart_3823662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823672 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 1, 2, 3]
def baseStart_3823672 : Nat := 118140960795 + 3823672 * 2 ^ 59
def prefixEnd_3823672 : Nat := 4983230072969 + 3 ^ 40 * 3823672 * 2
def baseEnd_3823672 : Nat := 1963381601138469099415259

theorem tailTrace_3823672 : CollatzResearch.WordTrace tailWord_3823672 prefixEnd_3823672 1963381601138469099415259 := by
  unfold tailWord_3823672
  simp only [CollatzResearch.WordTrace]
  refine ⟨69730387501748425016120635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92973850002331233354827513 69730387501748425016120635)
  ·
    refine ⟨104595581252622637524180953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69730387501748425016120635 104595581252622637524180953)
    ·
      refine ⟨78446685939466978143135715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104595581252622637524180953 78446685939466978143135715)
      ·
        refine ⟨117670028909200467214703573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78446685939466978143135715 117670028909200467214703573)
        ·
          refine ⟨2757891302559385950344615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117670028909200467214703573 2757891302559385950344615)
          ·
            refine ⟨4136836953839078925516923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757891302559385950344615 4136836953839078925516923)
            ·
              refine ⟨6205255430758618388275385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136836953839078925516923 6205255430758618388275385)
              ·
                refine ⟨4653941573068963791206539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205255430758618388275385 4653941573068963791206539)
                ·
                  refine ⟨6980912359603445686809809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653941573068963791206539 6980912359603445686809809)
                  ·
                    refine ⟨5235684269702584265107357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6980912359603445686809809 5235684269702584265107357)
                    ·
                      refine ⟨1963381601138469099415259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5235684269702584265107357 1963381601138469099415259)
                      ·
                        rfl

theorem cell23_3823672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_3823672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823672 prefixEnd_3823672 := by exact prefixLift 3823672
  have htrace : WordTrace (prefixWord ++ tailWord_3823672) baseStart_3823672 baseEnd_3823672 := by
    simpa [prefixWord, tailWord_3823672, baseEnd_3823672] using wordTrace_append hprefix tailTrace_3823672
  have hstable : (prefixWord ++ tailWord_3823672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823672).length < 2 ^ (prefixWord ++ tailWord_3823672).sum := by decide
  have hdescent : baseEnd_3823672 < baseStart_3823672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823674 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_3823674 : Nat := 118140960795 + 3823674 * 2 ^ 59
def prefixEnd_3823674 : Nat := 4983230072969 + 3 ^ 40 * 3823674 * 2
def baseEnd_3823674 : Nat := 1963382628099778091590249

theorem tailTrace_3823674 : CollatzResearch.WordTrace tailWord_3823674 prefixEnd_3823674 1963382628099778091590249 := by
  unfold tailWord_3823674
  simp only [CollatzResearch.WordTrace]
  refine ⟨34865211987372401093453519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92973898632993069582542717 34865211987372401093453519)
  ·
    refine ⟨52297817981058601640180279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34865211987372401093453519 52297817981058601640180279)
    ·
      refine ⟨78446726971587902460270419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52297817981058601640180279 78446726971587902460270419)
      ·
        refine ⟨117670090457381853690405629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78446726971587902460270419 117670090457381853690405629)
        ·
          refine ⟨44126283921518195133902111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117670090457381853690405629 44126283921518195133902111)
          ·
            refine ⟨66189425882277292700853167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44126283921518195133902111 66189425882277292700853167)
            ·
              refine ⟨99284138823415939051279751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66189425882277292700853167 99284138823415939051279751)
              ·
                refine ⟨148926208235123908576919627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99284138823415939051279751 148926208235123908576919627)
                ·
                  refine ⟨223389312352685862865379441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148926208235123908576919627 223389312352685862865379441)
                  ·
                    refine ⟨167541984264514397149034581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223389312352685862865379441 167541984264514397149034581)
                    ·
                      refine ⟨1963382628099778091590249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 167541984264514397149034581 1963382628099778091590249)
                      ·
                        rfl

theorem cell23_3823674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_3823674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823674 prefixEnd_3823674 := by exact prefixLift 3823674
  have htrace : WordTrace (prefixWord ++ tailWord_3823674) baseStart_3823674 baseEnd_3823674 := by
    simpa [prefixWord, tailWord_3823674, baseEnd_3823674] using wordTrace_append hprefix tailTrace_3823674
  have hstable : (prefixWord ++ tailWord_3823674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823674).length < 2 ^ (prefixWord ++ tailWord_3823674).sum := by decide
  have hdescent : baseEnd_3823674 < baseStart_3823674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823721 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_3823721 : Nat := 118140960795 + 3823721 * 2 ^ 59
def prefixEnd_3823721 : Nat := 4983230072969 + 3 ^ 40 * 3823721 * 2
def baseEnd_3823721 : Nat := 1963406761690539407702533

theorem tailTrace_3823721 : CollatzResearch.WordTrace tailWord_3823721 prefixEnd_3823721 1963406761690539407702533 := by
  unfold tailWord_3823721
  simp only [CollatzResearch.WordTrace]
  refine ⟨139462562180319331400775017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92975041453546220933850011 139462562180319331400775017)
  ·
    refine ⟨104596921635239498550581263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139462562180319331400775017 104596921635239498550581263)
    ·
      refine ⟨156895382452859247825871895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104596921635239498550581263 156895382452859247825871895)
      ·
        refine ⟨235343073679288871738807843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156895382452859247825871895 235343073679288871738807843)
        ·
          refine ⟨353014610518933307608211765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235343073679288871738807843 353014610518933307608211765)
          ·
            refine ⟨33095119736149997588269853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 353014610518933307608211765 33095119736149997588269853)
            ·
              refine ⟨12410669901056249095601195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33095119736149997588269853 12410669901056249095601195)
              ·
                refine ⟨18616004851584373643401793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12410669901056249095601195 18616004851584373643401793)
                ·
                  refine ⟨13962003638688280232551345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18616004851584373643401793 13962003638688280232551345)
                  ·
                    refine ⟨10471502729016210174413509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13962003638688280232551345 10471502729016210174413509)
                    ·
                      refine ⟨1963406761690539407702533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10471502729016210174413509 1963406761690539407702533)
                      ·
                        rfl

theorem cell23_3823721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_3823721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823721 prefixEnd_3823721 := by exact prefixLift 3823721
  have htrace : WordTrace (prefixWord ++ tailWord_3823721) baseStart_3823721 baseEnd_3823721 := by
    simpa [prefixWord, tailWord_3823721, baseEnd_3823721] using wordTrace_append hprefix tailTrace_3823721
  have hstable : (prefixWord ++ tailWord_3823721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823721).length < 2 ^ (prefixWord ++ tailWord_3823721).sum := by decide
  have hdescent : baseEnd_3823721 < baseStart_3823721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823725 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_3823725 : Nat := 118140960795 + 3823725 * 2 ^ 59
def prefixEnd_3823725 : Nat := 4983230072969 + 3 ^ 40 * 3823725 * 2
def baseEnd_3823725 : Nat := 1963408815613157392052515

theorem tailTrace_3823725 : CollatzResearch.WordTrace tailWord_3823725 prefixEnd_3823725 1963408815613157392052515 := by
  unfold tailWord_3823725
  simp only [CollatzResearch.WordTrace]
  refine ⟨139462708072304840083920629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92975138714869893389280419 139462708072304840083920629)
  ·
    refine ⟨13074628881778578757867559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139462708072304840083920629 13074628881778578757867559)
    ·
      refine ⟨19611943322667868136801339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13074628881778578757867559 19611943322667868136801339)
      ·
        refine ⟨29417914984001802205202009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19611943322667868136801339 29417914984001802205202009)
        ·
          refine ⟨22063436238001351653901507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29417914984001802205202009 22063436238001351653901507)
          ·
            refine ⟨33095154357002027480852261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22063436238001351653901507 33095154357002027480852261)
            ·
              refine ⟨6205341441937880152659799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33095154357002027480852261 6205341441937880152659799)
              ·
                refine ⟨9308012162906820228989699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205341441937880152659799 9308012162906820228989699)
                ·
                  refine ⟨13962018244360230343484549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9308012162906820228989699 13962018244360230343484549)
                  ·
                    refine ⟨2617878420817543189403353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13962018244360230343484549 2617878420817543189403353)
                    ·
                      refine ⟨1963408815613157392052515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617878420817543189403353 1963408815613157392052515)
                      ·
                        rfl

theorem cell23_3823725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_3823725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823725 prefixEnd_3823725 := by exact prefixLift 3823725
  have htrace : WordTrace (prefixWord ++ tailWord_3823725) baseStart_3823725 baseEnd_3823725 := by
    simpa [prefixWord, tailWord_3823725, baseEnd_3823725] using wordTrace_append hprefix tailTrace_3823725
  have hstable : (prefixWord ++ tailWord_3823725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823725).length < 2 ^ (prefixWord ++ tailWord_3823725).sum := by decide
  have hdescent : baseEnd_3823725 < baseStart_3823725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823778 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3823778 : Nat := 118140960795 + 3823778 * 2 ^ 59
def prefixEnd_3823778 : Nat := 4983230072969 + 3 ^ 40 * 3823778 * 2
def baseEnd_3823778 : Nat := 654478676695948561563257

theorem tailTrace_3823778 : CollatzResearch.WordTrace tailWord_3823778 prefixEnd_3823778 654478676695948561563257 := by
  unfold tailWord_3823778
  simp only [CollatzResearch.WordTrace]
  refine ⟨34866160285278207533899997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92976427427408553423733325 34866160285278207533899997)
  ·
    refine ⟨13074810106979327825212499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34866160285278207533899997 13074810106979327825212499)
    ·
      refine ⟨19612215160468991737818749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13074810106979327825212499 19612215160468991737818749)
      ·
        refine ⟨7354580685175871901682031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19612215160468991737818749 7354580685175871901682031)
        ·
          refine ⟨11031871027763807852523047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354580685175871901682031 11031871027763807852523047)
          ·
            refine ⟨16547806541645711778784571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11031871027763807852523047 16547806541645711778784571)
            ·
              refine ⟨24821709812468567668176857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16547806541645711778784571 24821709812468567668176857)
              ·
                refine ⟨18616282359351425751132643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24821709812468567668176857 18616282359351425751132643)
                ·
                  refine ⟨27924423539027138626698965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18616282359351425751132643 27924423539027138626698965)
                  ·
                    refine ⟨654478676695948561563257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27924423539027138626698965 654478676695948561563257)
                    ·
                      rfl

theorem cell23_3823778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3823778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823778 prefixEnd_3823778 := by exact prefixLift 3823778
  have htrace : WordTrace (prefixWord ++ tailWord_3823778) baseStart_3823778 baseEnd_3823778 := by
    simpa [prefixWord, tailWord_3823778, baseEnd_3823778] using wordTrace_append hprefix tailTrace_3823778
  have hstable : (prefixWord ++ tailWord_3823778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823778).length < 2 ^ (prefixWord ++ tailWord_3823778).sum := by decide
  have hdescent : baseEnd_3823778 < baseStart_3823778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823781 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3823781 : Nat := 118140960795 + 3823781 * 2 ^ 59
def prefixEnd_3823781 : Nat := 4983230072969 + 3 ^ 40 * 3823781 * 2
def baseEnd_3823781 : Nat := 1963437570529809172952257

theorem tailTrace_3823781 : CollatzResearch.WordTrace tailWord_3823781 prefixEnd_3823781 1963437570529809172952257 := by
  unfold tailWord_3823781
  simp only [CollatzResearch.WordTrace]
  refine ⟨139464750560101961647959197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92976500373401307765306131 139464750560101961647959197)
  ·
    refine ⟨52299281460038235617984699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139464750560101961647959197 52299281460038235617984699)
    ·
      refine ⟨78448922190057353426977049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52299281460038235617984699 78448922190057353426977049)
      ·
        refine ⟨58836691642543015070232787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78448922190057353426977049 58836691642543015070232787)
        ·
          refine ⟨88255037463814522605349181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58836691642543015070232787 88255037463814522605349181)
          ·
            refine ⟨33095639048930445977005943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88255037463814522605349181 33095639048930445977005943)
            ·
              refine ⟨49643458573395668965508915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33095639048930445977005943 49643458573395668965508915)
              ·
                refine ⟨74465187860093503448263373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49643458573395668965508915 74465187860093503448263373)
                ·
                  refine ⟨27924445447535063793098765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74465187860093503448263373 27924445447535063793098765)
                  ·
                    refine ⟨10471667042825648922412037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27924445447535063793098765 10471667042825648922412037)
                    ·
                      refine ⟨1963437570529809172952257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10471667042825648922412037 1963437570529809172952257)
                      ·
                        rfl

theorem cell23_3823781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3823781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823781 prefixEnd_3823781 := by exact prefixLift 3823781
  have htrace : WordTrace (prefixWord ++ tailWord_3823781) baseStart_3823781 baseEnd_3823781 := by
    simpa [prefixWord, tailWord_3823781, baseEnd_3823781] using wordTrace_append hprefix tailTrace_3823781
  have hstable : (prefixWord ++ tailWord_3823781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823781).length < 2 ^ (prefixWord ++ tailWord_3823781).sum := by decide
  have hdescent : baseEnd_3823781 < baseStart_3823781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823825 : List Nat := [1, 2, 2, 1, 2, 2, 2, 6, 1, 4]
def baseStart_3823825 : Nat := 118140960795 + 3823825 * 2 ^ 59
def prefixEnd_3823825 : Nat := 4983230072969 + 3 ^ 40 * 3823825 * 2
def baseEnd_3823825 : Nat := 654486721226202333600685

theorem tailTrace_3823825 : CollatzResearch.WordTrace tailWord_3823825 prefixEnd_3823825 654486721226202333600685 := by
  unfold tailWord_3823825
  simp only [CollatzResearch.WordTrace]
  refine ⟨139466355371942557162560929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92977570247961704775040619 139466355371942557162560929)
  ·
    refine ⟨104599766528956917871920697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139466355371942557162560929 104599766528956917871920697)
    ·
      refine ⟨78449824896717688403940523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104599766528956917871920697 78449824896717688403940523)
      ·
        refine ⟨117674737345076532605910785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78449824896717688403940523 117674737345076532605910785)
        ·
          refine ⟨88256053008807399454433089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117674737345076532605910785 88256053008807399454433089)
          ·
            refine ⟨66192039756605549590824817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88256053008807399454433089 66192039756605549590824817)
            ·
              refine ⟨49644029817454162193118613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66192039756605549590824817 49644029817454162193118613)
              ·
                refine ⟨2327063897693163852802435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49644029817454162193118613 2327063897693163852802435)
                ·
                  refine ⟨3490595846539745779203653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327063897693163852802435 3490595846539745779203653)
                  ·
                    refine ⟨654486721226202333600685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490595846539745779203653 654486721226202333600685)
                    ·
                      rfl

theorem cell23_3823825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_3823825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823825 prefixEnd_3823825 := by exact prefixLift 3823825
  have htrace : WordTrace (prefixWord ++ tailWord_3823825) baseStart_3823825 baseEnd_3823825 := by
    simpa [prefixWord, tailWord_3823825, baseEnd_3823825] using wordTrace_append hprefix tailTrace_3823825
  have hstable : (prefixWord ++ tailWord_3823825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823825).length < 2 ^ (prefixWord ++ tailWord_3823825).sum := by decide
  have hdescent : baseEnd_3823825 < baseStart_3823825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823875 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 2, 3, 2]
def baseStart_3823875 : Nat := 118140960795 + 3823875 * 2 ^ 59
def prefixEnd_3823875 : Nat := 4983230072969 + 3 ^ 40 * 3823875 * 2
def baseEnd_3823875 : Nat := 1963485837711331805176825

theorem tailTrace_3823875 : CollatzResearch.WordTrace tailWord_3823875 prefixEnd_3823875 1963485837711331805176825 := by
  unfold tailWord_3823875
  simp only [CollatzResearch.WordTrace]
  refine ⟨139468179021761415701881079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92978786014507610467920719 139468179021761415701881079)
  ·
    refine ⟨209202268532642123552821619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139468179021761415701881079 209202268532642123552821619)
    ·
      refine ⟨313803402798963185329232429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209202268532642123552821619 313803402798963185329232429)
      ·
        refine ⟨117676276049611194498462161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313803402798963185329232429 117676276049611194498462161)
        ·
          refine ⟨88257207037208395873846621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117676276049611194498462161 88257207037208395873846621)
          ·
            refine ⟨33096452638953148452692483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88257207037208395873846621 33096452638953148452692483)
            ·
              refine ⟨49644678958429722679038725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33096452638953148452692483 49644678958429722679038725)
              ·
                refine ⟨9308377304705573002319761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49644678958429722679038725 9308377304705573002319761)
                ·
                  refine ⟨6981282978529179751739821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9308377304705573002319761 6981282978529179751739821)
                  ·
                    refine ⟨2617981116948442406902433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6981282978529179751739821 2617981116948442406902433)
                    ·
                      refine ⟨1963485837711331805176825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2617981116948442406902433 1963485837711331805176825)
                      ·
                        rfl

theorem cell23_3823875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_3823875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823875 prefixEnd_3823875 := by exact prefixLift 3823875
  have htrace : WordTrace (prefixWord ++ tailWord_3823875) baseStart_3823875 baseEnd_3823875 := by
    simpa [prefixWord, tailWord_3823875, baseEnd_3823875] using wordTrace_append hprefix tailTrace_3823875
  have hstable : (prefixWord ++ tailWord_3823875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823875).length < 2 ^ (prefixWord ++ tailWord_3823875).sum := by decide
  have hdescent : baseEnd_3823875 < baseStart_3823875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823876 : List Nat := [2, 3, 2, 2, 3, 2, 2, 2, 1, 4]
def baseStart_3823876 : Nat := 118140960795 + 3823876 * 2 ^ 59
def prefixEnd_3823876 : Nat := 4983230072969 + 3 ^ 40 * 3823876 * 2
def baseEnd_3823876 : Nat := 654495450397328767088107

theorem tailTrace_3823876 : CollatzResearch.WordTrace tailWord_3823876 prefixEnd_3823876 654495450397328767088107 := by
  unfold tailWord_3823876
  simp only [CollatzResearch.WordTrace]
  refine ⟨69734107747378896436333741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92978810329838528581778321 69734107747378896436333741)
  ·
    refine ⟨26150290405267086163625153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69734107747378896436333741 26150290405267086163625153)
    ·
      refine ⟨19612717803950314622718865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26150290405267086163625153 19612717803950314622718865)
      ·
        refine ⟨14709538352962735967039149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19612717803950314622718865 14709538352962735967039149)
        ·
          refine ⟨5516076882361025987639681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14709538352962735967039149 5516076882361025987639681)
          ·
            refine ⟨4137057661770769490729761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5516076882361025987639681 4137057661770769490729761)
            ·
              refine ⟨3102793246328077118047321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137057661770769490729761 3102793246328077118047321)
              ·
                refine ⟨2327094934746057838535491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102793246328077118047321 2327094934746057838535491)
                ·
                  refine ⟨3490642402119086757803237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327094934746057838535491 3490642402119086757803237)
                  ·
                    refine ⟨654495450397328767088107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490642402119086757803237 654495450397328767088107)
                    ·
                      rfl

theorem cell23_3823876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_3823876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823876 prefixEnd_3823876 := by exact prefixLift 3823876
  have htrace : WordTrace (prefixWord ++ tailWord_3823876) baseStart_3823876 baseEnd_3823876 := by
    simpa [prefixWord, tailWord_3823876, baseEnd_3823876] using wordTrace_append hprefix tailTrace_3823876
  have hstable : (prefixWord ++ tailWord_3823876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823876).length < 2 ^ (prefixWord ++ tailWord_3823876).sum := by decide
  have hdescent : baseEnd_3823876 < baseStart_3823876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823902 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3823902 : Nat := 118140960795 + 3823902 * 2 ^ 59
def prefixEnd_3823902 : Nat := 4983230072969 + 3 ^ 40 * 3823902 * 2
def baseEnd_3823902 : Nat := 654499900563001066513067

theorem tailTrace_3823902 : CollatzResearch.WordTrace tailWord_3823902 prefixEnd_3823902 654499900563001066513067 := by
  unfold tailWord_3823902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17433645474082949914139245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92979442528442399542075973 17433645474082949914139245)
  ·
    refine ⟨6537617052781106217802217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17433645474082949914139245 6537617052781106217802217)
    ·
      refine ⟨4903212789585829663351663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6537617052781106217802217 4903212789585829663351663)
      ·
        refine ⟨7354819184378744495027495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903212789585829663351663 7354819184378744495027495)
        ·
          refine ⟨11032228776568116742541243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354819184378744495027495 11032228776568116742541243)
          ·
            refine ⟨16548343164852175113811865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11032228776568116742541243 16548343164852175113811865)
            ·
              refine ⟨12411257373639131335358899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16548343164852175113811865 12411257373639131335358899)
              ·
                refine ⟨18616886060458697003038349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12411257373639131335358899 18616886060458697003038349)
                ·
                  refine ⟨6981332272672011376139381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18616886060458697003038349 6981332272672011376139381)
                  ·
                    refine ⟨654499900563001066513067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6981332272672011376139381 654499900563001066513067)
                    ·
                      rfl

theorem cell23_3823902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3823902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823902 prefixEnd_3823902 := by exact prefixLift 3823902
  have htrace : WordTrace (prefixWord ++ tailWord_3823902) baseStart_3823902 baseEnd_3823902 := by
    simpa [prefixWord, tailWord_3823902, baseEnd_3823902] using wordTrace_append hprefix tailTrace_3823902
  have hstable : (prefixWord ++ tailWord_3823902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823902).length < 2 ^ (prefixWord ++ tailWord_3823902).sum := by decide
  have hdescent : baseEnd_3823902 < baseStart_3823902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823909 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 2, 3, 2]
def baseStart_3823909 : Nat := 118140960795 + 3823909 * 2 ^ 59
def prefixEnd_3823909 : Nat := 4983230072969 + 3 ^ 40 * 3823909 * 2
def baseEnd_3823909 : Nat := 1963503296053584672151669

theorem tailTrace_3823909 : CollatzResearch.WordTrace tailWord_3823909 prefixEnd_3823909 1963503296053584672151669 := by
  unfold tailWord_3823909
  simp only [CollatzResearch.WordTrace]
  refine ⟨139469419103638239508618781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92979612735758826339079187 139469419103638239508618781)
  ·
    refine ⟨52301032163864339815732043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139469419103638239508618781 52301032163864339815732043)
    ·
      refine ⟨78451548245796509723598065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52301032163864339815732043 78451548245796509723598065)
      ·
        refine ⟨58838661184347382292698549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78451548245796509723598065 58838661184347382292698549)
        ·
          refine ⟨5516124486032567089940489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58838661184347382292698549 5516124486032567089940489)
          ·
            refine ⟨4137093364524425317455367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5516124486032567089940489 4137093364524425317455367)
            ·
              refine ⟨6205640046786637976183051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137093364524425317455367 6205640046786637976183051)
              ·
                refine ⟨9308460070179956964274577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205640046786637976183051 9308460070179956964274577)
                ·
                  refine ⟨6981345052634967723205933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9308460070179956964274577 6981345052634967723205933)
                  ·
                    refine ⟨2618004394738112896202225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6981345052634967723205933 2618004394738112896202225)
                    ·
                      refine ⟨1963503296053584672151669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618004394738112896202225 1963503296053584672151669)
                      ·
                        rfl

theorem cell23_3823909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_3823909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823909 prefixEnd_3823909 := by exact prefixLift 3823909
  have htrace : WordTrace (prefixWord ++ tailWord_3823909) baseStart_3823909 baseEnd_3823909 := by
    simpa [prefixWord, tailWord_3823909, baseEnd_3823909] using wordTrace_append hprefix tailTrace_3823909
  have hstable : (prefixWord ++ tailWord_3823909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823909).length < 2 ^ (prefixWord ++ tailWord_3823909).sum := by decide
  have hdescent : baseEnd_3823909 < baseStart_3823909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823922 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_3823922 : Nat := 118140960795 + 3823922 * 2 ^ 59
def prefixEnd_3823922 : Nat := 4983230072969 + 3 ^ 40 * 3823922 * 2
def baseEnd_3823922 : Nat := 1963509971302093121289109

theorem tailTrace_3823922 : CollatzResearch.WordTrace tailWord_3823922 prefixEnd_3823922 1963509971302093121289109 := by
  unfold tailWord_3823922
  simp only [CollatzResearch.WordTrace]
  refine ⟨34867473313147785682210505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92979928835060761819228013 34867473313147785682210505)
  ·
    refine ⟨26150604984860839261657879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34867473313147785682210505 26150604984860839261657879)
    ·
      refine ⟨39225907477291258892486819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26150604984860839261657879 39225907477291258892486819)
      ·
        refine ⟨58838861215936888338730229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39225907477291258892486819 58838861215936888338730229)
        ·
          refine ⟨5516143238994083281755959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58838861215936888338730229 5516143238994083281755959)
          ·
            refine ⟨8274214858491124922633939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516143238994083281755959 8274214858491124922633939)
            ·
              refine ⟨12411322287736687383950909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274214858491124922633939 12411322287736687383950909)
              ·
                refine ⟨4654245857901257768981591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12411322287736687383950909 4654245857901257768981591)
                ·
                  refine ⟨6981368786851886653472387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654245857901257768981591 6981368786851886653472387)
                  ·
                    refine ⟨10472053180277829980208581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6981368786851886653472387 10472053180277829980208581)
                    ·
                      refine ⟨1963509971302093121289109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10472053180277829980208581 1963509971302093121289109)
                      ·
                        rfl

theorem cell23_3823922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_3823922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823922 prefixEnd_3823922 := by exact prefixLift 3823922
  have htrace : WordTrace (prefixWord ++ tailWord_3823922) baseStart_3823922 baseEnd_3823922 := by
    simpa [prefixWord, tailWord_3823922, baseEnd_3823922] using wordTrace_append hprefix tailTrace_3823922
  have hstable : (prefixWord ++ tailWord_3823922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823922).length < 2 ^ (prefixWord ++ tailWord_3823922).sum := by decide
  have hdescent : baseEnd_3823922 < baseStart_3823922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823939 : List Nat := [1, 1, 1, 3, 1, 3, 4, 4, 1, 2, 2]
def baseStart_3823939 : Nat := 118140960795 + 3823939 * 2 ^ 59
def prefixEnd_3823939 : Nat := 4983230072969 + 3 ^ 40 * 3823939 * 2
def baseEnd_3823939 : Nat := 1963518700473219554776531

theorem tailTrace_3823939 : CollatzResearch.WordTrace tailWord_3823939 prefixEnd_3823939 1963518700473219554776531 := by
  unfold tailWord_3823939
  simp only [CollatzResearch.WordTrace]
  refine ⟨139470513293529554632210871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92980342195686369754807247 139470513293529554632210871)
  ·
    refine ⟨209205769940294331948316307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139470513293529554632210871 209205769940294331948316307)
    ·
      refine ⟨313808654910441497922474461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209205769940294331948316307 313808654910441497922474461)
      ·
        refine ⟨117678245591415561720927923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313808654910441497922474461 117678245591415561720927923)
        ·
          refine ⟨176517368387123342581391885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117678245591415561720927923 176517368387123342581391885)
          ·
            refine ⟨66194013145171253468021957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176517368387123342581391885 66194013145171253468021957)
            ·
              refine ⟨12411377464719610025254117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66194013145171253468021957 12411377464719610025254117)
              ·
                refine ⟨2327133274634926879735147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12411377464719610025254117 2327133274634926879735147)
                ·
                  refine ⟨3490699911952390319602721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327133274634926879735147 3490699911952390319602721)
                  ·
                    refine ⟨2618024933964292739702041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3490699911952390319602721 2618024933964292739702041)
                    ·
                      refine ⟨1963518700473219554776531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618024933964292739702041 1963518700473219554776531)
                      ·
                        rfl

theorem cell23_3823939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_3823939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823939 prefixEnd_3823939 := by exact prefixLift 3823939
  have htrace : WordTrace (prefixWord ++ tailWord_3823939) baseStart_3823939 baseEnd_3823939 := by
    simpa [prefixWord, tailWord_3823939, baseEnd_3823939] using wordTrace_append hprefix tailTrace_3823939
  have hstable : (prefixWord ++ tailWord_3823939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823939).length < 2 ^ (prefixWord ++ tailWord_3823939).sum := by decide
  have hdescent : baseEnd_3823939 < baseStart_3823939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823990 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3823990 : Nat := 118140960795 + 3823990 * 2 ^ 59
def prefixEnd_3823990 : Nat := 4983230072969 + 3 ^ 40 * 3823990 * 2
def baseEnd_3823990 : Nat := 1963544887986598855238797

theorem tailTrace_3823990 : CollatzResearch.WordTrace tailWord_3823990 prefixEnd_3823990 1963544887986598855238797 := by
  unfold tailWord_3823990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717023338521549396394839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92981582277563193561544949 8717023338521549396394839)
  ·
    refine ⟨13075535007782324094592259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717023338521549396394839 13075535007782324094592259)
    ·
      refine ⟨19613302511673486141888389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13075535007782324094592259 19613302511673486141888389)
      ·
        refine ⟨3677494220938778651604073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19613302511673486141888389 3677494220938778651604073)
        ·
          refine ⟨2758120665704083988703055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677494220938778651604073 2758120665704083988703055)
          ·
            refine ⟨4137180998556125983054583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758120665704083988703055 4137180998556125983054583)
            ·
              refine ⟨6205771497834188974581875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137180998556125983054583 6205771497834188974581875)
              ·
                refine ⟨9308657246751283461872813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205771497834188974581875 9308657246751283461872813)
                ·
                  refine ⟨3490746467531731298202305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9308657246751283461872813 3490746467531731298202305)
                  ·
                    refine ⟨2618059850648798473651729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3490746467531731298202305 2618059850648798473651729)
                    ·
                      refine ⟨1963544887986598855238797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618059850648798473651729 1963544887986598855238797)
                      ·
                        rfl

theorem cell23_3823990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3823990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3823990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3823990 prefixEnd_3823990 := by exact prefixLift 3823990
  have htrace : WordTrace (prefixWord ++ tailWord_3823990) baseStart_3823990 baseEnd_3823990 := by
    simpa [prefixWord, tailWord_3823990, baseEnd_3823990] using wordTrace_append hprefix tailTrace_3823990
  have hstable : (prefixWord ++ tailWord_3823990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823990).length < 2 ^ (prefixWord ++ tailWord_3823990).sum := by decide
  have hdescent : baseEnd_3823990 < baseStart_3823990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824029 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_3824029 : Nat := 118140960795 + 3824029 * 2 ^ 59
def prefixEnd_3824029 : Nat := 4983230072969 + 3 ^ 40 * 3824029 * 2
def baseEnd_3824029 : Nat := 1963564913732124202651117

theorem tailTrace_3824029 : CollatzResearch.WordTrace tailWord_3824029 prefixEnd_3824029 1963564913732124202651117 := by
  unfold tailWord_3824029
  simp only [CollatzResearch.WordTrace]
  refine ⟨139473795863203500002987141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92982530575469000001991427 139473795863203500002987141)
  ·
    refine ⟨26151336724350656250560089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139473795863203500002987141 26151336724350656250560089)
    ·
      refine ⟨19613502543262992187920067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26151336724350656250560089 19613502543262992187920067)
      ·
        refine ⟨29420253814894488281880101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19613502543262992187920067 29420253814894488281880101)
        ·
          refine ⟨5516297590292716552852519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29420253814894488281880101 5516297590292716552852519)
          ·
            refine ⟨8274446385439074829278779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516297590292716552852519 8274446385439074829278779)
            ·
              refine ⟨12411669578158612243918169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274446385439074829278779 12411669578158612243918169)
              ·
                refine ⟨9308752183618959182938627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12411669578158612243918169 9308752183618959182938627)
                ·
                  refine ⟨13963128275428438774407941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9308752183618959182938627 13963128275428438774407941)
                  ·
                    refine ⟨2618086551642832270201489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13963128275428438774407941 2618086551642832270201489)
                    ·
                      refine ⟨1963564913732124202651117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618086551642832270201489 1963564913732124202651117)
                      ·
                        rfl

theorem cell23_3824029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_3824029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824029 prefixEnd_3824029 := by exact prefixLift 3824029
  have htrace : WordTrace (prefixWord ++ tailWord_3824029) baseStart_3824029 baseEnd_3824029 := by
    simpa [prefixWord, tailWord_3824029, baseEnd_3824029] using wordTrace_append hprefix tailTrace_3824029
  have hstable : (prefixWord ++ tailWord_3824029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824029).length < 2 ^ (prefixWord ++ tailWord_3824029).sum := by decide
  have hdescent : baseEnd_3824029 < baseStart_3824029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824033 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3824033 : Nat := 118140960795 + 3824033 * 2 ^ 59
def prefixEnd_3824033 : Nat := 4983230072969 + 3 ^ 40 * 3824033 * 2
def baseEnd_3824033 : Nat := 1963566967654742187001099

theorem tailTrace_3824033 : CollatzResearch.WordTrace tailWord_3824033 prefixEnd_3824033 1963566967654742187001099 := by
  unfold tailWord_3824033
  simp only [CollatzResearch.WordTrace]
  refine ⟨139473941755189008686132753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92982627836792672457421835 139473941755189008686132753)
  ·
    refine ⟨104605456316391756514599565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139473941755189008686132753 104605456316391756514599565)
    ·
      refine ⟨39227046118646908692974837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104605456316391756514599565 39227046118646908692974837)
      ·
        refine ⟨3677535573623147689966391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39227046118646908692974837 3677535573623147689966391)
        ·
          refine ⟨5516303360434721534949587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677535573623147689966391 5516303360434721534949587)
          ·
            refine ⟨8274455040652082302424381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516303360434721534949587 8274455040652082302424381)
            ·
              refine ⟨3102920640244530863409143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8274455040652082302424381 3102920640244530863409143)
              ·
                refine ⟨4654380960366796295113715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102920640244530863409143 4654380960366796295113715)
                ·
                  refine ⟨6981571440550194442670573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654380960366796295113715 6981571440550194442670573)
                  ·
                    refine ⟨2618089290206322916001465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6981571440550194442670573 2618089290206322916001465)
                    ·
                      refine ⟨1963566967654742187001099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618089290206322916001465 1963566967654742187001099)
                      ·
                        rfl

theorem cell23_3824033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3824033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824033 prefixEnd_3824033 := by exact prefixLift 3824033
  have htrace : WordTrace (prefixWord ++ tailWord_3824033) baseStart_3824033 baseEnd_3824033 := by
    simpa [prefixWord, tailWord_3824033, baseEnd_3824033] using wordTrace_append hprefix tailTrace_3824033
  have hstable : (prefixWord ++ tailWord_3824033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824033).length < 2 ^ (prefixWord ++ tailWord_3824033).sum := by decide
  have hdescent : baseEnd_3824033 < baseStart_3824033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824112 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 3, 4]
def baseStart_3824112 : Nat := 118140960795 + 3824112 * 2 ^ 59
def prefixEnd_3824112 : Nat := 4983230072969 + 3 ^ 40 * 3824112 * 2
def baseEnd_3824112 : Nat := 654535844208815792637745

theorem tailTrace_3824112 : CollatzResearch.WordTrace tailWord_3824112 prefixEnd_3824112 654535844208815792637745 := by
  unfold tailWord_3824112
  simp only [CollatzResearch.WordTrace]
  refine ⟨69738411560951402589129295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92984548747935203452172393 69738411560951402589129295)
  ·
    refine ⟨104607617341427103883693943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69738411560951402589129295 104607617341427103883693943)
    ·
      refine ⟨156911426012140655825540915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104607617341427103883693943 156911426012140655825540915)
      ·
        refine ⟨235367139018210983738311373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156911426012140655825540915 235367139018210983738311373)
        ·
          refine ⟨88262677131829118901866765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235367139018210983738311373 88262677131829118901866765)
          ·
            refine ⟨33098503924435919588200037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88262677131829118901866765 33098503924435919588200037)
            ·
              refine ⟨6205969485831734922787507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33098503924435919588200037 6205969485831734922787507)
              ·
                refine ⟨9308954228747602384181261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205969485831734922787507 9308954228747602384181261)
                ·
                  refine ⟨3490857835780350894067973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9308954228747602384181261 3490857835780350894067973)
                  ·
                    refine ⟨654535844208815792637745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490857835780350894067973 654535844208815792637745)
                    ·
                      rfl

theorem cell23_3824112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_3824112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824112 prefixEnd_3824112 := by exact prefixLift 3824112
  have htrace : WordTrace (prefixWord ++ tailWord_3824112) baseStart_3824112 baseEnd_3824112 := by
    simpa [prefixWord, tailWord_3824112, baseEnd_3824112] using wordTrace_append hprefix tailTrace_3824112
  have hstable : (prefixWord ++ tailWord_3824112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824112).length < 2 ^ (prefixWord ++ tailWord_3824112).sum := by decide
  have hdescent : baseEnd_3824112 < baseStart_3824112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824189 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_3824189 : Nat := 118140960795 + 3824189 * 2 ^ 59
def prefixEnd_3824189 : Nat := 4983230072969 + 3 ^ 40 * 3824189 * 2
def baseEnd_3824189 : Nat := 654549023545614525550127

theorem tailTrace_3824189 : CollatzResearch.WordTrace tailWord_3824189 prefixEnd_3824189 654549023545614525550127 := by
  unfold tailWord_3824189
  simp only [CollatzResearch.WordTrace]
  refine ⟨139479631542623847328811621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92986421028415898219207747 139479631542623847328811621)
  ·
    refine ⟨26152430914241971374152179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139479631542623847328811621 26152430914241971374152179)
    ·
      refine ⟨39228646371362957061228269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26152430914241971374152179 39228646371362957061228269)
      ·
        refine ⟨14710742389261108897960601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39228646371362957061228269 14710742389261108897960601)
        ·
          refine ⟨11033056791945831673470451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14710742389261108897960601 11033056791945831673470451)
          ·
            refine ⟨16549585187918747510205677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11033056791945831673470451 16549585187918747510205677)
            ·
              refine ⟨6206094445469530316327129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16549585187918747510205677 6206094445469530316327129)
              ·
                refine ⟨4654570834102147737245347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6206094445469530316327129 4654570834102147737245347)
                ·
                  refine ⟨6981856251153221605868021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654570834102147737245347 6981856251153221605868021)
                  ·
                    refine ⟨654549023545614525550127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6981856251153221605868021 654549023545614525550127)
                    ·
                      rfl

theorem cell23_3824189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_3824189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824189 prefixEnd_3824189 := by exact prefixLift 3824189
  have htrace : WordTrace (prefixWord ++ tailWord_3824189) baseStart_3824189 baseEnd_3824189 := by
    simpa [prefixWord, tailWord_3824189, baseEnd_3824189] using wordTrace_append hprefix tailTrace_3824189
  have hstable : (prefixWord ++ tailWord_3824189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824189).length < 2 ^ (prefixWord ++ tailWord_3824189).sum := by decide
  have hdescent : baseEnd_3824189 < baseStart_3824189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824192 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 2, 6, 2]
def baseStart_3824192 : Nat := 118140960795 + 3824192 * 2 ^ 59
def prefixEnd_3824192 : Nat := 4983230072969 + 3 ^ 40 * 3824192 * 2
def baseEnd_3824192 : Nat := 1963648611078807064912867

theorem tailTrace_3824192 : CollatzResearch.WordTrace tailWord_3824192 prefixEnd_3824192 1963648611078807064912867 := by
  unfold tailWord_3824192
  simp only [CollatzResearch.WordTrace]
  refine ⟨69739870480806489420585415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92986493974408652560780553 69739870480806489420585415)
  ·
    refine ⟨104609805721209734130878123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69739870480806489420585415 104609805721209734130878123)
    ·
      refine ⟨156914708581814601196317185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104609805721209734130878123 156914708581814601196317185)
      ·
        refine ⟨117686031436360950897237889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156914708581814601196317185 117686031436360950897237889)
        ·
          refine ⟨88264523577270713172928417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117686031436360950897237889 88264523577270713172928417)
          ·
            refine ⟨66198392682953034879696313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88264523577270713172928417 66198392682953034879696313)
            ·
              refine ⟨49648794512214776159772235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66198392682953034879696313 49648794512214776159772235)
              ·
                refine ⟨74473191768322164239658353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49648794512214776159772235 74473191768322164239658353)
                ·
                  refine ⟨55854893826241623179743765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74473191768322164239658353 55854893826241623179743765)
                  ·
                    refine ⟨2618198148105076086550489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55854893826241623179743765 2618198148105076086550489)
                    ·
                      refine ⟨1963648611078807064912867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618198148105076086550489 1963648611078807064912867)
                      ·
                        rfl

theorem cell23_3824192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_3824192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824192 prefixEnd_3824192 := by exact prefixLift 3824192
  have htrace : WordTrace (prefixWord ++ tailWord_3824192) baseStart_3824192 baseEnd_3824192 := by
    simpa [prefixWord, tailWord_3824192, baseEnd_3824192] using wordTrace_append hprefix tailTrace_3824192
  have hstable : (prefixWord ++ tailWord_3824192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824192).length < 2 ^ (prefixWord ++ tailWord_3824192).sum := by decide
  have hdescent : baseEnd_3824192 < baseStart_3824192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824195 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5]
def baseStart_3824195 : Nat := 118140960795 + 3824195 * 2 ^ 59
def prefixEnd_3824195 : Nat := 4983230072969 + 3 ^ 40 * 3824195 * 2
def baseEnd_3824195 : Nat := 1963650151520770553175353

theorem tailTrace_3824195 : CollatzResearch.WordTrace tailWord_3824195 prefixEnd_3824195 1963650151520770553175353 := by
  unfold tailWord_3824195
  simp only [CollatzResearch.WordTrace]
  refine ⟨139479850380602110353530039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92986566920401406902353359 139479850380602110353530039)
  ·
    refine ⟨209219775570903165530295059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139479850380602110353530039 209219775570903165530295059)
    ·
      refine ⟨313829663356354748295442589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209219775570903165530295059 313829663356354748295442589)
      ·
        refine ⟨117686123758633030610790971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313829663356354748295442589 117686123758633030610790971)
        ·
          refine ⟨176529185637949545916186457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117686123758633030610790971 176529185637949545916186457)
          ·
            refine ⟨132396889228462159437139843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176529185637949545916186457 132396889228462159437139843)
            ·
              refine ⟨198595333842693239155709765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132396889228462159437139843 198595333842693239155709765)
              ·
                refine ⟨37236625095504982341695581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198595333842693239155709765 37236625095504982341695581)
                ·
                  refine ⟨13963734410814368378135843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37236625095504982341695581 13963734410814368378135843)
                  ·
                    refine ⟨20945601616221552567203765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13963734410814368378135843 20945601616221552567203765)
                    ·
                      refine ⟨1963650151520770553175353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20945601616221552567203765 1963650151520770553175353)
                      ·
                        rfl

theorem cell23_3824195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_3824195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824195 prefixEnd_3824195 := by exact prefixLift 3824195
  have htrace : WordTrace (prefixWord ++ tailWord_3824195) baseStart_3824195 baseEnd_3824195 := by
    simpa [prefixWord, tailWord_3824195, baseEnd_3824195] using wordTrace_append hprefix tailTrace_3824195
  have hstable : (prefixWord ++ tailWord_3824195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824195).length < 2 ^ (prefixWord ++ tailWord_3824195).sum := by decide
  have hdescent : baseEnd_3824195 < baseStart_3824195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824202 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_3824202 : Nat := 118140960795 + 3824202 * 2 ^ 59
def prefixEnd_3824202 : Nat := 4983230072969 + 3 ^ 40 * 3824202 * 2
def baseEnd_3824202 : Nat := 654551248628450675262607

theorem tailTrace_3824202 : CollatzResearch.WordTrace tailWord_3824202 prefixEnd_3824202 654551248628450675262607 := by
  unfold tailWord_3824202
  simp only [CollatzResearch.WordTrace]
  refine ⟨34870026422894187637258715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92986737127717833699356573 34870026422894187637258715)
  ·
    refine ⟨52305039634341281455888073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34870026422894187637258715 52305039634341281455888073)
    ·
      refine ⟨39228779725755961091916055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52305039634341281455888073 39228779725755961091916055)
      ·
        refine ⟨58843169588633941637874083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39228779725755961091916055 58843169588633941637874083)
        ·
          refine ⟨88264754382950912456811125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58843169588633941637874083 88264754382950912456811125)
          ·
            refine ⟨8274820723401648042826043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88264754382950912456811125 8274820723401648042826043)
            ·
              refine ⟨12412231085102472064239065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274820723401648042826043 12412231085102472064239065)
              ·
                refine ⟨9309173313826854048179299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12412231085102472064239065 9309173313826854048179299)
                ·
                  refine ⟨13963759970740281072268949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309173313826854048179299 13963759970740281072268949)
                  ·
                    refine ⟨654551248628450675262607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13963759970740281072268949 654551248628450675262607)
                    ·
                      rfl

theorem cell23_3824202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_3824202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824202 prefixEnd_3824202 := by exact prefixLift 3824202
  have htrace : WordTrace (prefixWord ++ tailWord_3824202) baseStart_3824202 baseEnd_3824202 := by
    simpa [prefixWord, tailWord_3824202, baseEnd_3824202] using wordTrace_append hprefix tailTrace_3824202
  have hstable : (prefixWord ++ tailWord_3824202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824202).length < 2 ^ (prefixWord ++ tailWord_3824202).sum := by decide
  have hdescent : baseEnd_3824202 < baseStart_3824202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824260 : List Nat := [2, 3, 2, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_3824260 : Nat := 118140960795 + 3824260 * 2 ^ 59
def prefixEnd_3824260 : Nat := 4983230072969 + 3 ^ 40 * 3824260 * 2
def baseEnd_3824260 : Nat := 1963683527763312798862555

theorem tailTrace_3824260 : CollatzResearch.WordTrace tailWord_3824260 prefixEnd_3824260 1963683527763312798862555 := by
  unfold tailWord_3824260
  simp only [CollatzResearch.WordTrace]
  refine ⟨69741110562683313227323117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92988147416911084303097489 69741110562683313227323117)
  ·
    refine ⟨26152916461006242460246169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69741110562683313227323117 26152916461006242460246169)
    ·
      refine ⟨19614687345754681845184627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26152916461006242460246169 19614687345754681845184627)
      ·
        refine ⟨29422031018632022767776941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19614687345754681845184627 29422031018632022767776941)
        ·
          refine ⟨11033261631987008537916353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29422031018632022767776941 11033261631987008537916353)
          ·
            refine ⟨8274946223990256403437265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11033261631987008537916353 8274946223990256403437265)
            ·
              refine ⟨6206209667992692302577949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8274946223990256403437265 6206209667992692302577949)
              ·
                refine ⟨2327328625497259613466731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6206209667992692302577949 2327328625497259613466731)
                ·
                  refine ⟨3490992938245889420200097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327328625497259613466731 3490992938245889420200097)
                  ·
                    refine ⟨2618244703684417065150073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3490992938245889420200097 2618244703684417065150073)
                    ·
                      refine ⟨1963683527763312798862555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618244703684417065150073 1963683527763312798862555)
                      ·
                        rfl

theorem cell23_3824260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_3824260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824260 prefixEnd_3824260 := by exact prefixLift 3824260
  have htrace : WordTrace (prefixWord ++ tailWord_3824260) baseStart_3824260 baseEnd_3824260 := by
    simpa [prefixWord, tailWord_3824260, baseEnd_3824260] using wordTrace_append hprefix tailTrace_3824260
  have hstable : (prefixWord ++ tailWord_3824260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824260).length < 2 ^ (prefixWord ++ tailWord_3824260).sum := by decide
  have hdescent : baseEnd_3824260 < baseStart_3824260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824275 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 3, 8]
def baseStart_3824275 : Nat := 118140960795 + 3824275 * 2 ^ 59
def prefixEnd_3824275 : Nat := 4983230072969 + 3 ^ 40 * 3824275 * 2
def baseEnd_3824275 : Nat := 654563743324376746724995

theorem tailTrace_3824275 : CollatzResearch.WordTrace tailWord_3824275 prefixEnd_3824275 654563743324376746724995 := by
  unfold tailWord_3824275
  simp only [CollatzResearch.WordTrace]
  refine ⟨139482768220312284016442279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92988512146874856010961519 139482768220312284016442279)
  ·
    refine ⟨209224152330468426024663419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139482768220312284016442279 209224152330468426024663419)
    ·
      refine ⟨313836228495702639036995129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209224152330468426024663419 313836228495702639036995129)
      ·
        refine ⟨235377171371776979277746347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313836228495702639036995129 235377171371776979277746347)
        ·
          refine ⟨353065757057665468916619521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235377171371776979277746347 353065757057665468916619521)
          ·
            refine ⟨264799317793249101687464641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353065757057665468916619521 264799317793249101687464641)
            ·
              refine ⟨198599488344936826265598481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264799317793249101687464641 198599488344936826265598481)
              ·
                refine ⟨148949616258702619699198861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198599488344936826265598481 148949616258702619699198861)
                ·
                  refine ⟨55856106097013482387199573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148949616258702619699198861 55856106097013482387199573)
                  ·
                    refine ⟨654563743324376746724995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55856106097013482387199573 654563743324376746724995)
                    ·
                      rfl

theorem cell23_3824275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 8].length) (baseStart_3824275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824275 prefixEnd_3824275 := by exact prefixLift 3824275
  have htrace : WordTrace (prefixWord ++ tailWord_3824275) baseStart_3824275 baseEnd_3824275 := by
    simpa [prefixWord, tailWord_3824275, baseEnd_3824275] using wordTrace_append hprefix tailTrace_3824275
  have hstable : (prefixWord ++ tailWord_3824275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824275).length < 2 ^ (prefixWord ++ tailWord_3824275).sum := by decide
  have hdescent : baseEnd_3824275 < baseStart_3824275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824292 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_3824292 : Nat := 118140960795 + 3824292 * 2 ^ 59
def prefixEnd_3824292 : Nat := 4983230072969 + 3 ^ 40 * 3824292 * 2
def baseEnd_3824292 : Nat := 654566653048085557887469

theorem tailTrace_3824292 : CollatzResearch.WordTrace tailWord_3824292 prefixEnd_3824292 654566653048085557887469 := by
  unfold tailWord_3824292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69741694130625347959905565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92988925507500463946540753 69741694130625347959905565)
  ·
    refine ⟨26153135298984505484964587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69741694130625347959905565 26153135298984505484964587)
    ·
      refine ⟨39229702948476758227446881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26153135298984505484964587 39229702948476758227446881)
      ·
        refine ⟨29422277211357568670585161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39229702948476758227446881 29422277211357568670585161)
        ·
          refine ⟨22066707908518176502938871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29422277211357568670585161 22066707908518176502938871)
          ·
            refine ⟨33100061862777264754408307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22066707908518176502938871 33100061862777264754408307)
            ·
              refine ⟨49650092794165897131612461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33100061862777264754408307 49650092794165897131612461)
              ·
                refine ⟨18618784797812211424354673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49650092794165897131612461 18618784797812211424354673)
                ·
                  refine ⟨13964088598359158568266005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18618784797812211424354673 13964088598359158568266005)
                  ·
                    refine ⟨654566653048085557887469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13964088598359158568266005 654566653048085557887469)
                    ·
                      rfl

theorem cell23_3824292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_3824292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824292 prefixEnd_3824292 := by exact prefixLift 3824292
  have htrace : WordTrace (prefixWord ++ tailWord_3824292) baseStart_3824292 baseEnd_3824292 := by
    simpa [prefixWord, tailWord_3824292, baseEnd_3824292] using wordTrace_append hprefix tailTrace_3824292
  have hstable : (prefixWord ++ tailWord_3824292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824292).length < 2 ^ (prefixWord ++ tailWord_3824292).sum := by decide
  have hdescent : baseEnd_3824292 < baseStart_3824292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824316 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_3824316 : Nat := 118140960795 + 3824316 * 2 ^ 59
def prefixEnd_3824316 : Nat := 4983230072969 + 3 ^ 40 * 3824316 * 2
def baseEnd_3824316 : Nat := 1963712282679964579762297

theorem tailTrace_3824316 : CollatzResearch.WordTrace tailWord_3824316 prefixEnd_3824316 1963712282679964579762297 := by
  unfold tailWord_3824316
  simp only [CollatzResearch.WordTrace]
  refine ⟨69742131806581874009342401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92989509075442498679123201 69742131806581874009342401)
  ·
    refine ⟨52306598854936405507006801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69742131806581874009342401 52306598854936405507006801)
    ·
      refine ⟨39229949141202304130255101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52306598854936405507006801 39229949141202304130255101)
      ·
        refine ⟨14711230927950864048845663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39229949141202304130255101 14711230927950864048845663)
        ·
          refine ⟨22066846391926296073268495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14711230927950864048845663 22066846391926296073268495)
          ·
            refine ⟨33100269587889444109902743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22066846391926296073268495 33100269587889444109902743)
            ·
              refine ⟨49650404381834166164854115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33100269587889444109902743 49650404381834166164854115)
              ·
                refine ⟨74475606572751249247281173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49650404381834166164854115 74475606572751249247281173)
                ·
                  refine ⟨3491044058097714808466305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74475606572751249247281173 3491044058097714808466305)
                  ·
                    refine ⟨2618283043573286106349729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3491044058097714808466305 2618283043573286106349729)
                    ·
                      refine ⟨1963712282679964579762297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618283043573286106349729 1963712282679964579762297)
                      ·
                        rfl

theorem cell23_3824316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_3824316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824316 prefixEnd_3824316 := by exact prefixLift 3824316
  have htrace : WordTrace (prefixWord ++ tailWord_3824316) baseStart_3824316 baseEnd_3824316 := by
    simpa [prefixWord, tailWord_3824316, baseEnd_3824316] using wordTrace_append hprefix tailTrace_3824316
  have hstable : (prefixWord ++ tailWord_3824316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824316).length < 2 ^ (prefixWord ++ tailWord_3824316).sum := by decide
  have hdescent : baseEnd_3824316 < baseStart_3824316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824352 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 6, 5]
def baseStart_3824352 : Nat := 118140960795 + 3824352 * 2 ^ 59
def prefixEnd_3824352 : Nat := 4983230072969 + 3 ^ 40 * 3824352 * 2
def baseEnd_3824352 : Nat := 654576922661175479637377

theorem tailTrace_3824352 : CollatzResearch.WordTrace tailWord_3824352 prefixEnd_3824352 654576922661175479637377 := by
  unfold tailWord_3824352
  simp only [CollatzResearch.WordTrace]
  refine ⟨69742788320516663083497655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92990384427355550777996873 69742788320516663083497655)
  ·
    refine ⟨104614182480774994625246483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69742788320516663083497655 104614182480774994625246483)
    ·
      refine ⟨156921273721162491937869725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104614182480774994625246483 156921273721162491937869725)
      ·
        refine ⟨58845477645435934476701147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156921273721162491937869725 58845477645435934476701147)
        ·
          refine ⟨88268216468153901715051721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58845477645435934476701147 88268216468153901715051721)
          ·
            refine ⟨66201162351115426286288791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88268216468153901715051721 66201162351115426286288791)
            ·
              refine ⟨99301743526673139429433187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66201162351115426286288791 99301743526673139429433187)
              ·
                refine ⟨148952615290009709144149781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99301743526673139429433187 148952615290009709144149781)
                ·
                  refine ⟨6982153841719205116132021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148952615290009709144149781 6982153841719205116132021)
                  ·
                    refine ⟨654576922661175479637377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6982153841719205116132021 654576922661175479637377)
                    ·
                      rfl

theorem cell23_3824352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_3824352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824352 prefixEnd_3824352 := by exact prefixLift 3824352
  have htrace : WordTrace (prefixWord ++ tailWord_3824352) baseStart_3824352 baseEnd_3824352 := by
    simpa [prefixWord, tailWord_3824352, baseEnd_3824352] using wordTrace_append hprefix tailTrace_3824352
  have hstable : (prefixWord ++ tailWord_3824352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824352).length < 2 ^ (prefixWord ++ tailWord_3824352).sum := by decide
  have hdescent : baseEnd_3824352 < baseStart_3824352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824362 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_3824362 : Nat := 118140960795 + 3824362 * 2 ^ 59
def prefixEnd_3824362 : Nat := 4983230072969 + 3 ^ 40 * 3824362 * 2
def baseEnd_3824362 : Nat := 1963735902790071399787085

theorem tailTrace_3824362 : CollatzResearch.WordTrace tailWord_3824362 prefixEnd_3824362 1963735902790071399787085 := by
  unfold tailWord_3824362
  simp only [CollatzResearch.WordTrace]
  refine ⟨34871485342749274468714835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92990627580664731916572893 34871485342749274468714835)
  ·
    refine ⟨52307228014123911703072253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34871485342749274468714835 52307228014123911703072253)
    ·
      refine ⟨19615210505296466888652095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52307228014123911703072253 19615210505296466888652095)
      ·
        refine ⟨29422815757944700332978143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19615210505296466888652095 29422815757944700332978143)
        ·
          refine ⟨44134223636917050499467215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29422815757944700332978143 44134223636917050499467215)
          ·
            refine ⟨66201335455375575749200823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44134223636917050499467215 66201335455375575749200823)
            ·
              refine ⟨99302003183063363623801235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66201335455375575749200823 99302003183063363623801235)
              ·
                refine ⟨148953004774595045435701853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99302003183063363623801235 148953004774595045435701853)
                ·
                  refine ⟨55857376790473142038388195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148953004774595045435701853 55857376790473142038388195)
                  ·
                    refine ⟨83786065185709713057582293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55857376790473142038388195 83786065185709713057582293)
                    ·
                      refine ⟨1963735902790071399787085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83786065185709713057582293 1963735902790071399787085)
                      ·
                        rfl

theorem cell23_3824362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_3824362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824362 prefixEnd_3824362 := by exact prefixLift 3824362
  have htrace : WordTrace (prefixWord ++ tailWord_3824362) baseStart_3824362 baseEnd_3824362 := by
    simpa [prefixWord, tailWord_3824362, baseEnd_3824362] using wordTrace_append hprefix tailTrace_3824362
  have hstable : (prefixWord ++ tailWord_3824362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824362).length < 2 ^ (prefixWord ++ tailWord_3824362).sum := by decide
  have hdescent : baseEnd_3824362 < baseStart_3824362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824369 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 2, 5]
def baseStart_3824369 : Nat := 118140960795 + 3824369 * 2 ^ 59
def prefixEnd_3824369 : Nat := 4983230072969 + 3 ^ 40 * 3824369 * 2
def baseEnd_3824369 : Nat := 654579832384884290799851

theorem tailTrace_3824369 : CollatzResearch.WordTrace tailWord_3824369 prefixEnd_3824369 654579832384884290799851 := by
  unfold tailWord_3824369
  simp only [CollatzResearch.WordTrace]
  refine ⟨139486196681971738070364161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92990797787981158713576107 139486196681971738070364161)
  ·
    refine ⟨104614647511478803552773121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139486196681971738070364161 104614647511478803552773121)
    ·
      refine ⟨78460985633609102664579841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104614647511478803552773121 78460985633609102664579841)
      ·
        refine ⟨58845739225206826998434881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78460985633609102664579841 58845739225206826998434881)
        ·
          refine ⟨44134304418905120248826161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58845739225206826998434881 44134304418905120248826161)
          ·
            refine ⟨33100728314178840186619621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44134304418905120248826161 33100728314178840186619621)
            ·
              refine ⟨6206386558908532534991179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33100728314178840186619621 6206386558908532534991179)
              ·
                refine ⟨9309579838362798802486769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206386558908532534991179 9309579838362798802486769)
                ·
                  refine ⟨6982184878772099101865077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9309579838362798802486769 6982184878772099101865077)
                  ·
                    refine ⟨654579832384884290799851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6982184878772099101865077 654579832384884290799851)
                    ·
                      rfl

theorem cell23_3824369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_3824369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824369 prefixEnd_3824369 := by exact prefixLift 3824369
  have htrace : WordTrace (prefixWord ++ tailWord_3824369) baseStart_3824369 baseEnd_3824369 := by
    simpa [prefixWord, tailWord_3824369, baseEnd_3824369] using wordTrace_append hprefix tailTrace_3824369
  have hstable : (prefixWord ++ tailWord_3824369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824369).length < 2 ^ (prefixWord ++ tailWord_3824369).sum := by decide
  have hdescent : baseEnd_3824369 < baseStart_3824369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824386 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3824386 : Nat := 118140960795 + 3824386 * 2 ^ 59
def prefixEnd_3824386 : Nat := 4983230072969 + 3 ^ 40 * 3824386 * 2
def baseEnd_3824386 : Nat := 654582742108593101962325

theorem tailTrace_3824386 : CollatzResearch.WordTrace tailWord_3824386 prefixEnd_3824386 654582742108593101962325 := by
  unfold tailWord_3824386
  simp only [CollatzResearch.WordTrace]
  refine ⟨34871704180727537493433253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92991211148606766649155341 34871704180727537493433253)
  ·
    refine ⟨6538444533886413280018735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34871704180727537493433253 6538444533886413280018735)
    ·
      refine ⟨9807666800829619920028103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6538444533886413280018735 9807666800829619920028103)
      ·
        refine ⟨14711500201244429880042155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9807666800829619920028103 14711500201244429880042155)
        ·
          refine ⟨22067250301866644820063233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14711500201244429880042155 22067250301866644820063233)
          ·
            refine ⟨16550437726399983615047425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22067250301866644820063233 16550437726399983615047425)
            ·
              refine ⟨12412828294799987711285569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16550437726399983615047425 12412828294799987711285569)
              ·
                refine ⟨9309621221099990783464177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12412828294799987711285569 9309621221099990783464177)
                ·
                  refine ⟨6982215915824993087598133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9309621221099990783464177 6982215915824993087598133)
                  ·
                    refine ⟨654582742108593101962325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6982215915824993087598133 654582742108593101962325)
                    ·
                      rfl

theorem cell23_3824386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3824386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824386 prefixEnd_3824386 := by exact prefixLift 3824386
  have htrace : WordTrace (prefixWord ++ tailWord_3824386) baseStart_3824386 baseEnd_3824386 := by
    simpa [prefixWord, tailWord_3824386, baseEnd_3824386] using wordTrace_append hprefix tailTrace_3824386
  have hstable : (prefixWord ++ tailWord_3824386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824386).length < 2 ^ (prefixWord ++ tailWord_3824386).sum := by decide
  have hdescent : baseEnd_3824386 < baseStart_3824386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824389 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 3, 6, 2]
def baseStart_3824389 : Nat := 118140960795 + 3824389 * 2 ^ 59
def prefixEnd_3824389 : Nat := 4983230072969 + 3 ^ 40 * 3824389 * 2
def baseEnd_3824389 : Nat := 1963749766767742794149461

theorem tailTrace_3824389 : CollatzResearch.WordTrace tailWord_3824389 prefixEnd_3824389 1963749766767742794149461 := by
  unfold tailWord_3824389
  simp only [CollatzResearch.WordTrace]
  refine ⟨139486926141899281486092221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92991284094599520990728147 139486926141899281486092221)
  ·
    refine ⟨52307597303212230557284583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139486926141899281486092221 52307597303212230557284583)
    ·
      refine ⟨78461395954818345835926875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52307597303212230557284583 78461395954818345835926875)
      ·
        refine ⟨117692093932227518753890313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78461395954818345835926875 117692093932227518753890313)
        ·
          refine ⟨88269070449170639065417735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117692093932227518753890313 88269070449170639065417735)
          ·
            refine ⟨132403605673755958598126603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88269070449170639065417735 132403605673755958598126603)
            ·
              refine ⟨198605408510633937897189905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132403605673755958598126603 198605408510633937897189905)
              ·
                refine ⟨148954056382975453422892429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198605408510633937897189905 148954056382975453422892429)
                ·
                  refine ⟨55857771143615795033584661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148954056382975453422892429 55857771143615795033584661)
                  ·
                    refine ⟨2618333022356990392199281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55857771143615795033584661 2618333022356990392199281)
                    ·
                      refine ⟨1963749766767742794149461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618333022356990392199281 1963749766767742794149461)
                      ·
                        rfl

theorem cell23_3824389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_3824389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824389 prefixEnd_3824389 := by exact prefixLift 3824389
  have htrace : WordTrace (prefixWord ++ tailWord_3824389) baseStart_3824389 baseEnd_3824389 := by
    simpa [prefixWord, tailWord_3824389, baseEnd_3824389] using wordTrace_append hprefix tailTrace_3824389
  have hstable : (prefixWord ++ tailWord_3824389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824389).length < 2 ^ (prefixWord ++ tailWord_3824389).sum := by decide
  have hdescent : baseEnd_3824389 < baseStart_3824389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824399 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 3, 4]
def baseStart_3824399 : Nat := 118140960795 + 3824399 * 2 ^ 59
def prefixEnd_3824399 : Nat := 4983230072969 + 3 ^ 40 * 3824399 * 2
def baseEnd_3824399 : Nat := 654584967191429251674805

theorem tailTrace_3824399 : CollatzResearch.WordTrace tailWord_3824399 prefixEnd_3824399 654584967191429251674805 := by
  unfold tailWord_3824399
  simp only [CollatzResearch.WordTrace]
  refine ⟨139487290871863053193956251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92991527247908702129304167 139487290871863053193956251)
  ·
    refine ⟨209230936307794579790934377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139487290871863053193956251 209230936307794579790934377)
    ·
      refine ⟨156923202230845934843200783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209230936307794579790934377 156923202230845934843200783)
      ·
        refine ⟨235384803346268902264801175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156923202230845934843200783 235384803346268902264801175)
        ·
          refine ⟨353077205019403353397201763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235384803346268902264801175 353077205019403353397201763)
          ·
            refine ⟨529615807529105030095802645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353077205019403353397201763 529615807529105030095802645)
            ·
              refine ⟨24825740977926798285740749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 529615807529105030095802645 24825740977926798285740749)
              ·
                refine ⟨9309652866722549357152781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24825740977926798285740749 9309652866722549357152781)
                ·
                  refine ⟨3491119825020956008932293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9309652866722549357152781 3491119825020956008932293)
                  ·
                    refine ⟨654584967191429251674805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3491119825020956008932293 654584967191429251674805)
                    ·
                      rfl

theorem cell23_3824399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 4].length) (baseStart_3824399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824399 prefixEnd_3824399 := by exact prefixLift 3824399
  have htrace : WordTrace (prefixWord ++ tailWord_3824399) baseStart_3824399 baseEnd_3824399 := by
    simpa [prefixWord, tailWord_3824399, baseEnd_3824399] using wordTrace_append hprefix tailTrace_3824399
  have hstable : (prefixWord ++ tailWord_3824399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824399).length < 2 ^ (prefixWord ++ tailWord_3824399).sum := by decide
  have hdescent : baseEnd_3824399 < baseStart_3824399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824416 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 3, 4]
def baseStart_3824416 : Nat := 118140960795 + 3824416 * 2 ^ 59
def prefixEnd_3824416 : Nat := 4983230072969 + 3 ^ 40 * 3824416 * 2
def baseEnd_3824416 : Nat := 654587876915138062837279

theorem tailTrace_3824416 : CollatzResearch.WordTrace tailWord_3824416 prefixEnd_3824416 654587876915138062837279 := by
  unfold tailWord_3824416
  simp only [CollatzResearch.WordTrace]
  refine ⟨69743955456400732548662551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92991940608534310064883401 69743955456400732548662551)
  ·
    refine ⟨104615933184601098822993827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69743955456400732548662551 104615933184601098822993827)
    ·
      refine ⟨156923899776901648234490741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104615933184601098822993827 156923899776901648234490741)
      ·
        refine ⟨14711615604084529521983507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156923899776901648234490741 14711615604084529521983507)
        ·
          refine ⟨22067423406126794282975261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14711615604084529521983507 22067423406126794282975261)
          ·
            refine ⟨8275283777297547856115723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22067423406126794282975261 8275283777297547856115723)
            ·
              refine ⟨12412925665946321784173585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275283777297547856115723 12412925665946321784173585)
              ·
                refine ⟨9309694249459741338130189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12412925665946321784173585 9309694249459741338130189)
                ·
                  refine ⟨3491135343547403001798821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9309694249459741338130189 3491135343547403001798821)
                  ·
                    refine ⟨654587876915138062837279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3491135343547403001798821 654587876915138062837279)
                    ·
                      rfl

theorem cell23_3824416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_3824416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824416 prefixEnd_3824416 := by exact prefixLift 3824416
  have htrace : WordTrace (prefixWord ++ tailWord_3824416) baseStart_3824416 baseEnd_3824416 := by
    simpa [prefixWord, tailWord_3824416, baseEnd_3824416] using wordTrace_append hprefix tailTrace_3824416
  have hstable : (prefixWord ++ tailWord_3824416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824416).length < 2 ^ (prefixWord ++ tailWord_3824416).sum := by decide
  have hdescent : baseEnd_3824416 < baseStart_3824416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824432 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_3824432 : Nat := 118140960795 + 3824432 * 2 ^ 59
def prefixEnd_3824432 : Nat := 4983230072969 + 3 ^ 40 * 3824432 * 2
def baseEnd_3824432 : Nat := 1963771846435886125911763

theorem tailTrace_3824432 : CollatzResearch.WordTrace tailWord_3824432 prefixEnd_3824432 1963771846435886125911763 := by
  unfold tailWord_3824432
  simp only [CollatzResearch.WordTrace]
  refine ⟨69744247240371749914953775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92992329653828999886605033 69744247240371749914953775)
  ·
    refine ⟨104616370860557624872430663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69744247240371749914953775 104616370860557624872430663)
    ·
      refine ⟨156924556290836437308645995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104616370860557624872430663 156924556290836437308645995)
      ·
        refine ⟨235386834436254655962968993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156924556290836437308645995 235386834436254655962968993)
        ·
          refine ⟨176540125827190991972226745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235386834436254655962968993 176540125827190991972226745)
          ·
            refine ⟨132405094370393243979170059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176540125827190991972226745 132405094370393243979170059)
            ·
              refine ⟨198607641555589865968755089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132405094370393243979170059 198607641555589865968755089)
              ·
                refine ⟨148955731166692399476566317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198607641555589865968755089 148955731166692399476566317)
                ·
                  refine ⟨55858399187509649803712369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148955731166692399476566317 55858399187509649803712369)
                  ·
                    refine ⟨41893799390632237352784277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55858399187509649803712369 41893799390632237352784277)
                    ·
                      refine ⟨1963771846435886125911763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41893799390632237352784277 1963771846435886125911763)
                      ·
                        rfl

theorem cell23_3824432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_3824432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824432 prefixEnd_3824432 := by exact prefixLift 3824432
  have htrace : WordTrace (prefixWord ++ tailWord_3824432) baseStart_3824432 baseEnd_3824432 := by
    simpa [prefixWord, tailWord_3824432, baseEnd_3824432] using wordTrace_append hprefix tailTrace_3824432
  have hstable : (prefixWord ++ tailWord_3824432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824432).length < 2 ^ (prefixWord ++ tailWord_3824432).sum := by decide
  have hdescent : baseEnd_3824432 < baseStart_3824432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824433 : List Nat := [1, 2, 2, 3, 2, 1, 4, 3, 1, 4]
def baseStart_3824433 : Nat := 118140960795 + 3824433 * 2 ^ 59
def prefixEnd_3824433 : Nat := 4983230072969 + 3 ^ 40 * 3824433 * 2
def baseEnd_3824433 : Nat := 654590786638846873999753

theorem tailTrace_3824433 : CollatzResearch.WordTrace tailWord_3824433 prefixEnd_3824433 654590786638846873999753 := by
  unfold tailWord_3824433
  simp only [CollatzResearch.WordTrace]
  refine ⟨139488530953739877000693953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92992353969159918000462635 139488530953739877000693953)
  ·
    refine ⟨104616398215304907750520465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139488530953739877000693953 104616398215304907750520465)
    ·
      refine ⟨78462298661478680812890349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104616398215304907750520465 78462298661478680812890349)
      ·
        refine ⟨29423361998054505304833881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78462298661478680812890349 29423361998054505304833881)
        ·
          refine ⟨22067521498540878978625411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29423361998054505304833881 22067521498540878978625411)
          ·
            refine ⟨33101282247811318467938117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22067521498540878978625411 33101282247811318467938117)
            ·
              refine ⟨6206490421464622212738397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33101282247811318467938117 6206490421464622212738397)
              ·
                refine ⟨2327433908049233329776899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6206490421464622212738397 2327433908049233329776899)
                ·
                  refine ⟨3491150862073849994665349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327433908049233329776899 3491150862073849994665349)
                  ·
                    refine ⟨654590786638846873999753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3491150862073849994665349 654590786638846873999753)
                    ·
                      rfl

theorem cell23_3824433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_3824433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824433 prefixEnd_3824433 := by exact prefixLift 3824433
  have htrace : WordTrace (prefixWord ++ tailWord_3824433) baseStart_3824433 baseEnd_3824433 := by
    simpa [prefixWord, tailWord_3824433, baseEnd_3824433] using wordTrace_append hprefix tailTrace_3824433
  have hstable : (prefixWord ++ tailWord_3824433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824433).length < 2 ^ (prefixWord ++ tailWord_3824433).sum := by decide
  have hdescent : baseEnd_3824433 < baseStart_3824433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824446 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3824446 : Nat := 118140960795 + 3824446 * 2 ^ 59
def prefixEnd_3824446 : Nat := 4983230072969 + 3 ^ 40 * 3824446 * 2
def baseEnd_3824446 : Nat := 218197670573894341237411

theorem tailTrace_3824446 : CollatzResearch.WordTrace tailWord_3824446 prefixEnd_3824446 218197670573894341237411 := by
  unfold tailWord_3824446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17436125637836597527614649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92992670068461853480611461 17436125637836597527614649)
  ·
    refine ⟨13077094228377448145710987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17436125637836597527614649 13077094228377448145710987)
    ·
      refine ⟨19615641342566172218566481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13077094228377448145710987 19615641342566172218566481)
      ·
        refine ⟨14711731006924629163924861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19615641342566172218566481 14711731006924629163924861)
        ·
          refine ⟨5516899127596735936471823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14711731006924629163924861 5516899127596735936471823)
          ·
            refine ⟨8275348691395103904707735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516899127596735936471823 8275348691395103904707735)
            ·
              refine ⟨12413023037092655857061603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275348691395103904707735 12413023037092655857061603)
              ·
                refine ⟨18619534555638983785592405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12413023037092655857061603 18619534555638983785592405)
                ·
                  refine ⟨218197670573894341237411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18619534555638983785592405 218197670573894341237411)
                  ·
                    rfl

theorem cell23_3824446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3824446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824446 prefixEnd_3824446 := by exact prefixLift 3824446
  have htrace : WordTrace (prefixWord ++ tailWord_3824446) baseStart_3824446 baseEnd_3824446 := by
    simpa [prefixWord, tailWord_3824446, baseEnd_3824446] using wordTrace_append hprefix tailTrace_3824446
  have hstable : (prefixWord ++ tailWord_3824446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824446).length < 2 ^ (prefixWord ++ tailWord_3824446).sum := by decide
  have hdescent : baseEnd_3824446 < baseStart_3824446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824466 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_3824466 : Nat := 118140960795 + 3824466 * 2 ^ 59
def prefixEnd_3824466 : Nat := 4983230072969 + 3 ^ 40 * 3824466 * 2
def baseEnd_3824466 : Nat := 1963789304778138992886607

theorem tailTrace_3824466 : CollatzResearch.WordTrace tailWord_3824466 prefixEnd_3824466 1963789304778138992886607 := by
  unfold tailWord_3824466
  simp only [CollatzResearch.WordTrace]
  refine ⟨34872433640655080909161313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92993156375080215757763501 34872433640655080909161313)
  ·
    refine ⟨26154325230491310681870985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34872433640655080909161313 26154325230491310681870985)
    ·
      refine ⟨19615743922868483011403239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26154325230491310681870985 19615743922868483011403239)
      ·
        refine ⟨29423615884302724517104859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19615743922868483011403239 29423615884302724517104859)
        ·
          refine ⟨44135423826454086775657289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29423615884302724517104859 44135423826454086775657289)
          ·
            refine ⟨33101567869840565081742967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44135423826454086775657289 33101567869840565081742967)
            ·
              refine ⟨49652351804760847622614451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33101567869840565081742967 49652351804760847622614451)
              ·
                refine ⟨74478527707141271433921677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49652351804760847622614451 74478527707141271433921677)
                ·
                  refine ⟨27929447890177976787720629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74478527707141271433921677 27929447890177976787720629)
                  ·
                    refine ⟨2618385739704185323848809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27929447890177976787720629 2618385739704185323848809)
                    ·
                      refine ⟨1963789304778138992886607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618385739704185323848809 1963789304778138992886607)
                      ·
                        rfl

theorem cell23_3824466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_3824466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824466 prefixEnd_3824466 := by exact prefixLift 3824466
  have htrace : WordTrace (prefixWord ++ tailWord_3824466) baseStart_3824466 baseEnd_3824466 := by
    simpa [prefixWord, tailWord_3824466, baseEnd_3824466] using wordTrace_append hprefix tailTrace_3824466
  have hstable : (prefixWord ++ tailWord_3824466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824466).length < 2 ^ (prefixWord ++ tailWord_3824466).sum := by decide
  have hdescent : baseEnd_3824466 < baseStart_3824466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824496 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4]
def baseStart_3824496 : Nat := 118140960795 + 3824496 * 2 ^ 59
def prefixEnd_3824496 : Nat := 4983230072969 + 3 ^ 40 * 3824496 * 2
def baseEnd_3824496 : Nat := 1963804709197773875511469

theorem tailTrace_3824496 : CollatzResearch.WordTrace tailWord_3824496 prefixEnd_3824496 1963804709197773875511469 := by
  unfold tailWord_3824496
  simp only [CollatzResearch.WordTrace]
  refine ⟨69745414376255819380118671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92993885835007759173491561 69745414376255819380118671)
  ·
    refine ⟨104618121564383729070178007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69745414376255819380118671 104618121564383729070178007)
    ·
      refine ⟨156927182346575593605267011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104618121564383729070178007 156927182346575593605267011)
      ·
        refine ⟨235390773519863390407900517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156927182346575593605267011 235390773519863390407900517)
        ·
          refine ⟨44135770034974385701481347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235390773519863390407900517 44135770034974385701481347)
          ·
            refine ⟨66203655052461578552222021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44135770034974385701481347 66203655052461578552222021)
            ·
              refine ⟨12413185322336545978541629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66203655052461578552222021 12413185322336545978541629)
              ·
                refine ⟨4654944495876204741953111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12413185322336545978541629 4654944495876204741953111)
                ·
                  refine ⟨6982416743814307112929667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654944495876204741953111 6982416743814307112929667)
                  ·
                    refine ⟨10473625115721460669394501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6982416743814307112929667 10473625115721460669394501)
                    ·
                      refine ⟨1963804709197773875511469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10473625115721460669394501 1963804709197773875511469)
                      ·
                        rfl

theorem cell23_3824496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_3824496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824496 prefixEnd_3824496 := by exact prefixLift 3824496
  have htrace : WordTrace (prefixWord ++ tailWord_3824496) baseStart_3824496 baseEnd_3824496 := by
    simpa [prefixWord, tailWord_3824496, baseEnd_3824496] using wordTrace_append hprefix tailTrace_3824496
  have hstable : (prefixWord ++ tailWord_3824496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824496).length < 2 ^ (prefixWord ++ tailWord_3824496).sum := by decide
  have hdescent : baseEnd_3824496 < baseStart_3824496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824499 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5]
def baseStart_3824499 : Nat := 118140960795 + 3824499 * 2 ^ 59
def prefixEnd_3824499 : Nat := 4983230072969 + 3 ^ 40 * 3824499 * 2
def baseEnd_3824499 : Nat := 1963806249639737363773955

theorem tailTrace_3824499 : CollatzResearch.WordTrace tailWord_3824499 prefixEnd_3824499 1963806249639737363773955 := by
  unfold tailWord_3824499
  simp only [CollatzResearch.WordTrace]
  refine ⟨139490938171500770272596551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92993958781000513515064367 139490938171500770272596551)
  ·
    refine ⟨209236407257251155408894827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139490938171500770272596551 209236407257251155408894827)
    ·
      refine ⟨313854610885876733113342241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209236407257251155408894827 313854610885876733113342241)
      ·
        refine ⟨235390958164407549835006681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313854610885876733113342241 235390958164407549835006681)
        ·
          refine ⟨176543218623305662376255011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235390958164407549835006681 176543218623305662376255011)
          ·
            refine ⟨264814827934958493564382517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176543218623305662376255011 264814827934958493564382517)
            ·
              refine ⟨24826390118902358771660861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264814827934958493564382517 24826390118902358771660861)
              ·
                refine ⟨9309896294588384539372823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24826390118902358771660861 9309896294588384539372823)
                ·
                  refine ⟨13964844441882576809059235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9309896294588384539372823 13964844441882576809059235)
                  ·
                    refine ⟨20947266662823865213588853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13964844441882576809059235 20947266662823865213588853)
                    ·
                      refine ⟨1963806249639737363773955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20947266662823865213588853 1963806249639737363773955)
                      ·
                        rfl

theorem cell23_3824499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_3824499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824499 prefixEnd_3824499 := by exact prefixLift 3824499
  have htrace : WordTrace (prefixWord ++ tailWord_3824499) baseStart_3824499 baseEnd_3824499 := by
    simpa [prefixWord, tailWord_3824499, baseEnd_3824499] using wordTrace_append hprefix tailTrace_3824499
  have hstable : (prefixWord ++ tailWord_3824499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824499).length < 2 ^ (prefixWord ++ tailWord_3824499).sum := by decide
  have hdescent : baseEnd_3824499 < baseStart_3824499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824506 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_3824506 : Nat := 118140960795 + 3824506 * 2 ^ 59
def prefixEnd_3824506 : Nat := 4983230072969 + 3 ^ 40 * 3824506 * 2
def baseEnd_3824506 : Nat := 654603281334772945462141

theorem tailTrace_3824506 : CollatzResearch.WordTrace tailWord_3824506 prefixEnd_3824506 654603281334772945462141 := by
  unfold tailWord_3824506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34872798370618852617025343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92994128988316940312067581 34872798370618852617025343)
  ·
    refine ⟨52309197555928278925538015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34872798370618852617025343 52309197555928278925538015)
    ·
      refine ⟨78463796333892418388307023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52309197555928278925538015 78463796333892418388307023)
      ·
        refine ⟨117695694500838627582460535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78463796333892418388307023 117695694500838627582460535)
        ·
          refine ⟨176543541751257941373690803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117695694500838627582460535 176543541751257941373690803)
          ·
            refine ⟨264815312626886912060536205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176543541751257941373690803 264815312626886912060536205)
            ·
              refine ⟨99305742235082592022701077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264815312626886912060536205 99305742235082592022701077)
              ·
                refine ⟨4654956667269496501064113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99305742235082592022701077 4654956667269496501064113)
                ·
                  refine ⟨3491217500452122375798085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4654956667269496501064113 3491217500452122375798085)
                  ·
                    refine ⟨654603281334772945462141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3491217500452122375798085 654603281334772945462141)
                    ·
                      rfl

theorem cell23_3824506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_3824506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824506 prefixEnd_3824506 := by exact prefixLift 3824506
  have htrace : WordTrace (prefixWord ++ tailWord_3824506) baseStart_3824506 baseEnd_3824506 := by
    simpa [prefixWord, tailWord_3824506, baseEnd_3824506] using wordTrace_append hprefix tailTrace_3824506
  have hstable : (prefixWord ++ tailWord_3824506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824506).length < 2 ^ (prefixWord ++ tailWord_3824506).sum := by decide
  have hdescent : baseEnd_3824506 < baseStart_3824506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824509 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_3824509 : Nat := 118140960795 + 3824509 * 2 ^ 59
def prefixEnd_3824509 : Nat := 4983230072969 + 3 ^ 40 * 3824509 * 2
def baseEnd_3824509 : Nat := 1963811384446282324648909

theorem tailTrace_3824509 : CollatzResearch.WordTrace tailWord_3824509 prefixEnd_3824509 1963811384446282324648909 := by
  unfold tailWord_3824509
  simp only [CollatzResearch.WordTrace]
  refine ⟨139491302901464541980460581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92994201934309694653640387 139491302901464541980460581)
  ·
    refine ⟨26154619294024601621336359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139491302901464541980460581 26154619294024601621336359)
    ·
      refine ⟨39231928941036902432004539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26154619294024601621336359 39231928941036902432004539)
      ·
        refine ⟨58847893411555353648006809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39231928941036902432004539 58847893411555353648006809)
        ·
          refine ⟨44135920058666515236005107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58847893411555353648006809 44135920058666515236005107)
          ·
            refine ⟨66203880087999772854007661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44135920058666515236005107 66203880087999772854007661)
            ·
              refine ⟨24826455032999914820252873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66203880087999772854007661 24826455032999914820252873)
              ·
                refine ⟨18619841274749936115189655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24826455032999914820252873 18619841274749936115189655)
                ·
                  refine ⟨27929761912124904172784483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18619841274749936115189655 27929761912124904172784483)
                  ·
                    refine ⟨41894642868187356259176725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27929761912124904172784483 41894642868187356259176725)
                    ·
                      refine ⟨1963811384446282324648909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41894642868187356259176725 1963811384446282324648909)
                      ·
                        rfl

theorem cell23_3824509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_3824509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824509 prefixEnd_3824509 := by exact prefixLift 3824509
  have htrace : WordTrace (prefixWord ++ tailWord_3824509) baseStart_3824509 baseEnd_3824509 := by
    simpa [prefixWord, tailWord_3824509, baseEnd_3824509] using wordTrace_append hprefix tailTrace_3824509
  have hstable : (prefixWord ++ tailWord_3824509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824509).length < 2 ^ (prefixWord ++ tailWord_3824509).sum := by decide
  have hdescent : baseEnd_3824509 < baseStart_3824509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824514 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 6]
def baseStart_3824514 : Nat := 118140960795 + 3824514 * 2 ^ 59
def prefixEnd_3824514 : Nat := 4983230072969 + 3 ^ 40 * 3824514 * 2
def baseEnd_3824514 : Nat := 218201550205506089454043

theorem tailTrace_3824514 : CollatzResearch.WordTrace tailWord_3824514 prefixEnd_3824514 218201550205506089454043 := by
  unfold tailWord_3824514
  simp only [CollatzResearch.WordTrace]
  refine ⟨34872871316611606958598149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92994323510964285222928397 34872871316611606958598149)
  ·
    refine ⟨6538663371864676304737153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34872871316611606958598149 6538663371864676304737153)
    ·
      refine ⟨4903997528898507228552865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6538663371864676304737153 4903997528898507228552865)
      ·
        refine ⟨3677998146673880421414649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4903997528898507228552865 3677998146673880421414649)
        ·
          refine ⟨2758498610005410316060987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677998146673880421414649 2758498610005410316060987)
          ·
            refine ⟨4137747915008115474091481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758498610005410316060987 4137747915008115474091481)
            ·
              refine ⟨3103310936256086605568611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137747915008115474091481 3103310936256086605568611)
              ·
                refine ⟨4654966404384129908352917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103310936256086605568611 4654966404384129908352917)
                ·
                  refine ⟨218201550205506089454043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4654966404384129908352917 218201550205506089454043)
                  ·
                    rfl

theorem cell23_3824514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_3824514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824514 prefixEnd_3824514 := by exact prefixLift 3824514
  have htrace : WordTrace (prefixWord ++ tailWord_3824514) baseStart_3824514 baseEnd_3824514 := by
    simpa [prefixWord, tailWord_3824514, baseEnd_3824514] using wordTrace_append hprefix tailTrace_3824514
  have hstable : (prefixWord ++ tailWord_3824514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824514).length < 2 ^ (prefixWord ++ tailWord_3824514).sum := by decide
  have hdescent : baseEnd_3824514 < baseStart_3824514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824516 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3824516 : Nat := 118140960795 + 3824516 * 2 ^ 59
def prefixEnd_3824516 : Nat := 4983230072969 + 3 ^ 40 * 3824516 * 2
def baseEnd_3824516 : Nat := 1963814978810863797261377

theorem tailTrace_3824516 : CollatzResearch.WordTrace tailWord_3824516 prefixEnd_3824516 1963814978810863797261377 := by
  unfold tailWord_3824516
  simp only [CollatzResearch.WordTrace]
  refine ⟨69745779106219591087982701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92994372141626121450643601 69745779106219591087982701)
  ·
    refine ⟨26154667164832346657993513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69745779106219591087982701 26154667164832346657993513)
    ·
      refine ⟨19616000373624259993495135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26154667164832346657993513 19616000373624259993495135)
      ·
        refine ⟨29424000560436389990242703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19616000373624259993495135 29424000560436389990242703)
        ·
          refine ⟨44136000840654584985364055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29424000560436389990242703 44136000840654584985364055)
          ·
            refine ⟨66204001260981877478046083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44136000840654584985364055 66204001260981877478046083)
            ·
              refine ⟨99306001891472816217069125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66204001260981877478046083 99306001891472816217069125)
              ·
                refine ⟨18619875354651153040700461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99306001891472816217069125 18619875354651153040700461)
                ·
                  refine ⟨6982453257994182390262673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18619875354651153040700461 6982453257994182390262673)
                  ·
                    refine ⟨5236839943495636792697005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6982453257994182390262673 5236839943495636792697005)
                    ·
                      refine ⟨1963814978810863797261377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5236839943495636792697005 1963814978810863797261377)
                      ·
                        rfl

theorem cell23_3824516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3824516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824516 prefixEnd_3824516 := by exact prefixLift 3824516
  have htrace : WordTrace (prefixWord ++ tailWord_3824516) baseStart_3824516 baseEnd_3824516 := by
    simpa [prefixWord, tailWord_3824516, baseEnd_3824516] using wordTrace_append hprefix tailTrace_3824516
  have hstable : (prefixWord ++ tailWord_3824516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824516).length < 2 ^ (prefixWord ++ tailWord_3824516).sum := by decide
  have hdescent : baseEnd_3824516 < baseStart_3824516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824519 : List Nat := [1, 1, 4, 2, 3, 1, 1, 10]
def baseStart_3824519 : Nat := 118140960795 + 3824519 * 2 ^ 59
def prefixEnd_3824519 : Nat := 4983230072969 + 3 ^ 40 * 3824519 * 2
def baseEnd_3824519 : Nat := 72733945157512121686069

theorem tailTrace_3824519 : CollatzResearch.WordTrace tailWord_3824519 prefixEnd_3824519 72733945157512121686069 := by
  unfold tailWord_3824519
  simp only [CollatzResearch.WordTrace]
  refine ⟨139491667631428313688324611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92994445087618875792216407 139491667631428313688324611)
  ·
    refine ⟨209237501447142470532486917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139491667631428313688324611 209237501447142470532486917)
    ·
      refine ⟨39232031521339213224841297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209237501447142470532486917 39232031521339213224841297)
      ·
        refine ⟨29424023641004409918630973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39232031521339213224841297 29424023641004409918630973)
        ·
          refine ⟨11034008865376653719486615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29424023641004409918630973 11034008865376653719486615)
          ·
            refine ⟨16551013298064980579229923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11034008865376653719486615 16551013298064980579229923)
            ·
              refine ⟨24826519947097470868844885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16551013298064980579229923 24826519947097470868844885)
              ·
                refine ⟨72733945157512121686069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24826519947097470868844885 72733945157512121686069)
                ·
                  rfl

theorem cell23_3824519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 10].length) (baseStart_3824519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824519 prefixEnd_3824519 := by exact prefixLift 3824519
  have htrace : WordTrace (prefixWord ++ tailWord_3824519) baseStart_3824519 baseEnd_3824519 := by
    simpa [prefixWord, tailWord_3824519, baseEnd_3824519] using wordTrace_append hprefix tailTrace_3824519
  have hstable : (prefixWord ++ tailWord_3824519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824519).length < 2 ^ (prefixWord ++ tailWord_3824519).sum := by decide
  have hdescent : baseEnd_3824519 < baseStart_3824519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824523 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 2, 4]
def baseStart_3824523 : Nat := 118140960795 + 3824523 * 2 ^ 59
def prefixEnd_3824523 : Nat := 4983230072969 + 3 ^ 40 * 3824523 * 2
def baseEnd_3824523 : Nat := 654606191058481756624615

theorem tailTrace_3824523 : CollatzResearch.WordTrace tailWord_3824523 prefixEnd_3824523 654606191058481756624615 := by
  unfold tailWord_3824523
  simp only [CollatzResearch.WordTrace]
  refine ⟨139491813523413822371470223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92994542348942548247646815 139491813523413822371470223)
  ·
    refine ⟨209237720285120733557205335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139491813523413822371470223 209237720285120733557205335)
    ·
      refine ⟨313856580427681100335808003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209237720285120733557205335 313856580427681100335808003)
      ·
        refine ⟨470784870641521650503712005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313856580427681100335808003 470784870641521650503712005)
        ·
          refine ⟨88272163245285309469446001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470784870641521650503712005 88272163245285309469446001)
          ·
            refine ⟨66204122433963982102084501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88272163245285309469446001 66204122433963982102084501)
            ·
              refine ⟨3103318239092061661035211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66204122433963982102084501 3103318239092061661035211)
              ·
                refine ⟨4654977358638092491552817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103318239092061661035211 4654977358638092491552817)
                ·
                  refine ⟨3491233018978569368664613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4654977358638092491552817 3491233018978569368664613)
                  ·
                    refine ⟨654606191058481756624615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3491233018978569368664613 654606191058481756624615)
                    ·
                      rfl

theorem cell23_3824523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 4].length) (baseStart_3824523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824523 prefixEnd_3824523 := by exact prefixLift 3824523
  have htrace : WordTrace (prefixWord ++ tailWord_3824523) baseStart_3824523 baseEnd_3824523 := by
    simpa [prefixWord, tailWord_3824523, baseEnd_3824523] using wordTrace_append hprefix tailTrace_3824523
  have hstable : (prefixWord ++ tailWord_3824523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824523).length < 2 ^ (prefixWord ++ tailWord_3824523).sum := by decide
  have hdescent : baseEnd_3824523 < baseStart_3824523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824533 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_3824533 : Nat := 118140960795 + 3824533 * 2 ^ 59
def prefixEnd_3824533 : Nat := 4983230072969 + 3 ^ 40 * 3824533 * 2
def baseEnd_3824533 : Nat := 1963823707981990230748799

theorem tailTrace_3824533 : CollatzResearch.WordTrace tailWord_3824533 prefixEnd_3824533 1963823707981990230748799 := by
  unfold tailWord_3824533
  simp only [CollatzResearch.WordTrace]
  refine ⟨139492178253377594079334253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92994785502251729386222835 139492178253377594079334253)
  ·
    refine ⟨52309566845016597779750345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139492178253377594079334253 52309566845016597779750345)
    ·
      refine ⟨39232175133762448334812759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52309566845016597779750345 39232175133762448334812759)
      ·
        refine ⟨58848262700643672502219139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39232175133762448334812759 58848262700643672502219139)
        ·
          refine ⟨88272394050965508753328709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58848262700643672502219139 88272394050965508753328709)
          ·
            refine ⟨16551073884556032891249133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88272394050965508753328709 16551073884556032891249133)
            ·
              refine ⟨6206652706708512334218425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16551073884556032891249133 6206652706708512334218425)
              ·
                refine ⟨4654989530031384250663819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6206652706708512334218425 4654989530031384250663819)
                ·
                  refine ⟨6982484295047076375995729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654989530031384250663819 6982484295047076375995729)
                  ·
                    refine ⟨5236863221285307281996797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6982484295047076375995729 5236863221285307281996797)
                    ·
                      refine ⟨1963823707981990230748799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5236863221285307281996797 1963823707981990230748799)
                      ·
                        rfl

theorem cell23_3824533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_3824533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824533 prefixEnd_3824533 := by exact prefixLift 3824533
  have htrace : WordTrace (prefixWord ++ tailWord_3824533) baseStart_3824533 baseEnd_3824533 := by
    simpa [prefixWord, tailWord_3824533, baseEnd_3824533] using wordTrace_append hprefix tailTrace_3824533
  have hstable : (prefixWord ++ tailWord_3824533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824533).length < 2 ^ (prefixWord ++ tailWord_3824533).sum := by decide
  have hdescent : baseEnd_3824533 < baseStart_3824533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824534 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3824534 : Nat := 118140960795 + 3824534 * 2 ^ 59
def prefixEnd_3824534 : Nat := 4983230072969 + 3 ^ 40 * 3824534 * 2
def baseEnd_3824534 : Nat := 1963824221462644726836295

theorem tailTrace_3824534 : CollatzResearch.WordTrace tailWord_3824534 prefixEnd_3824534 1963824221462644726836295 := by
  unfold tailWord_3824534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8718263420398373203132541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92994809817582647500080437 8718263420398373203132541)
  ·
    refine ⟨3269348782649389951174703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8718263420398373203132541 3269348782649389951174703)
    ·
      refine ⟨4904023173974084926762055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269348782649389951174703 4904023173974084926762055)
      ·
        refine ⟨7356034760961127390143083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904023173974084926762055 7356034760961127390143083)
        ·
          refine ⟨11034052141441691085214625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356034760961127390143083 11034052141441691085214625)
          ·
            refine ⟨8275539106081268313910969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11034052141441691085214625 8275539106081268313910969)
            ·
              refine ⟨6206654329560951235433227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8275539106081268313910969 6206654329560951235433227)
              ·
                refine ⟨9309981494341426853149841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206654329560951235433227 9309981494341426853149841)
                ·
                  refine ⟨6982486120756070139862381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9309981494341426853149841 6982486120756070139862381)
                  ·
                    refine ⟨2618432295283526302448393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6982486120756070139862381 2618432295283526302448393)
                    ·
                      refine ⟨1963824221462644726836295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618432295283526302448393 1963824221462644726836295)
                      ·
                        rfl

theorem cell23_3824534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3824534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824534 prefixEnd_3824534 := by exact prefixLift 3824534
  have htrace : WordTrace (prefixWord ++ tailWord_3824534) baseStart_3824534 baseEnd_3824534 := by
    simpa [prefixWord, tailWord_3824534, baseEnd_3824534] using wordTrace_append hprefix tailTrace_3824534
  have hstable : (prefixWord ++ tailWord_3824534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824534).length < 2 ^ (prefixWord ++ tailWord_3824534).sum := by decide
  have hdescent : baseEnd_3824534 < baseStart_3824534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824557 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_3824557 : Nat := 118140960795 + 3824557 * 2 ^ 59
def prefixEnd_3824557 : Nat := 4983230072969 + 3 ^ 40 * 3824557 * 2
def baseEnd_3824557 : Nat := 654612010505899378949563

theorem tailTrace_3824557 : CollatzResearch.WordTrace tailWord_3824557 prefixEnd_3824557 654612010505899378949563 := by
  unfold tailWord_3824557
  simp only [CollatzResearch.WordTrace]
  refine ⟨139493053605290646178207925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92995369070193764118805283 139493053605290646178207925)
  ·
    refine ⟨13077473775495998079206993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139493053605290646178207925 13077473775495998079206993)
    ·
      refine ⟨9808105331621998559405245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13077473775495998079206993 9808105331621998559405245)
      ·
        refine ⟨3678039499358249459776967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9808105331621998559405245 3678039499358249459776967)
        ·
          refine ⟨5517059249037374189665451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678039499358249459776967 5517059249037374189665451)
          ·
            refine ⟨8275588873556061284498177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517059249037374189665451 8275588873556061284498177)
            ·
              refine ⟨6206691655167045963373633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8275588873556061284498177 6206691655167045963373633)
              ·
                refine ⟨4655018741375284472530225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6206691655167045963373633 4655018741375284472530225)
                ·
                  refine ⟨3491264056031463354397669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655018741375284472530225 3491264056031463354397669)
                  ·
                    refine ⟨654612010505899378949563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3491264056031463354397669 654612010505899378949563)
                    ·
                      rfl

theorem cell23_3824557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_3824557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824557 prefixEnd_3824557 := by exact prefixLift 3824557
  have htrace : WordTrace (prefixWord ++ tailWord_3824557) baseStart_3824557 baseEnd_3824557 := by
    simpa [prefixWord, tailWord_3824557, baseEnd_3824557] using wordTrace_append hprefix tailTrace_3824557
  have hstable : (prefixWord ++ tailWord_3824557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824557).length < 2 ^ (prefixWord ++ tailWord_3824557).sum := by decide
  have hdescent : baseEnd_3824557 < baseStart_3824557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824579 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 2, 6]
def baseStart_3824579 : Nat := 118140960795 + 3824579 * 2 ^ 59
def prefixEnd_3824579 : Nat := 4983230072969 + 3 ^ 40 * 3824579 * 2
def baseEnd_3824579 : Nat := 654615776030699016924529

theorem tailTrace_3824579 : CollatzResearch.WordTrace tailWord_3824579 prefixEnd_3824579 654615776030699016924529 := by
  unfold tailWord_3824579
  simp only [CollatzResearch.WordTrace]
  refine ⟨139493856011210943935508791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92995904007473962623672527 139493856011210943935508791)
  ·
    refine ⟨209240784016816415903263187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139493856011210943935508791 209240784016816415903263187)
    ·
      refine ⟨313861176025224623854894781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209240784016816415903263187 313861176025224623854894781)
      ·
        refine ⟨117697941009459233945585543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313861176025224623854894781 117697941009459233945585543)
        ·
          refine ⟨176546911514188850918378315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117697941009459233945585543 176546911514188850918378315)
          ·
            refine ⟨264820367271283276377567473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176546911514188850918378315 264820367271283276377567473)
            ·
              refine ⟨198615275453462457283175605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264820367271283276377567473 198615275453462457283175605)
              ·
                refine ⟨18620182073762105370297713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198615275453462457283175605 18620182073762105370297713)
                ·
                  refine ⟨13965136555321579027723285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18620182073762105370297713 13965136555321579027723285)
                  ·
                    refine ⟨654615776030699016924529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13965136555321579027723285 654615776030699016924529)
                    ·
                      rfl

theorem cell23_3824579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 6].length) (baseStart_3824579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824579 prefixEnd_3824579 := by exact prefixLift 3824579
  have htrace : WordTrace (prefixWord ++ tailWord_3824579) baseStart_3824579 baseEnd_3824579 := by
    simpa [prefixWord, tailWord_3824579, baseEnd_3824579] using wordTrace_append hprefix tailTrace_3824579
  have hstable : (prefixWord ++ tailWord_3824579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824579).length < 2 ^ (prefixWord ++ tailWord_3824579).sum := by decide
  have hdescent : baseEnd_3824579 < baseStart_3824579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824609 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 11]
def baseStart_3824609 : Nat := 118140960795 + 3824609 * 2 ^ 59
def prefixEnd_3824609 : Nat := 4983230072969 + 3 ^ 40 * 3824609 * 2
def baseEnd_3824609 : Nat := 218206970279081325933161

theorem tailTrace_3824609 : CollatzResearch.WordTrace tailWord_3824609 prefixEnd_3824609 218206970279081325933161 := by
  unfold tailWord_3824609
  simp only [CollatzResearch.WordTrace]
  refine ⟨139494950201102259059100881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92996633467401506039400587 139494950201102259059100881)
  ·
    refine ⟨104621212650826694294325661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139494950201102259059100881 104621212650826694294325661)
    ·
      refine ⟨39232954744060010360372123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104621212650826694294325661 39232954744060010360372123)
      ·
        refine ⟨58849432116090015540558185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39232954744060010360372123 58849432116090015540558185)
        ·
          refine ⟨44137074087067511655418639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58849432116090015540558185 44137074087067511655418639)
          ·
            refine ⟨66205611130601267483127959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44137074087067511655418639 66205611130601267483127959)
            ·
              refine ⟨99308416695901901224691939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66205611130601267483127959 99308416695901901224691939)
              ·
                refine ⟨148962625043852851837037909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99308416695901901224691939 148962625043852851837037909)
                ·
                  refine ⟨218206970279081325933161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 148962625043852851837037909 218206970279081325933161)
                  ·
                    rfl

theorem cell23_3824609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 11].length) (baseStart_3824609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824609 prefixEnd_3824609 := by exact prefixLift 3824609
  have htrace : WordTrace (prefixWord ++ tailWord_3824609) baseStart_3824609 baseEnd_3824609 := by
    simpa [prefixWord, tailWord_3824609, baseEnd_3824609] using wordTrace_append hprefix tailTrace_3824609
  have hstable : (prefixWord ++ tailWord_3824609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824609).length < 2 ^ (prefixWord ++ tailWord_3824609).sum := by decide
  have hdescent : baseEnd_3824609 < baseStart_3824609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824616 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3824616 : Nat := 118140960795 + 3824616 * 2 ^ 59
def prefixEnd_3824616 : Nat := 4983230072969 + 3 ^ 40 * 3824616 * 2
def baseEnd_3824616 : Nat := 1963866326876313406010917

theorem tailTrace_3824616 : CollatzResearch.WordTrace tailWord_3824616 prefixEnd_3824616 1963866326876313406010917 := by
  unfold tailWord_3824616
  simp only [CollatzResearch.WordTrace]
  refine ⟨69747602756038449627302851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92996803674717932836403801 69747602756038449627302851)
  ·
    refine ⟨104621404134057674440954277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69747602756038449627302851 104621404134057674440954277)
    ·
      refine ⟨19616513275135813957678927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104621404134057674440954277 19616513275135813957678927)
      ·
        refine ⟨29424769912703720936518391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19616513275135813957678927 29424769912703720936518391)
        ·
          refine ⟨44137154869055581404777587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29424769912703720936518391 44137154869055581404777587)
          ·
            refine ⟨66205732303583372107166381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44137154869055581404777587 66205732303583372107166381)
            ·
              refine ⟨24827149613843764540187393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66205732303583372107166381 24827149613843764540187393)
              ·
                refine ⟨18620362210382823405140545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24827149613843764540187393 18620362210382823405140545)
                ·
                  refine ⟨13965271657787117553855409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18620362210382823405140545 13965271657787117553855409)
                  ·
                    refine ⟨10473953743340338165391557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13965271657787117553855409 10473953743340338165391557)
                    ·
                      refine ⟨1963866326876313406010917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10473953743340338165391557 1963866326876313406010917)
                      ·
                        rfl

theorem cell23_3824616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3824616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824616 prefixEnd_3824616 := by exact prefixLift 3824616
  have htrace : WordTrace (prefixWord ++ tailWord_3824616) baseStart_3824616 baseEnd_3824616 := by
    simpa [prefixWord, tailWord_3824616, baseEnd_3824616] using wordTrace_append hprefix tailTrace_3824616
  have hstable : (prefixWord ++ tailWord_3824616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824616).length < 2 ^ (prefixWord ++ tailWord_3824616).sum := by decide
  have hdescent : baseEnd_3824616 < baseStart_3824616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824666 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3824666 : Nat := 118140960795 + 3824666 * 2 ^ 59
def prefixEnd_3824666 : Nat := 4983230072969 + 3 ^ 40 * 3824666 * 2
def baseEnd_3824666 : Nat := 1963892000909038210385687

theorem tailTrace_3824666 : CollatzResearch.WordTrace tailWord_3824666 prefixEnd_3824666 1963892000909038210385687 := by
  unfold tailWord_3824666
  simp only [CollatzResearch.WordTrace]
  refine ⟨34874257290473939448481463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92998019441263838529283901 34874257290473939448481463)
  ·
    refine ⟨52311385935710909172722195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34874257290473939448481463 52311385935710909172722195)
    ·
      refine ⟨78467078903566363759083293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52311385935710909172722195 78467078903566363759083293)
      ·
        refine ⟨29425154588837386409656235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78467078903566363759083293 29425154588837386409656235)
        ·
          refine ⟨44137731883256079614484353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29425154588837386409656235 44137731883256079614484353)
          ·
            refine ⟨33103298912442059710863265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44137731883256079614484353 33103298912442059710863265)
            ·
              refine ⟨24827474184331544783147449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33103298912442059710863265 24827474184331544783147449)
              ·
                refine ⟨18620605638248658587360587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24827474184331544783147449 18620605638248658587360587)
                ·
                  refine ⟨27930908457372987881040881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18620605638248658587360587 27930908457372987881040881)
                  ·
                    refine ⟨20948181343029740910780661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27930908457372987881040881 20948181343029740910780661)
                    ·
                      refine ⟨1963892000909038210385687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20948181343029740910780661 1963892000909038210385687)
                      ·
                        rfl

theorem cell23_3824666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3824666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824666 prefixEnd_3824666 := by exact prefixLift 3824666
  have htrace : WordTrace (prefixWord ++ tailWord_3824666) baseStart_3824666 baseEnd_3824666 := by
    simpa [prefixWord, tailWord_3824666, baseEnd_3824666] using wordTrace_append hprefix tailTrace_3824666
  have hstable : (prefixWord ++ tailWord_3824666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824666).length < 2 ^ (prefixWord ++ tailWord_3824666).sum := by decide
  have hdescent : baseEnd_3824666 < baseStart_3824666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824673 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3824673 : Nat := 118140960795 + 3824673 * 2 ^ 59
def prefixEnd_3824673 : Nat := 4983230072969 + 3 ^ 40 * 3824673 * 2
def baseEnd_3824673 : Nat := 654631865091206560999385

theorem tailTrace_3824673 : CollatzResearch.WordTrace tailWord_3824673 prefixEnd_3824673 654631865091206560999385 := by
  unfold tailWord_3824673
  simp only [CollatzResearch.WordTrace]
  refine ⟨139497284472870397989430673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92998189648580265326287115 139497284472870397989430673)
  ·
    refine ⟨104622963354652798492073005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139497284472870397989430673 104622963354652798492073005)
    ·
      refine ⟨39233611257994799434527377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104622963354652798492073005 39233611257994799434527377)
      ·
        refine ⟨29425208443496099575895533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39233611257994799434527377 29425208443496099575895533)
        ·
          refine ⟨11034453166311037340960825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29425208443496099575895533 11034453166311037340960825)
          ·
            refine ⟨8275839874733278005720619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11034453166311037340960825 8275839874733278005720619)
            ·
              refine ⟨12413759812099917008580929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275839874733278005720619 12413759812099917008580929)
              ·
                refine ⟨9310319859074937756435697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12413759812099917008580929 9310319859074937756435697)
                ·
                  refine ⟨6982739894306203317326773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9310319859074937756435697 6982739894306203317326773)
                  ·
                    refine ⟨654631865091206560999385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6982739894306203317326773 654631865091206560999385)
                    ·
                      rfl

theorem cell23_3824673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3824673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824673 prefixEnd_3824673 := by exact prefixLift 3824673
  have htrace : WordTrace (prefixWord ++ tailWord_3824673) baseStart_3824673 baseEnd_3824673 := by
    simpa [prefixWord, tailWord_3824673, baseEnd_3824673] using wordTrace_append hprefix tailTrace_3824673
  have hstable : (prefixWord ++ tailWord_3824673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824673).length < 2 ^ (prefixWord ++ tailWord_3824673).sum := by decide
  have hdescent : baseEnd_3824673 < baseStart_3824673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824693 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_3824693 : Nat := 118140960795 + 3824693 * 2 ^ 59
def prefixEnd_3824693 : Nat := 4983230072969 + 3 ^ 40 * 3824693 * 2
def baseEnd_3824693 : Nat := 1963905864886709604748063

theorem tailTrace_3824693 : CollatzResearch.WordTrace tailWord_3824693 prefixEnd_3824693 1963905864886709604748063 := by
  unfold tailWord_3824693
  simp only [CollatzResearch.WordTrace]
  refine ⟨139498013932797941405158733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92998675955198627603439155 139498013932797941405158733)
  ·
    refine ⟨52311755224799228026934525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139498013932797941405158733 52311755224799228026934525)
    ·
      refine ⟨19616908209299710510100447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52311755224799228026934525 19616908209299710510100447)
      ·
        refine ⟨29425362313949565765150671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19616908209299710510100447 29425362313949565765150671)
        ·
          refine ⟨44138043470924348647726007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29425362313949565765150671 44138043470924348647726007)
          ·
            refine ⟨66207065206386522971589011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44138043470924348647726007 66207065206386522971589011)
            ·
              refine ⟨99310597809579784457383517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66207065206386522971589011 99310597809579784457383517)
              ·
                refine ⟨37241474178592419171518819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99310597809579784457383517 37241474178592419171518819)
                ·
                  refine ⟨55862211267888628757278229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37241474178592419171518819 55862211267888628757278229)
                  ·
                    refine ⟨2618541153182279472997417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55862211267888628757278229 2618541153182279472997417)
                    ·
                      refine ⟨1963905864886709604748063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618541153182279472997417 1963905864886709604748063)
                      ·
                        rfl

theorem cell23_3824693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_3824693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824693 prefixEnd_3824693 := by exact prefixLift 3824693
  have htrace : WordTrace (prefixWord ++ tailWord_3824693) baseStart_3824693 baseEnd_3824693 := by
    simpa [prefixWord, tailWord_3824693, baseEnd_3824693] using wordTrace_append hprefix tailTrace_3824693
  have hstable : (prefixWord ++ tailWord_3824693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824693).length < 2 ^ (prefixWord ++ tailWord_3824693).sum := by decide
  have hdescent : baseEnd_3824693 < baseStart_3824693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824736 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_3824736 : Nat := 118140960795 + 3824736 * 2 ^ 59
def prefixEnd_3824736 : Nat := 4983230072969 + 3 ^ 40 * 3824736 * 2
def baseEnd_3824736 : Nat := 1963927944554852936510365

theorem tailTrace_3824736 : CollatzResearch.WordTrace tailWord_3824736 prefixEnd_3824736 1963927944554852936510365 := by
  unfold tailWord_3824736
  simp only [CollatzResearch.WordTrace]
  refine ⟨69749791135821079874487031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92999721514428106499316041 69749791135821079874487031)
  ·
    refine ⟨104624686703731619811730547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69749791135821079874487031 104624686703731619811730547)
    ·
      refine ⟨156937030055597429717595821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104624686703731619811730547 156937030055597429717595821)
      ·
        refine ⟨58851386270849036144098433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156937030055597429717595821 58851386270849036144098433)
        ·
          refine ⟨44138539703136777108073825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58851386270849036144098433 44138539703136777108073825)
          ·
            refine ⟨33103904777352582831055369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44138539703136777108073825 33103904777352582831055369)
            ·
              refine ⟨24827928583014437123291527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33103904777352582831055369 24827928583014437123291527)
              ·
                refine ⟨37241892874521655684937291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24827928583014437123291527 37241892874521655684937291)
                ·
                  refine ⟨55862839311782483527405937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37241892874521655684937291 55862839311782483527405937)
                  ·
                    refine ⟨41897129483836862645554453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55862839311782483527405937 41897129483836862645554453)
                    ·
                      refine ⟨1963927944554852936510365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41897129483836862645554453 1963927944554852936510365)
                      ·
                        rfl

theorem cell23_3824736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_3824736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824736 prefixEnd_3824736 := by exact prefixLift 3824736
  have htrace : WordTrace (prefixWord ++ tailWord_3824736) baseStart_3824736 baseEnd_3824736 := by
    simpa [prefixWord, tailWord_3824736, baseEnd_3824736] using wordTrace_append hprefix tailTrace_3824736
  have hstable : (prefixWord ++ tailWord_3824736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824736).length < 2 ^ (prefixWord ++ tailWord_3824736).sum := by decide
  have hdescent : baseEnd_3824736 < baseStart_3824736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824737 : List Nat := [1, 2, 3, 1, 1, 2, 6, 2, 1, 4]
def baseStart_3824737 : Nat := 118140960795 + 3824737 * 2 ^ 59
def prefixEnd_3824737 : Nat := 4983230072969 + 3 ^ 40 * 3824737 * 2
def baseEnd_3824737 : Nat := 654642819345169144199287

theorem tailTrace_3824737 : CollatzResearch.WordTrace tailWord_3824737 prefixEnd_3824737 654642819345169144199287 := by
  unfold tailWord_3824737
  simp only [CollatzResearch.WordTrace]
  refine ⟨139499618744638536919760465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92999745829759024613173643 139499618744638536919760465)
  ·
    refine ⟨104624714058478902689820349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139499618744638536919760465 104624714058478902689820349)
    ·
      refine ⟨39234267771929588508682631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104624714058478902689820349 39234267771929588508682631)
      ·
        refine ⟨58851401657894382763023947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39234267771929588508682631 58851401657894382763023947)
        ·
          refine ⟨88277102486841574144535921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58851401657894382763023947 88277102486841574144535921)
          ·
            refine ⟨66207826865131180608401941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88277102486841574144535921 66207826865131180608401941)
            ·
              refine ⟨3103491884303024091018841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66207826865131180608401941 3103491884303024091018841)
              ·
                refine ⟨2327618913227268068264131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103491884303024091018841 2327618913227268068264131)
                ·
                  refine ⟨3491428369840902102396197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327618913227268068264131 3491428369840902102396197)
                  ·
                    refine ⟨654642819345169144199287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3491428369840902102396197 654642819345169144199287)
                    ·
                      rfl

theorem cell23_3824737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_3824737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824737 prefixEnd_3824737 := by exact prefixLift 3824737
  have htrace : WordTrace (prefixWord ++ tailWord_3824737) baseStart_3824737 baseEnd_3824737 := by
    simpa [prefixWord, tailWord_3824737, baseEnd_3824737] using wordTrace_append hprefix tailTrace_3824737
  have hstable : (prefixWord ++ tailWord_3824737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824737).length < 2 ^ (prefixWord ++ tailWord_3824737).sum := by decide
  have hdescent : baseEnd_3824737 < baseStart_3824737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824777 : List Nat := [1, 2, 1, 1, 4, 3, 1, 5, 1, 1, 3]
def baseStart_3824777 : Nat := 118140960795 + 3824777 * 2 ^ 59
def prefixEnd_3824777 : Nat := 4983230072969 + 3 ^ 40 * 3824777 * 2
def baseEnd_3824777 : Nat := 1963948997261687276097677

theorem tailTrace_3824777 : CollatzResearch.WordTrace tailWord_3824777 prefixEnd_3824777 1963948997261687276097677 := by
  unfold tailWord_3824777
  simp only [CollatzResearch.WordTrace]
  refine ⟨139501077664493623751216585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93000718442995749167477723 139501077664493623751216585)
  ·
    refine ⟨104625808248370217813412439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139501077664493623751216585 104625808248370217813412439)
    ·
      refine ⟨156938712372555326720118659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104625808248370217813412439 156938712372555326720118659)
      ·
        refine ⟨235408068558832990080177989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156938712372555326720118659 235408068558832990080177989)
        ·
          refine ⟨44139012854781185640033373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235408068558832990080177989 44139012854781185640033373)
          ·
            refine ⟨16552129820542944615012515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44139012854781185640033373 16552129820542944615012515)
            ·
              refine ⟨24828194730814416922518773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16552129820542944615012515 24828194730814416922518773)
              ·
                refine ⟨2327643256013851586486135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24828194730814416922518773 2327643256013851586486135)
                ·
                  refine ⟨3491464884020777379729203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327643256013851586486135 3491464884020777379729203)
                  ·
                    refine ⟨5237197326031166069593805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3491464884020777379729203 5237197326031166069593805)
                    ·
                      refine ⟨1963948997261687276097677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237197326031166069593805 1963948997261687276097677)
                      ·
                        rfl

theorem cell23_3824777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 1, 3].length) (baseStart_3824777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824777 prefixEnd_3824777 := by exact prefixLift 3824777
  have htrace : WordTrace (prefixWord ++ tailWord_3824777) baseStart_3824777 baseEnd_3824777 := by
    simpa [prefixWord, tailWord_3824777, baseEnd_3824777] using wordTrace_append hprefix tailTrace_3824777
  have hstable : (prefixWord ++ tailWord_3824777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824777).length < 2 ^ (prefixWord ++ tailWord_3824777).sum := by decide
  have hdescent : baseEnd_3824777 < baseStart_3824777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824794 : List Nat := [3, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3824794 : Nat := 118140960795 + 3824794 * 2 ^ 59
def prefixEnd_3824794 : Nat := 4983230072969 + 3 ^ 40 * 3824794 * 2
def baseEnd_3824794 : Nat := 1963957726432813709585099

theorem tailTrace_3824794 : CollatzResearch.WordTrace tailWord_3824794 prefixEnd_3824794 1963957726432813709585099 := by
  unfold tailWord_3824794
  simp only [CollatzResearch.WordTrace]
  refine ⟨34875424426358008913646359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93001131803621357103056957 34875424426358008913646359)
  ·
    refine ⟨52313136639537013370469539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34875424426358008913646359 52313136639537013370469539)
    ·
      refine ⟨78469704959305520055704309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52313136639537013370469539 78469704959305520055704309)
      ·
        refine ⟨7356534839934892505222279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78469704959305520055704309 7356534839934892505222279)
        ·
          refine ⟨11034802259902338757833419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356534839934892505222279 11034802259902338757833419)
          ·
            refine ⟨16552203389853508136750129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11034802259902338757833419 16552203389853508136750129)
            ·
              refine ⟨12414152542390131102562597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16552203389853508136750129 12414152542390131102562597)
              ·
                refine ⟨2327653601698149581730487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12414152542390131102562597 2327653601698149581730487)
                ·
                  refine ⟨3491480402547224372595731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327653601698149581730487 3491480402547224372595731)
                  ·
                    refine ⟨5237220603820836558893597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3491480402547224372595731 5237220603820836558893597)
                    ·
                      refine ⟨1963957726432813709585099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237220603820836558893597 1963957726432813709585099)
                      ·
                        rfl

theorem cell23_3824794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3824794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824794 prefixEnd_3824794 := by exact prefixLift 3824794
  have htrace : WordTrace (prefixWord ++ tailWord_3824794) baseStart_3824794 baseEnd_3824794 := by
    simpa [prefixWord, tailWord_3824794, baseEnd_3824794] using wordTrace_append hprefix tailTrace_3824794
  have hstable : (prefixWord ++ tailWord_3824794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824794).length < 2 ^ (prefixWord ++ tailWord_3824794).sum := by decide
  have hdescent : baseEnd_3824794 < baseStart_3824794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824803 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 3]
def baseStart_3824803 : Nat := 118140960795 + 3824803 * 2 ^ 59
def prefixEnd_3824803 : Nat := 4983230072969 + 3 ^ 40 * 3824803 * 2
def baseEnd_3824803 : Nat := 1963962347758704174372557

theorem tailTrace_3824803 : CollatzResearch.WordTrace tailWord_3824803 prefixEnd_3824803 1963962347758704174372557 := by
  unfold tailWord_3824803
  simp only [CollatzResearch.WordTrace]
  refine ⟨139502025962399430191663063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93001350641599620127775375 139502025962399430191663063)
  ·
    refine ⟨209253038943599145287494595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139502025962399430191663063 209253038943599145287494595)
    ·
      refine ⟨313879558415398717931241893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209253038943599145287494595 313879558415398717931241893)
      ·
        refine ⟨58852417202887259612107855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313879558415398717931241893 58852417202887259612107855)
        ·
          refine ⟨88278625804330889418161783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58852417202887259612107855 88278625804330889418161783)
          ·
            refine ⟨132417938706496334127242675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88278625804330889418161783 132417938706496334127242675)
            ·
              refine ⟨198626908059744501190864013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132417938706496334127242675 198626908059744501190864013)
              ·
                refine ⟨74485090522404187946574005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198626908059744501190864013 74485090522404187946574005)
                ·
                  refine ⟨6982977236475392619991313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74485090522404187946574005 6982977236475392619991313)
                  ·
                    refine ⟨5237232927356544464993485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6982977236475392619991313 5237232927356544464993485)
                    ·
                      refine ⟨1963962347758704174372557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237232927356544464993485 1963962347758704174372557)
                      ·
                        rfl

theorem cell23_3824803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_3824803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824803 prefixEnd_3824803 := by exact prefixLift 3824803
  have htrace : WordTrace (prefixWord ++ tailWord_3824803) baseStart_3824803 baseEnd_3824803 := by
    simpa [prefixWord, tailWord_3824803, baseEnd_3824803] using wordTrace_append hprefix tailTrace_3824803
  have hstable : (prefixWord ++ tailWord_3824803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824803).length < 2 ^ (prefixWord ++ tailWord_3824803).sum := by decide
  have hdescent : baseEnd_3824803 < baseStart_3824803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824816 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_3824816 : Nat := 118140960795 + 3824816 * 2 ^ 59
def prefixEnd_3824816 : Nat := 4983230072969 + 3 ^ 40 * 3824816 * 2
def baseEnd_3824816 : Nat := 1963969023007212623509997

theorem tailTrace_3824816 : CollatzResearch.WordTrace tailWord_3824816 prefixEnd_3824816 1963969023007212623509997 := by
  unfold tailWord_3824816
  simp only [CollatzResearch.WordTrace]
  refine ⟨69751250055676166705943151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93001666740901555607924201 69751250055676166705943151)
  ·
    refine ⟨104626875083514250058914727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69751250055676166705943151 104626875083514250058914727)
    ·
      refine ⟨156940312625271375088372091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104626875083514250058914727 156940312625271375088372091)
      ·
        refine ⟨235410468937907062632558137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156940312625271375088372091 235410468937907062632558137)
        ·
          refine ⟨176557851703430296974418603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235410468937907062632558137 176557851703430296974418603)
          ·
            refine ⟨264836777555145445461627905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176557851703430296974418603 264836777555145445461627905)
            ·
              refine ⟨198627583166359084096220929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264836777555145445461627905 198627583166359084096220929)
              ·
                refine ⟨148970687374769313072165697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198627583166359084096220929 148970687374769313072165697)
                ·
                  refine ⟨111728015531076984804124273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148970687374769313072165697 111728015531076984804124273)
                  ·
                    refine ⟨83796011648307738603093205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111728015531076984804124273 83796011648307738603093205)
                    ·
                      refine ⟨1963969023007212623509997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83796011648307738603093205 1963969023007212623509997)
                      ·
                        rfl

theorem cell23_3824816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_3824816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824816 prefixEnd_3824816 := by exact prefixLift 3824816
  have htrace : WordTrace (prefixWord ++ tailWord_3824816) baseStart_3824816 baseEnd_3824816 := by
    simpa [prefixWord, tailWord_3824816, baseEnd_3824816] using wordTrace_append hprefix tailTrace_3824816
  have hstable : (prefixWord ++ tailWord_3824816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824816).length < 2 ^ (prefixWord ++ tailWord_3824816).sum := by decide
  have hdescent : baseEnd_3824816 < baseStart_3824816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824817 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3824817 : Nat := 118140960795 + 3824817 * 2 ^ 59
def prefixEnd_3824817 : Nat := 4983230072969 + 3 ^ 40 * 3824817 * 2
def baseEnd_3824817 : Nat := 1963969536487867119597493

theorem tailTrace_3824817 : CollatzResearch.WordTrace tailWord_3824817 prefixEnd_3824817 1963969536487867119597493 := by
  unfold tailWord_3824817
  simp only [CollatzResearch.WordTrace]
  refine ⟨139502536584348710582672705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93001691056232473721781803 139502536584348710582672705)
  ·
    refine ⟨104626902438261532937004529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139502536584348710582672705 104626902438261532937004529)
    ·
      refine ⟨78470176828696149702753397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104626902438261532937004529 78470176828696149702753397)
      ·
        refine ⟨7356579077690264034633131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78470176828696149702753397 7356579077690264034633131)
        ·
          refine ⟨11034868616535396051949697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356579077690264034633131 11034868616535396051949697)
          ·
            refine ⟨8276151462401547038962273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11034868616535396051949697 8276151462401547038962273)
            ·
              refine ⟨6207113596801160279221705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276151462401547038962273 6207113596801160279221705)
              ·
                refine ⟨4655335197600870209416279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6207113596801160279221705 4655335197600870209416279)
                ·
                  refine ⟨6983002796401305314124419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655335197600870209416279 6983002796401305314124419)
                  ·
                    refine ⟨10474504194601957971186629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6983002796401305314124419 10474504194601957971186629)
                    ·
                      refine ⟨1963969536487867119597493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10474504194601957971186629 1963969536487867119597493)
                      ·
                        rfl

theorem cell23_3824817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3824817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824817 prefixEnd_3824817 := by exact prefixLift 3824817
  have htrace : WordTrace (prefixWord ++ tailWord_3824817) baseStart_3824817 baseEnd_3824817 := by
    simpa [prefixWord, tailWord_3824817, baseEnd_3824817] using wordTrace_append hprefix tailTrace_3824817
  have hstable : (prefixWord ++ tailWord_3824817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824817).length < 2 ^ (prefixWord ++ tailWord_3824817).sum := by decide
  have hdescent : baseEnd_3824817 < baseStart_3824817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824838 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3824838 : Nat := 118140960795 + 3824838 * 2 ^ 59
def prefixEnd_3824838 : Nat := 4983230072969 + 3 ^ 40 * 3824838 * 2
def baseEnd_3824838 : Nat := 1963980319581611537434897

theorem tailTrace_3824838 : CollatzResearch.WordTrace tailWord_3824838 prefixEnd_3824838 1963980319581611537434897 := by
  unfold tailWord_3824838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4359478203664769724037099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93002201678181754112791445 4359478203664769724037099)
  ·
    refine ⟨6539217305497154586055649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4359478203664769724037099 6539217305497154586055649)
    ·
      refine ⟨4904412979122865939541737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6539217305497154586055649 4904412979122865939541737)
      ·
        refine ⟨3678309734342149454656303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4904412979122865939541737 3678309734342149454656303)
        ·
          refine ⟨5517464601513224181984455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678309734342149454656303 5517464601513224181984455)
          ·
            refine ⟨8276196902269836272976683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517464601513224181984455 8276196902269836272976683)
            ·
              refine ⟨12414295353404754409465025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8276196902269836272976683 12414295353404754409465025)
              ·
                refine ⟨9310721515053565807098769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12414295353404754409465025 9310721515053565807098769)
                ·
                  refine ⟨6983041136290174355324077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9310721515053565807098769 6983041136290174355324077)
                  ·
                    refine ⟨2618640426108815383246529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6983041136290174355324077 2618640426108815383246529)
                    ·
                      refine ⟨1963980319581611537434897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618640426108815383246529 1963980319581611537434897)
                      ·
                        rfl

theorem cell23_3824838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3824838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824838 prefixEnd_3824838 := by exact prefixLift 3824838
  have htrace : WordTrace (prefixWord ++ tailWord_3824838) baseStart_3824838 baseEnd_3824838 := by
    simpa [prefixWord, tailWord_3824838, baseEnd_3824838] using wordTrace_append hprefix tailTrace_3824838
  have hstable : (prefixWord ++ tailWord_3824838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824838).length < 2 ^ (prefixWord ++ tailWord_3824838).sum := by decide
  have hdescent : baseEnd_3824838 < baseStart_3824838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824845 : List Nat := [1, 6, 2, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3824845 : Nat := 118140960795 + 3824845 * 2 ^ 59
def prefixEnd_3824845 : Nat := 4983230072969 + 3 ^ 40 * 3824845 * 2
def baseEnd_3824845 : Nat := 1963983913946193010047365

theorem tailTrace_3824845 : CollatzResearch.WordTrace tailWord_3824845 prefixEnd_3824845 1963983913946193010047365 := by
  unfold tailWord_3824845
  simp only [CollatzResearch.WordTrace]
  refine ⟨139503557828247271364691989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93002371885498180909794659 139503557828247271364691989)
  ·
    refine ⟨6539229273199090845219937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139503557828247271364691989 6539229273199090845219937)
    ·
      refine ⟨4904421954899318133914953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6539229273199090845219937 4904421954899318133914953)
      ·
        refine ⟨3678316466174488600436215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4904421954899318133914953 3678316466174488600436215)
        ·
          refine ⟨5517474699261732900654323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678316466174488600436215 5517474699261732900654323)
          ·
            refine ⟨8276212048892599350981485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517474699261732900654323 8276212048892599350981485)
            ·
              refine ⟨3103579518334724756618057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8276212048892599350981485 3103579518334724756618057)
              ·
                refine ⟨2327684638751043567463543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103579518334724756618057 2327684638751043567463543)
                ·
                  refine ⟨3491526958126565351195315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327684638751043567463543 3491526958126565351195315)
                  ·
                    refine ⟨5237290437189848026792973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3491526958126565351195315 5237290437189848026792973)
                    ·
                      refine ⟨1963983913946193010047365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237290437189848026792973 1963983913946193010047365)
                      ·
                        rfl

theorem cell23_3824845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3824845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824845 prefixEnd_3824845 := by exact prefixLift 3824845
  have htrace : WordTrace (prefixWord ++ tailWord_3824845) baseStart_3824845 baseEnd_3824845 := by
    simpa [prefixWord, tailWord_3824845, baseEnd_3824845] using wordTrace_append hprefix tailTrace_3824845
  have hstable : (prefixWord ++ tailWord_3824845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824845).length < 2 ^ (prefixWord ++ tailWord_3824845).sum := by decide
  have hdescent : baseEnd_3824845 < baseStart_3824845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824861 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3824861 : Nat := 118140960795 + 3824861 * 2 ^ 59
def prefixEnd_3824861 : Nat := 4983230072969 + 3 ^ 40 * 3824861 * 2
def baseEnd_3824861 : Nat := 654664043212221649149097

theorem tailTrace_3824861 : CollatzResearch.WordTrace tailWord_3824861 prefixEnd_3824861 654664043212221649149097 := by
  unfold tailWord_3824861
  simp only [CollatzResearch.WordTrace]
  refine ⟨139504141396189306097274437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93002760930792870731516291 139504141396189306097274437)
  ·
    refine ⟨26157026511785494893238957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139504141396189306097274437 26157026511785494893238957)
    ·
      refine ⟨9808884941919560584964609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26157026511785494893238957 9808884941919560584964609)
      ·
        refine ⟨7356663706439670438723457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9808884941919560584964609 7356663706439670438723457)
        ·
          refine ⟨5517497779829752829042593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7356663706439670438723457 5517497779829752829042593)
          ·
            refine ⟨4138123334872314621781945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517497779829752829042593 4138123334872314621781945)
            ·
              refine ⟨3103592501154235966336459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4138123334872314621781945 3103592501154235966336459)
              ·
                refine ⟨4655388751731353949504689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103592501154235966336459 4655388751731353949504689)
                ·
                  refine ⟨3491541563798515462128517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655388751731353949504689 3491541563798515462128517)
                  ·
                    refine ⟨654664043212221649149097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3491541563798515462128517 654664043212221649149097)
                    ·
                      rfl

theorem cell23_3824861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3824861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824861 prefixEnd_3824861 := by exact prefixLift 3824861
  have htrace : WordTrace (prefixWord ++ tailWord_3824861) baseStart_3824861 baseEnd_3824861 := by
    simpa [prefixWord, tailWord_3824861, baseEnd_3824861] using wordTrace_append hprefix tailTrace_3824861
  have hstable : (prefixWord ++ tailWord_3824861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824861).length < 2 ^ (prefixWord ++ tailWord_3824861).sum := by decide
  have hdescent : baseEnd_3824861 < baseStart_3824861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824871 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3824871 : Nat := 118140960795 + 3824871 * 2 ^ 59
def prefixEnd_3824871 : Nat := 4983230072969 + 3 ^ 40 * 3824871 * 2
def baseEnd_3824871 : Nat := 1963997264443209908322245

theorem tailTrace_3824871 : CollatzResearch.WordTrace tailWord_3824871 prefixEnd_3824871 1963997264443209908322245 := by
  unfold tailWord_3824871
  simp only [CollatzResearch.WordTrace]
  refine ⟨139504506126153077805138467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93003004084102051870092311 139504506126153077805138467)
  ·
    refine ⟨209256759189229616707707701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139504506126153077805138467 209256759189229616707707701)
    ·
      refine ⟨19617821173990276566347597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209256759189229616707707701 19617821173990276566347597)
      ·
        refine ⟨7356682940246353712380349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19617821173990276566347597 7356682940246353712380349)
        ·
          refine ⟨2758756102592382642142631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7356682940246353712380349 2758756102592382642142631)
          ·
            refine ⟨4138134153888573963213947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758756102592382642142631 4138134153888573963213947)
            ·
              refine ⟨6207201230832860944820921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138134153888573963213947 6207201230832860944820921)
              ·
                refine ⟨4655400923124645708615691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6207201230832860944820921 4655400923124645708615691)
                ·
                  refine ⟨6983101384686968562923537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655400923124645708615691 6983101384686968562923537)
                  ·
                    refine ⟨5237326038515226422192653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6983101384686968562923537 5237326038515226422192653)
                    ·
                      refine ⟨1963997264443209908322245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237326038515226422192653 1963997264443209908322245)
                      ·
                        rfl

theorem cell23_3824871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3824871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824871 prefixEnd_3824871 := by exact prefixLift 3824871
  have htrace : WordTrace (prefixWord ++ tailWord_3824871) baseStart_3824871 baseEnd_3824871 := by
    simpa [prefixWord, tailWord_3824871, baseEnd_3824871] using wordTrace_append hprefix tailTrace_3824871
  have hstable : (prefixWord ++ tailWord_3824871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824871).length < 2 ^ (prefixWord ++ tailWord_3824871).sum := by decide
  have hdescent : baseEnd_3824871 < baseStart_3824871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824910 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3824910 : Nat := 118140960795 + 3824910 * 2 ^ 59
def prefixEnd_3824910 : Nat := 4983230072969 + 3 ^ 40 * 3824910 * 2
def baseEnd_3824910 : Nat := 1964017290188735255734565

theorem tailTrace_3824910 : CollatzResearch.WordTrace tailWord_3824910 prefixEnd_3824910 1964017290188735255734565 := by
  unfold tailWord_3824910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17438241071626473433226023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93003952382007858310538789 17438241071626473433226023)
  ·
    refine ⟨26157361607439710149839035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17438241071626473433226023 26157361607439710149839035)
    ·
      refine ⟨39236042411159565224758553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26157361607439710149839035 39236042411159565224758553)
      ·
        refine ⟨29427031808369673918568915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39236042411159565224758553 29427031808369673918568915)
        ·
          refine ⟨44140547712554510877853373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29427031808369673918568915 44140547712554510877853373)
          ·
            refine ⟨16552705392207941579195015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44140547712554510877853373 16552705392207941579195015)
            ·
              refine ⟨24829058088311912368792523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16552705392207941579195015 24829058088311912368792523)
              ·
                refine ⟨37243587132467868553188785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24829058088311912368792523 37243587132467868553188785)
                ·
                  refine ⟨27932690349350901414891589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37243587132467868553188785 27932690349350901414891589)
                  ·
                    refine ⟨5237379440503294015292173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27932690349350901414891589 5237379440503294015292173)
                    ·
                      refine ⟨1964017290188735255734565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5237379440503294015292173 1964017290188735255734565)
                      ·
                        rfl

theorem cell23_3824910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3824910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824910 prefixEnd_3824910 := by exact prefixLift 3824910
  have htrace : WordTrace (prefixWord ++ tailWord_3824910) baseStart_3824910 baseEnd_3824910 := by
    simpa [prefixWord, tailWord_3824910, baseEnd_3824910] using wordTrace_append hprefix tailTrace_3824910
  have hstable : (prefixWord ++ tailWord_3824910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824910).length < 2 ^ (prefixWord ++ tailWord_3824910).sum := by decide
  have hdescent : baseEnd_3824910 < baseStart_3824910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824913 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 7]
def baseStart_3824913 : Nat := 118140960795 + 3824913 * 2 ^ 59
def prefixEnd_3824913 : Nat := 4983230072969 + 3 ^ 40 * 3824913 * 2
def baseEnd_3824913 : Nat := 218224314514522082666339

theorem tailTrace_3824913 : CollatzResearch.WordTrace tailWord_3824913 prefixEnd_3824913 218224314514522082666339 := by
  unfold tailWord_3824913
  simp only [CollatzResearch.WordTrace]
  refine ⟨139506037992000918978167393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93004025328000612652111595 139506037992000918978167393)
  ·
    refine ⟨104629528494000689233625545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139506037992000918978167393 104629528494000689233625545)
    ·
      refine ⟨78472146370500516925219159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104629528494000689233625545 78472146370500516925219159)
      ·
        refine ⟨117708219555750775387828739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78472146370500516925219159 117708219555750775387828739)
        ·
          refine ⟨176562329333626163081743109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117708219555750775387828739 176562329333626163081743109)
          ·
            refine ⟨33105436750054905577826833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176562329333626163081743109 33105436750054905577826833)
            ·
              refine ⟨24829077562541179183370125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33105436750054905577826833 24829077562541179183370125)
              ·
                refine ⟨9310904085952942193763797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24829077562541179183370125 9310904085952942193763797)
                ·
                  refine ⟨218224314514522082666339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9310904085952942193763797 218224314514522082666339)
                  ·
                    rfl

theorem cell23_3824913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 7].length) (baseStart_3824913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824913 prefixEnd_3824913 := by exact prefixLift 3824913
  have htrace : WordTrace (prefixWord ++ tailWord_3824913) baseStart_3824913 baseEnd_3824913 := by
    simpa [prefixWord, tailWord_3824913, baseEnd_3824913] using wordTrace_append hprefix tailTrace_3824913
  have hstable : (prefixWord ++ tailWord_3824913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824913).length < 2 ^ (prefixWord ++ tailWord_3824913).sum := by decide
  have hdescent : baseEnd_3824913 < baseStart_3824913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824920 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3824920 : Nat := 118140960795 + 3824920 * 2 ^ 59
def prefixEnd_3824920 : Nat := 4983230072969 + 3 ^ 40 * 3824920 * 2
def baseEnd_3824920 : Nat := 1964022424995280216609519

theorem tailTrace_3824920 : CollatzResearch.WordTrace tailWord_3824920 prefixEnd_3824920 1964022424995280216609519 := by
  unfold tailWord_3824920
  simp only [CollatzResearch.WordTrace]
  refine ⟨69753146651487779586836107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93004195535317039449114809 69753146651487779586836107)
  ·
    refine ⟨104629719977231669380254161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69753146651487779586836107 104629719977231669380254161)
    ·
      refine ⟨78472289982923752035190621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104629719977231669380254161 78472289982923752035190621)
      ·
        refine ⟨29427108743596407013196483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78472289982923752035190621 29427108743596407013196483)
        ·
          refine ⟨44140663115394610519794725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29427108743596407013196483 44140663115394610519794725)
          ·
            refine ⟨8276374334136489472461511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44140663115394610519794725 8276374334136489472461511)
            ·
              refine ⟨12414561501204734208692267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8276374334136489472461511 12414561501204734208692267)
              ·
                refine ⟨18621842251807101313038401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12414561501204734208692267 18621842251807101313038401)
                ·
                  refine ⟨13966381688855325984778801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18621842251807101313038401 13966381688855325984778801)
                  ·
                    refine ⟨10474786266641494488584101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13966381688855325984778801 10474786266641494488584101)
                    ·
                      refine ⟨1964022424995280216609519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10474786266641494488584101 1964022424995280216609519)
                      ·
                        rfl

theorem cell23_3824920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3824920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824920 prefixEnd_3824920 := by exact prefixLift 3824920
  have htrace : WordTrace (prefixWord ++ tailWord_3824920) baseStart_3824920 baseEnd_3824920 := by
    simpa [prefixWord, tailWord_3824920, baseEnd_3824920] using wordTrace_append hprefix tailTrace_3824920
  have hstable : (prefixWord ++ tailWord_3824920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824920).length < 2 ^ (prefixWord ++ tailWord_3824920).sum := by decide
  have hdescent : baseEnd_3824920 < baseStart_3824920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824924 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_3824924 : Nat := 118140960795 + 3824924 * 2 ^ 59
def prefixEnd_3824924 : Nat := 4983230072969 + 3 ^ 40 * 3824924 * 2
def baseEnd_3824924 : Nat := 1964024478917898200959501

theorem tailTrace_3824924 : CollatzResearch.WordTrace tailWord_3824924 prefixEnd_3824924 1964024478917898200959501 := by
  unfold tailWord_3824924
  simp only [CollatzResearch.WordTrace]
  refine ⟨69753219597480533928408913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93004292796640711904545217 69753219597480533928408913)
  ·
    refine ⟨52314914698110400446306685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69753219597480533928408913 52314914698110400446306685)
    ·
      refine ⟨19618093011791400167365007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52314914698110400446306685 19618093011791400167365007)
      ·
        refine ⟨29427139517687100251047511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19618093011791400167365007 29427139517687100251047511)
        ·
          refine ⟨44140709276530650376571267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29427139517687100251047511 44140709276530650376571267)
          ·
            refine ⟨66211063914795975564856901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44140709276530650376571267 66211063914795975564856901)
            ·
              refine ⟨12414574484024245418410669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66211063914795975564856901 12414574484024245418410669)
              ·
                refine ⟨4655465431509092031904001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12414574484024245418410669 4655465431509092031904001)
                ·
                  refine ⟨3491599073631819023928001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655465431509092031904001 3491599073631819023928001)
                  ·
                    refine ⟨2618699305223864267946001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3491599073631819023928001 2618699305223864267946001)
                    ·
                      refine ⟨1964024478917898200959501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2618699305223864267946001 1964024478917898200959501)
                      ·
                        rfl

theorem cell23_3824924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_3824924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3824924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3824924 prefixEnd_3824924 := by exact prefixLift 3824924
  have htrace : WordTrace (prefixWord ++ tailWord_3824924) baseStart_3824924 baseEnd_3824924 := by
    simpa [prefixWord, tailWord_3824924, baseEnd_3824924] using wordTrace_append hprefix tailTrace_3824924
  have hstable : (prefixWord ++ tailWord_3824924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824924).length < 2 ^ (prefixWord ++ tailWord_3824924).sum := by decide
  have hdescent : baseEnd_3824924 < baseStart_3824924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
