import V185TrunkScan23Chunk0034

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_207911 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_207911 : Nat := 118140960795 + 207911 * 2 ^ 59
def prefixEnd_207911 : Nat := 4983230072969 + 3 ^ 40 * 207911 * 2
def baseEnd_207911 : Nat := 106758276357041280956341

theorem tailTrace_207911 : CollatzResearch.WordTrace tailWord_207911 prefixEnd_207911 106758276357041280956341 := by
  unfold tailWord_207911
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583137149781430216943587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5055424766520953477962391 7583137149781430216943587)
  ·
    refine ⟨11374705724672145325415381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7583137149781430216943587 11374705724672145325415381)
    ·
      refine ⟨266594665422003406064423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11374705724672145325415381 266594665422003406064423)
      ·
        refine ⟨399891998133005109096635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266594665422003406064423 399891998133005109096635)
        ·
          refine ⟨599837997199507663644953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399891998133005109096635 599837997199507663644953)
          ·
            refine ⟨449878497899630747733715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599837997199507663644953 449878497899630747733715)
            ·
              refine ⟨674817746849446121600573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449878497899630747733715 674817746849446121600573)
              ·
                refine ⟨253056655068542295600215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 674817746849446121600573 253056655068542295600215)
                ·
                  refine ⟨379584982602813443400323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253056655068542295600215 379584982602813443400323)
                  ·
                    refine ⟨569377473904220165100485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 379584982602813443400323 569377473904220165100485)
                    ·
                      refine ⟨106758276357041280956341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 569377473904220165100485 106758276357041280956341)
                      ·
                        rfl

theorem cell23_207911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_207911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207911 prefixEnd_207911 := by exact prefixLift 207911
  have htrace : WordTrace (prefixWord ++ tailWord_207911) baseStart_207911 baseEnd_207911 := by
    simpa [prefixWord, tailWord_207911, baseEnd_207911] using wordTrace_append hprefix tailTrace_207911
  have hstable : (prefixWord ++ tailWord_207911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207911).length < 2 ^ (prefixWord ++ tailWord_207911).sum := by decide
  have hdescent : baseEnd_207911 < baseStart_207911 := by decide
  rcases family_descends (prefixWord ++ tailWord_207911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207928 : List Nat := [2, 1, 2, 1, 5, 1, 2, 4, 1, 2, 2]
def baseStart_207928 : Nat := 118140960795 + 207928 * 2 ^ 59
def prefixEnd_207928 : Nat := 4983230072969 + 3 ^ 40 * 207928 * 2
def baseEnd_207928 : Nat := 106767005528167714443763

theorem tailTrace_207928 : CollatzResearch.WordTrace tailWord_207928 prefixEnd_207928 106767005528167714443763 := by
  unfold tailWord_207928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791878595359921060156219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5055838127146561413541625 3791878595359921060156219)
  ·
    refine ⟨5687817893039881590234329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3791878595359921060156219 5687817893039881590234329)
    ·
      refine ⟨4265863419779911192675747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5687817893039881590234329 4265863419779911192675747)
      ·
        refine ⟨6398795129669866789013621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265863419779911192675747 6398795129669866789013621)
        ·
          refine ⟨599887043406550011470027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6398795129669866789013621 599887043406550011470027)
          ·
            refine ⟨899830565109825017205041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599887043406550011470027 899830565109825017205041)
            ·
              refine ⟨674872923832368762903781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899830565109825017205041 674872923832368762903781)
              ·
                refine ⟨126538673218569143044459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674872923832368762903781 126538673218569143044459)
                ·
                  refine ⟨189808009827853714566689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126538673218569143044459 189808009827853714566689)
                  ·
                    refine ⟨142356007370890285925017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189808009827853714566689 142356007370890285925017)
                    ·
                      refine ⟨106767005528167714443763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142356007370890285925017 106767005528167714443763)
                      ·
                        rfl

theorem cell23_207928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_207928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207928 prefixEnd_207928 := by exact prefixLift 207928
  have htrace : WordTrace (prefixWord ++ tailWord_207928) baseStart_207928 baseEnd_207928 := by
    simpa [prefixWord, tailWord_207928, baseEnd_207928] using wordTrace_append hprefix tailTrace_207928
  have hstable : (prefixWord ++ tailWord_207928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207928).length < 2 ^ (prefixWord ++ tailWord_207928).sum := by decide
  have hdescent : baseEnd_207928 < baseStart_207928 := by decide
  rcases family_descends (prefixWord ++ tailWord_207928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207930 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_207930 : Nat := 118140960795 + 207930 * 2 ^ 59
def prefixEnd_207930 : Nat := 4983230072969 + 3 ^ 40 * 207930 * 2
def baseEnd_207930 : Nat := 35589344163158902206251

theorem tailTrace_207930 : CollatzResearch.WordTrace tailWord_207930 prefixEnd_207930 35589344163158902206251 := by
  unfold tailWord_207930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895957534178149115471311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5055886757808397641256829 1895957534178149115471311)
  ·
    refine ⟨2843936301267223673206967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1895957534178149115471311 2843936301267223673206967)
    ·
      refine ⟨4265904451900835509810451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843936301267223673206967 4265904451900835509810451)
      ·
        refine ⟨6398856677851253264715677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265904451900835509810451 6398856677851253264715677)
        ·
          refine ⟨2399571254194219974268379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6398856677851253264715677 2399571254194219974268379)
          ·
            refine ⟨3599356881291329961402569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399571254194219974268379 3599356881291329961402569)
            ·
              refine ⟨2699517660968497471051927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3599356881291329961402569 2699517660968497471051927)
              ·
                refine ⟨4049276491452746206577891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699517660968497471051927 4049276491452746206577891)
                ·
                  refine ⟨6073914737179119309866837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049276491452746206577891 6073914737179119309866837)
                  ·
                    refine ⟨35589344163158902206251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 6073914737179119309866837 35589344163158902206251)
                    ·
                      rfl

theorem cell23_207930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_207930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207930 prefixEnd_207930 := by exact prefixLift 207930
  have htrace : WordTrace (prefixWord ++ tailWord_207930) baseStart_207930 baseEnd_207930 := by
    simpa [prefixWord, tailWord_207930, baseEnd_207930] using wordTrace_append hprefix tailTrace_207930
  have hstable : (prefixWord ++ tailWord_207930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207930).length < 2 ^ (prefixWord ++ tailWord_207930).sum := by decide
  have hdescent : baseEnd_207930 < baseStart_207930 := by decide
  rcases family_descends (prefixWord ++ tailWord_207930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_207997 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_207997 : Nat := 118140960795 + 207997 * 2 ^ 59
def prefixEnd_207997 : Nat := 4983230072969 + 3 ^ 40 * 207997 * 2
def baseEnd_207997 : Nat := 106802435693327944480945

theorem tailTrace_207997 : CollatzResearch.WordTrace tailWord_207997 prefixEnd_207997 106802435693327944480945 := by
  unfold tailWord_207997
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586273827469866904574245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5057515884979911269716163 7586273827469866904574245)
  ·
    refine ⟨1422426342650600044607671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7586273827469866904574245 1422426342650600044607671)
    ·
      refine ⟨2133639513975900066911507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422426342650600044607671 2133639513975900066911507)
      ·
        refine ⟨3200459270963850100367261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133639513975900066911507 3200459270963850100367261)
        ·
          refine ⟨1200172226611443787637723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3200459270963850100367261 1200172226611443787637723)
          ·
            refine ⟨1800258339917165681456585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200172226611443787637723 1800258339917165681456585)
            ·
              refine ⟨1350193754937874261092439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1800258339917165681456585 1350193754937874261092439)
              ·
                refine ⟨2025290632406811391638659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350193754937874261092439 2025290632406811391638659)
                ·
                  refine ⟨3037935948610217087457989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025290632406811391638659 3037935948610217087457989)
                  ·
                    refine ⟨569612990364415703898373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037935948610217087457989 569612990364415703898373)
                    ·
                      refine ⟨106802435693327944480945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 569612990364415703898373 106802435693327944480945)
                      ·
                        rfl

theorem cell23_207997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_207997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_207997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_207997 prefixEnd_207997 := by exact prefixLift 207997
  have htrace : WordTrace (prefixWord ++ tailWord_207997) baseStart_207997 baseEnd_207997 := by
    simpa [prefixWord, tailWord_207997, baseEnd_207997] using wordTrace_append hprefix tailTrace_207997
  have hstable : (prefixWord ++ tailWord_207997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_207997).length < 2 ^ (prefixWord ++ tailWord_207997).sum := by decide
  have hdescent : baseEnd_207997 < baseStart_207997 := by decide
  rcases family_descends (prefixWord ++ tailWord_207997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208005 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 1, 3, 2]
def baseStart_208005 : Nat := 118140960795 + 208005 * 2 ^ 59
def prefixEnd_208005 : Nat := 4983230072969 + 3 ^ 40 * 208005 * 2
def baseEnd_208005 : Nat := 106806543538563913180909

theorem tailTrace_208005 : CollatzResearch.WordTrace tailWord_208005 prefixEnd_208005 106806543538563913180909 := by
  unfold tailWord_208005
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586565611440884270865469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5057710407627256180576979 7586565611440884270865469)
  ·
    refine ⟨2844962104290331601574551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7586565611440884270865469 2844962104290331601574551)
    ·
      refine ⟨4267443156435497402361827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2844962104290331601574551 4267443156435497402361827)
      ·
        refine ⟨6401164734653246103542741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267443156435497402361827 6401164734653246103542741)
        ·
          refine ⟨150027298468435455551783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6401164734653246103542741 150027298468435455551783)
          ·
            refine ⟨225040947702653183327675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150027298468435455551783 225040947702653183327675)
            ·
              refine ⟨337561421553979774991513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225040947702653183327675 337561421553979774991513)
              ·
                refine ⟨253171066165484831243635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337561421553979774991513 253171066165484831243635)
                ·
                  refine ⟨379756599248227246865453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253171066165484831243635 379756599248227246865453)
                  ·
                    refine ⟨142408724718085217574545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379756599248227246865453 142408724718085217574545)
                    ·
                      refine ⟨106806543538563913180909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142408724718085217574545 106806543538563913180909)
                      ·
                        rfl

theorem cell23_208005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_208005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208005 prefixEnd_208005 := by exact prefixLift 208005
  have htrace : WordTrace (prefixWord ++ tailWord_208005) baseStart_208005 baseEnd_208005 := by
    simpa [prefixWord, tailWord_208005, baseEnd_208005] using wordTrace_append hprefix tailTrace_208005
  have hstable : (prefixWord ++ tailWord_208005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208005).length < 2 ^ (prefixWord ++ tailWord_208005).sum := by decide
  have hdescent : baseEnd_208005 < baseStart_208005 := by decide
  rcases family_descends (prefixWord ++ tailWord_208005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208047 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_208047 : Nat := 118140960795 + 208047 * 2 ^ 59
def prefixEnd_208047 : Nat := 4983230072969 + 3 ^ 40 * 208047 * 2
def baseEnd_208047 : Nat := 106828109726052748855715

theorem tailTrace_208047 : CollatzResearch.WordTrace tailWord_208047 prefixEnd_208047 106828109726052748855715 := by
  unfold tailWord_208047
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588097477288725443894395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5058731651525816962596263 7588097477288725443894395)
  ·
    refine ⟨11382146215933088165841593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7588097477288725443894395 11382146215933088165841593)
    ·
      refine ⟨8536609661949816124381195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11382146215933088165841593 8536609661949816124381195)
      ·
        refine ⟨12804914492924724186571793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536609661949816124381195 12804914492924724186571793)
        ·
          refine ⟨9603685869693543139928845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12804914492924724186571793 9603685869693543139928845)
          ·
            refine ⟨3601382201135078677473317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9603685869693543139928845 3601382201135078677473317)
            ·
              refine ⟨675259162712827252026247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3601382201135078677473317 675259162712827252026247)
              ·
                refine ⟨1012888744069240878039371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675259162712827252026247 1012888744069240878039371)
                ·
                  refine ⟨1519333116103861317059057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012888744069240878039371 1519333116103861317059057)
                  ·
                    refine ⟨1139499837077895987794293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1519333116103861317059057 1139499837077895987794293)
                    ·
                      refine ⟨106828109726052748855715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1139499837077895987794293 106828109726052748855715)
                      ·
                        rfl

theorem cell23_208047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_208047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208047 prefixEnd_208047 := by exact prefixLift 208047
  have htrace : WordTrace (prefixWord ++ tailWord_208047) baseStart_208047 baseEnd_208047 := by
    simpa [prefixWord, tailWord_208047, baseEnd_208047] using wordTrace_append hprefix tailTrace_208047
  have hstable : (prefixWord ++ tailWord_208047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208047).length < 2 ^ (prefixWord ++ tailWord_208047).sum := by decide
  have hdescent : baseEnd_208047 < baseStart_208047 := by decide
  rcases family_descends (prefixWord ++ tailWord_208047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208074 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_208074 : Nat := 118140960795 + 208074 * 2 ^ 59
def prefixEnd_208074 : Nat := 4983230072969 + 3 ^ 40 * 208074 * 2
def baseEnd_208074 : Nat := 106841973703724143218091

theorem tailTrace_208074 : CollatzResearch.WordTrace tailWord_208074 prefixEnd_208074 106841973703724143218091 := by
  unfold tailWord_208074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897270562047727263781819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5059388165460606036751517 1897270562047727263781819)
  ·
    refine ⟨2845905843071590895672729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1897270562047727263781819 2845905843071590895672729)
    ·
      refine ⟨2134429382303693171754547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2845905843071590895672729 2134429382303693171754547)
      ·
        refine ⟨3201644073455539757631821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134429382303693171754547 3201644073455539757631821)
        ·
          refine ⟨1200616527545827409111933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3201644073455539757631821 1200616527545827409111933)
          ·
            refine ⟨450231197829685278416975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1200616527545827409111933 450231197829685278416975)
            ·
              refine ⟨675346796744527917625463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450231197829685278416975 675346796744527917625463)
              ·
                refine ⟨1013020195116791876438195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675346796744527917625463 1013020195116791876438195)
                ·
                  refine ⟨1519530292675187814657293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013020195116791876438195 1519530292675187814657293)
                  ·
                    refine ⟨569823859753195430496485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519530292675187814657293 569823859753195430496485)
                    ·
                      refine ⟨106841973703724143218091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 569823859753195430496485 106841973703724143218091)
                      ·
                        rfl

theorem cell23_208074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_208074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208074 prefixEnd_208074 := by exact prefixLift 208074
  have htrace : WordTrace (prefixWord ++ tailWord_208074) baseStart_208074 baseEnd_208074 := by
    simpa [prefixWord, tailWord_208074, baseEnd_208074] using wordTrace_append hprefix tailTrace_208074
  have hstable : (prefixWord ++ tailWord_208074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208074).length < 2 ^ (prefixWord ++ tailWord_208074).sum := by decide
  have hdescent : baseEnd_208074 < baseStart_208074 := by decide
  rcases family_descends (prefixWord ++ tailWord_208074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208087 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_208087 : Nat := 118140960795 + 208087 * 2 ^ 59
def prefixEnd_208087 : Nat := 4983230072969 + 3 ^ 40 * 208087 * 2
def baseEnd_208087 : Nat := 106848648952232592355531

theorem tailTrace_208087 : CollatzResearch.WordTrace tailWord_208087 prefixEnd_208087 106848648952232592355531 := by
  unfold tailWord_208087
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589556397143812275350515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5059704264762541516900343 7589556397143812275350515)
  ·
    refine ⟨11384334595715718413025773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7589556397143812275350515 11384334595715718413025773)
    ·
      refine ⟨4269125473393394404884665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11384334595715718413025773 4269125473393394404884665)
      ·
        refine ⟨3201844105045045803663499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4269125473393394404884665 3201844105045045803663499)
        ·
          refine ⟨4802766157567568705495249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201844105045045803663499 4802766157567568705495249)
          ·
            refine ⟨3602074618175676529121437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4802766157567568705495249 3602074618175676529121437)
            ·
              refine ⟨1350777981815878698420539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3602074618175676529121437 1350777981815878698420539)
              ·
                refine ⟨2026166972723818047630809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350777981815878698420539 2026166972723818047630809)
                ·
                  refine ⟨1519625229542863535723107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026166972723818047630809 1519625229542863535723107)
                  ·
                    refine ⟨2279437844314295303584661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1519625229542863535723107 2279437844314295303584661)
                    ·
                      refine ⟨106848648952232592355531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2279437844314295303584661 106848648952232592355531)
                      ·
                        rfl

theorem cell23_208087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_208087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208087 prefixEnd_208087 := by exact prefixLift 208087
  have htrace : WordTrace (prefixWord ++ tailWord_208087) baseStart_208087 baseEnd_208087 := by
    simpa [prefixWord, tailWord_208087, baseEnd_208087] using wordTrace_append hprefix tailTrace_208087
  have hstable : (prefixWord ++ tailWord_208087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208087).length < 2 ^ (prefixWord ++ tailWord_208087).sum := by decide
  have hdescent : baseEnd_208087 < baseStart_208087 := by decide
  rcases family_descends (prefixWord ++ tailWord_208087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208178 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_208178 : Nat := 118140960795 + 208178 * 2 ^ 59
def prefixEnd_208178 : Nat := 4983230072969 + 3 ^ 40 * 208178 * 2
def baseEnd_208178 : Nat := 35631791897263912105871

theorem tailTrace_208178 : CollatzResearch.WordTrace tailWord_208178 prefixEnd_208178 35631791897263912105871 := by
  unfold tailWord_208178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898218859953533704228297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5061916959876089877942125 1898218859953533704228297)
  ·
    refine ⟨1423664144965150278171223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1898218859953533704228297 1423664144965150278171223)
    ·
      refine ⟨2135496217447725417256835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423664144965150278171223 2135496217447725417256835)
      ·
        refine ⟨3203244326171588125885253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135496217447725417256835 3203244326171588125885253)
        ·
          refine ⟨600608311157172773603485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3203244326171588125885253 600608311157172773603485)
          ·
            refine ⟨225228116683939790101307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600608311157172773603485 225228116683939790101307)
            ·
              refine ⟨337842175025909685151961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225228116683939790101307 337842175025909685151961)
              ·
                refine ⟨253381631269432263863971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337842175025909685151961 253381631269432263863971)
                ·
                  refine ⟨380072446904148395795957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253381631269432263863971 380072446904148395795957)
                  ·
                    refine ⟨35631791897263912105871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 380072446904148395795957 35631791897263912105871)
                    ·
                      rfl

theorem cell23_208178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_208178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208178 prefixEnd_208178 := by exact prefixLift 208178
  have htrace : WordTrace (prefixWord ++ tailWord_208178) baseStart_208178 baseEnd_208178 := by
    simpa [prefixWord, tailWord_208178, baseEnd_208178] using wordTrace_append hprefix tailTrace_208178
  have hstable : (prefixWord ++ tailWord_208178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208178).length < 2 ^ (prefixWord ++ tailWord_208178).sum := by decide
  have hdescent : baseEnd_208178 < baseStart_208178 := by decide
  rcases family_descends (prefixWord ++ tailWord_208178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208181 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_208181 : Nat := 118140960795 + 208181 * 2 ^ 59
def prefixEnd_208181 : Nat := 4983230072969 + 3 ^ 40 * 208181 * 2
def baseEnd_208181 : Nat := 106896916133755224580099

theorem tailTrace_208181 : CollatzResearch.WordTrace tailWord_208181 prefixEnd_208181 106896916133755224580099 := by
  unfold tailWord_208181
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592984858803266329272397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5061989905868844219514931 7592984858803266329272397)
  ·
    refine ⟨2847369322051224873477149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7592984858803266329272397 2847369322051224873477149)
    ·
      refine ⟨1067763495769209327553931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2847369322051224873477149 1067763495769209327553931)
      ·
        refine ⟨1601645243653813991330897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067763495769209327553931 1601645243653813991330897)
        ·
          refine ⟨1201233932740360493498173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1601645243653813991330897 1201233932740360493498173)
          ·
            refine ⟨450462724777635185061815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1201233932740360493498173 450462724777635185061815)
            ·
              refine ⟨675694087166452777592723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450462724777635185061815 675694087166452777592723)
              ·
                refine ⟨1013541130749679166389085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675694087166452777592723 1013541130749679166389085)
                ·
                  refine ⟨380077924031129687395907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013541130749679166389085 380077924031129687395907)
                  ·
                    refine ⟨570116886046694531093861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 380077924031129687395907 570116886046694531093861)
                    ·
                      refine ⟨106896916133755224580099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 570116886046694531093861 106896916133755224580099)
                      ·
                        rfl

theorem cell23_208181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_208181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208181 prefixEnd_208181 := by exact prefixLift 208181
  have htrace : WordTrace (prefixWord ++ tailWord_208181) baseStart_208181 baseEnd_208181 := by
    simpa [prefixWord, tailWord_208181, baseEnd_208181] using wordTrace_append hprefix tailTrace_208181
  have hstable : (prefixWord ++ tailWord_208181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208181).length < 2 ^ (prefixWord ++ tailWord_208181).sum := by decide
  have hdescent : baseEnd_208181 < baseStart_208181 := by decide
  rcases family_descends (prefixWord ++ tailWord_208181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208185 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 2, 3, 2]
def baseStart_208185 : Nat := 118140960795 + 208185 * 2 ^ 59
def prefixEnd_208185 : Nat := 4983230072969 + 3 ^ 40 * 208185 * 2
def baseEnd_208185 : Nat := 106898970056373208930081

theorem tailTrace_208185 : CollatzResearch.WordTrace tailWord_208185 prefixEnd_208185 106898970056373208930081 := by
  unfold tailWord_208185
  simp only [CollatzResearch.WordTrace]
  refine ⟨7593130750788775012418009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5062087167192516674945339 7593130750788775012418009)
  ·
    refine ⟨5694848063091581259313507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7593130750788775012418009 5694848063091581259313507)
    ·
      refine ⟨8542272094637371888970261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694848063091581259313507 8542272094637371888970261)
      ·
        refine ⟨400419004436126807295481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8542272094637371888970261 400419004436126807295481)
        ·
          refine ⟨300314253327095105471611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400419004436126807295481 300314253327095105471611)
          ·
            refine ⟨450471379990642658207417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300314253327095105471611 450471379990642658207417)
            ·
              refine ⟨337853534992981993655563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450471379990642658207417 337853534992981993655563)
              ·
                refine ⟨506780302489472990483345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337853534992981993655563 506780302489472990483345)
                ·
                  refine ⟨380085226867104742862509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506780302489472990483345 380085226867104742862509)
                  ·
                    refine ⟨142531960075164278573441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380085226867104742862509 142531960075164278573441)
                    ·
                      refine ⟨106898970056373208930081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142531960075164278573441 106898970056373208930081)
                      ·
                        rfl

theorem cell23_208185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_208185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208185 prefixEnd_208185 := by exact prefixLift 208185
  have htrace : WordTrace (prefixWord ++ tailWord_208185) baseStart_208185 baseEnd_208185 := by
    simpa [prefixWord, tailWord_208185, baseEnd_208185] using wordTrace_append hprefix tailTrace_208185
  have hstable : (prefixWord ++ tailWord_208185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208185).length < 2 ^ (prefixWord ++ tailWord_208185).sum := by decide
  have hdescent : baseEnd_208185 < baseStart_208185 := by decide
  rcases family_descends (prefixWord ++ tailWord_208185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208201 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 3]
def baseStart_208201 : Nat := 118140960795 + 208201 * 2 ^ 59
def prefixEnd_208201 : Nat := 4983230072969 + 3 ^ 40 * 208201 * 2
def baseEnd_208201 : Nat := 106907185746845146330007

theorem tailTrace_208201 : CollatzResearch.WordTrace tailWord_208201 prefixEnd_208201 106907185746845146330007 := by
  unfold tailWord_208201
  simp only [CollatzResearch.WordTrace]
  refine ⟨7593714318730809745000457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5062476212487206496666971 7593714318730809745000457)
  ·
    refine ⟨5695285739048107308750343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7593714318730809745000457 5695285739048107308750343)
    ·
      refine ⟨8542928608572160963125515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5695285739048107308750343 8542928608572160963125515)
      ·
        refine ⟨12814392912858241444688273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542928608572160963125515 12814392912858241444688273)
        ·
          refine ⟨9610794684643681083516205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12814392912858241444688273 9610794684643681083516205)
          ·
            refine ⟨3604048006741380406318577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9610794684643681083516205 3604048006741380406318577)
            ·
              refine ⟨2703036005056035304738933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604048006741380406318577 2703036005056035304738933)
              ·
                refine ⟨253409625474003309819275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2703036005056035304738933 253409625474003309819275)
                ·
                  refine ⟨380114438211004964728913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253409625474003309819275 380114438211004964728913)
                  ·
                    refine ⟨285085828658253723546685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 380114438211004964728913 285085828658253723546685)
                    ·
                      refine ⟨106907185746845146330007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 285085828658253723546685 106907185746845146330007)
                      ·
                        rfl

theorem cell23_208201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_208201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208201 prefixEnd_208201 := by exact prefixLift 208201
  have htrace : WordTrace (prefixWord ++ tailWord_208201) baseStart_208201 baseEnd_208201 := by
    simpa [prefixWord, tailWord_208201, baseEnd_208201] using wordTrace_append hprefix tailTrace_208201
  have hstable : (prefixWord ++ tailWord_208201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208201).length < 2 ^ (prefixWord ++ tailWord_208201).sum := by decide
  have hdescent : baseEnd_208201 < baseStart_208201 := by decide
  rcases family_descends (prefixWord ++ tailWord_208201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208314 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_208314 : Nat := 118140960795 + 208314 * 2 ^ 59
def prefixEnd_208314 : Nat := 4983230072969 + 3 ^ 40 * 208314 * 2
def baseEnd_208314 : Nat := 106965209060803204216987

theorem tailTrace_208314 : CollatzResearch.WordTrace tailWord_208314 prefixEnd_208314 106965209060803204216987 := by
  unfold tailWord_208314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1899458941830357510965999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5065223844880953362575997 1899458941830357510965999)
  ·
    refine ⟨2849188412745536266448999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1899458941830357510965999 2849188412745536266448999)
    ·
      refine ⟨4273782619118304399673499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2849188412745536266448999 4273782619118304399673499)
      ·
        refine ⟨6410673928677456599510249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4273782619118304399673499 6410673928677456599510249)
        ·
          refine ⟨4808005446508092449632687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6410673928677456599510249 4808005446508092449632687)
          ·
            refine ⟨7212008169762138674449031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808005446508092449632687 7212008169762138674449031)
            ·
              refine ⟨10818012254643208011673547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7212008169762138674449031 10818012254643208011673547)
              ·
                refine ⟨16227018381964812017510321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10818012254643208011673547 16227018381964812017510321)
                ·
                  refine ⟨12170263786473609013132741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16227018381964812017510321 12170263786473609013132741)
                  ·
                    refine ⟨2281924459963801689962389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12170263786473609013132741 2281924459963801689962389)
                    ·
                      refine ⟨106965209060803204216987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2281924459963801689962389 106965209060803204216987)
                      ·
                        rfl

theorem cell23_208314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_208314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208314 prefixEnd_208314 := by exact prefixLift 208314
  have htrace : WordTrace (prefixWord ++ tailWord_208314) baseStart_208314 baseEnd_208314 := by
    simpa [prefixWord, tailWord_208314, baseEnd_208314] using wordTrace_append hprefix tailTrace_208314
  have hstable : (prefixWord ++ tailWord_208314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208314).length < 2 ^ (prefixWord ++ tailWord_208314).sum := by decide
  have hdescent : baseEnd_208314 < baseStart_208314 := by decide
  rcases family_descends (prefixWord ++ tailWord_208314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208341 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_208341 : Nat := 118140960795 + 208341 * 2 ^ 59
def prefixEnd_208341 : Nat := 4983230072969 + 3 ^ 40 * 208341 * 2
def baseEnd_208341 : Nat := 35659691012824866193121

theorem tailTrace_208341 : CollatzResearch.WordTrace tailWord_208341 prefixEnd_208341 35659691012824866193121 := by
  unfold tailWord_208341
  simp only [CollatzResearch.WordTrace]
  refine ⟨7598820538223613655096877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5065880358815742436731251 7598820538223613655096877)
  ·
    refine ⟨2849557701833855120661329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7598820538223613655096877 2849557701833855120661329)
    ·
      refine ⟨2137168276375391340495997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2849557701833855120661329 2137168276375391340495997)
      ·
        refine ⟨801438103640771752685999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2137168276375391340495997 801438103640771752685999)
        ·
          refine ⟨1202157155461157629028999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801438103640771752685999 1202157155461157629028999)
          ·
            refine ⟨1803235733191736443543499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202157155461157629028999 1803235733191736443543499)
            ·
              refine ⟨2704853599787604665315249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803235733191736443543499 2704853599787604665315249)
              ·
                refine ⟨2028640199840703498986437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704853599787604665315249 2028640199840703498986437)
                ·
                  refine ⟨380370037470131906059957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2028640199840703498986437 380370037470131906059957)
                  ·
                    refine ⟨35659691012824866193121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 380370037470131906059957 35659691012824866193121)
                    ·
                      rfl

theorem cell23_208341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_208341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208341 prefixEnd_208341 := by exact prefixLift 208341
  have htrace : WordTrace (prefixWord ++ tailWord_208341) baseStart_208341 baseEnd_208341 := by
    simpa [prefixWord, tailWord_208341, baseEnd_208341] using wordTrace_append hprefix tailTrace_208341
  have hstable : (prefixWord ++ tailWord_208341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208341).length < 2 ^ (prefixWord ++ tailWord_208341).sum := by decide
  have hdescent : baseEnd_208341 < baseStart_208341 := by decide
  rcases family_descends (prefixWord ++ tailWord_208341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208371 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 7, 4]
def baseStart_208371 : Nat := 118140960795 + 208371 * 2 ^ 59
def prefixEnd_208371 : Nat := 4983230072969 + 3 ^ 40 * 208371 * 2
def baseEnd_208371 : Nat := 35664825819369827068075

theorem tailTrace_208371 : CollatzResearch.WordTrace tailWord_208371 prefixEnd_208371 35664825819369827068075 := by
  unfold tailWord_208371
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599914728114928778688967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5066609818743285852459311 7599914728114928778688967)
  ·
    refine ⟨11399872092172393168033451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599914728114928778688967 11399872092172393168033451)
    ·
      refine ⟨17099808138258589752050177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11399872092172393168033451 17099808138258589752050177)
      ·
        refine ⟨12824856103693942314037633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17099808138258589752050177 12824856103693942314037633)
        ·
          refine ⟨9618642077770456735528225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12824856103693942314037633 9618642077770456735528225)
          ·
            refine ⟨7213981558327842551646169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9618642077770456735528225 7213981558327842551646169)
            ·
              refine ⟨5410486168745881913734627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7213981558327842551646169 5410486168745881913734627)
              ·
                refine ⟨8115729253118822870601941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5410486168745881913734627 8115729253118822870601941)
                ·
                  refine ⟨190212404369972411029733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8115729253118822870601941 190212404369972411029733)
                  ·
                    refine ⟨35664825819369827068075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190212404369972411029733 35664825819369827068075)
                    ·
                      rfl

theorem cell23_208371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 4].length) (baseStart_208371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208371 prefixEnd_208371 := by exact prefixLift 208371
  have htrace : WordTrace (prefixWord ++ tailWord_208371) baseStart_208371 baseEnd_208371 := by
    simpa [prefixWord, tailWord_208371, baseEnd_208371] using wordTrace_append hprefix tailTrace_208371
  have hstable : (prefixWord ++ tailWord_208371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208371).length < 2 ^ (prefixWord ++ tailWord_208371).sum := by decide
  have hdescent : baseEnd_208371 < baseStart_208371 := by decide
  rcases family_descends (prefixWord ++ tailWord_208371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208378 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2]
def baseStart_208378 : Nat := 118140960795 + 208378 * 2 ^ 59
def prefixEnd_208378 : Nat := 4983230072969 + 3 ^ 40 * 208378 * 2
def baseEnd_208378 : Nat := 106998071822690953816693

theorem tailTrace_208378 : CollatzResearch.WordTrace tailWord_208378 prefixEnd_208378 106998071822690953816693 := by
  unfold tailWord_208378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900042509772392243548447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5066780026059712649462525 1900042509772392243548447)
  ·
    refine ⟨2850063764658588365322671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1900042509772392243548447 2850063764658588365322671)
    ·
      refine ⟨4275095646987882547984007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850063764658588365322671 4275095646987882547984007)
      ·
        refine ⟨6412643470481823821976011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275095646987882547984007 6412643470481823821976011)
        ·
          refine ⟨9618965205722735732964017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6412643470481823821976011 9618965205722735732964017)
          ·
            refine ⟨7214223904292051799723013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9618965205722735732964017 7214223904292051799723013)
            ·
              refine ⟨1352666982054759712448065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7214223904292051799723013 1352666982054759712448065)
              ·
                refine ⟨1014500236541069784336049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352666982054759712448065 1014500236541069784336049)
                ·
                  refine ⟨760875177405802338252037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1014500236541069784336049 760875177405802338252037)
                  ·
                    refine ⟨142664095763587938422257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760875177405802338252037 142664095763587938422257)
                    ·
                      refine ⟨106998071822690953816693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142664095763587938422257 106998071822690953816693)
                      ·
                        rfl

theorem cell23_208378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_208378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208378 prefixEnd_208378 := by exact prefixLift 208378
  have htrace : WordTrace (prefixWord ++ tailWord_208378) baseStart_208378 baseEnd_208378 := by
    simpa [prefixWord, tailWord_208378, baseEnd_208378] using wordTrace_append hprefix tailTrace_208378
  have hstable : (prefixWord ++ tailWord_208378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208378).length < 2 ^ (prefixWord ++ tailWord_208378).sum := by decide
  have hdescent : baseEnd_208378 < baseStart_208378 := by decide
  rcases family_descends (prefixWord ++ tailWord_208378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208395 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 2, 4, 2]
def baseStart_208395 : Nat := 118140960795 + 208395 * 2 ^ 59
def prefixEnd_208395 : Nat := 4983230072969 + 3 ^ 40 * 208395 * 2
def baseEnd_208395 : Nat := 107006800993817387304115

theorem tailTrace_208395 : CollatzResearch.WordTrace tailWord_208395 prefixEnd_208395 107006800993817387304115 := by
  unfold tailWord_208395
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600790080027980877562639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5067193386685320585041759 7600790080027980877562639)
  ·
    refine ⟨11401185120041971316343959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7600790080027980877562639 11401185120041971316343959)
    ·
      refine ⟨17101777680062956974515939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11401185120041971316343959 17101777680062956974515939)
      ·
        refine ⟨25652666520094435461773909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17101777680062956974515939 25652666520094435461773909)
        ·
          refine ⟨300617185782356665567663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 25652666520094435461773909 300617185782356665567663)
          ·
            refine ⟨450925778673534998351495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300617185782356665567663 450925778673534998351495)
            ·
              refine ⟨676388668010302497527243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450925778673534998351495 676388668010302497527243)
              ·
                refine ⟨1014583002015453746290865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676388668010302497527243 1014583002015453746290865)
                ·
                  refine ⟨760937251511590309718149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1014583002015453746290865 760937251511590309718149)
                  ·
                    refine ⟨142675734658423183072153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760937251511590309718149 142675734658423183072153)
                    ·
                      refine ⟨107006800993817387304115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142675734658423183072153 107006800993817387304115)
                      ·
                        rfl

theorem cell23_208395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4, 2].length) (baseStart_208395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208395 prefixEnd_208395 := by exact prefixLift 208395
  have htrace : WordTrace (prefixWord ++ tailWord_208395) baseStart_208395 baseEnd_208395 := by
    simpa [prefixWord, tailWord_208395, baseEnd_208395] using wordTrace_append hprefix tailTrace_208395
  have hstable : (prefixWord ++ tailWord_208395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208395).length < 2 ^ (prefixWord ++ tailWord_208395).sum := by decide
  have hdescent : baseEnd_208395 < baseStart_208395 := by decide
  rcases family_descends (prefixWord ++ tailWord_208395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208401 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 6]
def baseStart_208401 : Nat := 118140960795 + 208401 * 2 ^ 59
def prefixEnd_208401 : Nat := 4983230072969 + 3 ^ 40 * 208401 * 2
def baseEnd_208401 : Nat := 11889986875304929314343

theorem tailTrace_208401 : CollatzResearch.WordTrace tailWord_208401 prefixEnd_208401 11889986875304929314343 := by
  unfold tailWord_208401
  simp only [CollatzResearch.WordTrace]
  refine ⟨7601008918006243902281057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5067339278670829268187371 7601008918006243902281057)
  ·
    refine ⟨5700756688504682926710793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7601008918006243902281057 5700756688504682926710793)
    ·
      refine ⟨4275567516378512195033095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700756688504682926710793 4275567516378512195033095)
      ·
        refine ⟨6413351274567768292549643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275567516378512195033095 6413351274567768292549643)
        ·
          refine ⟨9620026911851652438824465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413351274567768292549643 9620026911851652438824465)
          ·
            refine ⟨7215020183888739329118349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9620026911851652438824465 7215020183888739329118349)
            ·
              refine ⟨2705632568958277248419381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7215020183888739329118349 2705632568958277248419381)
              ·
                refine ⟨253653053339838492039317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2705632568958277248419381 253653053339838492039317)
                ·
                  refine ⟨11889986875304929314343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 253653053339838492039317 11889986875304929314343)
                  ·
                    rfl

theorem cell23_208401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 6].length) (baseStart_208401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208401 prefixEnd_208401 := by exact prefixLift 208401
  have htrace : WordTrace (prefixWord ++ tailWord_208401) baseStart_208401 baseEnd_208401 := by
    simpa [prefixWord, tailWord_208401, baseEnd_208401] using wordTrace_append hprefix tailTrace_208401
  have hstable : (prefixWord ++ tailWord_208401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208401).length < 2 ^ (prefixWord ++ tailWord_208401).sum := by decide
  have hdescent : baseEnd_208401 < baseStart_208401 := by decide
  rcases family_descends (prefixWord ++ tailWord_208401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208485 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_208485 : Nat := 118140960795 + 208485 * 2 ^ 59
def prefixEnd_208485 : Nat := 4983230072969 + 3 ^ 40 * 208485 * 2
def baseEnd_208485 : Nat := 107053014252722035178701

theorem tailTrace_208485 : CollatzResearch.WordTrace tailWord_208485 prefixEnd_208485 107053014252722035178701 := by
  unfold tailWord_208485
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604072649701926248338909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5069381766467950832225939 7604072649701926248338909)
  ·
    refine ⟨2851527243638222343127091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7604072649701926248338909 2851527243638222343127091)
    ·
      refine ⟨4277290865457333514690637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851527243638222343127091 4277290865457333514690637)
      ·
        refine ⟨1603984074546500068008989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4277290865457333514690637 1603984074546500068008989)
        ·
          refine ⟨601494027954937525503371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1603984074546500068008989 601494027954937525503371)
          ·
            refine ⟨902241041932406288255057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601494027954937525503371 902241041932406288255057)
            ·
              refine ⟨676680781449304716191293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902241041932406288255057 676680781449304716191293)
              ·
                refine ⟨253755293043489268571735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676680781449304716191293 253755293043489268571735)
                ·
                  refine ⟨380632939565233902857603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253755293043489268571735 380632939565233902857603)
                  ·
                    refine ⟨570949409347850854286405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 380632939565233902857603 570949409347850854286405)
                    ·
                      refine ⟨107053014252722035178701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 570949409347850854286405 107053014252722035178701)
                      ·
                        rfl

theorem cell23_208485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_208485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208485 prefixEnd_208485 := by exact prefixLift 208485
  have htrace : WordTrace (prefixWord ++ tailWord_208485) baseStart_208485 baseEnd_208485 := by
    simpa [prefixWord, tailWord_208485, baseEnd_208485] using wordTrace_append hprefix tailTrace_208485
  have hstable : (prefixWord ++ tailWord_208485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208485).length < 2 ^ (prefixWord ++ tailWord_208485).sum := by decide
  have hdescent : baseEnd_208485 < baseStart_208485 := by decide
  rcases family_descends (prefixWord ++ tailWord_208485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208498 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_208498 : Nat := 118140960795 + 208498 * 2 ^ 59
def prefixEnd_208498 : Nat := 4983230072969 + 3 ^ 40 * 208498 * 2
def baseEnd_208498 : Nat := 107059689501230484316141

theorem tailTrace_208498 : CollatzResearch.WordTrace tailWord_208498 prefixEnd_208498 107059689501230484316141 := by
  unfold tailWord_208498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901136699663707367140537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5069697865769886312374765 1901136699663707367140537)
  ·
    refine ⟨1425852524747780525355403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1901136699663707367140537 1425852524747780525355403)
    ·
      refine ⟨2138778787121670788033105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1425852524747780525355403 2138778787121670788033105)
      ·
        refine ⟨1604084090341253091024829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138778787121670788033105 1604084090341253091024829)
        ·
          refine ⟨601531533877969909134311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1604084090341253091024829 601531533877969909134311)
          ·
            refine ⟨902297300816954863701467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601531533877969909134311 902297300816954863701467)
            ·
              refine ⟨1353445951225432295552201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902297300816954863701467 1353445951225432295552201)
              ·
                refine ⟨1015084463419074221664151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353445951225432295552201 1015084463419074221664151)
                ·
                  refine ⟨1522626695128611332496227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015084463419074221664151 1522626695128611332496227)
                  ·
                    refine ⟨2283940042692916998744341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1522626695128611332496227 2283940042692916998744341)
                    ·
                      refine ⟨107059689501230484316141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2283940042692916998744341 107059689501230484316141)
                      ·
                        rfl

theorem cell23_208498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_208498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208498 prefixEnd_208498 := by exact prefixLift 208498
  have htrace : WordTrace (prefixWord ++ tailWord_208498) baseStart_208498 baseEnd_208498 := by
    simpa [prefixWord, tailWord_208498, baseEnd_208498] using wordTrace_append hprefix tailTrace_208498
  have hstable : (prefixWord ++ tailWord_208498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208498).length < 2 ^ (prefixWord ++ tailWord_208498).sum := by decide
  have hdescent : baseEnd_208498 < baseStart_208498 := by decide
  rcases family_descends (prefixWord ++ tailWord_208498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208522 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_208522 : Nat := 118140960795 + 208522 * 2 ^ 59
def prefixEnd_208522 : Nat := 4983230072969 + 3 ^ 40 * 208522 * 2
def baseEnd_208522 : Nat := 107072013036938390416031

theorem tailTrace_208522 : CollatzResearch.WordTrace tailWord_208522 prefixEnd_208522 107072013036938390416031 := by
  unfold tailWord_208522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901355537641970391858955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5070281433711921044957213 1901355537641970391858955)
  ·
    refine ⟨2852033306462955587788433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901355537641970391858955 2852033306462955587788433)
    ·
      refine ⟨2139024979847216690841325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2852033306462955587788433 2139024979847216690841325)
      ·
        refine ⟨802134367442706259065497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2139024979847216690841325 802134367442706259065497)
        ·
          refine ⟨601600775582029694299123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802134367442706259065497 601600775582029694299123)
          ·
            refine ⟨902401163373044541448685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601600775582029694299123 902401163373044541448685)
            ·
              refine ⟨338400436264891703043257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 902401163373044541448685 338400436264891703043257)
              ·
                refine ⟨253800327198668777282443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338400436264891703043257 253800327198668777282443)
                ·
                  refine ⟨380700490798003165923665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253800327198668777282443 380700490798003165923665)
                  ·
                    refine ⟨285525368098502374442749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 380700490798003165923665 285525368098502374442749)
                    ·
                      refine ⟨107072013036938390416031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 285525368098502374442749 107072013036938390416031)
                      ·
                        rfl

theorem cell23_208522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_208522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208522 prefixEnd_208522 := by exact prefixLift 208522
  have htrace : WordTrace (prefixWord ++ tailWord_208522) baseStart_208522 baseEnd_208522 := by
    simpa [prefixWord, tailWord_208522, baseEnd_208522] using wordTrace_append hprefix tailTrace_208522
  have hstable : (prefixWord ++ tailWord_208522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208522).length < 2 ^ (prefixWord ++ tailWord_208522).sum := by decide
  have hdescent : baseEnd_208522 < baseStart_208522 := by decide
  rcases family_descends (prefixWord ++ tailWord_208522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208532 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_208532 : Nat := 118140960795 + 208532 * 2 ^ 59
def prefixEnd_208532 : Nat := 4983230072969 + 3 ^ 40 * 208532 * 2
def baseEnd_208532 : Nat := 107077147843483351290985

theorem tailTrace_208532 : CollatzResearch.WordTrace tailWord_208532 prefixEnd_208532 107077147843483351290985 := by
  unfold tailWord_208532
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802893440265826637649925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5070524587021102183533233 3802893440265826637649925)
  ·
    refine ⟨713042520049842494559361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3802893440265826637649925 713042520049842494559361)
    ·
      refine ⟨534781890037381870919521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 713042520049842494559361 534781890037381870919521)
      ·
        refine ⟨401086417528036403189641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534781890037381870919521 401086417528036403189641)
        ·
          refine ⟨300814813146027302392231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401086417528036403189641 300814813146027302392231)
          ·
            refine ⟨451222219719040953588347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300814813146027302392231 451222219719040953588347)
            ·
              refine ⟨676833329578561430382521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451222219719040953588347 676833329578561430382521)
              ·
                refine ⟨507624997183921072786891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676833329578561430382521 507624997183921072786891)
                ·
                  refine ⟨761437495775881609180337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507624997183921072786891 761437495775881609180337)
                  ·
                    refine ⟨571078121831911206885253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761437495775881609180337 571078121831911206885253)
                    ·
                      refine ⟨107077147843483351290985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 571078121831911206885253 107077147843483351290985)
                      ·
                        rfl

theorem cell23_208532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_208532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208532 prefixEnd_208532 := by exact prefixLift 208532
  have htrace : WordTrace (prefixWord ++ tailWord_208532) baseStart_208532 baseEnd_208532 := by
    simpa [prefixWord, tailWord_208532, baseEnd_208532] using wordTrace_append hprefix tailTrace_208532
  have hstable : (prefixWord ++ tailWord_208532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208532).length < 2 ^ (prefixWord ++ tailWord_208532).sum := by decide
  have hdescent : baseEnd_208532 < baseStart_208532 := by decide
  rcases family_descends (prefixWord ++ tailWord_208532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208535 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_208535 : Nat := 118140960795 + 208535 * 2 ^ 59
def prefixEnd_208535 : Nat := 4983230072969 + 3 ^ 40 * 208535 * 2
def baseEnd_208535 : Nat := 107078688285446839553471

theorem tailTrace_208535 : CollatzResearch.WordTrace tailWord_208535 prefixEnd_208535 107078688285446839553471 := by
  unfold tailWord_208535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605896299520784787659059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5070597533013856525106039 7605896299520784787659059)
  ·
    refine ⟨11408844449281177181488589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7605896299520784787659059 11408844449281177181488589)
    ·
      refine ⟨4278316668480441443058221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11408844449281177181488589 4278316668480441443058221)
      ·
        refine ⟨1604368750680165541146833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4278316668480441443058221 1604368750680165541146833)
        ·
          refine ⟨1203276563010124155860125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604368750680165541146833 1203276563010124155860125)
          ·
            refine ⟨451228711128796558447547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1203276563010124155860125 451228711128796558447547)
            ·
              refine ⟨676843066693194837671321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451228711128796558447547 676843066693194837671321)
              ·
                refine ⟨507632300019896128253491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676843066693194837671321 507632300019896128253491)
                ·
                  refine ⟨761448450029844192380237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507632300019896128253491 761448450029844192380237)
                  ·
                    refine ⟨285543168761191572142589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761448450029844192380237 285543168761191572142589)
                    ·
                      refine ⟨107078688285446839553471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 285543168761191572142589 107078688285446839553471)
                      ·
                        rfl

theorem cell23_208535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_208535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208535 prefixEnd_208535 := by exact prefixLift 208535
  have htrace : WordTrace (prefixWord ++ tailWord_208535) baseStart_208535 baseEnd_208535 := by
    simpa [prefixWord, tailWord_208535, baseEnd_208535] using wordTrace_append hprefix tailTrace_208535
  have hstable : (prefixWord ++ tailWord_208535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208535).length < 2 ^ (prefixWord ++ tailWord_208535).sum := by decide
  have hdescent : baseEnd_208535 < baseStart_208535 := by decide
  rcases family_descends (prefixWord ++ tailWord_208535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208596 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_208596 : Nat := 118140960795 + 208596 * 2 ^ 59
def prefixEnd_208596 : Nat := 4983230072969 + 3 ^ 40 * 208596 * 2
def baseEnd_208596 : Nat := 107110010605371100890691

theorem tailTrace_208596 : CollatzResearch.WordTrace tailWord_208596 prefixEnd_208596 107110010605371100890691 := by
  unfold tailWord_208596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804060576149896102814821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5072080768199861470419761 3804060576149896102814821)
  ·
    refine ⟨713261358028105519277779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3804060576149896102814821 713261358028105519277779)
    ·
      refine ⟨1069892037042158278916669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 713261358028105519277779 1069892037042158278916669)
      ·
        refine ⟨401209513890809354593751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1069892037042158278916669 401209513890809354593751)
        ·
          refine ⟨601814270836214031890627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401209513890809354593751 601814270836214031890627)
          ·
            refine ⟨902721406254321047835941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601814270836214031890627 902721406254321047835941)
            ·
              refine ⟨169260263672685196469239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 902721406254321047835941 169260263672685196469239)
              ·
                refine ⟨253890395509027794703859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169260263672685196469239 253890395509027794703859)
                ·
                  refine ⟨380835593263541692055789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253890395509027794703859 380835593263541692055789)
                  ·
                    refine ⟨142813347473828134520921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380835593263541692055789 142813347473828134520921)
                    ·
                      refine ⟨107110010605371100890691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142813347473828134520921 107110010605371100890691)
                      ·
                        rfl

theorem cell23_208596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_208596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208596 prefixEnd_208596 := by exact prefixLift 208596
  have htrace : WordTrace (prefixWord ++ tailWord_208596) baseStart_208596 baseEnd_208596 := by
    simpa [prefixWord, tailWord_208596, baseEnd_208596] using wordTrace_append hprefix tailTrace_208596
  have hstable : (prefixWord ++ tailWord_208596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208596).length < 2 ^ (prefixWord ++ tailWord_208596).sum := by decide
  have hdescent : baseEnd_208596 < baseStart_208596 := by decide
  rcases family_descends (prefixWord ++ tailWord_208596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208609 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_208609 : Nat := 118140960795 + 208609 * 2 ^ 59
def prefixEnd_208609 : Nat := 4983230072969 + 3 ^ 40 * 208609 * 2
def baseEnd_208609 : Nat := 107116685853879550028131

theorem tailTrace_208609 : CollatzResearch.WordTrace tailWord_208609 prefixEnd_208609 107116685853879550028131 := by
  unfold tailWord_208609
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608595301252695425852881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5072396867501796950568587 7608595301252695425852881)
  ·
    refine ⟨5706446475939521569389661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7608595301252695425852881 5706446475939521569389661)
    ·
      refine ⟨2139917428477320588521123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5706446475939521569389661 2139917428477320588521123)
      ·
        refine ⟨3209876142715980882781685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139917428477320588521123 3209876142715980882781685)
        ·
          refine ⟨300925888379623207760783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3209876142715980882781685 300925888379623207760783)
          ·
            refine ⟨451388832569434811641175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300925888379623207760783 451388832569434811641175)
            ·
              refine ⟨677083248854152217461763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451388832569434811641175 677083248854152217461763)
              ·
                refine ⟨1015624873281228326192645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677083248854152217461763 1015624873281228326192645)
                ·
                  refine ⟨190429663740230311161121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015624873281228326192645 190429663740230311161121)
                  ·
                    refine ⟨142822247805172733370841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190429663740230311161121 142822247805172733370841)
                    ·
                      refine ⟨107116685853879550028131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142822247805172733370841 107116685853879550028131)
                      ·
                        rfl

theorem cell23_208609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_208609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208609 prefixEnd_208609 := by exact prefixLift 208609
  have htrace : WordTrace (prefixWord ++ tailWord_208609) baseStart_208609 baseEnd_208609 := by
    simpa [prefixWord, tailWord_208609, baseEnd_208609] using wordTrace_append hprefix tailTrace_208609
  have hstable : (prefixWord ++ tailWord_208609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208609).length < 2 ^ (prefixWord ++ tailWord_208609).sum := by decide
  have hdescent : baseEnd_208609 < baseStart_208609 := by decide
  rcases family_descends (prefixWord ++ tailWord_208609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208625 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_208625 : Nat := 118140960795 + 208625 * 2 ^ 59
def prefixEnd_208625 : Nat := 4983230072969 + 3 ^ 40 * 208625 * 2
def baseEnd_208625 : Nat := 107124901544351487428057

theorem tailTrace_208625 : CollatzResearch.WordTrace tailWord_208625 prefixEnd_208625 107124901544351487428057 := by
  unfold tailWord_208625
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609178869194730158435329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5072785912796486772290219 7609178869194730158435329)
  ·
    refine ⟨5706884151896047618826497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7609178869194730158435329 5706884151896047618826497)
    ·
      refine ⟨4280163113922035714119873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5706884151896047618826497 4280163113922035714119873)
      ·
        refine ⟨3210122335441526785589905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4280163113922035714119873 3210122335441526785589905)
        ·
          refine ⟨2407591751581145089192429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210122335441526785589905 2407591751581145089192429)
          ·
            refine ⟨902846906842929408447161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2407591751581145089192429 902846906842929408447161)
            ·
              refine ⟨677135180132197056335371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902846906842929408447161 677135180132197056335371)
              ·
                refine ⟨1015702770198295584503057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677135180132197056335371 1015702770198295584503057)
                ·
                  refine ⟨761777077648721688377293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1015702770198295584503057 761777077648721688377293)
                  ·
                    refine ⟨285666404118270633141485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761777077648721688377293 285666404118270633141485)
                    ·
                      refine ⟨107124901544351487428057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 285666404118270633141485 107124901544351487428057)
                      ·
                        rfl

theorem cell23_208625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_208625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208625 prefixEnd_208625 := by exact prefixLift 208625
  have htrace : WordTrace (prefixWord ++ tailWord_208625) baseStart_208625 baseEnd_208625 := by
    simpa [prefixWord, tailWord_208625, baseEnd_208625] using wordTrace_append hprefix tailTrace_208625
  have hstable : (prefixWord ++ tailWord_208625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208625).length < 2 ^ (prefixWord ++ tailWord_208625).sum := by decide
  have hdescent : baseEnd_208625 < baseStart_208625 := by decide
  rcases family_descends (prefixWord ++ tailWord_208625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208626 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_208626 : Nat := 118140960795 + 208626 * 2 ^ 59
def prefixEnd_208626 : Nat := 4983230072969 + 3 ^ 40 * 208626 * 2
def baseEnd_208626 : Nat := 107125415025005983515553

theorem tailTrace_208626 : CollatzResearch.WordTrace tailWord_208626 prefixEnd_208626 107125415025005983515553 := by
  unfold tailWord_208626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902303835547776832305433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5072810228127404886147821 1902303835547776832305433)
  ·
    refine ⟨1426727876660832624229075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1902303835547776832305433 1426727876660832624229075)
    ·
      refine ⟨2140091814991248936343613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426727876660832624229075 2140091814991248936343613)
      ·
        refine ⟨802534430621718351128855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2140091814991248936343613 802534430621718351128855)
        ·
          refine ⟨1203801645932577526693283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802534430621718351128855 1203801645932577526693283)
          ·
            refine ⟨1805702468898866290039925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203801645932577526693283 1805702468898866290039925)
            ·
              refine ⟨169284606459268714691243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1805702468898866290039925 169284606459268714691243)
              ·
                refine ⟨253926909688903072036865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169284606459268714691243 253926909688903072036865)
                ·
                  refine ⟨190445182266677304027649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253926909688903072036865 190445182266677304027649)
                  ·
                    refine ⟨142833886700007978020737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190445182266677304027649 142833886700007978020737)
                    ·
                      refine ⟨107125415025005983515553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142833886700007978020737 107125415025005983515553)
                      ·
                        rfl

theorem cell23_208626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_208626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208626 prefixEnd_208626 := by exact prefixLift 208626
  have htrace : WordTrace (prefixWord ++ tailWord_208626) baseStart_208626 baseEnd_208626 := by
    simpa [prefixWord, tailWord_208626, baseEnd_208626] using wordTrace_append hprefix tailTrace_208626
  have hstable : (prefixWord ++ tailWord_208626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208626).length < 2 ^ (prefixWord ++ tailWord_208626).sum := by decide
  have hdescent : baseEnd_208626 < baseStart_208626 := by decide
  rcases family_descends (prefixWord ++ tailWord_208626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208722 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 6]
def baseStart_208722 : Nat := 118140960795 + 208722 * 2 ^ 59
def prefixEnd_208722 : Nat := 4983230072969 + 3 ^ 40 * 208722 * 2
def baseEnd_208722 : Nat := 11908301018648623101679

theorem tailTrace_208722 : CollatzResearch.WordTrace tailWord_208722 prefixEnd_208722 11908301018648623101679 := by
  unfold tailWord_208722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903179187460828931179105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5075144499895543816477613 1903179187460828931179105)
  ·
    refine ⟨1427384390595621698384329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1903179187460828931179105 1427384390595621698384329)
    ·
      refine ⟨1070538292946716273788247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1427384390595621698384329 1070538292946716273788247)
      ·
        refine ⟨1605807439420074410682371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070538292946716273788247 1605807439420074410682371)
        ·
          refine ⟨2408711159130111616023557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605807439420074410682371 2408711159130111616023557)
          ·
            refine ⟨451633342336895928004417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2408711159130111616023557 451633342336895928004417)
            ·
              refine ⟨338725006752671946003313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451633342336895928004417 338725006752671946003313)
              ·
                refine ⟨254043755064503959502485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338725006752671946003313 254043755064503959502485)
                ·
                  refine ⟨11908301018648623101679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 254043755064503959502485 11908301018648623101679)
                  ·
                    rfl

theorem cell23_208722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_208722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208722 prefixEnd_208722 := by exact prefixLift 208722
  have htrace : WordTrace (prefixWord ++ tailWord_208722) baseStart_208722 baseEnd_208722 := by
    simpa [prefixWord, tailWord_208722, baseEnd_208722] using wordTrace_append hprefix tailTrace_208722
  have hstable : (prefixWord ++ tailWord_208722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208722).length < 2 ^ (prefixWord ++ tailWord_208722).sum := by decide
  have hdescent : baseEnd_208722 < baseStart_208722 := by decide
  rcases family_descends (prefixWord ++ tailWord_208722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208735 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 3, 5]
def baseStart_208735 : Nat := 118140960795 + 208735 * 2 ^ 59
def prefixEnd_208735 : Nat := 4983230072969 + 3 ^ 40 * 208735 * 2
def baseEnd_208735 : Nat := 35727128138782019017517

theorem tailTrace_208735 : CollatzResearch.WordTrace tailWord_208735 prefixEnd_208735 35727128138782019017517 := by
  unfold tailWord_208735
  simp only [CollatzResearch.WordTrace]
  refine ⟨7613190898796218944939659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5075460599197479296626439 7613190898796218944939659)
  ·
    refine ⟨11419786348194328417409489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7613190898796218944939659 11419786348194328417409489)
    ·
      refine ⟨8564839761145746313057117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11419786348194328417409489 8564839761145746313057117)
      ·
        refine ⟨3211814910429654867396419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8564839761145746313057117 3211814910429654867396419)
        ·
          refine ⟨4817722365644482301094629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211814910429654867396419 4817722365644482301094629)
          ·
            refine ⟨903322943558340431455243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4817722365644482301094629 903322943558340431455243)
            ·
              refine ⟨1354984415337510647182865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903322943558340431455243 1354984415337510647182865)
              ·
                refine ⟨1016238311503132985387149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354984415337510647182865 1016238311503132985387149)
                ·
                  refine ⟨381089366813674869520181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016238311503132985387149 381089366813674869520181)
                  ·
                    refine ⟨35727128138782019017517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 381089366813674869520181 35727128138782019017517)
                    ·
                      rfl

theorem cell23_208735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_208735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208735 prefixEnd_208735 := by exact prefixLift 208735
  have htrace : WordTrace (prefixWord ++ tailWord_208735) baseStart_208735 baseEnd_208735 := by
    simpa [prefixWord, tailWord_208735, baseEnd_208735] using wordTrace_append hprefix tailTrace_208735
  have hstable : (prefixWord ++ tailWord_208735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208735).length < 2 ^ (prefixWord ++ tailWord_208735).sum := by decide
  have hdescent : baseEnd_208735 < baseStart_208735 := by decide
  rcases family_descends (prefixWord ++ tailWord_208735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208785 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_208785 : Nat := 118140960795 + 208785 * 2 ^ 59
def prefixEnd_208785 : Nat := 4983230072969 + 3 ^ 40 * 208785 * 2
def baseEnd_208785 : Nat := 107207058449070861427321

theorem tailTrace_208785 : CollatzResearch.WordTrace tailWord_208785 prefixEnd_208785 107207058449070861427321 := by
  unfold tailWord_208785
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615014548615077484259809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5076676365743384989506539 7615014548615077484259809)
  ·
    refine ⟨5711260911461308113194857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7615014548615077484259809 5711260911461308113194857)
    ·
      refine ⟨4283445683595981084896143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5711260911461308113194857 4283445683595981084896143)
      ·
        refine ⟨6425168525393971627344215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283445683595981084896143 6425168525393971627344215)
        ·
          refine ⟨9637752788090957441016323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6425168525393971627344215 9637752788090957441016323)
          ·
            refine ⟨14456629182136436161524485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9637752788090957441016323 14456629182136436161524485)
            ·
              refine ⟨2710617971650581780285841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14456629182136436161524485 2710617971650581780285841)
              ·
                refine ⟨2032963478737936335214381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710617971650581780285841 2032963478737936335214381)
                ·
                  refine ⟨762361304526726125705393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2032963478737936335214381 762361304526726125705393)
                  ·
                    refine ⟨571770978395044594279045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 762361304526726125705393 571770978395044594279045)
                    ·
                      refine ⟨107207058449070861427321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 571770978395044594279045 107207058449070861427321)
                      ·
                        rfl

theorem cell23_208785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_208785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208785 prefixEnd_208785 := by exact prefixLift 208785
  have htrace : WordTrace (prefixWord ++ tailWord_208785) baseStart_208785 baseEnd_208785 := by
    simpa [prefixWord, tailWord_208785, baseEnd_208785] using wordTrace_append hprefix tailTrace_208785
  have hstable : (prefixWord ++ tailWord_208785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208785).length < 2 ^ (prefixWord ++ tailWord_208785).sum := by decide
  have hdescent : baseEnd_208785 < baseStart_208785 := by decide
  rcases family_descends (prefixWord ++ tailWord_208785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208799 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 1, 6]
def baseStart_208799 : Nat := 118140960795 + 208799 * 2 ^ 59
def prefixEnd_208799 : Nat := 4983230072969 + 3 ^ 40 * 208799 * 2
def baseEnd_208799 : Nat := 35738082392744602217419

theorem tailTrace_208799 : CollatzResearch.WordTrace tailWord_208799 prefixEnd_208799 35738082392744602217419 := by
  unfold tailWord_208799
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615525170564357875269451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5077016780376238583512967 7615525170564357875269451)
  ·
    refine ⟨11423287755846536812904177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7615525170564357875269451 11423287755846536812904177)
    ·
      refine ⟨8567465816884902609678133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11423287755846536812904177 8567465816884902609678133)
      ·
        refine ⟨803199920332959619657325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8567465816884902609678133 803199920332959619657325)
        ·
          refine ⟨301199970124859857371497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803199920332959619657325 301199970124859857371497)
          ·
            refine ⟨225899977593644893028623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301199970124859857371497 225899977593644893028623)
            ·
              refine ⟨338849966390467339542935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225899977593644893028623 338849966390467339542935)
              ·
                refine ⟨508274949585701009314403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338849966390467339542935 508274949585701009314403)
                ·
                  refine ⟨762412424378551513971605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508274949585701009314403 762412424378551513971605)
                  ·
                    refine ⟨35738082392744602217419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 762412424378551513971605 35738082392744602217419)
                    ·
                      rfl

theorem cell23_208799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 6].length) (baseStart_208799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208799 prefixEnd_208799 := by exact prefixLift 208799
  have htrace : WordTrace (prefixWord ++ tailWord_208799) baseStart_208799 baseEnd_208799 := by
    simpa [prefixWord, tailWord_208799, baseEnd_208799] using wordTrace_append hprefix tailTrace_208799
  have hstable : (prefixWord ++ tailWord_208799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208799).length < 2 ^ (prefixWord ++ tailWord_208799).sum := by decide
  have hdescent : baseEnd_208799 < baseStart_208799 := by decide
  rcases family_descends (prefixWord ++ tailWord_208799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208839 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_208839 : Nat := 118140960795 + 208839 * 2 ^ 59
def prefixEnd_208839 : Nat := 4983230072969 + 3 ^ 40 * 208839 * 2
def baseEnd_208839 : Nat := 107234786404413650152073

theorem tailTrace_208839 : CollatzResearch.WordTrace tailWord_208839 prefixEnd_208839 107234786404413650152073 := by
  unfold tailWord_208839
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616984090419444706725571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5077989393612963137817047 7616984090419444706725571)
  ·
    refine ⟨11425476135629167060088357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7616984090419444706725571 11425476135629167060088357)
    ·
      refine ⟨2142276775430468823766567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11425476135629167060088357 2142276775430468823766567)
      ·
        refine ⟨3213415163145703235649851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142276775430468823766567 3213415163145703235649851)
        ·
          refine ⟨4820122744718554853474777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213415163145703235649851 4820122744718554853474777)
          ·
            refine ⟨3615092058538916140106083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4820122744718554853474777 3615092058538916140106083)
            ·
              refine ⟨5422638087808374210159125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615092058538916140106083 5422638087808374210159125)
              ·
                refine ⟨254186160366017541101209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5422638087808374210159125 254186160366017541101209)
                ·
                  refine ⟨190639620274513155825907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254186160366017541101209 190639620274513155825907)
                  ·
                    refine ⟨285959430411769733738861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190639620274513155825907 285959430411769733738861)
                    ·
                      refine ⟨107234786404413650152073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 285959430411769733738861 107234786404413650152073)
                      ·
                        rfl

theorem cell23_208839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_208839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208839 prefixEnd_208839 := by exact prefixLift 208839
  have htrace : WordTrace (prefixWord ++ tailWord_208839) baseStart_208839 baseEnd_208839 := by
    simpa [prefixWord, tailWord_208839, baseEnd_208839] using wordTrace_append hprefix tailTrace_208839
  have hstable : (prefixWord ++ tailWord_208839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208839).length < 2 ^ (prefixWord ++ tailWord_208839).sum := by decide
  have hdescent : baseEnd_208839 < baseStart_208839 := by decide
  rcases family_descends (prefixWord ++ tailWord_208839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208840 : List Nat := [2, 1, 3, 1, 4, 2, 3, 2, 1, 2, 2]
def baseStart_208840 : Nat := 118140960795 + 208840 * 2 ^ 59
def prefixEnd_208840 : Nat := 4983230072969 + 3 ^ 40 * 208840 * 2
def baseEnd_208840 : Nat := 107235299885068146239569

theorem tailTrace_208840 : CollatzResearch.WordTrace tailWord_208840 prefixEnd_208840 107235299885068146239569 := by
  unfold tailWord_208840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808510281707910938755987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5078013708943881251674649 3808510281707910938755987)
  ·
    refine ⟨5712765422561866408133981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3808510281707910938755987 5712765422561866408133981)
    ·
      refine ⟨2142287033460699903050243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5712765422561866408133981 2142287033460699903050243)
      ·
        refine ⟨3213430550191049854575365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142287033460699903050243 3213430550191049854575365)
        ·
          refine ⟨602518228160821847732881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3213430550191049854575365 602518228160821847732881)
          ·
            refine ⟨451888671120616385799661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602518228160821847732881 451888671120616385799661)
            ·
              refine ⟨169458251670231144674873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 451888671120616385799661 169458251670231144674873)
              ·
                refine ⟨127093688752673358506155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169458251670231144674873 127093688752673358506155)
                ·
                  refine ⟨190640533129010037759233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127093688752673358506155 190640533129010037759233)
                  ·
                    refine ⟨142980399846757528319425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190640533129010037759233 142980399846757528319425)
                    ·
                      refine ⟨107235299885068146239569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 142980399846757528319425 107235299885068146239569)
                      ·
                        rfl

theorem cell23_208840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_208840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208840 prefixEnd_208840 := by exact prefixLift 208840
  have htrace : WordTrace (prefixWord ++ tailWord_208840) baseStart_208840 baseEnd_208840 := by
    simpa [prefixWord, tailWord_208840, baseEnd_208840] using wordTrace_append hprefix tailTrace_208840
  have hstable : (prefixWord ++ tailWord_208840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208840).length < 2 ^ (prefixWord ++ tailWord_208840).sum := by decide
  have hdescent : baseEnd_208840 < baseStart_208840 := by decide
  rcases family_descends (prefixWord ++ tailWord_208840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208850 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_208850 : Nat := 118140960795 + 208850 * 2 ^ 59
def prefixEnd_208850 : Nat := 4983230072969 + 3 ^ 40 * 208850 * 2
def baseEnd_208850 : Nat := 35746811563871035704841

theorem tailTrace_208850 : CollatzResearch.WordTrace tailWord_208850 prefixEnd_208850 35746811563871035704841 := by
  unfold tailWord_208850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904346323344898396344001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5078256862253062390250669 1904346323344898396344001)
  ·
    refine ⟨1428259742508673797258001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1904346323344898396344001 1428259742508673797258001)
    ·
      refine ⟨1071194806881505347943501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1428259742508673797258001 1071194806881505347943501)
      ·
        refine ⟨401698052580564505478813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1071194806881505347943501 401698052580564505478813)
        ·
          refine ⟨150636769717711689554555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401698052580564505478813 150636769717711689554555)
          ·
            refine ⟨225955154576567534331833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150636769717711689554555 225955154576567534331833)
            ·
              refine ⟨169466365932425650748875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225955154576567534331833 169466365932425650748875)
              ·
                refine ⟨254199548898638476123313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169466365932425650748875 254199548898638476123313)
                ·
                  refine ⟨190649661673978857092485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254199548898638476123313 190649661673978857092485)
                  ·
                    refine ⟨35746811563871035704841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190649661673978857092485 35746811563871035704841)
                    ·
                      rfl

theorem cell23_208850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_208850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208850 prefixEnd_208850 := by exact prefixLift 208850
  have htrace : WordTrace (prefixWord ++ tailWord_208850) baseStart_208850 baseEnd_208850 := by
    simpa [prefixWord, tailWord_208850, baseEnd_208850] using wordTrace_append hprefix tailTrace_208850
  have hstable : (prefixWord ++ tailWord_208850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208850).length < 2 ^ (prefixWord ++ tailWord_208850).sum := by decide
  have hdescent : baseEnd_208850 < baseStart_208850 := by decide
  rcases family_descends (prefixWord ++ tailWord_208850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208855 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 1, 8]
def baseStart_208855 : Nat := 118140960795 + 208855 * 2 ^ 59
def prefixEnd_208855 : Nat := 4983230072969 + 3 ^ 40 * 208855 * 2
def baseEnd_208855 : Nat := 35747667364961862517333

theorem tailTrace_208855 : CollatzResearch.WordTrace tailWord_208855 prefixEnd_208855 35747667364961862517333 := by
  unfold tailWord_208855
  simp only [CollatzResearch.WordTrace]
  refine ⟨7617567658361479439308019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5078378438907652959538679 7617567658361479439308019)
  ·
    refine ⟨11426351487542219158962029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7617567658361479439308019 11426351487542219158962029)
    ·
      refine ⟨4284881807828332184610761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11426351487542219158962029 4284881807828332184610761)
      ·
        refine ⟨3213661355871249138458071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4284881807828332184610761 3213661355871249138458071)
        ·
          refine ⟨4820492033806873707687107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213661355871249138458071 4820492033806873707687107)
          ·
            refine ⟨7230738050710310561530661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820492033806873707687107 7230738050710310561530661)
            ·
              refine ⟨1355763384508183230286999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7230738050710310561530661 1355763384508183230286999)
              ·
                refine ⟨2033645076762274845430499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355763384508183230286999 2033645076762274845430499)
                ·
                  refine ⟨3050467615143412268145749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033645076762274845430499 3050467615143412268145749)
                  ·
                    refine ⟨35747667364961862517333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3050467615143412268145749 35747667364961862517333)
                    ·
                      rfl

theorem cell23_208855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_208855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208855 prefixEnd_208855 := by exact prefixLift 208855
  have htrace : WordTrace (prefixWord ++ tailWord_208855) baseStart_208855 baseEnd_208855 := by
    simpa [prefixWord, tailWord_208855, baseEnd_208855] using wordTrace_append hprefix tailTrace_208855
  have hstable : (prefixWord ++ tailWord_208855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208855).length < 2 ^ (prefixWord ++ tailWord_208855).sum := by decide
  have hdescent : baseEnd_208855 < baseStart_208855 := by decide
  rcases family_descends (prefixWord ++ tailWord_208855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208879 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 1, 4, 2]
def baseStart_208879 : Nat := 118140960795 + 208879 * 2 ^ 59
def prefixEnd_208879 : Nat := 4983230072969 + 3 ^ 40 * 208879 * 2
def baseEnd_208879 : Nat := 107255325630593493651889

theorem tailTrace_208879 : CollatzResearch.WordTrace tailWord_208879 prefixEnd_208879 107255325630593493651889 := by
  unfold tailWord_208879
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618443010274531538181691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5078962006849687692121127 7618443010274531538181691)
  ·
    refine ⟨11427664515411797307272537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7618443010274531538181691 11427664515411797307272537)
    ·
      refine ⟨8570748386558847980454403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11427664515411797307272537 8570748386558847980454403)
      ·
        refine ⟨12856122579838271970681605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8570748386558847980454403 12856122579838271970681605)
        ·
          refine ⟨2410522983719675994502801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12856122579838271970681605 2410522983719675994502801)
          ·
            refine ⟨1807892237789756995877101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410522983719675994502801 1807892237789756995877101)
            ·
              refine ⟨677959589171158873453913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1807892237789756995877101 677959589171158873453913)
              ·
                refine ⟨508469691878369155090435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677959589171158873453913 508469691878369155090435)
                ·
                  refine ⟨762704537817553732635653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508469691878369155090435 762704537817553732635653)
                  ·
                    refine ⟨143007100840791324869185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762704537817553732635653 143007100840791324869185)
                    ·
                      refine ⟨107255325630593493651889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143007100840791324869185 107255325630593493651889)
                      ·
                        rfl

theorem cell23_208879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4, 2].length) (baseStart_208879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208879 prefixEnd_208879 := by exact prefixLift 208879
  have htrace : WordTrace (prefixWord ++ tailWord_208879) baseStart_208879 baseEnd_208879 := by
    simpa [prefixWord, tailWord_208879, baseEnd_208879] using wordTrace_append hprefix tailTrace_208879
  have hstable : (prefixWord ++ tailWord_208879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208879).length < 2 ^ (prefixWord ++ tailWord_208879).sum := by decide
  have hdescent : baseEnd_208879 < baseStart_208879 := by decide
  rcases family_descends (prefixWord ++ tailWord_208879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208892 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_208892 : Nat := 118140960795 + 208892 * 2 ^ 59
def prefixEnd_208892 : Nat := 4983230072969 + 3 ^ 40 * 208892 * 2
def baseEnd_208892 : Nat := 107262000879101942789329

theorem tailTrace_208892 : CollatzResearch.WordTrace tailWord_208892 prefixEnd_208892 107262000879101942789329 := by
  unfold tailWord_208892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809458579613717379202465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5079278106151623172269953 3809458579613717379202465)
  ·
    refine ⟨2857093934710288034401849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3809458579613717379202465 2857093934710288034401849)
    ·
      refine ⟨2142820451032716025801387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2857093934710288034401849 2142820451032716025801387)
      ·
        refine ⟨3214230676549074038702081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142820451032716025801387 3214230676549074038702081)
        ·
          refine ⟨2410673007411805529026561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214230676549074038702081 2410673007411805529026561)
          ·
            refine ⟨1808004755558854146769921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410673007411805529026561 1808004755558854146769921)
            ·
              refine ⟨1356003566669140610077441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808004755558854146769921 1356003566669140610077441)
              ·
                refine ⟨1017002675001855457558081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356003566669140610077441 1017002675001855457558081)
                ·
                  refine ⟨762752006251391593168561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017002675001855457558081 762752006251391593168561)
                  ·
                    refine ⟨572064004688543694876421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 762752006251391593168561 572064004688543694876421)
                    ·
                      refine ⟨107262000879101942789329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 572064004688543694876421 107262000879101942789329)
                      ·
                        rfl

theorem cell23_208892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_208892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208892 prefixEnd_208892 := by exact prefixLift 208892
  have htrace : WordTrace (prefixWord ++ tailWord_208892) baseStart_208892 baseEnd_208892 := by
    simpa [prefixWord, tailWord_208892, baseEnd_208892] using wordTrace_append hprefix tailTrace_208892
  have hstable : (prefixWord ++ tailWord_208892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208892).length < 2 ^ (prefixWord ++ tailWord_208892).sum := by decide
  have hdescent : baseEnd_208892 < baseStart_208892 := by decide
  rcases family_descends (prefixWord ++ tailWord_208892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208895 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_208895 : Nat := 118140960795 + 208895 * 2 ^ 59
def prefixEnd_208895 : Nat := 4983230072969 + 3 ^ 40 * 208895 * 2
def baseEnd_208895 : Nat := 107263541321065431051815

theorem tailTrace_208895 : CollatzResearch.WordTrace tailWord_208895 prefixEnd_208895 107263541321065431051815 := by
  unfold tailWord_208895
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619026578216566270764139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5079351052144377513842759 7619026578216566270764139)
  ·
    refine ⟨11428539867324849406146209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619026578216566270764139 11428539867324849406146209)
    ·
      refine ⟨8571404900493637054609657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11428539867324849406146209 8571404900493637054609657)
      ·
        refine ⟨6428553675370227790957243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8571404900493637054609657 6428553675370227790957243)
        ·
          refine ⟨9642830513055341686435865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6428553675370227790957243 9642830513055341686435865)
          ·
            refine ⟨7232122884791506264826899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9642830513055341686435865 7232122884791506264826899)
            ·
              refine ⟨10848184327187259397240349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7232122884791506264826899 10848184327187259397240349)
              ·
                refine ⟨4068069122695222273965131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10848184327187259397240349 4068069122695222273965131)
                ·
                  refine ⟨6102103684042833410947697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068069122695222273965131 6102103684042833410947697)
                  ·
                    refine ⟨4576577763032125058210773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6102103684042833410947697 4576577763032125058210773)
                    ·
                      refine ⟨107263541321065431051815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4576577763032125058210773 107263541321065431051815)
                      ·
                        rfl

theorem cell23_208895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_208895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208895 prefixEnd_208895 := by exact prefixLift 208895
  have htrace : WordTrace (prefixWord ++ tailWord_208895) baseStart_208895 baseEnd_208895 := by
    simpa [prefixWord, tailWord_208895, baseEnd_208895] using wordTrace_append hprefix tailTrace_208895
  have hstable : (prefixWord ++ tailWord_208895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208895).length < 2 ^ (prefixWord ++ tailWord_208895).sum := by decide
  have hdescent : baseEnd_208895 < baseStart_208895 := by decide
  rcases family_descends (prefixWord ++ tailWord_208895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208905 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_208905 : Nat := 118140960795 + 208905 * 2 ^ 59
def prefixEnd_208905 : Nat := 4983230072969 + 3 ^ 40 * 208905 * 2
def baseEnd_208905 : Nat := 107268676127610391926769

theorem tailTrace_208905 : CollatzResearch.WordTrace tailWord_208905 prefixEnd_208905 107268676127610391926769 := by
  unfold tailWord_208905
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619391308180337978628169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5079594205453558652418779 7619391308180337978628169)
  ·
    refine ⟨5714543481135253483971127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7619391308180337978628169 5714543481135253483971127)
    ·
      refine ⟨8571815221702880225956691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5714543481135253483971127 8571815221702880225956691)
      ·
        refine ⟨12857722832554320338935037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8571815221702880225956691 12857722832554320338935037)
        ·
          refine ⟨4821646062207870127100639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12857722832554320338935037 4821646062207870127100639)
          ·
            refine ⟨7232469093311805190650959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821646062207870127100639 7232469093311805190650959)
            ·
              refine ⟨10848703639967707785976439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7232469093311805190650959 10848703639967707785976439)
              ·
                refine ⟨16273055459951561678964659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10848703639967707785976439 16273055459951561678964659)
                ·
                  refine ⟨24409583189927342518446989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16273055459951561678964659 24409583189927342518446989)
                  ·
                    refine ⟨9153593696222753444417621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24409583189927342518446989 9153593696222753444417621)
                    ·
                      refine ⟨107268676127610391926769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 9153593696222753444417621 107268676127610391926769)
                      ·
                        rfl

theorem cell23_208905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_208905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208905 prefixEnd_208905 := by exact prefixLift 208905
  have htrace : WordTrace (prefixWord ++ tailWord_208905) baseStart_208905 baseEnd_208905 := by
    simpa [prefixWord, tailWord_208905, baseEnd_208905] using wordTrace_append hprefix tailTrace_208905
  have hstable : (prefixWord ++ tailWord_208905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208905).length < 2 ^ (prefixWord ++ tailWord_208905).sum := by decide
  have hdescent : baseEnd_208905 < baseStart_208905 := by decide
  rcases family_descends (prefixWord ++ tailWord_208905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208912 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3]
def baseStart_208912 : Nat := 118140960795 + 208912 * 2 ^ 59
def prefixEnd_208912 : Nat := 4983230072969 + 3 ^ 40 * 208912 * 2
def baseEnd_208912 : Nat := 107272270492191864539237

theorem tailTrace_208912 : CollatzResearch.WordTrace tailWord_208912 prefixEnd_208912 107272270492191864539237 := by
  unfold tailWord_208912
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809823309577489087066495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5079764412769985449421993 3809823309577489087066495)
  ·
    refine ⟨5714734964366233630599743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3809823309577489087066495 5714734964366233630599743)
    ·
      refine ⟨8572102446549350445899615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5714734964366233630599743 8572102446549350445899615)
      ·
        refine ⟨12858153669824025668849423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572102446549350445899615 12858153669824025668849423)
        ·
          refine ⟨19287230504736038503274135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12858153669824025668849423 19287230504736038503274135)
          ·
            refine ⟨28930845757104057754911203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287230504736038503274135 28930845757104057754911203)
            ·
              refine ⟨43396268635656086632366805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28930845757104057754911203 43396268635656086632366805)
              ·
                refine ⟨1017100046148189530446097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43396268635656086632366805 1017100046148189530446097)
                ·
                  refine ⟨762825034611142147834573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017100046148189530446097 762825034611142147834573)
                  ·
                    refine ⟨286059387979178305437965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762825034611142147834573 286059387979178305437965)
                    ·
                      refine ⟨107272270492191864539237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 286059387979178305437965 107272270492191864539237)
                      ·
                        rfl

theorem cell23_208912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_208912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208912 prefixEnd_208912 := by exact prefixLift 208912
  have htrace : WordTrace (prefixWord ++ tailWord_208912) baseStart_208912 baseEnd_208912 := by
    simpa [prefixWord, tailWord_208912, baseEnd_208912] using wordTrace_append hprefix tailTrace_208912
  have hstable : (prefixWord ++ tailWord_208912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208912).length < 2 ^ (prefixWord ++ tailWord_208912).sum := by decide
  have hdescent : baseEnd_208912 < baseStart_208912 := by decide
  rcases family_descends (prefixWord ++ tailWord_208912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208919 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 7]
def baseStart_208919 : Nat := 118140960795 + 208919 * 2 ^ 59
def prefixEnd_208919 : Nat := 4983230072969 + 3 ^ 40 * 208919 * 2
def baseEnd_208919 : Nat := 11919540539641481905745

theorem tailTrace_208919 : CollatzResearch.WordTrace tailWord_208919 prefixEnd_208919 11919540539641481905745 := by
  unfold tailWord_208919
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619901930129618369637811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5079934620086412246425207 7619901930129618369637811)
  ·
    refine ⟨11429852895194427554456717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619901930129618369637811 11429852895194427554456717)
    ·
      refine ⟨4286194835697910332921269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11429852895194427554456717 4286194835697910332921269)
      ·
        refine ⟨401830765846679093711369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4286194835697910332921269 401830765846679093711369)
        ·
          refine ⟨301373074385009320283527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401830765846679093711369 301373074385009320283527)
          ·
            refine ⟨452059611577513980425291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301373074385009320283527 452059611577513980425291)
            ·
              refine ⟨678089417366270970637937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452059611577513980425291 678089417366270970637937)
              ·
                refine ⟨508567063024703227978453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678089417366270970637937 508567063024703227978453)
                ·
                  refine ⟨11919540539641481905745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 508567063024703227978453 11919540539641481905745)
                  ·
                    rfl

theorem cell23_208919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 7].length) (baseStart_208919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208919 prefixEnd_208919 := by exact prefixLift 208919
  have htrace : WordTrace (prefixWord ++ tailWord_208919) baseStart_208919 baseEnd_208919 := by
    simpa [prefixWord, tailWord_208919, baseEnd_208919] using wordTrace_append hprefix tailTrace_208919
  have hstable : (prefixWord ++ tailWord_208919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208919).length < 2 ^ (prefixWord ++ tailWord_208919).sum := by decide
  have hdescent : baseEnd_208919 < baseStart_208919 := by decide
  rcases family_descends (prefixWord ++ tailWord_208919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208969 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 2, 4, 2]
def baseStart_208969 : Nat := 118140960795 + 208969 * 2 ^ 59
def prefixEnd_208969 : Nat := 4983230072969 + 3 ^ 40 * 208969 * 2
def baseEnd_208969 : Nat := 107301538889498141526475

theorem tailTrace_208969 : CollatzResearch.WordTrace tailWord_208969 prefixEnd_208969 107301538889498141526475 := by
  unfold tailWord_208969
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621725579948476908957961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5081150386632317939305307 7621725579948476908957961)
  ·
    refine ⟨5716294184961357681718471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7621725579948476908957961 5716294184961357681718471)
    ·
      refine ⟨8574441277442036522577707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716294184961357681718471 8574441277442036522577707)
      ·
        refine ⟨12861661916163054783866561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8574441277442036522577707 12861661916163054783866561)
        ·
          refine ⟨9646246437122291087899921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12861661916163054783866561 9646246437122291087899921)
          ·
            refine ⟨7234684827841718315924941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9646246437122291087899921 7234684827841718315924941)
            ·
              refine ⟨2713006810440644368471853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7234684827841718315924941 2713006810440644368471853)
              ·
                refine ⟨1017377553915241638176945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2713006810440644368471853 1017377553915241638176945)
                ·
                  refine ⟨763033165436431228632709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017377553915241638176945 763033165436431228632709)
                  ·
                    refine ⟨143068718519330855368633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763033165436431228632709 143068718519330855368633)
                    ·
                      refine ⟨107301538889498141526475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143068718519330855368633 107301538889498141526475)
                      ·
                        rfl

theorem cell23_208969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 4, 2].length) (baseStart_208969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208969 prefixEnd_208969 := by exact prefixLift 208969
  have htrace : WordTrace (prefixWord ++ tailWord_208969) baseStart_208969 baseEnd_208969 := by
    simpa [prefixWord, tailWord_208969, baseEnd_208969] using wordTrace_append hprefix tailTrace_208969
  have hstable : (prefixWord ++ tailWord_208969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208969).length < 2 ^ (prefixWord ++ tailWord_208969).sum := by decide
  have hdescent : baseEnd_208969 < baseStart_208969 := by decide
  rcases family_descends (prefixWord ++ tailWord_208969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_208992 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 8]
def baseStart_208992 : Nat := 118140960795 + 208992 * 2 ^ 59
def prefixEnd_208992 : Nat := 4983230072969 + 3 ^ 40 * 208992 * 2
def baseEnd_208992 : Nat := 11923705438283505726541

theorem tailTrace_208992 : CollatzResearch.WordTrace tailWord_208992 prefixEnd_208992 11923705438283505726541 := by
  unfold tailWord_208992
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811282229432575918522615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5081709639243434558030153 3811282229432575918522615)
  ·
    refine ⟨5716923344148863877783923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3811282229432575918522615 5716923344148863877783923)
    ·
      refine ⟨8575385016223295816675885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716923344148863877783923 8575385016223295816675885)
      ·
        refine ⟨3215769381083735931253457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8575385016223295816675885 3215769381083735931253457)
        ·
          refine ⟨2411827035812801948440093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3215769381083735931253457 2411827035812801948440093)
          ·
            refine ⟨904435138429800730665035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2411827035812801948440093 904435138429800730665035)
            ·
              refine ⟨1356652707644701095997553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904435138429800730665035 1356652707644701095997553)
              ·
                refine ⟨1017489530733525821998165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356652707644701095997553 1017489530733525821998165)
                ·
                  refine ⟨11923705438283505726541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1017489530733525821998165 11923705438283505726541)
                  ·
                    rfl

theorem cell23_208992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_208992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_208992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_208992 prefixEnd_208992 := by exact prefixLift 208992
  have htrace : WordTrace (prefixWord ++ tailWord_208992) baseStart_208992 baseEnd_208992 := by
    simpa [prefixWord, tailWord_208992, baseEnd_208992] using wordTrace_append hprefix tailTrace_208992
  have hstable : (prefixWord ++ tailWord_208992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_208992).length < 2 ^ (prefixWord ++ tailWord_208992).sum := by decide
  have hdescent : baseEnd_208992 < baseStart_208992 := by decide
  rcases family_descends (prefixWord ++ tailWord_208992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209006 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_209006 : Nat := 118140960795 + 209006 * 2 ^ 59
def prefixEnd_209006 : Nat := 4983230072969 + 3 ^ 40 * 209006 * 2
def baseEnd_209006 : Nat := 107320537673714496763805

theorem tailTrace_209006 : CollatzResearch.WordTrace tailWord_209006 prefixEnd_209006 107320537673714496763805 := by
  unfold tailWord_209006
  simp only [CollatzResearch.WordTrace]
  refine ⟨952884385101804028506859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5082050053876288152036581 952884385101804028506859)
  ·
    refine ⟨1429326577652706042760289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 952884385101804028506859 1429326577652706042760289)
    ·
      refine ⟨1071994933239529532070217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1429326577652706042760289 1071994933239529532070217)
      ·
        refine ⟨803996199929647149052663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1071994933239529532070217 803996199929647149052663)
        ·
          refine ⟨1205994299894470723578995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803996199929647149052663 1205994299894470723578995)
          ·
            refine ⟨1808991449841706085368493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205994299894470723578995 1808991449841706085368493)
            ·
              refine ⟨678371793690639782013185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1808991449841706085368493 678371793690639782013185)
              ·
                refine ⟨508778845267979836509889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678371793690639782013185 508778845267979836509889)
                ·
                  refine ⟨381584133950984877382417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508778845267979836509889 381584133950984877382417)
                  ·
                    refine ⟨286188100463238658036813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 381584133950984877382417 286188100463238658036813)
                    ·
                      refine ⟨107320537673714496763805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 286188100463238658036813 107320537673714496763805)
                      ·
                        rfl

theorem cell23_209006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_209006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209006 prefixEnd_209006 := by exact prefixLift 209006
  have htrace : WordTrace (prefixWord ++ tailWord_209006) baseStart_209006 baseEnd_209006 := by
    simpa [prefixWord, tailWord_209006, baseEnd_209006] using wordTrace_append hprefix tailTrace_209006
  have hstable : (prefixWord ++ tailWord_209006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209006).length < 2 ^ (prefixWord ++ tailWord_209006).sum := by decide
  have hdescent : baseEnd_209006 < baseStart_209006 := by decide
  rcases family_descends (prefixWord ++ tailWord_209006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209096 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_209096 : Nat := 118140960795 + 209096 * 2 ^ 59
def prefixEnd_209096 : Nat := 4983230072969 + 3 ^ 40 * 209096 * 2
def baseEnd_209096 : Nat := 107366750932619144638391

theorem tailTrace_209096 : CollatzResearch.WordTrace tailWord_209096 prefixEnd_209096 107366750932619144638391 := by
  unfold tailWord_209096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813178825244188799415571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5084238433658918399220761 3813178825244188799415571)
  ·
    refine ⟨5719768237866283199123357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813178825244188799415571 5719768237866283199123357)
    ·
      refine ⟨2144913089199856199671259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5719768237866283199123357 2144913089199856199671259)
      ·
        refine ⟨3217369633799784299506889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144913089199856199671259 3217369633799784299506889)
        ·
          refine ⟨2413027225349838224630167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217369633799784299506889 2413027225349838224630167)
          ·
            refine ⟨3619540838024757336945251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413027225349838224630167 3619540838024757336945251)
            ·
              refine ⟨5429311257037136005417877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619540838024757336945251 5429311257037136005417877)
              ·
                refine ⟨254498965173615750253963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5429311257037136005417877 254498965173615750253963)
                ·
                  refine ⟨381748447760423625380945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254498965173615750253963 381748447760423625380945)
                  ·
                    refine ⟨286311335820317719035709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 381748447760423625380945 286311335820317719035709)
                    ·
                      refine ⟨107366750932619144638391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 286311335820317719035709 107366750932619144638391)
                      ·
                        rfl

theorem cell23_209096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_209096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209096 prefixEnd_209096 := by exact prefixLift 209096
  have htrace : WordTrace (prefixWord ++ tailWord_209096) baseStart_209096 baseEnd_209096 := by
    simpa [prefixWord, tailWord_209096, baseEnd_209096] using wordTrace_append hprefix tailTrace_209096
  have hstable : (prefixWord ++ tailWord_209096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209096).length < 2 ^ (prefixWord ++ tailWord_209096).sum := by decide
  have hdescent : baseEnd_209096 < baseStart_209096 := by decide
  rcases family_descends (prefixWord ++ tailWord_209096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209099 : List Nat := [1, 1, 1, 1, 3, 2, 7, 7]
def baseStart_209099 : Nat := 118140960795 + 209099 * 2 ^ 59
def prefixEnd_209099 : Nat := 4983230072969 + 3 ^ 40 * 209099 * 2
def baseEnd_209099 : Nat := 3976603384243801218551

theorem tailTrace_209099 : CollatzResearch.WordTrace tailWord_209099 prefixEnd_209099 3976603384243801218551 := by
  unfold tailWord_209099
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626467069477509111190351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5084311379651672740793567 7626467069477509111190351)
  ·
    refine ⟨11439700604216263666785527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7626467069477509111190351 11439700604216263666785527)
    ·
      refine ⟨17159550906324395500178291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11439700604216263666785527 17159550906324395500178291)
      ·
        refine ⟨25739326359486593250267437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17159550906324395500178291 25739326359486593250267437)
        ·
          refine ⟨9652247384807472468850289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25739326359486593250267437 9652247384807472468850289)
          ·
            refine ⟨7239185538605604351637717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9652247384807472468850289 7239185538605604351637717)
            ·
              refine ⟨169668411061068851991509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7239185538605604351637717 169668411061068851991509)
              ·
                refine ⟨3976603384243801218551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 169668411061068851991509 3976603384243801218551)
                ·
                  rfl

theorem cell23_209099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 7].length) (baseStart_209099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209099 prefixEnd_209099 := by exact prefixLift 209099
  have htrace : WordTrace (prefixWord ++ tailWord_209099) baseStart_209099 baseEnd_209099 := by
    simpa [prefixWord, tailWord_209099, baseEnd_209099] using wordTrace_append hprefix tailTrace_209099
  have hstable : (prefixWord ++ tailWord_209099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209099).length < 2 ^ (prefixWord ++ tailWord_209099).sum := by decide
  have hdescent : baseEnd_209099 < baseStart_209099 := by decide
  rcases family_descends (prefixWord ++ tailWord_209099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209106 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_209106 : Nat := 118140960795 + 209106 * 2 ^ 59
def prefixEnd_209106 : Nat := 4983230072969 + 3 ^ 40 * 209106 * 2
def baseEnd_209106 : Nat := 107371885739164105513345

theorem tailTrace_209106 : CollatzResearch.WordTrace tailWord_209106 prefixEnd_209106 107371885739164105513345 := by
  unfold tailWord_209106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906680595113037326673793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5084481586968099537796781 1906680595113037326673793)
  ·
    refine ⟨1430010446334777995005345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1906680595113037326673793 1430010446334777995005345)
    ·
      refine ⟨1072507834751083496254009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430010446334777995005345 1072507834751083496254009)
      ·
        refine ⟨804380876063312622190507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072507834751083496254009 804380876063312622190507)
        ·
          refine ⟨1206571314094968933285761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804380876063312622190507 1206571314094968933285761)
          ·
            refine ⟨904928485571226699964321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206571314094968933285761 904928485571226699964321)
            ·
              refine ⟨678696364178420024973241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904928485571226699964321 678696364178420024973241)
              ·
                refine ⟨509022273133815018729931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678696364178420024973241 509022273133815018729931)
                ·
                  refine ⟨763533409700722528094897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509022273133815018729931 763533409700722528094897)
                  ·
                    refine ⟨572650057275541896071173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 763533409700722528094897 572650057275541896071173)
                    ·
                      refine ⟨107371885739164105513345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 572650057275541896071173 107371885739164105513345)
                      ·
                        rfl

theorem cell23_209106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_209106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209106 prefixEnd_209106 := by exact prefixLift 209106
  have htrace : WordTrace (prefixWord ++ tailWord_209106) baseStart_209106 baseEnd_209106 := by
    simpa [prefixWord, tailWord_209106, baseEnd_209106] using wordTrace_append hprefix tailTrace_209106
  have hstable : (prefixWord ++ tailWord_209106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209106).length < 2 ^ (prefixWord ++ tailWord_209106).sum := by decide
  have hdescent : baseEnd_209106 < baseStart_209106 := by decide
  rcases family_descends (prefixWord ++ tailWord_209106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209110 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_209110 : Nat := 118140960795 + 209110 * 2 ^ 59
def prefixEnd_209110 : Nat := 4983230072969 + 3 ^ 40 * 209110 * 2
def baseEnd_209110 : Nat := 107373939661782089863327

theorem tailTrace_209110 : CollatzResearch.WordTrace tailWord_209110 prefixEnd_209110 107373939661782089863327 := by
  unfold tailWord_209110
  simp only [CollatzResearch.WordTrace]
  refine ⟨476679267027353624365049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5084578848291771993227189 476679267027353624365049)
  ·
    refine ⟨357509450270515218273787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 476679267027353624365049 357509450270515218273787)
    ·
      refine ⟨536264175405772827410681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357509450270515218273787 536264175405772827410681)
      ·
        refine ⟨402198131554329620558011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536264175405772827410681 402198131554329620558011)
        ·
          refine ⟨603297197331494430837017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402198131554329620558011 603297197331494430837017)
          ·
            refine ⟨452472897998620823127763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603297197331494430837017 452472897998620823127763)
            ·
              refine ⟨678709346997931234691645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452472897998620823127763 678709346997931234691645)
              ·
                refine ⟨254516005124224213009367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 678709346997931234691645 254516005124224213009367)
                ·
                  refine ⟨381774007686336319514051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254516005124224213009367 381774007686336319514051)
                  ·
                    refine ⟨572661011529504479271077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 381774007686336319514051 572661011529504479271077)
                    ·
                      refine ⟨107373939661782089863327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 572661011529504479271077 107373939661782089863327)
                      ·
                        rfl

theorem cell23_209110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_209110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209110 prefixEnd_209110 := by exact prefixLift 209110
  have htrace : WordTrace (prefixWord ++ tailWord_209110) baseStart_209110 baseEnd_209110 := by
    simpa [prefixWord, tailWord_209110, baseEnd_209110] using wordTrace_append hprefix tailTrace_209110
  have hstable : (prefixWord ++ tailWord_209110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209110).length < 2 ^ (prefixWord ++ tailWord_209110).sum := by decide
  have hdescent : baseEnd_209110 < baseStart_209110 := by decide
  rcases family_descends (prefixWord ++ tailWord_209110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209113 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 1, 2, 3]
def baseStart_209113 : Nat := 118140960795 + 209113 * 2 ^ 59
def prefixEnd_209113 : Nat := 4983230072969 + 3 ^ 40 * 209113 * 2
def baseEnd_209113 : Nat := 107375480103745578125813

theorem tailTrace_209113 : CollatzResearch.WordTrace tailWord_209113 prefixEnd_209113 107375480103745578125813 := by
  unfold tailWord_209113
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626977691426789502199993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5084651794284526334799995 7626977691426789502199993)
  ·
    refine ⟨5720233268570092126649995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7626977691426789502199993 5720233268570092126649995)
    ·
      refine ⟨8580349902855138189974993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5720233268570092126649995 8580349902855138189974993)
      ·
        refine ⟨6435262427141353642481245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8580349902855138189974993 6435262427141353642481245)
        ·
          refine ⟨2413223410178007615930467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6435262427141353642481245 2413223410178007615930467)
          ·
            refine ⟨3619835115267011423895701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413223410178007615930467 3619835115267011423895701)
            ·
              refine ⟨169679771028141160495111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3619835115267011423895701 169679771028141160495111)
              ·
                refine ⟨254519656542211740742667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169679771028141160495111 254519656542211740742667)
                ·
                  refine ⟨381779484813317611114001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254519656542211740742667 381779484813317611114001)
                  ·
                    refine ⟨286334613609988208335501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 381779484813317611114001 286334613609988208335501)
                    ·
                      refine ⟨107375480103745578125813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 286334613609988208335501 107375480103745578125813)
                      ·
                        rfl

theorem cell23_209113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_209113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209113 prefixEnd_209113 := by exact prefixLift 209113
  have htrace : WordTrace (prefixWord ++ tailWord_209113) baseStart_209113 baseEnd_209113 := by
    simpa [prefixWord, tailWord_209113, baseEnd_209113] using wordTrace_append hprefix tailTrace_209113
  have hstable : (prefixWord ++ tailWord_209113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209113).length < 2 ^ (prefixWord ++ tailWord_209113).sum := by decide
  have hdescent : baseEnd_209113 < baseStart_209113 := by decide
  rcases family_descends (prefixWord ++ tailWord_209113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209127 : List Nat := [1, 1, 5, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_209127 : Nat := 118140960795 + 209127 * 2 ^ 59
def prefixEnd_209127 : Nat := 4983230072969 + 3 ^ 40 * 209127 * 2
def baseEnd_209127 : Nat := 107382668832908523350749

theorem tailTrace_209127 : CollatzResearch.WordTrace tailWord_209127 prefixEnd_209127 107382668832908523350749 := by
  unfold tailWord_209127
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627488313376069893209635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5084992208917379928806423 7627488313376069893209635)
  ·
    refine ⟨11441232470064104839814453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7627488313376069893209635 11441232470064104839814453)
    ·
      refine ⟨1072615544068509828732605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11441232470064104839814453 1072615544068509828732605)
      ·
        refine ⟨402230829025691185774727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1072615544068509828732605 402230829025691185774727)
        ·
          refine ⟨603346243538536778662091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402230829025691185774727 603346243538536778662091)
          ·
            refine ⟨905019365307805167993137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603346243538536778662091 905019365307805167993137)
            ·
              refine ⟨678764523980853875994853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905019365307805167993137 678764523980853875994853)
              ·
                refine ⟨127268348246410101749035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678764523980853875994853 127268348246410101749035)
                ·
                  refine ⟨190902522369615152623553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127268348246410101749035 190902522369615152623553)
                  ·
                    refine ⟨143176891777211364467665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190902522369615152623553 143176891777211364467665)
                    ·
                      refine ⟨107382668832908523350749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143176891777211364467665 107382668832908523350749)
                      ·
                        rfl

theorem cell23_209127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_209127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209127 prefixEnd_209127 := by exact prefixLift 209127
  have htrace : WordTrace (prefixWord ++ tailWord_209127) baseStart_209127 baseEnd_209127 := by
    simpa [prefixWord, tailWord_209127, baseEnd_209127] using wordTrace_append hprefix tailTrace_209127
  have hstable : (prefixWord ++ tailWord_209127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209127).length < 2 ^ (prefixWord ++ tailWord_209127).sum := by decide
  have hdescent : baseEnd_209127 < baseStart_209127 := by decide
  rcases family_descends (prefixWord ++ tailWord_209127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209136 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 5, 3, 2]
def baseStart_209136 : Nat := 118140960795 + 209136 * 2 ^ 59
def prefixEnd_209136 : Nat := 4983230072969 + 3 ^ 40 * 209136 * 2
def baseEnd_209136 : Nat := 107387290158798988138207

theorem tailTrace_209136 : CollatzResearch.WordTrace tailWord_209136 prefixEnd_209136 107387290158798988138207 := by
  unfold tailWord_209136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813908285171732215143631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5085211046895642953524841 3813908285171732215143631)
  ·
    refine ⟨5720862427757598322715447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813908285171732215143631 5720862427757598322715447)
    ·
      refine ⟨8581293641636397484073171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5720862427757598322715447 8581293641636397484073171)
      ·
        refine ⟨12871940462454596226109757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8581293641636397484073171 12871940462454596226109757)
        ·
          refine ⟨4826977673420473584791159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12871940462454596226109757 4826977673420473584791159)
          ·
            refine ⟨7240466510130710377186739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826977673420473584791159 7240466510130710377186739)
            ·
              refine ⟨10860699765196065565780109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240466510130710377186739 10860699765196065565780109)
              ·
                refine ⟨4072762411948524587167541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10860699765196065565780109 4072762411948524587167541)
                ·
                  refine ⟨381821476120174180046957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072762411948524587167541 381821476120174180046957)
                  ·
                    refine ⟨143183053545065317517609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381821476120174180046957 143183053545065317517609)
                    ·
                      refine ⟨107387290158798988138207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143183053545065317517609 107387290158798988138207)
                      ·
                        rfl

theorem cell23_209136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 3, 2].length) (baseStart_209136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209136 prefixEnd_209136 := by exact prefixLift 209136
  have htrace : WordTrace (prefixWord ++ tailWord_209136) baseStart_209136 baseEnd_209136 := by
    simpa [prefixWord, tailWord_209136, baseEnd_209136] using wordTrace_append hprefix tailTrace_209136
  have hstable : (prefixWord ++ tailWord_209136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209136).length < 2 ^ (prefixWord ++ tailWord_209136).sum := by decide
  have hdescent : baseEnd_209136 < baseStart_209136 := by decide
  rcases family_descends (prefixWord ++ tailWord_209136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209149 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_209149 : Nat := 118140960795 + 209149 * 2 ^ 59
def prefixEnd_209149 : Nat := 4983230072969 + 3 ^ 40 * 209149 * 2
def baseEnd_209149 : Nat := 107393965407307437275647

theorem tailTrace_209149 : CollatzResearch.WordTrace tailWord_209149 prefixEnd_209149 107393965407307437275647 := by
  unfold tailWord_209149
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628290719296367650510501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5085527146197578433673667 7628290719296367650510501)
  ·
    refine ⟨1430304509868068934470719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7628290719296367650510501 1430304509868068934470719)
    ·
      refine ⟨2145456764802103401706079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430304509868068934470719 2145456764802103401706079)
      ·
        refine ⟨3218185147203155102559119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145456764802103401706079 3218185147203155102559119)
        ·
          refine ⟨4827277720804732653838679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218185147203155102559119 4827277720804732653838679)
          ·
            refine ⟨7240916581207098980758019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827277720804732653838679 7240916581207098980758019)
            ·
              refine ⟨10861374871810648471137029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240916581207098980758019 10861374871810648471137029)
              ·
                refine ⟨2036507788464496588338193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10861374871810648471137029 2036507788464496588338193)
                ·
                  refine ⟨1527380841348372441253645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2036507788464496588338193 1527380841348372441253645)
                  ·
                    refine ⟨572767815505639665470117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1527380841348372441253645 572767815505639665470117)
                    ·
                      refine ⟨107393965407307437275647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 572767815505639665470117 107393965407307437275647)
                      ·
                        rfl

theorem cell23_209149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_209149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209149 prefixEnd_209149 := by exact prefixLift 209149
  have htrace : WordTrace (prefixWord ++ tailWord_209149) baseStart_209149 baseEnd_209149 := by
    simpa [prefixWord, tailWord_209149, baseEnd_209149] using wordTrace_append hprefix tailTrace_209149
  have hstable : (prefixWord ++ tailWord_209149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209149).length < 2 ^ (prefixWord ++ tailWord_209149).sum := by decide
  have hdescent : baseEnd_209149 < baseStart_209149 := by decide
  rcases family_descends (prefixWord ++ tailWord_209149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209169 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_209169 : Nat := 118140960795 + 209169 * 2 ^ 59
def prefixEnd_209169 : Nat := 4983230072969 + 3 ^ 40 * 209169 * 2
def baseEnd_209169 : Nat := 107404235020397359025555

theorem tailTrace_209169 : CollatzResearch.WordTrace tailWord_209169 prefixEnd_209169 107404235020397359025555 := by
  unfold tailWord_209169
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629020179223911066238561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5086013452815940710825707 7629020179223911066238561)
  ·
    refine ⟨5721765134417933299678921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7629020179223911066238561 5721765134417933299678921)
    ·
      refine ⟨4291323850813449974759191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5721765134417933299678921 4291323850813449974759191)
      ·
        refine ⟨6436985776220174962138787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4291323850813449974759191 6436985776220174962138787)
        ·
          refine ⟨9655478664330262443208181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436985776220174962138787 9655478664330262443208181)
          ·
            refine ⟨905201124780962104050767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9655478664330262443208181 905201124780962104050767)
            ·
              refine ⟨1357801687171443156076151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905201124780962104050767 1357801687171443156076151)
              ·
                refine ⟨2036702530757164734114227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357801687171443156076151 2036702530757164734114227)
                ·
                  refine ⟨3055053796135747101171341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036702530757164734114227 3055053796135747101171341)
                  ·
                    refine ⟨1145645173550905162939253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055053796135747101171341 1145645173550905162939253)
                    ·
                      refine ⟨107404235020397359025555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1145645173550905162939253 107404235020397359025555)
                      ·
                        rfl

theorem cell23_209169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_209169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209169 prefixEnd_209169 := by exact prefixLift 209169
  have htrace : WordTrace (prefixWord ++ tailWord_209169) baseStart_209169 baseEnd_209169 := by
    simpa [prefixWord, tailWord_209169, baseEnd_209169] using wordTrace_append hprefix tailTrace_209169
  have hstable : (prefixWord ++ tailWord_209169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209169).length < 2 ^ (prefixWord ++ tailWord_209169).sum := by decide
  have hdescent : baseEnd_209169 < baseStart_209169 := by decide
  rcases family_descends (prefixWord ++ tailWord_209169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209179 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4]
def baseStart_209179 : Nat := 118140960795 + 209179 * 2 ^ 59
def prefixEnd_209179 : Nat := 4983230072969 + 3 ^ 40 * 209179 * 2
def baseEnd_209179 : Nat := 107409369826942319900509

theorem tailTrace_209179 : CollatzResearch.WordTrace tailWord_209179 prefixEnd_209179 107409369826942319900509 := by
  unfold tailWord_209179
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629384909187682774102591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5086256606125121849401727 7629384909187682774102591)
  ·
    refine ⟨11444077363781524161153887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629384909187682774102591 11444077363781524161153887)
    ·
      refine ⟨17166116045672286241730831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444077363781524161153887 17166116045672286241730831)
      ·
        refine ⟨25749174068508429362596247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17166116045672286241730831 25749174068508429362596247)
        ·
          refine ⟨38623761102762644043894371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25749174068508429362596247 38623761102762644043894371)
          ·
            refine ⟨57935641654143966065841557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38623761102762644043894371 57935641654143966065841557)
            ·
              refine ⟨2715733202537998409336323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57935641654143966065841557 2715733202537998409336323)
              ·
                refine ⟨4073599803806997614004485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715733202537998409336323 4073599803806997614004485)
                ·
                  refine ⟨763799963213812052625841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4073599803806997614004485 763799963213812052625841)
                  ·
                    refine ⟨572849972410359039469381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 763799963213812052625841 572849972410359039469381)
                    ·
                      refine ⟨107409369826942319900509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 572849972410359039469381 107409369826942319900509)
                      ·
                        rfl

theorem cell23_209179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_209179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209179 prefixEnd_209179 := by exact prefixLift 209179
  have htrace : WordTrace (prefixWord ++ tailWord_209179) baseStart_209179 baseEnd_209179 := by
    simpa [prefixWord, tailWord_209179, baseEnd_209179] using wordTrace_append hprefix tailTrace_209179
  have hstable : (prefixWord ++ tailWord_209179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209179).length < 2 ^ (prefixWord ++ tailWord_209179).sum := by decide
  have hdescent : baseEnd_209179 < baseStart_209179 := by decide
  rcases family_descends (prefixWord ++ tailWord_209179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209194 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_209194 : Nat := 118140960795 + 209194 * 2 ^ 59
def prefixEnd_209194 : Nat := 4983230072969 + 3 ^ 40 * 209194 * 2
def baseEnd_209194 : Nat := 107417072036759761212941

theorem tailTrace_209194 : CollatzResearch.WordTrace tailWord_209194 prefixEnd_209194 107417072036759761212941 := by
  unfold tailWord_209194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907483001033335083974659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5086621336088893557265757 1907483001033335083974659)
  ·
    refine ⟨2861224501550002625961989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1907483001033335083974659 2861224501550002625961989)
    ·
      refine ⟨536479594040625492367873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2861224501550002625961989 536479594040625492367873)
      ·
        refine ⟨402359695530469119275905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536479594040625492367873 402359695530469119275905)
        ·
          refine ⟨301769771647851839456929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402359695530469119275905 301769771647851839456929)
          ·
            refine ⟨226327328735888879592697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301769771647851839456929 226327328735888879592697)
            ·
              refine ⟨169745496551916659694523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226327328735888879592697 169745496551916659694523)
              ·
                refine ⟨254618244827874989541785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169745496551916659694523 254618244827874989541785)
                ·
                  refine ⟨190963683620906242156339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254618244827874989541785 190963683620906242156339)
                  ·
                    refine ⟨286445525431359363234509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190963683620906242156339 286445525431359363234509)
                    ·
                      refine ⟨107417072036759761212941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 286445525431359363234509 107417072036759761212941)
                      ·
                        rfl

theorem cell23_209194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_209194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209194 prefixEnd_209194 := by exact prefixLift 209194
  have htrace : WordTrace (prefixWord ++ tailWord_209194) baseStart_209194 baseEnd_209194 := by
    simpa [prefixWord, tailWord_209194, baseEnd_209194] using wordTrace_append hprefix tailTrace_209194
  have hstable : (prefixWord ++ tailWord_209194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209194).length < 2 ^ (prefixWord ++ tailWord_209194).sum := by decide
  have hdescent : baseEnd_209194 < baseStart_209194 := by decide
  rcases family_descends (prefixWord ++ tailWord_209194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209219 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 1, 7]
def baseStart_209219 : Nat := 118140960795 + 209219 * 2 ^ 59
def prefixEnd_209219 : Nat := 4983230072969 + 3 ^ 40 * 209219 * 2
def baseEnd_209219 : Nat := 35809969684374054466775

theorem tailTrace_209219 : CollatzResearch.WordTrace tailWord_209219 prefixEnd_209219 35809969684374054466775 := by
  unfold tailWord_209219
  simp only [CollatzResearch.WordTrace]
  refine ⟨7630843829042769605558711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5087229219361846403705807 7630843829042769605558711)
  ·
    refine ⟨11446265743564154408338067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7630843829042769605558711 11446265743564154408338067)
    ·
      refine ⟨17169398615346231612507101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11446265743564154408338067 17169398615346231612507101)
      ·
        refine ⟨6438524480754836854690163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17169398615346231612507101 6438524480754836854690163)
        ·
          refine ⟨9657786721132255282035245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438524480754836854690163 9657786721132255282035245)
          ·
            refine ⟨3621670020424595730763217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9657786721132255282035245 3621670020424595730763217)
            ·
              refine ⟨2716252515318446798072413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621670020424595730763217 2716252515318446798072413)
              ·
                refine ⟨1018594693244417549277155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2716252515318446798072413 1018594693244417549277155)
                ·
                  refine ⟨1527892039866626323915733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018594693244417549277155 1527892039866626323915733)
                  ·
                    refine ⟨35809969684374054466775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1527892039866626323915733 35809969684374054466775)
                    ·
                      rfl

theorem cell23_209219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7].length) (baseStart_209219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209219 prefixEnd_209219 := by exact prefixLift 209219
  have htrace : WordTrace (prefixWord ++ tailWord_209219) baseStart_209219 baseEnd_209219 := by
    simpa [prefixWord, tailWord_209219, baseEnd_209219] using wordTrace_append hprefix tailTrace_209219
  have hstable : (prefixWord ++ tailWord_209219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209219).length < 2 ^ (prefixWord ++ tailWord_209219).sum := by decide
  have hdescent : baseEnd_209219 < baseStart_209219 := by decide
  rcases family_descends (prefixWord ++ tailWord_209219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209249 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 4, 8]
def baseStart_209249 : Nat := 118140960795 + 209249 * 2 ^ 59
def prefixEnd_209249 : Nat := 4983230072969 + 3 ^ 40 * 209249 * 2
def baseEnd_209249 : Nat := 35815104490919015341729

theorem tailTrace_209249 : CollatzResearch.WordTrace tailWord_209249 prefixEnd_209249 35815104490919015341729 := by
  unfold tailWord_209249
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631938018934084729150801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5087958679289389819433867 7631938018934084729150801)
  ·
    refine ⟨5723953514200563546863101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7631938018934084729150801 5723953514200563546863101)
    ·
      refine ⟨2146482567825211330073663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5723953514200563546863101 2146482567825211330073663)
      ·
        refine ⟨3219723851737816995110495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146482567825211330073663 3219723851737816995110495)
        ·
          refine ⟨4829585777606725492665743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3219723851737816995110495 4829585777606725492665743)
          ·
            refine ⟨7244378666410088238998615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4829585777606725492665743 7244378666410088238998615)
            ·
              refine ⟨10866567999615132358497923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244378666410088238998615 10866567999615132358497923)
              ·
                refine ⟨16299851999422698537746885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10866567999615132358497923 16299851999422698537746885)
                ·
                  refine ⟨3056222249891755975827541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16299851999422698537746885 3056222249891755975827541)
                  ·
                    refine ⟨35815104490919015341729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3056222249891755975827541 35815104490919015341729)
                    ·
                      rfl

theorem cell23_209249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_209249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209249 prefixEnd_209249 := by exact prefixLift 209249
  have htrace : WordTrace (prefixWord ++ tailWord_209249) baseStart_209249 baseEnd_209249 := by
    simpa [prefixWord, tailWord_209249, baseEnd_209249] using wordTrace_append hprefix tailTrace_209249
  have hstable : (prefixWord ++ tailWord_209249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209249).length < 2 ^ (prefixWord ++ tailWord_209249).sum := by decide
  have hdescent : baseEnd_209249 < baseStart_209249 := by decide
  rcases family_descends (prefixWord ++ tailWord_209249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209259 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5]
def baseStart_209259 : Nat := 118140960795 + 209259 * 2 ^ 59
def prefixEnd_209259 : Nat := 4983230072969 + 3 ^ 40 * 209259 * 2
def baseEnd_209259 : Nat := 107450448279302006900141

theorem tailTrace_209259 : CollatzResearch.WordTrace tailWord_209259 prefixEnd_209259 107450448279302006900141 := by
  unfold tailWord_209259
  simp only [CollatzResearch.WordTrace]
  refine ⟨7632302748897856437014831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5088201832598570958009887 7632302748897856437014831)
  ·
    refine ⟨11448454123346784655522247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7632302748897856437014831 11448454123346784655522247)
    ·
      refine ⟨17172681185020176983283371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11448454123346784655522247 17172681185020176983283371)
      ·
        refine ⟨25759021777530265474925057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17172681185020176983283371 25759021777530265474925057)
        ·
          refine ⟨19319266333147699106193793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25759021777530265474925057 19319266333147699106193793)
          ·
            refine ⟨14489449749860774329645345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19319266333147699106193793 14489449749860774329645345)
            ·
              refine ⟨10867087312395580747234009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14489449749860774329645345 10867087312395580747234009)
              ·
                refine ⟨8150315484296685560425507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10867087312395580747234009 8150315484296685560425507)
                ·
                  refine ⟨12225473226445028340638261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150315484296685560425507 12225473226445028340638261)
                  ·
                    refine ⟨1146138114979221406934837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12225473226445028340638261 1146138114979221406934837)
                    ·
                      refine ⟨107450448279302006900141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1146138114979221406934837 107450448279302006900141)
                      ·
                        rfl

theorem cell23_209259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_209259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209259 prefixEnd_209259 := by exact prefixLift 209259
  have htrace : WordTrace (prefixWord ++ tailWord_209259) baseStart_209259 baseEnd_209259 := by
    simpa [prefixWord, tailWord_209259, baseEnd_209259] using wordTrace_append hprefix tailTrace_209259
  have hstable : (prefixWord ++ tailWord_209259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209259).length < 2 ^ (prefixWord ++ tailWord_209259).sum := by decide
  have hdescent : baseEnd_209259 < baseStart_209259 := by decide
  rcases family_descends (prefixWord ++ tailWord_209259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209270 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_209270 : Nat := 118140960795 + 209270 * 2 ^ 59
def prefixEnd_209270 : Nat := 4983230072969 + 3 ^ 40 * 209270 * 2
def baseEnd_209270 : Nat := 35818698855500487954197

theorem tailTrace_209270 : CollatzResearch.WordTrace tailWord_209270 prefixEnd_209270 35818698855500487954197 := by
  unfold tailWord_209270
  simp only [CollatzResearch.WordTrace]
  refine ⟨477043996991125332229079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5088469301238670210443509 477043996991125332229079)
  ·
    refine ⟨715565995486687998343619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 477043996991125332229079 715565995486687998343619)
    ·
      refine ⟨1073348993230031997515429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715565995486687998343619 1073348993230031997515429)
      ·
        refine ⟨201252936230630999534143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1073348993230031997515429 201252936230630999534143)
        ·
          refine ⟨301879404345946499301215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201252936230630999534143 301879404345946499301215)
          ·
            refine ⟨452819106518919748951823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301879404345946499301215 452819106518919748951823)
            ·
              refine ⟨679228659778379623427735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452819106518919748951823 679228659778379623427735)
              ·
                refine ⟨1018842989667569435141603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679228659778379623427735 1018842989667569435141603)
                ·
                  refine ⟨1528264484501354152712405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018842989667569435141603 1528264484501354152712405)
                  ·
                    refine ⟨35818698855500487954197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1528264484501354152712405 35818698855500487954197)
                    ·
                      rfl

theorem cell23_209270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_209270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209270 prefixEnd_209270 := by exact prefixLift 209270
  have htrace : WordTrace (prefixWord ++ tailWord_209270) baseStart_209270 baseEnd_209270 := by
    simpa [prefixWord, tailWord_209270, baseEnd_209270] using wordTrace_append hprefix tailTrace_209270
  have hstable : (prefixWord ++ tailWord_209270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209270).length < 2 ^ (prefixWord ++ tailWord_209270).sum := by decide
  have hdescent : baseEnd_209270 < baseStart_209270 := by decide
  rcases family_descends (prefixWord ++ tailWord_209270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209279 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 10]
def baseStart_209279 : Nat := 118140960795 + 209279 * 2 ^ 59
def prefixEnd_209279 : Nat := 4983230072969 + 3 ^ 40 * 209279 * 2
def baseEnd_209279 : Nat := 11940079765821325405561

theorem tailTrace_209279 : CollatzResearch.WordTrace tailWord_209279 prefixEnd_209279 11940079765821325405561 := by
  unfold tailWord_209279
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633032208825399852742891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5088688139216933235161927 7633032208825399852742891)
  ·
    refine ⟨11449548313238099779114337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7633032208825399852742891 11449548313238099779114337)
    ·
      refine ⟨8587161234928574834335753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11449548313238099779114337 8587161234928574834335753)
      ·
        refine ⟨6440370926196431125751815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8587161234928574834335753 6440370926196431125751815)
        ·
          refine ⟨9660556389294646688627723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440370926196431125751815 9660556389294646688627723)
          ·
            refine ⟨14490834583941970032941585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9660556389294646688627723 14490834583941970032941585)
            ·
              refine ⟨10868125937956477524706189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14490834583941970032941585 10868125937956477524706189)
              ·
                refine ⟨4075547226733679071764821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10868125937956477524706189 4075547226733679071764821)
                ·
                  refine ⟨11940079765821325405561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 4075547226733679071764821 11940079765821325405561)
                  ·
                    rfl

theorem cell23_209279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 10].length) (baseStart_209279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209279 prefixEnd_209279 := by exact prefixLift 209279
  have htrace : WordTrace (prefixWord ++ tailWord_209279) baseStart_209279 baseEnd_209279 := by
    simpa [prefixWord, tailWord_209279, baseEnd_209279] using wordTrace_append hprefix tailTrace_209279
  have hstable : (prefixWord ++ tailWord_209279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209279).length < 2 ^ (prefixWord ++ tailWord_209279).sum := by decide
  have hdescent : baseEnd_209279 < baseStart_209279 := by decide
  rcases family_descends (prefixWord ++ tailWord_209279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209310 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_209310 : Nat := 118140960795 + 209310 * 2 ^ 59
def prefixEnd_209310 : Nat := 4983230072969 + 3 ^ 40 * 209310 * 2
def baseEnd_209310 : Nat := 107476635792681307362407

theorem tailTrace_209310 : CollatzResearch.WordTrace tailWord_209310 prefixEnd_209310 107476635792681307362407 := by
  unfold tailWord_209310
  simp only [CollatzResearch.WordTrace]
  refine ⟨954270358964136518390173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5089441914475394764747589 954270358964136518390173)
  ·
    refine ⟨357851384611551194396315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 954270358964136518390173 357851384611551194396315)
    ·
      refine ⟨536777076917326791594473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357851384611551194396315 536777076917326791594473)
      ·
        refine ⟨402582807687995093695855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536777076917326791594473 402582807687995093695855)
        ·
          refine ⟨603874211531992640543783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402582807687995093695855 603874211531992640543783)
          ·
            refine ⟨905811317297988960815675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603874211531992640543783 905811317297988960815675)
            ·
              refine ⟨1358716975946983441223513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905811317297988960815675 1358716975946983441223513)
              ·
                refine ⟨1019037731960237580917635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358716975946983441223513 1019037731960237580917635)
                ·
                  refine ⟨1528556597940356371376453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019037731960237580917635 1528556597940356371376453)
                  ·
                    refine ⟨286604362113816819633085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528556597940356371376453 286604362113816819633085)
                    ·
                      refine ⟨107476635792681307362407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 286604362113816819633085 107476635792681307362407)
                      ·
                        rfl

theorem cell23_209310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_209310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209310 prefixEnd_209310 := by exact prefixLift 209310
  have htrace : WordTrace (prefixWord ++ tailWord_209310) baseStart_209310 baseEnd_209310 := by
    simpa [prefixWord, tailWord_209310, baseEnd_209310] using wordTrace_append hprefix tailTrace_209310
  have hstable : (prefixWord ++ tailWord_209310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209310).length < 2 ^ (prefixWord ++ tailWord_209310).sum := by decide
  have hdescent : baseEnd_209310 < baseStart_209310 := by decide
  rcases family_descends (prefixWord ++ tailWord_209310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209373 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_209373 : Nat := 118140960795 + 209373 * 2 ^ 59
def prefixEnd_209373 : Nat := 4983230072969 + 3 ^ 40 * 209373 * 2
def baseEnd_209373 : Nat := 35836328357971520291539

theorem tailTrace_209373 : CollatzResearch.WordTrace tailWord_209373 prefixEnd_209373 35836328357971520291539 := by
  unfold tailWord_209373
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636460670484853906664773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5090973780323235937776515 7636460670484853906664773)
  ·
    refine ⟨1431836375715910107499645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7636460670484853906664773 1431836375715910107499645)
    ·
      refine ⟨536938640893466290312367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1431836375715910107499645 536938640893466290312367)
      ·
        refine ⟨805407961340199435468551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536938640893466290312367 805407961340199435468551)
        ·
          refine ⟨1208111942010299153202827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805407961340199435468551 1208111942010299153202827)
          ·
            refine ⟨1812167913015448729804241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208111942010299153202827 1812167913015448729804241)
            ·
              refine ⟨1359125934761586547353181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812167913015448729804241 1359125934761586547353181)
              ·
                refine ⟨509672225535594955257443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359125934761586547353181 509672225535594955257443)
                ·
                  refine ⟨764508338303392432886165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509672225535594955257443 764508338303392432886165)
                  ·
                    refine ⟨35836328357971520291539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 764508338303392432886165 35836328357971520291539)
                    ·
                      rfl

theorem cell23_209373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_209373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209373 prefixEnd_209373 := by exact prefixLift 209373
  have htrace : WordTrace (prefixWord ++ tailWord_209373) baseStart_209373 baseEnd_209373 := by
    simpa [prefixWord, tailWord_209373, baseEnd_209373] using wordTrace_append hprefix tailTrace_209373
  have hstable : (prefixWord ++ tailWord_209373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209373).length < 2 ^ (prefixWord ++ tailWord_209373).sum := by decide
  have hdescent : baseEnd_209373 < baseStart_209373 := by decide
  rcases family_descends (prefixWord ++ tailWord_209373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209376 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_209376 : Nat := 118140960795 + 209376 * 2 ^ 59
def prefixEnd_209376 : Nat := 4983230072969 + 3 ^ 40 * 209376 * 2
def baseEnd_209376 : Nat := 107510525515878049137103

theorem tailTrace_209376 : CollatzResearch.WordTrace tailWord_209376 prefixEnd_209376 107510525515878049137103 := by
  unfold tailWord_209376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818285044736992709511991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5091046726315990279349321 3818285044736992709511991)
  ·
    refine ⟨5727427567105489064267987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818285044736992709511991 5727427567105489064267987)
    ·
      refine ⟨8591141350658233596401981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727427567105489064267987 8591141350658233596401981)
      ·
        refine ⟨3221678006496837598650743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8591141350658233596401981 3221678006496837598650743)
        ·
          refine ⟨4832517009745256397976115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221678006496837598650743 4832517009745256397976115)
          ·
            refine ⟨7248775514617884596964173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832517009745256397976115 7248775514617884596964173)
            ·
              refine ⟨2718290817981706723861565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7248775514617884596964173 2718290817981706723861565)
              ·
                refine ⟨1019359056743140021448087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718290817981706723861565 1019359056743140021448087)
                ·
                  refine ⟨1529038585114710032172131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019359056743140021448087 1529038585114710032172131)
                  ·
                    refine ⟨2293557877672065048258197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529038585114710032172131 2293557877672065048258197)
                    ·
                      refine ⟨107510525515878049137103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2293557877672065048258197 107510525515878049137103)
                      ·
                        rfl

theorem cell23_209376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_209376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209376 prefixEnd_209376 := by exact prefixLift 209376
  have htrace : WordTrace (prefixWord ++ tailWord_209376) baseStart_209376 baseEnd_209376 := by
    simpa [prefixWord, tailWord_209376, baseEnd_209376] using wordTrace_append hprefix tailTrace_209376
  have hstable : (prefixWord ++ tailWord_209376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209376).length < 2 ^ (prefixWord ++ tailWord_209376).sum := by decide
  have hdescent : baseEnd_209376 < baseStart_209376 := by decide
  rcases family_descends (prefixWord ++ tailWord_209376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209393 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_209393 : Nat := 118140960795 + 209393 * 2 ^ 59
def prefixEnd_209393 : Nat := 4983230072969 + 3 ^ 40 * 209393 * 2
def baseEnd_209393 : Nat := 107519254687004482624525

theorem tailTrace_209393 : CollatzResearch.WordTrace tailWord_209393 prefixEnd_209393 107519254687004482624525 := by
  unfold tailWord_209393
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637190130412397322392833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5091460086941598214928555 7637190130412397322392833)
  ·
    refine ⟨5727892597809297991794625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7637190130412397322392833 5727892597809297991794625)
    ·
      refine ⟨4295919448356973493845969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5727892597809297991794625 4295919448356973493845969)
      ·
        refine ⟨3221939586267730120384477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4295919448356973493845969 3221939586267730120384477)
        ·
          refine ⟨1208227344850398795144179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3221939586267730120384477 1208227344850398795144179)
          ·
            refine ⟨1812341017275598192716269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208227344850398795144179 1812341017275598192716269)
            ·
              refine ⟨679627881478349322268601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1812341017275598192716269 679627881478349322268601)
              ·
                refine ⟨509720911108761991701451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679627881478349322268601 509720911108761991701451)
                ·
                  refine ⟨764581366663142987552177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509720911108761991701451 764581366663142987552177)
                  ·
                    refine ⟨573436024997357240664133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764581366663142987552177 573436024997357240664133)
                    ·
                      refine ⟨107519254687004482624525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 573436024997357240664133 107519254687004482624525)
                      ·
                        rfl

theorem cell23_209393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_209393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209393 prefixEnd_209393 := by exact prefixLift 209393
  have htrace : WordTrace (prefixWord ++ tailWord_209393) baseStart_209393 baseEnd_209393 := by
    simpa [prefixWord, tailWord_209393, baseEnd_209393] using wordTrace_append hprefix tailTrace_209393
  have hstable : (prefixWord ++ tailWord_209393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209393).length < 2 ^ (prefixWord ++ tailWord_209393).sum := by decide
  have hdescent : baseEnd_209393 < baseStart_209393 := by decide
  rcases family_descends (prefixWord ++ tailWord_209393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209414 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_209414 : Nat := 118140960795 + 209414 * 2 ^ 59
def prefixEnd_209414 : Nat := 4983230072969 + 3 ^ 40 * 209414 * 2
def baseEnd_209414 : Nat := 107530037780748900461929

theorem tailTrace_209414 : CollatzResearch.WordTrace tailWord_209414 prefixEnd_209414 107530037780748900461929 := by
  unfold tailWord_209414
  simp only [CollatzResearch.WordTrace]
  refine ⟨238686126979259934653353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5091970708890878605938197 238686126979259934653353)
  ·
    refine ⟨179014595234444950990015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238686126979259934653353 179014595234444950990015)
    ·
      refine ⟨268521892851667426485023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179014595234444950990015 268521892851667426485023)
      ·
        refine ⟨402782839277501139727535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268521892851667426485023 402782839277501139727535)
        ·
          refine ⟨604174258916251709591303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402782839277501139727535 604174258916251709591303)
          ·
            refine ⟨906261388374377564386955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604174258916251709591303 906261388374377564386955)
            ·
              refine ⟨1359392082561566346580433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906261388374377564386955 1359392082561566346580433)
              ·
                refine ⟨1019544061921174759935325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359392082561566346580433 1019544061921174759935325)
                ·
                  refine ⟨382329023220440534975747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019544061921174759935325 382329023220440534975747)
                  ·
                    refine ⟨573493534830660802463621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 382329023220440534975747 573493534830660802463621)
                    ·
                      refine ⟨107530037780748900461929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 573493534830660802463621 107530037780748900461929)
                      ·
                        rfl

theorem cell23_209414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_209414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209414 prefixEnd_209414 := by exact prefixLift 209414
  have htrace : WordTrace (prefixWord ++ tailWord_209414) baseStart_209414 baseEnd_209414 := by
    simpa [prefixWord, tailWord_209414, baseEnd_209414] using wordTrace_append hprefix tailTrace_209414
  have hstable : (prefixWord ++ tailWord_209414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209414).length < 2 ^ (prefixWord ++ tailWord_209414).sum := by decide
  have hdescent : baseEnd_209414 < baseStart_209414 := by decide
  rcases family_descends (prefixWord ++ tailWord_209414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209423 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 7, 2]
def baseStart_209423 : Nat := 118140960795 + 209423 * 2 ^ 59
def prefixEnd_209423 : Nat := 4983230072969 + 3 ^ 40 * 209423 * 2
def baseEnd_209423 : Nat := 107534659106639365249387

theorem tailTrace_209423 : CollatzResearch.WordTrace tailWord_209423 prefixEnd_209423 107534659106639365249387 := by
  unfold tailWord_209423
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638284320303712445984923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5092189546869141630656615 7638284320303712445984923)
  ·
    refine ⟨11457426480455568668977385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7638284320303712445984923 11457426480455568668977385)
    ·
      refine ⟨8593069860341676501733039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11457426480455568668977385 8593069860341676501733039)
      ·
        refine ⟨12889604790512514752599559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593069860341676501733039 12889604790512514752599559)
        ·
          refine ⟨19334407185768772128899339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889604790512514752599559 19334407185768772128899339)
          ·
            refine ⟨29001610778653158193349009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19334407185768772128899339 29001610778653158193349009)
            ·
              refine ⟨21751208083989868645011757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29001610778653158193349009 21751208083989868645011757)
              ·
                refine ⟨8156703031496200741879409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21751208083989868645011757 8156703031496200741879409)
                ·
                  refine ⟨6117527273622150556409557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8156703031496200741879409 6117527273622150556409557)
                  ·
                    refine ⟨143379545475519153665849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6117527273622150556409557 143379545475519153665849)
                    ·
                      refine ⟨107534659106639365249387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143379545475519153665849 107534659106639365249387)
                      ·
                        rfl

theorem cell23_209423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7, 2].length) (baseStart_209423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209423 prefixEnd_209423 := by exact prefixLift 209423
  have htrace : WordTrace (prefixWord ++ tailWord_209423) baseStart_209423 baseEnd_209423 := by
    simpa [prefixWord, tailWord_209423, baseEnd_209423] using wordTrace_append hprefix tailTrace_209423
  have hstable : (prefixWord ++ tailWord_209423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209423).length < 2 ^ (prefixWord ++ tailWord_209423).sum := by decide
  have hdescent : baseEnd_209423 < baseStart_209423 := by decide
  rcases family_descends (prefixWord ++ tailWord_209423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209483 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4]
def baseStart_209483 : Nat := 118140960795 + 209483 * 2 ^ 59
def prefixEnd_209483 : Nat := 4983230072969 + 3 ^ 40 * 209483 * 2
def baseEnd_209483 : Nat := 107565467945909130499111

theorem tailTrace_209483 : CollatzResearch.WordTrace tailWord_209483 prefixEnd_209483 107565467945909130499111 := by
  unfold tailWord_209483
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640472700086342693169103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5093648466724228462112735 7640472700086342693169103)
  ·
    refine ⟨11460709050129514039753655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7640472700086342693169103 11460709050129514039753655)
    ·
      refine ⟨17191063575194271059630483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11460709050129514039753655 17191063575194271059630483)
      ·
        refine ⟨25786595362791406589445725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17191063575194271059630483 25786595362791406589445725)
        ·
          refine ⟨9669973261046777471042147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25786595362791406589445725 9669973261046777471042147)
          ·
            refine ⟨14504959891570166206563221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9669973261046777471042147 14504959891570166206563221)
            ·
              refine ⟨679919994917351540932651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14504959891570166206563221 679919994917351540932651)
              ·
                refine ⟨1019879992376027311398977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679919994917351540932651 1019879992376027311398977)
                ·
                  refine ⟨764909994282020483549233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1019879992376027311398977 764909994282020483549233)
                  ·
                    refine ⟨573682495711515362661925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764909994282020483549233 573682495711515362661925)
                    ·
                      refine ⟨107565467945909130499111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 573682495711515362661925 107565467945909130499111)
                      ·
                        rfl

theorem cell23_209483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_209483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209483 prefixEnd_209483 := by exact prefixLift 209483
  have htrace : WordTrace (prefixWord ++ tailWord_209483) baseStart_209483 baseEnd_209483 := by
    simpa [prefixWord, tailWord_209483, baseEnd_209483] using wordTrace_append hprefix tailTrace_209483
  have hstable : (prefixWord ++ tailWord_209483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209483).length < 2 ^ (prefixWord ++ tailWord_209483).sum := by decide
  have hdescent : baseEnd_209483 < baseStart_209483 := by decide
  rcases family_descends (prefixWord ++ tailWord_209483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209487 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 2, 2, 2]
def baseStart_209487 : Nat := 118140960795 + 209487 * 2 ^ 59
def prefixEnd_209487 : Nat := 4983230072969 + 3 ^ 40 * 209487 * 2
def baseEnd_209487 : Nat := 107567521868527114849093

theorem tailTrace_209487 : CollatzResearch.WordTrace tailWord_209487 prefixEnd_209487 107567521868527114849093 := by
  unfold tailWord_209487
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640618592071851376314715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5093745728047900917543143 7640618592071851376314715)
  ·
    refine ⟨11460927888107777064472073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7640618592071851376314715 11460927888107777064472073)
    ·
      refine ⟨8595695916080832798354055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11460927888107777064472073 8595695916080832798354055)
      ·
        refine ⟨12893543874121249197531083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8595695916080832798354055 12893543874121249197531083)
        ·
          refine ⟨19340315811181873796296625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893543874121249197531083 19340315811181873796296625)
          ·
            refine ⟨14505236858386405347222469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19340315811181873796296625 14505236858386405347222469)
            ·
              refine ⟨2719731910947451002604213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14505236858386405347222469 2719731910947451002604213)
              ·
                refine ⟨254974866651323531494145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2719731910947451002604213 254974866651323531494145)
                ·
                  refine ⟨191231149988492648620609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254974866651323531494145 191231149988492648620609)
                  ·
                    refine ⟨143423362491369486465457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 191231149988492648620609 143423362491369486465457)
                    ·
                      refine ⟨107567521868527114849093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143423362491369486465457 107567521868527114849093)
                      ·
                        rfl

theorem cell23_209487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 2, 2].length) (baseStart_209487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209487 prefixEnd_209487 := by exact prefixLift 209487
  have htrace : WordTrace (prefixWord ++ tailWord_209487) baseStart_209487 baseEnd_209487 := by
    simpa [prefixWord, tailWord_209487, baseEnd_209487] using wordTrace_append hprefix tailTrace_209487
  have hstable : (prefixWord ++ tailWord_209487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209487).length < 2 ^ (prefixWord ++ tailWord_209487).sum := by decide
  have hdescent : baseEnd_209487 < baseStart_209487 := by decide
  rcases family_descends (prefixWord ++ tailWord_209487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209493 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 7]
def baseStart_209493 : Nat := 118140960795 + 209493 * 2 ^ 59
def prefixEnd_209493 : Nat := 4983230072969 + 3 ^ 40 * 209493 * 2
def baseEnd_209493 : Nat := 11952289194717121263785

theorem tailTrace_209493 : CollatzResearch.WordTrace tailWord_209493 prefixEnd_209493 11952289194717121263785 := by
  unfold tailWord_209493
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640837430050114401033133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5093891620033409600688755 7640837430050114401033133)
  ·
    refine ⟨2865314036268792900387425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7640837430050114401033133 2865314036268792900387425)
    ·
      refine ⟨2148985527201594675290569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2865314036268792900387425 2148985527201594675290569)
      ·
        refine ⟨1611739145401196006467927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2148985527201594675290569 1611739145401196006467927)
        ·
          refine ⟨2417608718101794009701891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611739145401196006467927 2417608718101794009701891)
          ·
            refine ⟨3626413077152691014552837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417608718101794009701891 3626413077152691014552837)
            ·
              refine ⟨679952451966129565228657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3626413077152691014552837 679952451966129565228657)
              ·
                refine ⟨509964338974597173921493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679952451966129565228657 509964338974597173921493)
                ·
                  refine ⟨11952289194717121263785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 509964338974597173921493 11952289194717121263785)
                  ·
                    rfl

theorem cell23_209493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_209493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209493 prefixEnd_209493 := by exact prefixLift 209493
  have htrace : WordTrace (prefixWord ++ tailWord_209493) baseStart_209493 baseEnd_209493 := by
    simpa [prefixWord, tailWord_209493, baseEnd_209493] using wordTrace_append hprefix tailTrace_209493
  have hstable : (prefixWord ++ tailWord_209493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209493).length < 2 ^ (prefixWord ++ tailWord_209493).sum := by decide
  have hdescent : baseEnd_209493 < baseStart_209493 := by decide
  rcases family_descends (prefixWord ++ tailWord_209493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209503 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 3]
def baseStart_209503 : Nat := 118140960795 + 209503 * 2 ^ 59
def prefixEnd_209503 : Nat := 4983230072969 + 3 ^ 40 * 209503 * 2
def baseEnd_209503 : Nat := 107575737558999052249019

theorem tailTrace_209503 : CollatzResearch.WordTrace tailWord_209503 prefixEnd_209503 107575737558999052249019 := by
  unfold tailWord_209503
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641202160013886108897163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5094134773342590739264775 7641202160013886108897163)
  ·
    refine ⟨11461803240020829163345745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7641202160013886108897163 11461803240020829163345745)
    ·
      refine ⟨8596352430015621872509309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11461803240020829163345745 8596352430015621872509309)
      ·
        refine ⟨3223632161255858202190991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8596352430015621872509309 3223632161255858202190991)
        ·
          refine ⟨4835448241883787303286487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223632161255858202190991 4835448241883787303286487)
          ·
            refine ⟨7253172362825680954929731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835448241883787303286487 7253172362825680954929731)
            ·
              refine ⟨10879758544238521432394597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253172362825680954929731 10879758544238521432394597)
              ·
                refine ⟨2039954727044722768573987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10879758544238521432394597 2039954727044722768573987)
                ·
                  refine ⟨3059932090567084152860981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039954727044722768573987 3059932090567084152860981)
                  ·
                    refine ⟨286868633490664139330717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3059932090567084152860981 286868633490664139330717)
                    ·
                      refine ⟨107575737558999052249019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 286868633490664139330717 107575737558999052249019)
                      ·
                        rfl

theorem cell23_209503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_209503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209503 prefixEnd_209503 := by exact prefixLift 209503
  have htrace : WordTrace (prefixWord ++ tailWord_209503) baseStart_209503 baseEnd_209503 := by
    simpa [prefixWord, tailWord_209503, baseEnd_209503] using wordTrace_append hprefix tailTrace_209503
  have hstable : (prefixWord ++ tailWord_209503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209503).length < 2 ^ (prefixWord ++ tailWord_209503).sum := by decide
  have hdescent : baseEnd_209503 < baseStart_209503 := by decide
  rcases family_descends (prefixWord ++ tailWord_209503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209573 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_209573 : Nat := 118140960795 + 209573 * 2 ^ 59
def prefixEnd_209573 : Nat := 4983230072969 + 3 ^ 40 * 209573 * 2
def baseEnd_209573 : Nat := 107611681204813778373697

theorem tailTrace_209573 : CollatzResearch.WordTrace tailWord_209573 prefixEnd_209573 107611681204813778373697 := by
  unfold tailWord_209573
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643755269760288063945373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5095836846506858709296915 7643755269760288063945373)
  ·
    refine ⟨2866408226160108023979515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7643755269760288063945373 2866408226160108023979515)
    ·
      refine ⟨4299612339240162035969273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2866408226160108023979515 4299612339240162035969273)
      ·
        refine ⟨3224709254430121526976955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4299612339240162035969273 3224709254430121526976955)
        ·
          refine ⟨4837063881645182290465433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224709254430121526976955 4837063881645182290465433)
          ·
            refine ⟨3627797911233886717849075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4837063881645182290465433 3627797911233886717849075)
            ·
              refine ⟨5441696866850830076773613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627797911233886717849075 5441696866850830076773613)
              ·
                refine ⟨2040636325069061278790105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5441696866850830076773613 2040636325069061278790105)
                ·
                  refine ⟨1530477243801795959092579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2040636325069061278790105 1530477243801795959092579)
                  ·
                    refine ⟨2295715865702693938638869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1530477243801795959092579 2295715865702693938638869)
                    ·
                      refine ⟨107611681204813778373697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2295715865702693938638869 107611681204813778373697)
                      ·
                        rfl

theorem cell23_209573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_209573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209573 prefixEnd_209573 := by exact prefixLift 209573
  have htrace : WordTrace (prefixWord ++ tailWord_209573) baseStart_209573 baseEnd_209573 := by
    simpa [prefixWord, tailWord_209573, baseEnd_209573] using wordTrace_append hprefix tailTrace_209573
  have hstable : (prefixWord ++ tailWord_209573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209573).length < 2 ^ (prefixWord ++ tailWord_209573).sum := by decide
  have hdescent : baseEnd_209573 < baseStart_209573 := by decide
  rcases family_descends (prefixWord ++ tailWord_209573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209578 : List Nat := [3, 1, 5, 2, 1, 2, 2, 2, 5]
def baseStart_209578 : Nat := 118140960795 + 209578 * 2 ^ 59
def prefixEnd_209578 : Nat := 4983230072969 + 3 ^ 40 * 209578 * 2
def baseEnd_209578 : Nat := 11957138734231806534575

theorem tailTrace_209578 : CollatzResearch.WordTrace tailWord_209578 prefixEnd_209578 11957138734231806534575 := by
  unfold tailWord_209578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910984408685543479469347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5095958423161449278584925 1910984408685543479469347)
  ·
    refine ⟨2866476613028315219204021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1910984408685543479469347 2866476613028315219204021)
    ·
      refine ⟨268732182471404551800377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2866476613028315219204021 268732182471404551800377)
      ·
        refine ⟨201549136853553413850283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268732182471404551800377 201549136853553413850283)
        ·
          refine ⟨302323705280330120775425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201549136853553413850283 302323705280330120775425)
          ·
            refine ⟨226742778960247590581569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302323705280330120775425 226742778960247590581569)
            ·
              refine ⟨170057084220185692936177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226742778960247590581569 170057084220185692936177)
              ·
                refine ⟨127542813165139269702133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170057084220185692936177 127542813165139269702133)
                ·
                  refine ⟨11957138734231806534575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127542813165139269702133 11957138734231806534575)
                  ·
                    rfl

theorem cell23_209578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_209578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209578 prefixEnd_209578 := by exact prefixLift 209578
  have htrace : WordTrace (prefixWord ++ tailWord_209578) baseStart_209578 baseEnd_209578 := by
    simpa [prefixWord, tailWord_209578, baseEnd_209578] using wordTrace_append hprefix tailTrace_209578
  have hstable : (prefixWord ++ tailWord_209578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209578).length < 2 ^ (prefixWord ++ tailWord_209578).sum := by decide
  have hdescent : baseEnd_209578 < baseStart_209578 := by decide
  rcases family_descends (prefixWord ++ tailWord_209578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209600 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 6]
def baseStart_209600 : Nat := 118140960795 + 209600 * 2 ^ 59
def prefixEnd_209600 : Nat := 4983230072969 + 3 ^ 40 * 209600 * 2
def baseEnd_209600 : Nat := 11958393909165019192897

theorem tailTrace_209600 : CollatzResearch.WordTrace tailWord_209600 prefixEnd_209600 11958393909165019192897 := by
  unfold tailWord_209600
  simp only [CollatzResearch.WordTrace]
  refine ⟨3822370020331235837589127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5096493360441647783452169 3822370020331235837589127)
  ·
    refine ⟨5733555030496853756383691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3822370020331235837589127 5733555030496853756383691)
    ·
      refine ⟨8600332545745280634575537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5733555030496853756383691 8600332545745280634575537)
      ·
        refine ⟨6450249409308960475931653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8600332545745280634575537 6450249409308960475931653)
        ·
          refine ⟨1209421764245430089237185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6450249409308960475931653 1209421764245430089237185)
          ·
            refine ⟨907066323184072566927889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1209421764245430089237185 907066323184072566927889)
            ·
              refine ⟨680299742388054425195917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907066323184072566927889 680299742388054425195917)
              ·
                refine ⟨255112403395520409448469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680299742388054425195917 255112403395520409448469)
                ·
                  refine ⟨11958393909165019192897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 255112403395520409448469 11958393909165019192897)
                  ·
                    rfl

theorem cell23_209600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 6].length) (baseStart_209600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209600 prefixEnd_209600 := by exact prefixLift 209600
  have htrace : WordTrace (prefixWord ++ tailWord_209600) baseStart_209600 baseEnd_209600 := by
    simpa [prefixWord, tailWord_209600, baseEnd_209600] using wordTrace_append hprefix tailTrace_209600
  have hstable : (prefixWord ++ tailWord_209600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209600).length < 2 ^ (prefixWord ++ tailWord_209600).sum := by decide
  have hdescent : baseEnd_209600 < baseStart_209600 := by decide
  rcases family_descends (prefixWord ++ tailWord_209600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209614 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_209614 : Nat := 118140960795 + 209614 * 2 ^ 59
def prefixEnd_209614 : Nat := 4983230072969 + 3 ^ 40 * 209614 * 2
def baseEnd_209614 : Nat := 107632733911648117961009

theorem tailTrace_209614 : CollatzResearch.WordTrace tailWord_209614 prefixEnd_209614 107632733911648117961009 := by
  unfold tailWord_209614
  simp only [CollatzResearch.WordTrace]
  refine ⟨955656332826469008273487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5096833775074501377458597 955656332826469008273487)
  ·
    refine ⟨1433484499239703512410231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 955656332826469008273487 1433484499239703512410231)
    ·
      refine ⟨2150226748859555268615347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1433484499239703512410231 2150226748859555268615347)
      ·
        refine ⟨3225340123289332902923021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150226748859555268615347 3225340123289332902923021)
        ·
          refine ⟨1209502546233499838596133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3225340123289332902923021 1209502546233499838596133)
          ·
            refine ⟨226781727418781219736775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1209502546233499838596133 226781727418781219736775)
            ·
              refine ⟨340172591128171829605163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226781727418781219736775 340172591128171829605163)
              ·
                refine ⟨510258886692257744407745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340172591128171829605163 510258886692257744407745)
                ·
                  refine ⟨382694165019193308305809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510258886692257744407745 382694165019193308305809)
                  ·
                    refine ⟨287020623764394981229357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 382694165019193308305809 287020623764394981229357)
                    ·
                      refine ⟨107632733911648117961009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 287020623764394981229357 107632733911648117961009)
                      ·
                        rfl

theorem cell23_209614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_209614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209614 prefixEnd_209614 := by exact prefixLift 209614
  have htrace : WordTrace (prefixWord ++ tailWord_209614) baseStart_209614 baseEnd_209614 := by
    simpa [prefixWord, tailWord_209614, baseEnd_209614] using wordTrace_append hprefix tailTrace_209614
  have hstable : (prefixWord ++ tailWord_209614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209614).length < 2 ^ (prefixWord ++ tailWord_209614).sum := by decide
  have hdescent : baseEnd_209614 < baseStart_209614 := by decide
  rcases family_descends (prefixWord ++ tailWord_209614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209718 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_209718 : Nat := 118140960795 + 209718 * 2 ^ 59
def prefixEnd_209718 : Nat := 4983230072969 + 3 ^ 40 * 209718 * 2
def baseEnd_209718 : Nat := 107686135899715711060531

theorem tailTrace_209718 : CollatzResearch.WordTrace tailWord_209718 prefixEnd_209718 107686135899715711060531 := by
  unfold tailWord_209718
  simp only [CollatzResearch.WordTrace]
  refine ⟨478065240889686114248363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5099362569489985218649205 478065240889686114248363)
  ·
    refine ⟨717097861334529171372545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478065240889686114248363 717097861334529171372545)
    ·
      refine ⟨537823396000896878529409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717097861334529171372545 537823396000896878529409)
      ·
        refine ⟨403367547000672658897057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537823396000896878529409 403367547000672658897057)
        ·
          refine ⟨302525660250504494172793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403367547000672658897057 302525660250504494172793)
          ·
            refine ⟨226894245187878370629595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302525660250504494172793 226894245187878370629595)
            ·
              refine ⟨340341367781817555944393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226894245187878370629595 340341367781817555944393)
              ·
                refine ⟨255256025836363166958295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340341367781817555944393 255256025836363166958295)
                ·
                  refine ⟨382884038754544750437443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255256025836363166958295 382884038754544750437443)
                  ·
                    refine ⟨574326058131817125656165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 382884038754544750437443 574326058131817125656165)
                    ·
                      refine ⟨107686135899715711060531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 574326058131817125656165 107686135899715711060531)
                      ·
                        rfl

theorem cell23_209718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_209718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209718 prefixEnd_209718 := by exact prefixLift 209718
  have htrace : WordTrace (prefixWord ++ tailWord_209718) baseStart_209718 baseEnd_209718 := by
    simpa [prefixWord, tailWord_209718, baseEnd_209718] using wordTrace_append hprefix tailTrace_209718
  have hstable : (prefixWord ++ tailWord_209718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209718).length < 2 ^ (prefixWord ++ tailWord_209718).sum := by decide
  have hdescent : baseEnd_209718 < baseStart_209718 := by decide
  rcases family_descends (prefixWord ++ tailWord_209718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209744 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 1, 3, 2]
def baseStart_209744 : Nat := 118140960795 + 209744 * 2 ^ 59
def prefixEnd_209744 : Nat := 4983230072969 + 3 ^ 40 * 209744 * 2
def baseEnd_209744 : Nat := 107699486396732609335411

theorem tailTrace_209744 : CollatzResearch.WordTrace tailWord_209744 prefixEnd_209744 107699486396732609335411 := by
  unfold tailWord_209744
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824996076070392134210143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5099994768093856178946857 3824996076070392134210143)
  ·
    refine ⟨5737494114105588201315215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3824996076070392134210143 5737494114105588201315215)
    ·
      refine ⟨8606241171158382301972823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5737494114105588201315215 8606241171158382301972823)
      ·
        refine ⟨12909361756737573452959235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8606241171158382301972823 12909361756737573452959235)
        ·
          refine ⟨19364042635106360179438853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12909361756737573452959235 19364042635106360179438853)
          ·
            refine ⟨3630757994082442533644785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19364042635106360179438853 3630757994082442533644785)
            ·
              refine ⟨2723068495561831900233589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3630757994082442533644785 2723068495561831900233589)
              ·
                refine ⟨255287671458921740646899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2723068495561831900233589 255287671458921740646899)
                ·
                  refine ⟨382931507188382610970349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255287671458921740646899 382931507188382610970349)
                  ·
                    refine ⟨143599315195643479113881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382931507188382610970349 143599315195643479113881)
                    ·
                      refine ⟨107699486396732609335411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143599315195643479113881 107699486396732609335411)
                      ·
                        rfl

theorem cell23_209744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 3, 2].length) (baseStart_209744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209744 prefixEnd_209744 := by exact prefixLift 209744
  have htrace : WordTrace (prefixWord ++ tailWord_209744) baseStart_209744 baseEnd_209744 := by
    simpa [prefixWord, tailWord_209744, baseEnd_209744] using wordTrace_append hprefix tailTrace_209744
  have hstable : (prefixWord ++ tailWord_209744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209744).length < 2 ^ (prefixWord ++ tailWord_209744).sum := by decide
  have hdescent : baseEnd_209744 < baseStart_209744 := by decide
  rcases family_descends (prefixWord ++ tailWord_209744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209751 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_209751 : Nat := 118140960795 + 209751 * 2 ^ 59
def prefixEnd_209751 : Nat := 4983230072969 + 3 ^ 40 * 209751 * 2
def baseEnd_209751 : Nat := 107703080761314081947879

theorem tailTrace_209751 : CollatzResearch.WordTrace tailWord_209751 prefixEnd_209751 107703080761314081947879 := by
  unfold tailWord_209751
  simp only [CollatzResearch.WordTrace]
  refine ⟨7650247463115424463925107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5100164975410282975950071 7650247463115424463925107)
  ·
    refine ⟨11475371194673136695887661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7650247463115424463925107 11475371194673136695887661)
    ·
      refine ⟨4303264198002426260957873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11475371194673136695887661 4303264198002426260957873)
      ·
        refine ⟨3227448148501819695718405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4303264198002426260957873 3227448148501819695718405)
        ·
          refine ⟨605146527844091192947201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3227448148501819695718405 605146527844091192947201)
          ·
            refine ⟨453859895883068394710401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605146527844091192947201 453859895883068394710401)
            ·
              refine ⟨340394921912301296032801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453859895883068394710401 340394921912301296032801)
              ·
                refine ⟨255296191434225972024601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340394921912301296032801 255296191434225972024601)
                ·
                  refine ⟨191472143575669479018451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255296191434225972024601 191472143575669479018451)
                  ·
                    refine ⟨287208215363504218527677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191472143575669479018451 287208215363504218527677)
                    ·
                      refine ⟨107703080761314081947879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 287208215363504218527677 107703080761314081947879)
                      ·
                        rfl

theorem cell23_209751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_209751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209751 prefixEnd_209751 := by exact prefixLift 209751
  have htrace : WordTrace (prefixWord ++ tailWord_209751) baseStart_209751 baseEnd_209751 := by
    simpa [prefixWord, tailWord_209751, baseEnd_209751] using wordTrace_append hprefix tailTrace_209751
  have hstable : (prefixWord ++ tailWord_209751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209751).length < 2 ^ (prefixWord ++ tailWord_209751).sum := by decide
  have hdescent : baseEnd_209751 < baseStart_209751 := by decide
  rcases family_descends (prefixWord ++ tailWord_209751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209767 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 2, 6]
def baseStart_209767 : Nat := 118140960795 + 209767 * 2 ^ 59
def prefixEnd_209767 : Nat := 4983230072969 + 3 ^ 40 * 209767 * 2
def baseEnd_209767 : Nat := 35903765483928673115935

theorem tailTrace_209767 : CollatzResearch.WordTrace tailWord_209767 prefixEnd_209767 35903765483928673115935 := by
  unfold tailWord_209767
  simp only [CollatzResearch.WordTrace]
  refine ⟨7650831031057459196507555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5100554020704972797671703 7650831031057459196507555)
  ·
    refine ⟨11476246546586188794761333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7650831031057459196507555 11476246546586188794761333)
    ·
      refine ⟨1075898113742455199508875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11476246546586188794761333 1075898113742455199508875)
      ·
        refine ⟨1613847170613682799263313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075898113742455199508875 1613847170613682799263313)
        ·
          refine ⟨1210385377960262099447485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613847170613682799263313 1210385377960262099447485)
          ·
            refine ⟨453894516735098287292807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1210385377960262099447485 453894516735098287292807)
            ·
              refine ⟨680841775102647430939211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453894516735098287292807 680841775102647430939211)
              ·
                refine ⟨1021262662653971146408817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680841775102647430939211 1021262662653971146408817)
                ·
                  refine ⟨765946996990478359806613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021262662653971146408817 765946996990478359806613)
                  ·
                    refine ⟨35903765483928673115935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 765946996990478359806613 35903765483928673115935)
                    ·
                      rfl

theorem cell23_209767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_209767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209767 prefixEnd_209767 := by exact prefixLift 209767
  have htrace : WordTrace (prefixWord ++ tailWord_209767) baseStart_209767 baseEnd_209767 := by
    simpa [prefixWord, tailWord_209767, baseEnd_209767] using wordTrace_append hprefix tailTrace_209767
  have hstable : (prefixWord ++ tailWord_209767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209767).length < 2 ^ (prefixWord ++ tailWord_209767).sum := by decide
  have hdescent : baseEnd_209767 < baseStart_209767 := by decide
  rcases family_descends (prefixWord ++ tailWord_209767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209825 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_209825 : Nat := 118140960795 + 209825 * 2 ^ 59
def prefixEnd_209825 : Nat := 4983230072969 + 3 ^ 40 * 209825 * 2
def baseEnd_209825 : Nat := 107741078329746792422539

theorem tailTrace_209825 : CollatzResearch.WordTrace tailWord_209825 prefixEnd_209825 107741078329746792422539 := by
  unfold tailWord_209825
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652946464847335102118929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5101964309898223401412619 7652946464847335102118929)
  ·
    refine ⟨5739709848635501326589197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7652946464847335102118929 5739709848635501326589197)
    ·
      refine ⟨2152391193238312997470949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5739709848635501326589197 2152391193238312997470949)
      ·
        refine ⟨403573348732183687025803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2152391193238312997470949 403573348732183687025803)
        ·
          refine ⟨605360023098275530538705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403573348732183687025803 605360023098275530538705)
          ·
            refine ⟨454020017323706647904029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605360023098275530538705 454020017323706647904029)
            ·
              refine ⟨170257506496389992964011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454020017323706647904029 170257506496389992964011)
              ·
                refine ⟨255386259744584989446017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170257506496389992964011 255386259744584989446017)
                ·
                  refine ⟨191539694808438742084513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255386259744584989446017 191539694808438742084513)
                  ·
                    refine ⟨143654771106329056563385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 191539694808438742084513 143654771106329056563385)
                    ·
                      refine ⟨107741078329746792422539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143654771106329056563385 107741078329746792422539)
                      ·
                        rfl

theorem cell23_209825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_209825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209825 prefixEnd_209825 := by exact prefixLift 209825
  have htrace : WordTrace (prefixWord ++ tailWord_209825) baseStart_209825 baseEnd_209825 := by
    simpa [prefixWord, tailWord_209825, baseEnd_209825] using wordTrace_append hprefix tailTrace_209825
  have hstable : (prefixWord ++ tailWord_209825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209825).length < 2 ^ (prefixWord ++ tailWord_209825).sum := by decide
  have hdescent : baseEnd_209825 < baseStart_209825 := by decide
  rcases family_descends (prefixWord ++ tailWord_209825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209847 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_209847 : Nat := 118140960795 + 209847 * 2 ^ 59
def prefixEnd_209847 : Nat := 4983230072969 + 3 ^ 40 * 209847 * 2
def baseEnd_209847 : Nat := 107752374904145706347437

theorem tailTrace_209847 : CollatzResearch.WordTrace tailWord_209847 prefixEnd_209847 107752374904145706347437 := by
  unfold tailWord_209847
  simp only [CollatzResearch.WordTrace]
  refine ⟨7653748870767632859419795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5102499247178421906279863 7653748870767632859419795)
  ·
    refine ⟨11480623306151449289129693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7653748870767632859419795 11480623306151449289129693)
    ·
      refine ⟨4305233739806793483423635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11480623306151449289129693 4305233739806793483423635)
      ·
        refine ⟨6457850609710190225135453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4305233739806793483423635 6457850609710190225135453)
        ·
          refine ⟨2421693978641321334425795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6457850609710190225135453 2421693978641321334425795)
          ·
            refine ⟨3632540967961982001638693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2421693978641321334425795 3632540967961982001638693)
            ·
              refine ⟨681101431492871625307255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3632540967961982001638693 681101431492871625307255)
              ·
                refine ⟨1021652147239307437960883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681101431492871625307255 1021652147239307437960883)
                ·
                  refine ⟨1532478220858961156941325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021652147239307437960883 1532478220858961156941325)
                  ·
                    refine ⟨574679332822110433852997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1532478220858961156941325 574679332822110433852997)
                    ·
                      refine ⟨107752374904145706347437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 574679332822110433852997 107752374904145706347437)
                      ·
                        rfl

theorem cell23_209847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_209847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209847 prefixEnd_209847 := by exact prefixLift 209847
  have htrace : WordTrace (prefixWord ++ tailWord_209847) baseStart_209847 baseEnd_209847 := by
    simpa [prefixWord, tailWord_209847, baseEnd_209847] using wordTrace_append hprefix tailTrace_209847
  have hstable : (prefixWord ++ tailWord_209847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209847).length < 2 ^ (prefixWord ++ tailWord_209847).sum := by decide
  have hdescent : baseEnd_209847 < baseStart_209847 := by decide
  rcases family_descends (prefixWord ++ tailWord_209847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209934 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_209934 : Nat := 118140960795 + 209934 * 2 ^ 59
def prefixEnd_209934 : Nat := 4983230072969 + 3 ^ 40 * 209934 * 2
def baseEnd_209934 : Nat := 35932349240362288653179

theorem tailTrace_209934 : CollatzResearch.WordTrace tailWord_209934 prefixEnd_209934 35932349240362288653179 := by
  unfold tailWord_209934
  simp only [CollatzResearch.WordTrace]
  refine ⟨957115252681555839729607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5104614680968297811891237 957115252681555839729607)
  ·
    refine ⟨1435672879022333759594411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 957115252681555839729607 1435672879022333759594411)
    ·
      refine ⟨2153509318533500639391617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435672879022333759594411 2153509318533500639391617)
      ·
        refine ⟨1615131988900125479543713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2153509318533500639391617 1615131988900125479543713)
        ·
          refine ⟨1211348991675094109657785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615131988900125479543713 1211348991675094109657785)
          ·
            refine ⟨908511743756320582243339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211348991675094109657785 908511743756320582243339)
            ·
              refine ⟨1362767615634480873365009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908511743756320582243339 1362767615634480873365009)
              ·
                refine ⟨1022075711725860655023757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362767615634480873365009 1022075711725860655023757)
                ·
                  refine ⟨383278391897197745633909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022075711725860655023757 383278391897197745633909)
                  ·
                    refine ⟨35932349240362288653179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 383278391897197745633909 35932349240362288653179)
                    ·
                      rfl

theorem cell23_209934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_209934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209934 prefixEnd_209934 := by exact prefixLift 209934
  have htrace : WordTrace (prefixWord ++ tailWord_209934) baseStart_209934 baseEnd_209934 := by
    simpa [prefixWord, tailWord_209934, baseEnd_209934] using wordTrace_append hprefix tailTrace_209934
  have hstable : (prefixWord ++ tailWord_209934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209934).length < 2 ^ (prefixWord ++ tailWord_209934).sum := by decide
  have hdescent : baseEnd_209934 < baseStart_209934 := by decide
  rcases family_descends (prefixWord ++ tailWord_209934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209948 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_209948 : Nat := 118140960795 + 209948 * 2 ^ 59
def prefixEnd_209948 : Nat := 4983230072969 + 3 ^ 40 * 209948 * 2
def baseEnd_209948 : Nat := 107804236450249811184473

theorem tailTrace_209948 : CollatzResearch.WordTrace tailWord_209948 prefixEnd_209948 107804236450249811184473 := by
  unfold tailWord_209948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3828716321700863554423249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5104955095601151405897665 3828716321700863554423249)
  ·
    refine ⟨2871537241275647665817437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3828716321700863554423249 2871537241275647665817437)
    ·
      refine ⟨1076826465478367874681539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2871537241275647665817437 1076826465478367874681539)
      ·
        refine ⟨1615239698217551812022309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076826465478367874681539 1615239698217551812022309)
        ·
          refine ⟨302857443415790964754183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1615239698217551812022309 302857443415790964754183)
          ·
            refine ⟨454286165123686447131275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302857443415790964754183 454286165123686447131275)
            ·
              refine ⟨681429247685529670696913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454286165123686447131275 681429247685529670696913)
              ·
                refine ⟨511071935764147253022685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681429247685529670696913 511071935764147253022685)
                ·
                  refine ⟨191651975911555219883507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511071935764147253022685 191651975911555219883507)
                  ·
                    refine ⟨287477963867332829825261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191651975911555219883507 287477963867332829825261)
                    ·
                      refine ⟨107804236450249811184473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 287477963867332829825261 107804236450249811184473)
                      ·
                        rfl

theorem cell23_209948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_209948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209948 prefixEnd_209948 := by exact prefixLift 209948
  have htrace : WordTrace (prefixWord ++ tailWord_209948) baseStart_209948 baseEnd_209948 := by
    simpa [prefixWord, tailWord_209948, baseEnd_209948] using wordTrace_append hprefix tailTrace_209948
  have hstable : (prefixWord ++ tailWord_209948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209948).length < 2 ^ (prefixWord ++ tailWord_209948).sum := by decide
  have hdescent : baseEnd_209948 < baseStart_209948 := by decide
  rcases family_descends (prefixWord ++ tailWord_209948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209964 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_209964 : Nat := 118140960795 + 209964 * 2 ^ 59
def prefixEnd_209964 : Nat := 4983230072969 + 3 ^ 40 * 209964 * 2
def baseEnd_209964 : Nat := 35937484046907249528133

theorem tailTrace_209964 : CollatzResearch.WordTrace tailWord_209964 prefixEnd_209964 35937484046907249528133 := by
  unfold tailWord_209964
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829008105671880920714473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5105344140895841227619297 3829008105671880920714473)
  ·
    refine ⟨2871756079253910690535855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3829008105671880920714473 2871756079253910690535855)
    ·
      refine ⟨4307634118880866035803783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2871756079253910690535855 4307634118880866035803783)
      ·
        refine ⟨6461451178321299053705675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307634118880866035803783 6461451178321299053705675)
        ·
          refine ⟨9692176767481948580558513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461451178321299053705675 9692176767481948580558513)
          ·
            refine ⟨7269132575611461435418885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9692176767481948580558513 7269132575611461435418885)
            ·
              refine ⟨1362962357927149019141041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7269132575611461435418885 1362962357927149019141041)
              ·
                refine ⟨1022221768445361764355781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362962357927149019141041 1022221768445361764355781)
                ·
                  refine ⟨191666581583505330816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022221768445361764355781 191666581583505330816709)
                  ·
                    refine ⟨35937484046907249528133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191666581583505330816709 35937484046907249528133)
                    ·
                      rfl

theorem cell23_209964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_209964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209964 prefixEnd_209964 := by exact prefixLift 209964
  have htrace : WordTrace (prefixWord ++ tailWord_209964) baseStart_209964 baseEnd_209964 := by
    simpa [prefixWord, tailWord_209964, baseEnd_209964] using wordTrace_append hprefix tailTrace_209964
  have hstable : (prefixWord ++ tailWord_209964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209964).length < 2 ^ (prefixWord ++ tailWord_209964).sum := by decide
  have hdescent : baseEnd_209964 < baseStart_209964 := by decide
  rcases family_descends (prefixWord ++ tailWord_209964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209967 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 4]
def baseStart_209967 : Nat := 118140960795 + 209967 * 2 ^ 59
def prefixEnd_209967 : Nat := 4983230072969 + 3 ^ 40 * 209967 * 2
def baseEnd_209967 : Nat := 107813992582685236846885

theorem tailTrace_209967 : CollatzResearch.WordTrace tailWord_209967 prefixEnd_209967 107813992582685236846885 := by
  unfold tailWord_209967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658125630332893353788155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5105417086888595569192103 7658125630332893353788155)
  ·
    refine ⟨11487188445499340030682233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658125630332893353788155 11487188445499340030682233)
    ·
      refine ⟨8615391334124505023011675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11487188445499340030682233 8615391334124505023011675)
      ·
        refine ⟨12923087001186757534517513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615391334124505023011675 12923087001186757534517513)
        ·
          refine ⟨9692315250890068150888135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12923087001186757534517513 9692315250890068150888135)
          ·
            refine ⟨14538472876335102226332203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9692315250890068150888135 14538472876335102226332203)
            ·
              refine ⟨21807709314502653339498305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14538472876335102226332203 21807709314502653339498305)
              ·
                refine ⟨16355781985876990004623729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21807709314502653339498305 16355781985876990004623729)
                ·
                  refine ⟨12266836489407742503467797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16355781985876990004623729 12266836489407742503467797)
                  ·
                    refine ⟨575007960440987929850053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12266836489407742503467797 575007960440987929850053)
                    ·
                      refine ⟨107813992582685236846885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 575007960440987929850053 107813992582685236846885)
                      ·
                        rfl

theorem cell23_209967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_209967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209967 prefixEnd_209967 := by exact prefixLift 209967
  have htrace : WordTrace (prefixWord ++ tailWord_209967) baseStart_209967 baseEnd_209967 := by
    simpa [prefixWord, tailWord_209967, baseEnd_209967] using wordTrace_append hprefix tailTrace_209967
  have hstable : (prefixWord ++ tailWord_209967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209967).length < 2 ^ (prefixWord ++ tailWord_209967).sum := by decide
  have hdescent : baseEnd_209967 < baseStart_209967 := by decide
  rcases family_descends (prefixWord ++ tailWord_209967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209971 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 7, 2, 2]
def baseStart_209971 : Nat := 118140960795 + 209971 * 2 ^ 59
def prefixEnd_209971 : Nat := 4983230072969 + 3 ^ 40 * 209971 * 2
def baseEnd_209971 : Nat := 107816046505303221196867

theorem tailTrace_209971 : CollatzResearch.WordTrace tailWord_209971 prefixEnd_209971 107816046505303221196867 := by
  unfold tailWord_209971
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658271522318402036933767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5105514348212268024622511 7658271522318402036933767)
  ·
    refine ⟨11487407283477603055400651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658271522318402036933767 11487407283477603055400651)
    ·
      refine ⟨17231110925216404583100977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11487407283477603055400651 17231110925216404583100977)
      ·
        refine ⟨12923333193912303437325733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17231110925216404583100977 12923333193912303437325733)
        ·
          refine ⟨2423124973858556894498575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12923333193912303437325733 2423124973858556894498575)
          ·
            refine ⟨3634687460787835341747863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423124973858556894498575 3634687460787835341747863)
            ·
              refine ⟨5452031191181753012621795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634687460787835341747863 5452031191181753012621795)
              ·
                refine ⟨8178046786772629518932693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452031191181753012621795 8178046786772629518932693)
                ·
                  refine ⟨191672971564983504349985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8178046786772629518932693 191672971564983504349985)
                  ·
                    refine ⟨143754728673737628262489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 191672971564983504349985 143754728673737628262489)
                    ·
                      refine ⟨107816046505303221196867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 143754728673737628262489 107816046505303221196867)
                      ·
                        rfl

theorem cell23_209971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 2, 2].length) (baseStart_209971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209971 prefixEnd_209971 := by exact prefixLift 209971
  have htrace : WordTrace (prefixWord ++ tailWord_209971) baseStart_209971 baseEnd_209971 := by
    simpa [prefixWord, tailWord_209971, baseEnd_209971] using wordTrace_append hprefix tailTrace_209971
  have hstable : (prefixWord ++ tailWord_209971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209971).length < 2 ^ (prefixWord ++ tailWord_209971).sum := by decide
  have hdescent : baseEnd_209971 < baseStart_209971 := by decide
  rcases family_descends (prefixWord ++ tailWord_209971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209981 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_209981 : Nat := 118140960795 + 209981 * 2 ^ 59
def prefixEnd_209981 : Nat := 4983230072969 + 3 ^ 40 * 209981 * 2
def baseEnd_209981 : Nat := 35940393770616060690607

theorem tailTrace_209981 : CollatzResearch.WordTrace tailWord_209981 prefixEnd_209981 35940393770616060690607 := by
  unfold tailWord_209981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658636252282173744797797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5105757501521449163198531 7658636252282173744797797)
  ·
    refine ⟨1435994297302907577149587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7658636252282173744797797 1435994297302907577149587)
    ·
      refine ⟨2153991445954361365724381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435994297302907577149587 2153991445954361365724381)
      ·
        refine ⟨807746792232885512146643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2153991445954361365724381 807746792232885512146643)
        ·
          refine ⟨1211620188349328268219965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807746792232885512146643 1211620188349328268219965)
          ·
            refine ⟨454357570630998100582487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1211620188349328268219965 454357570630998100582487)
            ·
              refine ⟨681536355946497150873731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454357570630998100582487 681536355946497150873731)
              ·
                refine ⟨1022304533919745726310597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681536355946497150873731 1022304533919745726310597)
                ·
                  refine ⟨191682100109952323683237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022304533919745726310597 191682100109952323683237)
                  ·
                    refine ⟨35940393770616060690607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191682100109952323683237 35940393770616060690607)
                    ·
                      rfl

theorem cell23_209981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_209981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209981 prefixEnd_209981 := by exact prefixLift 209981
  have htrace : WordTrace (prefixWord ++ tailWord_209981) baseStart_209981 baseEnd_209981 := by
    simpa [prefixWord, tailWord_209981, baseEnd_209981] using wordTrace_append hprefix tailTrace_209981
  have hstable : (prefixWord ++ tailWord_209981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209981).length < 2 ^ (prefixWord ++ tailWord_209981).sum := by decide
  have hdescent : baseEnd_209981 < baseStart_209981 := by decide
  rcases family_descends (prefixWord ++ tailWord_209981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_209998 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_209998 : Nat := 118140960795 + 209998 * 2 ^ 59
def prefixEnd_209998 : Nat := 4983230072969 + 3 ^ 40 * 209998 * 2
def baseEnd_209998 : Nat := 35943303494324871853081

theorem tailTrace_209998 : CollatzResearch.WordTrace tailWord_209998 prefixEnd_209998 35943303494324871853081 := by
  unfold tailWord_209998
  simp only [CollatzResearch.WordTrace]
  refine ⟨957407036652573206020831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5106170862147057098777765 957407036652573206020831)
  ·
    refine ⟨1436110554978859809031247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 957407036652573206020831 1436110554978859809031247)
    ·
      refine ⟨2154165832468289713546871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436110554978859809031247 2154165832468289713546871)
      ·
        refine ⟨3231248748702434570320307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154165832468289713546871 3231248748702434570320307)
        ·
          refine ⟨4846873123053651855480461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231248748702434570320307 4846873123053651855480461)
          ·
            refine ⟨1817577421145119445805173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4846873123053651855480461 1817577421145119445805173)
            ·
              refine ⟨170397883232354948044235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1817577421145119445805173 170397883232354948044235)
              ·
                refine ⟨255596824848532422066353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170397883232354948044235 255596824848532422066353)
                ·
                  refine ⟨191697618636399316549765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255596824848532422066353 191697618636399316549765)
                  ·
                    refine ⟨35943303494324871853081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191697618636399316549765 35943303494324871853081)
                    ·
                      rfl

theorem cell23_209998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_209998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_209998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_209998 prefixEnd_209998 := by exact prefixLift 209998
  have htrace : WordTrace (prefixWord ++ tailWord_209998) baseStart_209998 baseEnd_209998 := by
    simpa [prefixWord, tailWord_209998, baseEnd_209998] using wordTrace_append hprefix tailTrace_209998
  have hstable : (prefixWord ++ tailWord_209998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_209998).length < 2 ^ (prefixWord ++ tailWord_209998).sum := by decide
  have hdescent : baseEnd_209998 < baseStart_209998 := by decide
  rcases family_descends (prefixWord ++ tailWord_209998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210021 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_210021 : Nat := 118140960795 + 210021 * 2 ^ 59
def prefixEnd_210021 : Nat := 4983230072969 + 3 ^ 40 * 210021 * 2
def baseEnd_210021 : Nat := 107841720538028025571637

theorem tailTrace_210021 : CollatzResearch.WordTrace tailWord_210021 prefixEnd_210021 107841720538028025571637 := by
  unfold tailWord_210021
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660095172137260576253917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5106730114758173717502611 7660095172137260576253917)
  ·
    refine ⟨2872535689551472716095219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7660095172137260576253917 2872535689551472716095219)
    ·
      refine ⟨4308803534327209074142829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872535689551472716095219 4308803534327209074142829)
      ·
        refine ⟨1615801325372703402803561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4308803534327209074142829 1615801325372703402803561)
        ·
          refine ⟨1211850994029527552102671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615801325372703402803561 1211850994029527552102671)
          ·
            refine ⟨1817776491044291328154007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211850994029527552102671 1817776491044291328154007)
            ·
              refine ⟨2726664736566436992231011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817776491044291328154007 2726664736566436992231011)
              ·
                refine ⟨4089997104849655488346517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726664736566436992231011 4089997104849655488346517)
                ·
                  refine ⟨191718614289827601016243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4089997104849655488346517 191718614289827601016243)
                  ·
                    refine ⟨287577921434741401524365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191718614289827601016243 287577921434741401524365)
                    ·
                      refine ⟨107841720538028025571637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 287577921434741401524365 107841720538028025571637)
                      ·
                        rfl

theorem cell23_210021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_210021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210021 prefixEnd_210021 := by exact prefixLift 210021
  have htrace : WordTrace (prefixWord ++ tailWord_210021) baseStart_210021 baseEnd_210021 := by
    simpa [prefixWord, tailWord_210021, baseEnd_210021] using wordTrace_append hprefix tailTrace_210021
  have hstable : (prefixWord ++ tailWord_210021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210021).length < 2 ^ (prefixWord ++ tailWord_210021).sum := by decide
  have hdescent : baseEnd_210021 < baseStart_210021 := by decide
  rcases family_descends (prefixWord ++ tailWord_210021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210027 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8]
def baseStart_210027 : Nat := 118140960795 + 210027 * 2 ^ 59
def prefixEnd_210027 : Nat := 4983230072969 + 3 ^ 40 * 210027 * 2
def baseEnd_210027 : Nat := 107844801421955002096609

theorem tailTrace_210027 : CollatzResearch.WordTrace tailWord_210027 prefixEnd_210027 107844801421955002096609 := by
  unfold tailWord_210027
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660314010115523600972335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5106876006743682400648223 7660314010115523600972335)
  ·
    refine ⟨11490471015173285401458503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7660314010115523600972335 11490471015173285401458503)
    ·
      refine ⟨17235706522759928102187755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11490471015173285401458503 17235706522759928102187755)
      ·
        refine ⟨25853559784139892153281633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17235706522759928102187755 25853559784139892153281633)
        ·
          refine ⟨19390169838104919114961225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25853559784139892153281633 19390169838104919114961225)
          ·
            refine ⟨14542627378578689336220919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19390169838104919114961225 14542627378578689336220919)
            ·
              refine ⟨21813941067868034004331379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14542627378578689336220919 21813941067868034004331379)
              ·
                refine ⟨32720911601802051006497069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21813941067868034004331379 32720911601802051006497069)
                ·
                  refine ⟨12270341850675769127436401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32720911601802051006497069 12270341850675769127436401)
                  ·
                    refine ⟨9202756388006826845577301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12270341850675769127436401 9202756388006826845577301)
                    ·
                      refine ⟨107844801421955002096609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 9202756388006826845577301 107844801421955002096609)
                      ·
                        rfl

theorem cell23_210027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_210027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210027 prefixEnd_210027 := by exact prefixLift 210027
  have htrace : WordTrace (prefixWord ++ tailWord_210027) baseStart_210027 baseEnd_210027 := by
    simpa [prefixWord, tailWord_210027, baseEnd_210027] using wordTrace_append hprefix tailTrace_210027
  have hstable : (prefixWord ++ tailWord_210027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210027).length < 2 ^ (prefixWord ++ tailWord_210027).sum := by decide
  have hdescent : baseEnd_210027 < baseStart_210027 := by decide
  rcases family_descends (prefixWord ++ tailWord_210027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210034 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_210034 : Nat := 118140960795 + 210034 * 2 ^ 59
def prefixEnd_210034 : Nat := 4983230072969 + 3 ^ 40 * 210034 * 2
def baseEnd_210034 : Nat := 107848395786536474709077

theorem tailTrace_210034 : CollatzResearch.WordTrace tailWord_210034 prefixEnd_210034 107848395786536474709077 := by
  unfold tailWord_210034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915142330272540949119289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5107046214060109197651437 1915142330272540949119289)
  ·
    refine ⟨1436356747704405711839467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1915142330272540949119289 1436356747704405711839467)
    ·
      refine ⟨2154535121556608567759201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436356747704405711839467 2154535121556608567759201)
      ·
        refine ⟨1615901341167456425819401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2154535121556608567759201 1615901341167456425819401)
        ·
          refine ⟨1211926005875592319364551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615901341167456425819401 1211926005875592319364551)
          ·
            refine ⟨1817889008813388479046827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211926005875592319364551 1817889008813388479046827)
            ·
              refine ⟨2726833513220082718570241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817889008813388479046827 2726833513220082718570241)
              ·
                refine ⟨2045125134915062038927681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726833513220082718570241 2045125134915062038927681)
                ·
                  refine ⟨1533843851186296529195761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2045125134915062038927681 1533843851186296529195761)
                  ·
                    refine ⟨1150382888389722396896821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1533843851186296529195761 1150382888389722396896821)
                    ·
                      refine ⟨107848395786536474709077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1150382888389722396896821 107848395786536474709077)
                      ·
                        rfl

theorem cell23_210034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_210034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210034 prefixEnd_210034 := by exact prefixLift 210034
  have htrace : WordTrace (prefixWord ++ tailWord_210034) baseStart_210034 baseEnd_210034 := by
    simpa [prefixWord, tailWord_210034, baseEnd_210034] using wordTrace_append hprefix tailTrace_210034
  have hstable : (prefixWord ++ tailWord_210034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210034).length < 2 ^ (prefixWord ++ tailWord_210034).sum := by decide
  have hdescent : baseEnd_210034 < baseStart_210034 := by decide
  rcases family_descends (prefixWord ++ tailWord_210034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210038 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_210038 : Nat := 118140960795 + 210038 * 2 ^ 59
def prefixEnd_210038 : Nat := 4983230072969 + 3 ^ 40 * 210038 * 2
def baseEnd_210038 : Nat := 107850449709154459059059

theorem tailTrace_210038 : CollatzResearch.WordTrace tailWord_210038 prefixEnd_210038 107850449709154459059059 := by
  unfold tailWord_210038
  simp only [CollatzResearch.WordTrace]
  refine ⟨478794700817229529976423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5107143475383781653081845 478794700817229529976423)
  ·
    refine ⟨718192051225844294964635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478794700817229529976423 718192051225844294964635)
    ·
      refine ⟨1077288076838766442446953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718192051225844294964635 1077288076838766442446953)
      ·
        refine ⟨807966057629074831835215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1077288076838766442446953 807966057629074831835215)
        ·
          refine ⟨1211949086443612247752823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807966057629074831835215 1211949086443612247752823)
          ·
            refine ⟨1817923629665418371629235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211949086443612247752823 1817923629665418371629235)
            ·
              refine ⟨2726885444498127557443853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817923629665418371629235 2726885444498127557443853)
              ·
                refine ⟨1022582041686797834041445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2726885444498127557443853 1022582041686797834041445)
                ·
                  refine ⟨191734132816274593882771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1022582041686797834041445 191734132816274593882771)
                  ·
                    refine ⟨287601199224411890824157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191734132816274593882771 287601199224411890824157)
                    ·
                      refine ⟨107850449709154459059059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 287601199224411890824157 107850449709154459059059)
                      ·
                        rfl

theorem cell23_210038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_210038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210038 prefixEnd_210038 := by exact prefixLift 210038
  have htrace : WordTrace (prefixWord ++ tailWord_210038) baseStart_210038 baseEnd_210038 := by
    simpa [prefixWord, tailWord_210038, baseEnd_210038] using wordTrace_append hprefix tailTrace_210038
  have hstable : (prefixWord ++ tailWord_210038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210038).length < 2 ^ (prefixWord ++ tailWord_210038).sum := by decide
  have hdescent : baseEnd_210038 < baseStart_210038 := by decide
  rcases family_descends (prefixWord ++ tailWord_210038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210044 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_210044 : Nat := 118140960795 + 210044 * 2 ^ 59
def prefixEnd_210044 : Nat := 4983230072969 + 3 ^ 40 * 210044 * 2
def baseEnd_210044 : Nat := 107853530593081435584031

theorem tailTrace_210044 : CollatzResearch.WordTrace tailWord_210044 prefixEnd_210044 107853530593081435584031 := by
  unfold tailWord_210044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830467025526967752170593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5107289367369290336227457 3830467025526967752170593)
  ·
    refine ⟨2872850269145225814127945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3830467025526967752170593 2872850269145225814127945)
    ·
      refine ⟨2154637701858919360595959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2872850269145225814127945 2154637701858919360595959)
      ·
        refine ⟨3231956552788379040893939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154637701858919360595959 3231956552788379040893939)
        ·
          refine ⟨4847934829182568561340909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231956552788379040893939 4847934829182568561340909)
          ·
            refine ⟨1817975560943463210502841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4847934829182568561340909 1817975560943463210502841)
            ·
              refine ⟨1363481670707597407877131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817975560943463210502841 1363481670707597407877131)
              ·
                refine ⟨2045222506061396111815697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363481670707597407877131 2045222506061396111815697)
                ·
                  refine ⟨1533916879546047083861773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2045222506061396111815697 1533916879546047083861773)
                  ·
                    refine ⟨575218829829767656448165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533916879546047083861773 575218829829767656448165)
                    ·
                      refine ⟨107853530593081435584031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 575218829829767656448165 107853530593081435584031)
                      ·
                        rfl

theorem cell23_210044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_210044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210044 prefixEnd_210044 := by exact prefixLift 210044
  have htrace : WordTrace (prefixWord ++ tailWord_210044) baseStart_210044 baseEnd_210044 := by
    simpa [prefixWord, tailWord_210044, baseEnd_210044] using wordTrace_append hprefix tailTrace_210044
  have hstable : (prefixWord ++ tailWord_210044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210044).length < 2 ^ (prefixWord ++ tailWord_210044).sum := by decide
  have hdescent : baseEnd_210044 < baseStart_210044 := by decide
  rcases family_descends (prefixWord ++ tailWord_210044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210064 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3]
def baseStart_210064 : Nat := 118140960795 + 210064 * 2 ^ 59
def prefixEnd_210064 : Nat := 4983230072969 + 3 ^ 40 * 210064 * 2
def baseEnd_210064 : Nat := 107863800206171357333939

theorem tailTrace_210064 : CollatzResearch.WordTrace tailWord_210064 prefixEnd_210064 107863800206171357333939 := by
  unfold tailWord_210064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3830831755490739460034623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5107775673987652613379497 3830831755490739460034623)
  ·
    refine ⟨5746247633236109190051935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3830831755490739460034623 5746247633236109190051935)
    ·
      refine ⟨8619371449854163785077903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746247633236109190051935 8619371449854163785077903)
      ·
        refine ⟨12929057174781245677616855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619371449854163785077903 12929057174781245677616855)
        ·
          refine ⟨19393585762171868516425283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12929057174781245677616855 19393585762171868516425283)
          ·
            refine ⟨29090378643257802774637925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19393585762171868516425283 29090378643257802774637925)
            ·
              refine ⟨5454445995610838020244611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29090378643257802774637925 5454445995610838020244611)
              ·
                refine ⟨8181668993416257030366917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454445995610838020244611 8181668993416257030366917)
                ·
                  refine ⟨1534062936265548193193797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8181668993416257030366917 1534062936265548193193797)
                  ·
                    refine ⟨287636800549790286223837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1534062936265548193193797 287636800549790286223837)
                    ·
                      refine ⟨107863800206171357333939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 287636800549790286223837 107863800206171357333939)
                      ·
                        rfl

theorem cell23_210064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_210064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210064 prefixEnd_210064 := by exact prefixLift 210064
  have htrace : WordTrace (prefixWord ++ tailWord_210064) baseStart_210064 baseEnd_210064 := by
    simpa [prefixWord, tailWord_210064, baseEnd_210064] using wordTrace_append hprefix tailTrace_210064
  have hstable : (prefixWord ++ tailWord_210064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210064).length < 2 ^ (prefixWord ++ tailWord_210064).sum := by decide
  have hdescent : baseEnd_210064 < baseStart_210064 := by decide
  rcases family_descends (prefixWord ++ tailWord_210064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210205 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_210205 : Nat := 118140960795 + 210205 * 2 ^ 59
def prefixEnd_210205 : Nat := 4983230072969 + 3 ^ 40 * 210205 * 2
def baseEnd_210205 : Nat := 107936200978455305670791

theorem tailTrace_210205 : CollatzResearch.WordTrace tailWord_210205 prefixEnd_210205 107936200978455305670791 := by
  unfold tailWord_210205
  simp only [CollatzResearch.WordTrace]
  refine ⟨7666806203470660000952069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5111204135647106667301379 7666806203470660000952069)
  ·
    refine ⟨1437526163150748750178513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7666806203470660000952069 1437526163150748750178513)
    ·
      refine ⟨1078144622363061562633885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1437526163150748750178513 1078144622363061562633885)
      ·
        refine ⟨404304233386148085987707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1078144622363061562633885 404304233386148085987707)
        ·
          refine ⟨606456350079222128981561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404304233386148085987707 606456350079222128981561)
          ·
            refine ⟨454842262559416596736171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606456350079222128981561 454842262559416596736171)
            ·
              refine ⟨682263393839124895104257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454842262559416596736171 682263393839124895104257)
              ·
                refine ⟨511697545379343671328193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682263393839124895104257 511697545379343671328193)
                ·
                  refine ⟨383773159034507753496145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511697545379343671328193 383773159034507753496145)
                  ·
                    refine ⟨287829869275880815122109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383773159034507753496145 287829869275880815122109)
                    ·
                      refine ⟨107936200978455305670791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 287829869275880815122109 107936200978455305670791)
                      ·
                        rfl

theorem cell23_210205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_210205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210205 prefixEnd_210205 := by exact prefixLift 210205
  have htrace : WordTrace (prefixWord ++ tailWord_210205) baseStart_210205 baseEnd_210205 := by
    simpa [prefixWord, tailWord_210205, baseEnd_210205] using wordTrace_append hprefix tailTrace_210205
  have hstable : (prefixWord ++ tailWord_210205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210205).length < 2 ^ (prefixWord ++ tailWord_210205).sum := by decide
  have hdescent : baseEnd_210205 < baseStart_210205 := by decide
  rcases family_descends (prefixWord ++ tailWord_210205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210212 : List Nat := [2, 3, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_210212 : Nat := 118140960795 + 210212 * 2 ^ 59
def prefixEnd_210212 : Nat := 4983230072969 + 3 ^ 40 * 210212 * 2
def baseEnd_210212 : Nat := 35979931781012259427753

theorem tailTrace_210212 : CollatzResearch.WordTrace tailWord_210212 prefixEnd_210212 35979931781012259427753 := by
  unfold tailWord_210212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833530757222650098228445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5111374342963533464304593 3833530757222650098228445)
  ·
    refine ⟨1437574033958493786835667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3833530757222650098228445 1437574033958493786835667)
    ·
      refine ⟨2156361050937740680253501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437574033958493786835667 2156361050937740680253501)
      ·
        refine ⟨808635394101652755095063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2156361050937740680253501 808635394101652755095063)
        ·
          refine ⟨1212953091152479132642595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808635394101652755095063 1212953091152479132642595)
          ·
            refine ⟨1819429636728718698963893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212953091152479132642595 1819429636728718698963893)
            ·
              refine ⟨170571528443317378027865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1819429636728718698963893 170571528443317378027865)
              ·
                refine ⟨127928646332488033520899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170571528443317378027865 127928646332488033520899)
                ·
                  refine ⟨191892969498732050281349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127928646332488033520899 191892969498732050281349)
                  ·
                    refine ⟨35979931781012259427753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191892969498732050281349 35979931781012259427753)
                    ·
                      rfl

theorem cell23_210212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_210212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210212 prefixEnd_210212 := by exact prefixLift 210212
  have htrace : WordTrace (prefixWord ++ tailWord_210212) baseStart_210212 baseEnd_210212 := by
    simpa [prefixWord, tailWord_210212, baseEnd_210212] using wordTrace_append hprefix tailTrace_210212
  have hstable : (prefixWord ++ tailWord_210212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210212).length < 2 ^ (prefixWord ++ tailWord_210212).sum := by decide
  have hdescent : baseEnd_210212 < baseStart_210212 := by decide
  rcases family_descends (prefixWord ++ tailWord_210212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210225 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 6]
def baseStart_210225 : Nat := 118140960795 + 210225 * 2 ^ 59
def prefixEnd_210225 : Nat := 4983230072969 + 3 ^ 40 * 210225 * 2
def baseEnd_210225 : Nat := 11994052287949469713411

theorem tailTrace_210225 : CollatzResearch.WordTrace tailWord_210225 prefixEnd_210225 11994052287949469713411 := by
  unfold tailWord_210225
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667535663398203416680129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5111690442265468944453419 7667535663398203416680129)
  ·
    refine ⟨5750651747548652562510097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7667535663398203416680129 5750651747548652562510097)
    ·
      refine ⟨4312988810661489421882573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5750651747548652562510097 4312988810661489421882573)
      ·
        refine ⟨1617370803998058533205965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4312988810661489421882573 1617370803998058533205965)
        ·
          refine ⟨606514051499271949952237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1617370803998058533205965 606514051499271949952237)
          ·
            refine ⟨227442769312226981232089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 606514051499271949952237 227442769312226981232089)
            ·
              refine ⟨170582076984170235924067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227442769312226981232089 170582076984170235924067)
              ·
                refine ⟨255873115476255353886101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170582076984170235924067 255873115476255353886101)
                ·
                  refine ⟨11994052287949469713411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 255873115476255353886101 11994052287949469713411)
                  ·
                    rfl

theorem cell23_210225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 6].length) (baseStart_210225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210225 prefixEnd_210225 := by exact prefixLift 210225
  have htrace : WordTrace (prefixWord ++ tailWord_210225) baseStart_210225 baseEnd_210225 := by
    simpa [prefixWord, tailWord_210225, baseEnd_210225] using wordTrace_append hprefix tailTrace_210225
  have hstable : (prefixWord ++ tailWord_210225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210225).length < 2 ^ (prefixWord ++ tailWord_210225).sum := by decide
  have hdescent : baseEnd_210225 < baseStart_210225 := by decide
  rcases family_descends (prefixWord ++ tailWord_210225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210238 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_210238 : Nat := 118140960795 + 210238 * 2 ^ 59
def prefixEnd_210238 : Nat := 4983230072969 + 3 ^ 40 * 210238 * 2
def baseEnd_210238 : Nat := 35984381946684558852713

theorem tailTrace_210238 : CollatzResearch.WordTrace tailWord_210238 prefixEnd_210238 35984381946684558852713 := by
  unfold tailWord_210238
  simp only [CollatzResearch.WordTrace]
  refine ⟨958501226543888329612921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5112006541567404424602245 958501226543888329612921)
  ·
    refine ⟨718875919907916247209691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 958501226543888329612921 718875919907916247209691)
    ·
      refine ⟨1078313879861874370814537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718875919907916247209691 1078313879861874370814537)
      ·
        refine ⟨808735409896405778110903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1078313879861874370814537 808735409896405778110903)
        ·
          refine ⟨1213103114844608667166355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808735409896405778110903 1213103114844608667166355)
          ·
            refine ⟨1819654672266913000749533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213103114844608667166355 1819654672266913000749533)
            ·
              refine ⟨682370502100092375281075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1819654672266913000749533 682370502100092375281075)
              ·
                refine ⟨1023555753150138562921613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682370502100092375281075 1023555753150138562921613)
                ·
                  refine ⟨383833407431301961095605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023555753150138562921613 383833407431301961095605)
                  ·
                    refine ⟨35984381946684558852713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 383833407431301961095605 35984381946684558852713)
                    ·
                      rfl

theorem cell23_210238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_210238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210238 prefixEnd_210238 := by exact prefixLift 210238
  have htrace : WordTrace (prefixWord ++ tailWord_210238) baseStart_210238 baseEnd_210238 := by
    simpa [prefixWord, tailWord_210238, baseEnd_210238] using wordTrace_append hprefix tailTrace_210238
  have hstable : (prefixWord ++ tailWord_210238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210238).length < 2 ^ (prefixWord ++ tailWord_210238).sum := by decide
  have hdescent : baseEnd_210238 < baseStart_210238 := by decide
  rcases family_descends (prefixWord ++ tailWord_210238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210271 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 4]
def baseStart_210271 : Nat := 118140960795 + 210271 * 2 ^ 59
def prefixEnd_210271 : Nat := 4983230072969 + 3 ^ 40 * 210271 * 2
def baseEnd_210271 : Nat := 107970090701652047445487

theorem tailTrace_210271 : CollatzResearch.WordTrace tailWord_210271 prefixEnd_210271 107970090701652047445487 := by
  unfold tailWord_210271
  simp only [CollatzResearch.WordTrace]
  refine ⟨7669213421231553272854667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5112808947487702181903111 7669213421231553272854667)
  ·
    refine ⟨11503820131847329909282001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7669213421231553272854667 11503820131847329909282001)
    ·
      refine ⟨8627865098885497431961501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11503820131847329909282001 8627865098885497431961501)
      ·
        refine ⟨3235449412082061536985563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8627865098885497431961501 3235449412082061536985563)
        ·
          refine ⟨4853174118123092305478345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235449412082061536985563 4853174118123092305478345)
          ·
            refine ⟨3639880588592319229108759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4853174118123092305478345 3639880588592319229108759)
            ·
              refine ⟨5459820882888478843663139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639880588592319229108759 5459820882888478843663139)
              ·
                refine ⟨8189731324332718265494709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459820882888478843663139 8189731324332718265494709)
                ·
                  refine ⟨767787311656192337390129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8189731324332718265494709 767787311656192337390129)
                  ·
                    refine ⟨575840483742144253042597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 767787311656192337390129 575840483742144253042597)
                    ·
                      refine ⟨107970090701652047445487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 575840483742144253042597 107970090701652047445487)
                      ·
                        rfl

theorem cell23_210271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_210271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210271 prefixEnd_210271 := by exact prefixLift 210271
  have htrace : WordTrace (prefixWord ++ tailWord_210271) baseStart_210271 baseEnd_210271 := by
    simpa [prefixWord, tailWord_210271, baseEnd_210271] using wordTrace_append hprefix tailTrace_210271
  have hstable : (prefixWord ++ tailWord_210271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210271).length < 2 ^ (prefixWord ++ tailWord_210271).sum := by decide
  have hdescent : baseEnd_210271 < baseStart_210271 := by decide
  rcases family_descends (prefixWord ++ tailWord_210271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210285 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_210285 : Nat := 118140960795 + 210285 * 2 ^ 59
def prefixEnd_210285 : Nat := 4983230072969 + 3 ^ 40 * 210285 * 2
def baseEnd_210285 : Nat := 35992426476938330890141

theorem tailTrace_210285 : CollatzResearch.WordTrace tailWord_210285 prefixEnd_210285 35992426476938330890141 := by
  unfold tailWord_210285
  simp only [CollatzResearch.WordTrace]
  refine ⟨7669724043180833663864309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5113149362120555775909539 7669724043180833663864309)
  ·
    refine ⟨719036629048203155987279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7669724043180833663864309 719036629048203155987279)
    ·
      refine ⟨1078554943572304733980919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 719036629048203155987279 1078554943572304733980919)
      ·
        refine ⟨1617832415358457100971379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078554943572304733980919 1617832415358457100971379)
        ·
          refine ⟨2426748623037685651457069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617832415358457100971379 2426748623037685651457069)
          ·
            refine ⟨910030733639132119296401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2426748623037685651457069 910030733639132119296401)
            ·
              refine ⟨682523050229349089472301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910030733639132119296401 682523050229349089472301)
              ·
                refine ⟨255946143836005908552113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 682523050229349089472301 255946143836005908552113)
                ·
                  refine ⟨191959607877004431414085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255946143836005908552113 191959607877004431414085)
                  ·
                    refine ⟨35992426476938330890141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191959607877004431414085 35992426476938330890141)
                    ·
                      rfl

theorem cell23_210285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_210285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210285 prefixEnd_210285 := by exact prefixLift 210285
  have htrace : WordTrace (prefixWord ++ tailWord_210285) baseStart_210285 baseEnd_210285 := by
    simpa [prefixWord, tailWord_210285, baseEnd_210285] using wordTrace_append hprefix tailTrace_210285
  have hstable : (prefixWord ++ tailWord_210285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210285).length < 2 ^ (prefixWord ++ tailWord_210285).sum := by decide
  have hdescent : baseEnd_210285 < baseStart_210285 := by decide
  rcases family_descends (prefixWord ++ tailWord_210285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210288 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4]
def baseStart_210288 : Nat := 118140960795 + 210288 * 2 ^ 59
def prefixEnd_210288 : Nat := 4983230072969 + 3 ^ 40 * 210288 * 2
def baseEnd_210288 : Nat := 107978819872778480932909

theorem tailTrace_210288 : CollatzResearch.WordTrace tailWord_210288 prefixEnd_210288 107978819872778480932909 := by
  unfold tailWord_210288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3834916731084982588111759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5113222308113310117482345 3834916731084982588111759)
  ·
    refine ⟨5752375096627473882167639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3834916731084982588111759 5752375096627473882167639)
    ·
      refine ⟨8628562644941210823251459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752375096627473882167639 8628562644941210823251459)
      ·
        refine ⟨12942843967411816234877189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628562644941210823251459 12942843967411816234877189)
        ·
          refine ⟨2426783243889715544039473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12942843967411816234877189 2426783243889715544039473)
          ·
            refine ⟨1820087432917286658029605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426783243889715544039473 1820087432917286658029605)
            ·
              refine ⟨341266393671991248380551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1820087432917286658029605 341266393671991248380551)
              ·
                refine ⟨511899590507986872570827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341266393671991248380551 511899590507986872570827)
                ·
                  refine ⟨767849385761980308856241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511899590507986872570827 767849385761980308856241)
                  ·
                    refine ⟨575887039321485231642181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 767849385761980308856241 575887039321485231642181)
                    ·
                      refine ⟨107978819872778480932909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 575887039321485231642181 107978819872778480932909)
                      ·
                        rfl

theorem cell23_210288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_210288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210288 prefixEnd_210288 := by exact prefixLift 210288
  have htrace : WordTrace (prefixWord ++ tailWord_210288) baseStart_210288 baseEnd_210288 := by
    simpa [prefixWord, tailWord_210288, baseEnd_210288] using wordTrace_append hprefix tailTrace_210288
  have hstable : (prefixWord ++ tailWord_210288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210288).length < 2 ^ (prefixWord ++ tailWord_210288).sum := by decide
  have hdescent : baseEnd_210288 < baseStart_210288 := by decide
  rcases family_descends (prefixWord ++ tailWord_210288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210312 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_210312 : Nat := 118140960795 + 210312 * 2 ^ 59
def prefixEnd_210312 : Nat := 4983230072969 + 3 ^ 40 * 210312 * 2
def baseEnd_210312 : Nat := 107991143408486387032799

theorem tailTrace_210312 : CollatzResearch.WordTrace tailWord_210312 prefixEnd_210312 107991143408486387032799 := by
  unfold tailWord_210312
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835354407041508637548595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5113805876055344850064793 3835354407041508637548595)
  ·
    refine ⟨5753031610562262956322893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3835354407041508637548595 5753031610562262956322893)
    ·
      refine ⟨2157386853960848608621085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5753031610562262956322893 2157386853960848608621085)
      ·
        refine ⟨809020070235318228232907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2157386853960848608621085 809020070235318228232907)
        ·
          refine ⟨1213530105352977342349361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809020070235318228232907 1213530105352977342349361)
          ·
            refine ⟨910147579014733006762021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213530105352977342349361 910147579014733006762021)
            ·
              refine ⟨170652671065262438767879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 910147579014733006762021 170652671065262438767879)
              ·
                refine ⟨255979006597893658151819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170652671065262438767879 255979006597893658151819)
                ·
                  refine ⟨383968509896840487227729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255979006597893658151819 383968509896840487227729)
                  ·
                    refine ⟨287976382422630365420797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383968509896840487227729 287976382422630365420797)
                    ·
                      refine ⟨107991143408486387032799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 287976382422630365420797 107991143408486387032799)
                      ·
                        rfl

theorem cell23_210312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_210312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210312 prefixEnd_210312 := by exact prefixLift 210312
  have htrace : WordTrace (prefixWord ++ tailWord_210312) baseStart_210312 baseEnd_210312 := by
    simpa [prefixWord, tailWord_210312, baseEnd_210312] using wordTrace_append hprefix tailTrace_210312
  have hstable : (prefixWord ++ tailWord_210312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210312).length < 2 ^ (prefixWord ++ tailWord_210312).sum := by decide
  have hdescent : baseEnd_210312 < baseStart_210312 := by decide
  rcases family_descends (prefixWord ++ tailWord_210312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210321 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_210321 : Nat := 118140960795 + 210321 * 2 ^ 59
def prefixEnd_210321 : Nat := 4983230072969 + 3 ^ 40 * 210321 * 2
def baseEnd_210321 : Nat := 107995764734376851820257

theorem tailTrace_210321 : CollatzResearch.WordTrace tailWord_210321 prefixEnd_210321 107995764734376851820257 := by
  unfold tailWord_210321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7671037071050411812174817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5114024714033607874783211 7671037071050411812174817)
  ·
    refine ⟨5753277803287808859131113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7671037071050411812174817 5753277803287808859131113)
    ·
      refine ⟨4314958352465856644348335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5753277803287808859131113 4314958352465856644348335)
      ·
        refine ⟨6472437528698784966522503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314958352465856644348335 6472437528698784966522503)
        ·
          refine ⟨9708656293048177449783755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472437528698784966522503 9708656293048177449783755)
          ·
            refine ⟨14562984439572266174675633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9708656293048177449783755 14562984439572266174675633)
            ·
              refine ⟨10922238329679199631006725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14562984439572266174675633 10922238329679199631006725)
              ·
                refine ⟨2047919686814849930813761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10922238329679199631006725 2047919686814849930813761)
                ·
                  refine ⟨1535939765111137448110321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047919686814849930813761 1535939765111137448110321)
                  ·
                    refine ⟨1151954823833353086082741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1535939765111137448110321 1151954823833353086082741)
                    ·
                      refine ⟨107995764734376851820257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1151954823833353086082741 107995764734376851820257)
                      ·
                        rfl

theorem cell23_210321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_210321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210321 prefixEnd_210321 := by exact prefixLift 210321
  have htrace : WordTrace (prefixWord ++ tailWord_210321) baseStart_210321 baseEnd_210321 := by
    simpa [prefixWord, tailWord_210321, baseEnd_210321] using wordTrace_append hprefix tailTrace_210321
  have hstable : (prefixWord ++ tailWord_210321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210321).length < 2 ^ (prefixWord ++ tailWord_210321).sum := by decide
  have hdescent : baseEnd_210321 < baseStart_210321 := by decide
  rcases family_descends (prefixWord ++ tailWord_210321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210341 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_210341 : Nat := 118140960795 + 210341 * 2 ^ 59
def prefixEnd_210341 : Nat := 4983230072969 + 3 ^ 40 * 210341 * 2
def baseEnd_210341 : Nat := 36002011449155591190055

theorem tailTrace_210341 : CollatzResearch.WordTrace tailWord_210341 prefixEnd_210341 36002011449155591190055 := by
  unfold tailWord_210341
  simp only [CollatzResearch.WordTrace]
  refine ⟨7671766530977955227902877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5114511020651970151935251 7671766530977955227902877)
  ·
    refine ⟨2876912449116733210463579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7671766530977955227902877 2876912449116733210463579)
    ·
      refine ⟨4315368673675099815695369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876912449116733210463579 4315368673675099815695369)
      ·
        refine ⟨3236526505256324861771527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4315368673675099815695369 3236526505256324861771527)
        ·
          refine ⟨4854789757884487292657291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236526505256324861771527 4854789757884487292657291)
          ·
            refine ⟨7282184636826730938985937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854789757884487292657291 7282184636826730938985937)
            ·
              refine ⟨5461638477620048204239453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282184636826730938985937 5461638477620048204239453)
              ·
                refine ⟨2048114429107518076589795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5461638477620048204239453 2048114429107518076589795)
                ·
                  refine ⟨3072171643661277114884693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048114429107518076589795 3072171643661277114884693)
                  ·
                    refine ⟨36002011449155591190055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3072171643661277114884693 36002011449155591190055)
                    ·
                      rfl

theorem cell23_210341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_210341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210341 prefixEnd_210341 := by exact prefixLift 210341
  have htrace : WordTrace (prefixWord ++ tailWord_210341) baseStart_210341 baseEnd_210341 := by
    simpa [prefixWord, tailWord_210341, baseEnd_210341] using wordTrace_append hprefix tailTrace_210341
  have hstable : (prefixWord ++ tailWord_210341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210341).length < 2 ^ (prefixWord ++ tailWord_210341).sum := by decide
  have hdescent : baseEnd_210341 < baseStart_210341 := by decide
  rcases family_descends (prefixWord ++ tailWord_210341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210351 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 5]
def baseStart_210351 : Nat := 118140960795 + 210351 * 2 ^ 59
def prefixEnd_210351 : Nat := 4983230072969 + 3 ^ 40 * 210351 * 2
def baseEnd_210351 : Nat := 108011169154011734445119

theorem tailTrace_210351 : CollatzResearch.WordTrace tailWord_210351 prefixEnd_210351 108011169154011734445119 := by
  unfold tailWord_210351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672131260941726935766907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5114754173961151290511271 7672131260941726935766907)
  ·
    refine ⟨11508196891412590403650361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7672131260941726935766907 11508196891412590403650361)
    ·
      refine ⟨8631147668559442802737771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11508196891412590403650361 8631147668559442802737771)
      ·
        refine ⟨12946721502839164204106657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631147668559442802737771 12946721502839164204106657)
        ·
          refine ⟨9710041127129373153079993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12946721502839164204106657 9710041127129373153079993)
          ·
            refine ⟨7282530845347029864809995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9710041127129373153079993 7282530845347029864809995)
            ·
              refine ⟨10923796268020544797214993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282530845347029864809995 10923796268020544797214993)
              ·
                refine ⟨8192847201015408597911245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10923796268020544797214993 8192847201015408597911245)
                ·
                  refine ⟨3072317700380778224216717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8192847201015408597911245 3072317700380778224216717)
                  ·
                    refine ⟨1152119137642791834081269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3072317700380778224216717 1152119137642791834081269)
                    ·
                      refine ⟨108011169154011734445119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1152119137642791834081269 108011169154011734445119)
                      ·
                        rfl

theorem cell23_210351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_210351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210351 prefixEnd_210351 := by exact prefixLift 210351
  have htrace : WordTrace (prefixWord ++ tailWord_210351) baseStart_210351 baseEnd_210351 := by
    simpa [prefixWord, tailWord_210351, baseEnd_210351] using wordTrace_append hprefix tailTrace_210351
  have hstable : (prefixWord ++ tailWord_210351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210351).length < 2 ^ (prefixWord ++ tailWord_210351).sum := by decide
  have hdescent : baseEnd_210351 < baseStart_210351 := by decide
  rcases family_descends (prefixWord ++ tailWord_210351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210365 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_210365 : Nat := 118140960795 + 210365 * 2 ^ 59
def prefixEnd_210365 : Nat := 4983230072969 + 3 ^ 40 * 210365 * 2
def baseEnd_210365 : Nat := 108018357883174679670055

theorem tailTrace_210365 : CollatzResearch.WordTrace tailWord_210365 prefixEnd_210365 108018357883174679670055 := by
  unfold tailWord_210365
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672641882891007326776549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5115094588594004884517699 7672641882891007326776549)
  ·
    refine ⟨1438620353042063873770603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7672641882891007326776549 1438620353042063873770603)
    ·
      refine ⟨2157930529563095810655905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438620353042063873770603 2157930529563095810655905)
      ·
        refine ⟨1618447897172321857991929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2157930529563095810655905 1618447897172321857991929)
        ·
          refine ⟨1213835922879241393493947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1618447897172321857991929 1213835922879241393493947)
          ·
            refine ⟨1820753884318862090240921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213835922879241393493947 1820753884318862090240921)
            ·
              refine ⟨1365565413239146567680691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820753884318862090240921 1365565413239146567680691)
              ·
                refine ⟨2048348119858719851521037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365565413239146567680691 2048348119858719851521037)
                ·
                  refine ⟨768130544947019944320389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2048348119858719851521037 768130544947019944320389)
                  ·
                    refine ⟨144024477177566239560073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 768130544947019944320389 144024477177566239560073)
                    ·
                      refine ⟨108018357883174679670055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144024477177566239560073 108018357883174679670055)
                      ·
                        rfl

theorem cell23_210365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_210365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210365 prefixEnd_210365 := by exact prefixLift 210365
  have htrace : WordTrace (prefixWord ++ tailWord_210365) baseStart_210365 baseEnd_210365 := by
    simpa [prefixWord, tailWord_210365, baseEnd_210365] using wordTrace_append hprefix tailTrace_210365
  have hstable : (prefixWord ++ tailWord_210365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210365).length < 2 ^ (prefixWord ++ tailWord_210365).sum := by decide
  have hdescent : baseEnd_210365 < baseStart_210365 := by decide
  rcases family_descends (prefixWord ++ tailWord_210365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210371 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 9]
def baseStart_210371 : Nat := 118140960795 + 210371 * 2 ^ 59
def prefixEnd_210371 : Nat := 4983230072969 + 3 ^ 40 * 210371 * 2
def baseEnd_210371 : Nat := 12002382085233517355003

theorem tailTrace_210371 : CollatzResearch.WordTrace tailWord_210371 prefixEnd_210371 12002382085233517355003 := by
  unfold tailWord_210371
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672860720869270351494967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5115240480579513567663311 7672860720869270351494967)
  ·
    refine ⟨11509291081303905527242451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7672860720869270351494967 11509291081303905527242451)
    ·
      refine ⟨17263936621955858290863677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11509291081303905527242451 17263936621955858290863677)
      ·
        refine ⟨6473976233233446859073879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17263936621955858290863677 6473976233233446859073879)
        ·
          refine ⟨9710964349850170288610819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473976233233446859073879 9710964349850170288610819)
          ·
            refine ⟨14566446524775255432916229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710964349850170288610819 14566446524775255432916229)
            ·
              refine ⟨2731208723395360393671793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14566446524775255432916229 2731208723395360393671793)
              ·
                refine ⟨2048406542546520295253845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731208723395360393671793 2048406542546520295253845)
                ·
                  refine ⟨12002382085233517355003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2048406542546520295253845 12002382085233517355003)
                  ·
                    rfl

theorem cell23_210371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 9].length) (baseStart_210371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210371 prefixEnd_210371 := by exact prefixLift 210371
  have htrace : WordTrace (prefixWord ++ tailWord_210371) baseStart_210371 baseEnd_210371 := by
    simpa [prefixWord, tailWord_210371, baseEnd_210371] using wordTrace_append hprefix tailTrace_210371
  have hstable : (prefixWord ++ tailWord_210371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210371).length < 2 ^ (prefixWord ++ tailWord_210371).sum := by decide
  have hdescent : baseEnd_210371 < baseStart_210371 := by decide
  rcases family_descends (prefixWord ++ tailWord_210371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210382 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_210382 : Nat := 118140960795 + 210382 * 2 ^ 59
def prefixEnd_210382 : Nat := 4983230072969 + 3 ^ 40 * 210382 * 2
def baseEnd_210382 : Nat := 108027087054301113157477

theorem tailTrace_210382 : CollatzResearch.WordTrace tailWord_210382 prefixEnd_210382 108027087054301113157477 := by
  unfold tailWord_210382
  simp only [CollatzResearch.WordTrace]
  refine ⟨959157740478677403768175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5115507949219612820096933 959157740478677403768175)
  ·
    refine ⟨1438736610718016105652263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959157740478677403768175 1438736610718016105652263)
    ·
      refine ⟨2158104916077024158478395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438736610718016105652263 2158104916077024158478395)
      ·
        refine ⟨3237157374115536237717593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158104916077024158478395 3237157374115536237717593)
        ·
          refine ⟨2427868030586652178288195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3237157374115536237717593 2427868030586652178288195)
          ·
            refine ⟨3641802045879978267432293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427868030586652178288195 3641802045879978267432293)
            ·
              refine ⟨682837883602495925143555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3641802045879978267432293 682837883602495925143555)
              ·
                refine ⟨1024256825403743887715333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682837883602495925143555 1024256825403743887715333)
                ·
                  refine ⟨192048154763201978946625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1024256825403743887715333 192048154763201978946625)
                  ·
                    refine ⟨144036116072401484209969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 192048154763201978946625 144036116072401484209969)
                    ·
                      refine ⟨108027087054301113157477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144036116072401484209969 108027087054301113157477)
                      ·
                        rfl

theorem cell23_210382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_210382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210382 prefixEnd_210382 := by exact prefixLift 210382
  have htrace : WordTrace (prefixWord ++ tailWord_210382) baseStart_210382 baseEnd_210382 := by
    simpa [prefixWord, tailWord_210382, baseEnd_210382] using wordTrace_append hprefix tailTrace_210382
  have hstable : (prefixWord ++ tailWord_210382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210382).length < 2 ^ (prefixWord ++ tailWord_210382).sum := by decide
  have hdescent : baseEnd_210382 < baseStart_210382 := by decide
  rcases family_descends (prefixWord ++ tailWord_210382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210428 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_210428 : Nat := 118140960795 + 210428 * 2 ^ 59
def prefixEnd_210428 : Nat := 4983230072969 + 3 ^ 40 * 210428 * 2
def baseEnd_210428 : Nat := 108050707164407933182265

theorem tailTrace_210428 : CollatzResearch.WordTrace tailWord_210428 prefixEnd_210428 108050707164407933182265 := by
  unfold tailWord_210428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3837469840831384543159969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5116626454441846057546625 3837469840831384543159969)
  ·
    refine ⟨2878102380623538407369977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3837469840831384543159969 2878102380623538407369977)
    ·
      refine ⟨2158576785467653805527483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2878102380623538407369977 2158576785467653805527483)
      ·
        refine ⟨3237865178201480708291225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158576785467653805527483 3237865178201480708291225)
        ·
          refine ⟨2428398883651110531218419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3237865178201480708291225 2428398883651110531218419)
          ·
            refine ⟨3642598325476665796827629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428398883651110531218419 3642598325476665796827629)
            ·
              refine ⟨1365974372053749673810361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3642598325476665796827629 1365974372053749673810361)
              ·
                refine ⟨1024480779040312255357771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365974372053749673810361 1024480779040312255357771)
                ·
                  refine ⟨1536721168560468383036657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024480779040312255357771 1536721168560468383036657)
                  ·
                    refine ⟨1152540876420351287277493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1536721168560468383036657 1152540876420351287277493)
                    ·
                      refine ⟨108050707164407933182265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1152540876420351287277493 108050707164407933182265)
                      ·
                        rfl

theorem cell23_210428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_210428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210428 prefixEnd_210428 := by exact prefixLift 210428
  have htrace : WordTrace (prefixWord ++ tailWord_210428) baseStart_210428 baseEnd_210428 := by
    simpa [prefixWord, tailWord_210428, baseEnd_210428] using wordTrace_append hprefix tailTrace_210428
  have hstable : (prefixWord ++ tailWord_210428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210428).length < 2 ^ (prefixWord ++ tailWord_210428).sum := by decide
  have hdescent : baseEnd_210428 < baseStart_210428 := by decide
  rcases family_descends (prefixWord ++ tailWord_210428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210439 : List Nat := [1, 1, 4, 3, 2, 3, 2, 2, 5]
def baseStart_210439 : Nat := 118140960795 + 210439 * 2 ^ 59
def prefixEnd_210439 : Nat := 4983230072969 + 3 ^ 40 * 210439 * 2
def baseEnd_210439 : Nat := 12006261716845265571635

theorem tailTrace_210439 : CollatzResearch.WordTrace tailWord_210439 prefixEnd_210439 12006261716845265571635 := by
  unfold tailWord_210439
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675340884622917964970371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5116893923081945309980247 7675340884622917964970371)
  ·
    refine ⟨11513011326934376947455557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7675340884622917964970371 11513011326934376947455557)
    ·
      refine ⟨2158689623800195677647917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11513011326934376947455557 2158689623800195677647917)
      ·
        refine ⟨809508608925073379117969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2158689623800195677647917 809508608925073379117969)
        ·
          refine ⟨607131456693805034338477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809508608925073379117969 607131456693805034338477)
          ·
            refine ⟨227674296260176887876929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607131456693805034338477 227674296260176887876929)
            ·
              refine ⟨170755722195132665907697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227674296260176887876929 170755722195132665907697)
              ·
                refine ⟨128066791646349499430773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170755722195132665907697 128066791646349499430773)
                ·
                  refine ⟨12006261716845265571635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128066791646349499430773 12006261716845265571635)
                  ·
                    rfl

theorem cell23_210439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 5].length) (baseStart_210439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210439 prefixEnd_210439 := by exact prefixLift 210439
  have htrace : WordTrace (prefixWord ++ tailWord_210439) baseStart_210439 baseEnd_210439 := by
    simpa [prefixWord, tailWord_210439, baseEnd_210439] using wordTrace_append hprefix tailTrace_210439
  have hstable : (prefixWord ++ tailWord_210439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210439).length < 2 ^ (prefixWord ++ tailWord_210439).sum := by decide
  have hdescent : baseEnd_210439 < baseStart_210439 := by decide
  rcases family_descends (prefixWord ++ tailWord_210439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210465 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 5, 4]
def baseStart_210465 : Nat := 118140960795 + 210465 * 2 ^ 59
def prefixEnd_210465 : Nat := 4983230072969 + 3 ^ 40 * 210465 * 2
def baseEnd_210465 : Nat := 36023235316208096139865

theorem tailTrace_210465 : CollatzResearch.WordTrace tailWord_210465 prefixEnd_210465 36023235316208096139865 := by
  unfold tailWord_210465
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676289182528724405416849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5117526121685816270277899 7676289182528724405416849)
  ·
    refine ⟨5757216886896543304062637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7676289182528724405416849 5757216886896543304062637)
    ·
      refine ⟨2158956332586203739023489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5757216886896543304062637 2158956332586203739023489)
      ·
        refine ⟨1619217249439652804267617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158956332586203739023489 1619217249439652804267617)
        ·
          refine ⟨1214412937079739603200713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1619217249439652804267617 1214412937079739603200713)
          ·
            refine ⟨910809702809804702400535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214412937079739603200713 910809702809804702400535)
            ·
              refine ⟨1366214554214707053600803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910809702809804702400535 1366214554214707053600803)
              ·
                refine ⟨2049321831322060580401205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366214554214707053600803 2049321831322060580401205)
                ·
                  refine ⟨192123921686443179412613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2049321831322060580401205 192123921686443179412613)
                  ·
                    refine ⟨36023235316208096139865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192123921686443179412613 36023235316208096139865)
                    ·
                      rfl

theorem cell23_210465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_210465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210465 prefixEnd_210465 := by exact prefixLift 210465
  have htrace : WordTrace (prefixWord ++ tailWord_210465) baseStart_210465 baseEnd_210465 := by
    simpa [prefixWord, tailWord_210465, baseEnd_210465] using wordTrace_append hprefix tailTrace_210465
  have hstable : (prefixWord ++ tailWord_210465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210465).length < 2 ^ (prefixWord ++ tailWord_210465).sum := by decide
  have hdescent : baseEnd_210465 < baseStart_210465 := by decide
  rcases family_descends (prefixWord ++ tailWord_210465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210472 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_210472 : Nat := 118140960795 + 210472 * 2 ^ 59
def prefixEnd_210472 : Nat := 4983230072969 + 3 ^ 40 * 210472 * 2
def baseEnd_210472 : Nat := 108073300313205761032063

theorem tailTrace_210472 : CollatzResearch.WordTrace tailWord_210472 prefixEnd_210472 108073300313205761032063 := by
  unfold tailWord_210472
  simp only [CollatzResearch.WordTrace]
  refine ⟨3838272246751682300460835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5117696329002243067281113 3838272246751682300460835)
  ·
    refine ⟨5757408370127523450691253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3838272246751682300460835 5757408370127523450691253)
    ·
      refine ⟨539757034699455323502305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5757408370127523450691253 539757034699455323502305)
      ·
        refine ⟨404817776024591492626729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539757034699455323502305 404817776024591492626729)
        ·
          refine ⟨303613332018443619470047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404817776024591492626729 303613332018443619470047)
          ·
            refine ⟨455419998027665429205071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303613332018443619470047 455419998027665429205071)
            ·
              refine ⟨683129997041498143807607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455419998027665429205071 683129997041498143807607)
              ·
                refine ⟨1024694995562247215711411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683129997041498143807607 1024694995562247215711411)
                ·
                  refine ⟨1537042493343370823567117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024694995562247215711411 1537042493343370823567117)
                  ·
                    refine ⟨576390935003764058837669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537042493343370823567117 576390935003764058837669)
                    ·
                      refine ⟨108073300313205761032063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 576390935003764058837669 108073300313205761032063)
                      ·
                        rfl

theorem cell23_210472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_210472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210472 prefixEnd_210472 := by exact prefixLift 210472
  have htrace : WordTrace (prefixWord ++ tailWord_210472) baseStart_210472 baseEnd_210472 := by
    simpa [prefixWord, tailWord_210472, baseEnd_210472] using wordTrace_append hprefix tailTrace_210472
  have hstable : (prefixWord ++ tailWord_210472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210472).length < 2 ^ (prefixWord ++ tailWord_210472).sum := by decide
  have hdescent : baseEnd_210472 < baseStart_210472 := by decide
  rcases family_descends (prefixWord ++ tailWord_210472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210495 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 6]
def baseStart_210495 : Nat := 118140960795 + 210495 * 2 ^ 59
def prefixEnd_210495 : Nat := 4983230072969 + 3 ^ 40 * 210495 * 2
def baseEnd_210495 : Nat := 12009456707584352338273

theorem tailTrace_210495 : CollatzResearch.WordTrace tailWord_210495 prefixEnd_210495 12009456707584352338273 := by
  unfold tailWord_210495
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677383372420039529008939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5118255581613359686005959 7677383372420039529008939)
  ·
    refine ⟨11516075058630059293513409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677383372420039529008939 11516075058630059293513409)
    ·
      refine ⟨8637056293972544470135057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11516075058630059293513409 8637056293972544470135057)
      ·
        refine ⟨6477792220479408352601293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8637056293972544470135057 6477792220479408352601293)
        ·
          refine ⟨2429172082679778132225485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6477792220479408352601293 2429172082679778132225485)
          ·
            refine ⟨910939531004916799584557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2429172082679778132225485 910939531004916799584557)
            ·
              refine ⟨341602324126843799844209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 910939531004916799584557 341602324126843799844209)
              ·
                refine ⟨256201743095132849883157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341602324126843799844209 256201743095132849883157)
                ·
                  refine ⟨12009456707584352338273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256201743095132849883157 12009456707584352338273)
                  ·
                    rfl

theorem cell23_210495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 6].length) (baseStart_210495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210495 prefixEnd_210495 := by exact prefixLift 210495
  have htrace : WordTrace (prefixWord ++ tailWord_210495) baseStart_210495 baseEnd_210495 := by
    simpa [prefixWord, tailWord_210495, baseEnd_210495] using wordTrace_append hprefix tailTrace_210495
  have hstable : (prefixWord ++ tailWord_210495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210495).length < 2 ^ (prefixWord ++ tailWord_210495).sum := by decide
  have hdescent : baseEnd_210495 < baseStart_210495 := by decide
  rcases family_descends (prefixWord ++ tailWord_210495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210532 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_210532 : Nat := 118140960795 + 210532 * 2 ^ 59
def prefixEnd_210532 : Nat := 4983230072969 + 3 ^ 40 * 210532 * 2
def baseEnd_210532 : Nat := 108104109152475526281787

theorem tailTrace_210532 : CollatzResearch.WordTrace tailWord_210532 prefixEnd_210532 108104109152475526281787 := by
  unfold tailWord_210532
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839366436642997424052925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5119155248857329898737233 3839366436642997424052925)
  ·
    refine ⟨1439762413741124034019847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3839366436642997424052925 1439762413741124034019847)
    ·
      refine ⟨2159643620611686051029771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439762413741124034019847 2159643620611686051029771)
      ·
        refine ⟨3239465430917529076544657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2159643620611686051029771 3239465430917529076544657)
        ·
          refine ⟨2429599073188146807408493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3239465430917529076544657 2429599073188146807408493)
          ·
            refine ⟨911099652445555052778185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2429599073188146807408493 911099652445555052778185)
            ·
              refine ⟨683324739334166289583639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911099652445555052778185 683324739334166289583639)
              ·
                refine ⟨1024987109001249434375459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683324739334166289583639 1024987109001249434375459)
                ·
                  refine ⟨1537480663501874151563189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024987109001249434375459 1537480663501874151563189)
                  ·
                    refine ⟨144138812203300701709049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1537480663501874151563189 144138812203300701709049)
                    ·
                      refine ⟨108104109152475526281787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144138812203300701709049 108104109152475526281787)
                      ·
                        rfl

theorem cell23_210532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_210532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210532 prefixEnd_210532 := by exact prefixLift 210532
  have htrace : WordTrace (prefixWord ++ tailWord_210532) baseStart_210532 baseEnd_210532 := by
    simpa [prefixWord, tailWord_210532, baseEnd_210532] using wordTrace_append hprefix tailTrace_210532
  have hstable : (prefixWord ++ tailWord_210532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210532).length < 2 ^ (prefixWord ++ tailWord_210532).sum := by decide
  have hdescent : baseEnd_210532 < baseStart_210532 := by decide
  rcases family_descends (prefixWord ++ tailWord_210532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210549 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_210549 : Nat := 118140960795 + 210549 * 2 ^ 59
def prefixEnd_210549 : Nat := 4983230072969 + 3 ^ 40 * 210549 * 2
def baseEnd_210549 : Nat := 108112838323601959769209

theorem tailTrace_210549 : CollatzResearch.WordTrace tailWord_210549 prefixEnd_210549 108112838323601959769209 := by
  unfold tailWord_210549
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679352914224406751474701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5119568609482937834316467 7679352914224406751474701)
  ·
    refine ⟨2879757342834152531803013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7679352914224406751474701 2879757342834152531803013)
    ·
      refine ⟨539954501781403599713065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2879757342834152531803013 539954501781403599713065)
      ·
        refine ⟨404965876336052699784799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539954501781403599713065 404965876336052699784799)
        ·
          refine ⟨607448814504079049677199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404965876336052699784799 607448814504079049677199)
          ·
            refine ⟨911173221756118574515799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607448814504079049677199 911173221756118574515799)
            ·
              refine ⟨1366759832634177861773699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911173221756118574515799 1366759832634177861773699)
              ·
                refine ⟨2050139748951266792660549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366759832634177861773699 2050139748951266792660549)
                ·
                  refine ⟨384401202928362523623853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050139748951266792660549 384401202928362523623853)
                  ·
                    refine ⟨144150451098135946358945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384401202928362523623853 144150451098135946358945)
                    ·
                      refine ⟨108112838323601959769209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144150451098135946358945 108112838323601959769209)
                      ·
                        rfl

theorem cell23_210549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_210549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210549 prefixEnd_210549 := by exact prefixLift 210549
  have htrace : WordTrace (prefixWord ++ tailWord_210549) baseStart_210549 baseEnd_210549 := by
    simpa [prefixWord, tailWord_210549, baseEnd_210549] using wordTrace_append hprefix tailTrace_210549
  have hstable : (prefixWord ++ tailWord_210549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210549).length < 2 ^ (prefixWord ++ tailWord_210549).sum := by decide
  have hdescent : baseEnd_210549 < baseStart_210549 := by decide
  rcases family_descends (prefixWord ++ tailWord_210549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210555 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 4, 4]
def baseStart_210555 : Nat := 118140960795 + 210555 * 2 ^ 59
def prefixEnd_210555 : Nat := 4983230072969 + 3 ^ 40 * 210555 * 2
def baseEnd_210555 : Nat := 36038639735842978764727

theorem tailTrace_210555 : CollatzResearch.WordTrace tailWord_210555 prefixEnd_210555 36038639735842978764727 := by
  unfold tailWord_210555
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679571752202669776193119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5119714501468446517462079 7679571752202669776193119)
  ·
    refine ⟨11519357628304004664289679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7679571752202669776193119 11519357628304004664289679)
    ·
      refine ⟨17279036442456006996434519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11519357628304004664289679 17279036442456006996434519)
      ·
        refine ⟨25918554663684010494651779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17279036442456006996434519 25918554663684010494651779)
        ·
          refine ⟨38877831995526015741977669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25918554663684010494651779 38877831995526015741977669)
          ·
            refine ⟨7289593499161127951620813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38877831995526015741977669 7289593499161127951620813)
            ·
              refine ⟨2733597562185422981857805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7289593499161127951620813 2733597562185422981857805)
              ·
                refine ⟨1025099085819533618196677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2733597562185422981857805 1025099085819533618196677)
                ·
                  refine ⟨192206078591162553411877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1025099085819533618196677 192206078591162553411877)
                  ·
                    refine ⟨36038639735842978764727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192206078591162553411877 36038639735842978764727)
                    ·
                      rfl

theorem cell23_210555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 4].length) (baseStart_210555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210555 prefixEnd_210555 := by exact prefixLift 210555
  have htrace : WordTrace (prefixWord ++ tailWord_210555) baseStart_210555 baseEnd_210555 := by
    simpa [prefixWord, tailWord_210555, baseEnd_210555] using wordTrace_append hprefix tailTrace_210555
  have hstable : (prefixWord ++ tailWord_210555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210555).length < 2 ^ (prefixWord ++ tailWord_210555).sum := by decide
  have hdescent : baseEnd_210555 < baseStart_210555 := by decide
  rcases family_descends (prefixWord ++ tailWord_210555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210565 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_210565 : Nat := 118140960795 + 210565 * 2 ^ 59
def prefixEnd_210565 : Nat := 4983230072969 + 3 ^ 40 * 210565 * 2
def baseEnd_210565 : Nat := 108121054014073897169135

theorem tailTrace_210565 : CollatzResearch.WordTrace tailWord_210565 prefixEnd_210565 108121054014073897169135 := by
  unfold tailWord_210565
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679936482166441484057149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5119957654777627656038099 7679936482166441484057149)
  ·
    refine ⟨2879976180812415556521431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7679936482166441484057149 2879976180812415556521431)
    ·
      refine ⟨4319964271218623334782147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879976180812415556521431 4319964271218623334782147)
      ·
        refine ⟨6479946406827935002173221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319964271218623334782147 6479946406827935002173221)
        ·
          refine ⟨1214989951280237812907479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6479946406827935002173221 1214989951280237812907479)
          ·
            refine ⟨1822484926920356719361219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214989951280237812907479 1822484926920356719361219)
            ·
              refine ⟨2733727390380535079041829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822484926920356719361219 2733727390380535079041829)
              ·
                refine ⟨512573885696350327320343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2733727390380535079041829 512573885696350327320343)
                ·
                  refine ⟨768860828544525490980515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512573885696350327320343 768860828544525490980515)
                  ·
                    refine ⟨1153291242816788236470773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 768860828544525490980515 1153291242816788236470773)
                    ·
                      refine ⟨108121054014073897169135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1153291242816788236470773 108121054014073897169135)
                      ·
                        rfl

theorem cell23_210565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_210565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210565 prefixEnd_210565 := by exact prefixLift 210565
  have htrace : WordTrace (prefixWord ++ tailWord_210565) baseStart_210565 baseEnd_210565 := by
    simpa [prefixWord, tailWord_210565, baseEnd_210565] using wordTrace_append hprefix tailTrace_210565
  have hstable : (prefixWord ++ tailWord_210565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210565).length < 2 ^ (prefixWord ++ tailWord_210565).sum := by decide
  have hdescent : baseEnd_210565 < baseStart_210565 := by decide
  rcases family_descends (prefixWord ++ tailWord_210565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210572 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_210572 : Nat := 118140960795 + 210572 * 2 ^ 59
def prefixEnd_210572 : Nat := 4983230072969 + 3 ^ 40 * 210572 * 2
def baseEnd_210572 : Nat := 36041549459551789927201

theorem tailTrace_210572 : CollatzResearch.WordTrace tailWord_210572 prefixEnd_210572 36041549459551789927201 := by
  unfold tailWord_210572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840095896570540839780985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5120127862094054453041313 3840095896570540839780985)
  ·
    refine ⟨2880071922427905629835739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3840095896570540839780985 2880071922427905629835739)
    ·
      refine ⟨4320107883641858444753609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2880071922427905629835739 4320107883641858444753609)
      ·
        refine ⟨3240080912731393833565207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4320107883641858444753609 3240080912731393833565207)
        ·
          refine ⟨4860121369097090750347811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240080912731393833565207 4860121369097090750347811)
          ·
            refine ⟨7290182053645636125521717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860121369097090750347811 7290182053645636125521717)
            ·
              refine ⟨683454567529278386767661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7290182053645636125521717 683454567529278386767661)
              ·
                refine ⟨256295462823479395037873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 683454567529278386767661 256295462823479395037873)
                ·
                  refine ⟨192221597117609546278405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256295462823479395037873 192221597117609546278405)
                  ·
                    refine ⟨36041549459551789927201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192221597117609546278405 36041549459551789927201)
                    ·
                      rfl

theorem cell23_210572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_210572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210572 prefixEnd_210572 := by exact prefixLift 210572
  have htrace : WordTrace (prefixWord ++ tailWord_210572) baseStart_210572 baseEnd_210572 := by
    simpa [prefixWord, tailWord_210572, baseEnd_210572] using wordTrace_append hprefix tailTrace_210572
  have hstable : (prefixWord ++ tailWord_210572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210572).length < 2 ^ (prefixWord ++ tailWord_210572).sum := by decide
  have hdescent : baseEnd_210572 < baseStart_210572 := by decide
  rcases family_descends (prefixWord ++ tailWord_210572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210592 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_210592 : Nat := 118140960795 + 210592 * 2 ^ 59
def prefixEnd_210592 : Nat := 4983230072969 + 3 ^ 40 * 210592 * 2
def baseEnd_210592 : Nat := 108134917991745291531511

theorem tailTrace_210592 : CollatzResearch.WordTrace tailWord_210592 prefixEnd_210592 108134917991745291531511 := by
  unfold tailWord_210592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840460626534312547645015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5120614168712416730193353 3840460626534312547645015)
  ·
    refine ⟨5760690939801468821467523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3840460626534312547645015 5760690939801468821467523)
    ·
      refine ⟨8641036409702203232201285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5760690939801468821467523 8641036409702203232201285)
      ·
        refine ⟨1620194326819163106037741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8641036409702203232201285 1620194326819163106037741)
        ·
          refine ⟨607572872557186164764153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1620194326819163106037741 607572872557186164764153)
          ·
            refine ⟨455679654417889623573115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607572872557186164764153 455679654417889623573115)
            ·
              refine ⟨683519481626834435359673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455679654417889623573115 683519481626834435359673)
              ·
                refine ⟨512639611220125826519755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683519481626834435359673 512639611220125826519755)
                ·
                  refine ⟨768959416830188739779633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512639611220125826519755 768959416830188739779633)
                  ·
                    refine ⟨576719562622641554834725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768959416830188739779633 576719562622641554834725)
                    ·
                      refine ⟨108134917991745291531511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 576719562622641554834725 108134917991745291531511)
                      ·
                        rfl

theorem cell23_210592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_210592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210592 prefixEnd_210592 := by exact prefixLift 210592
  have htrace : WordTrace (prefixWord ++ tailWord_210592) baseStart_210592 baseEnd_210592 := by
    simpa [prefixWord, tailWord_210592, baseEnd_210592] using wordTrace_append hprefix tailTrace_210592
  have hstable : (prefixWord ++ tailWord_210592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210592).length < 2 ^ (prefixWord ++ tailWord_210592).sum := by decide
  have hdescent : baseEnd_210592 < baseStart_210592 := by decide
  rcases family_descends (prefixWord ++ tailWord_210592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210615 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 2, 7]
def baseStart_210615 : Nat := 118140960795 + 210615 * 2 ^ 59
def prefixEnd_210615 : Nat := 4983230072969 + 3 ^ 40 * 210615 * 2
def baseEnd_210615 : Nat := 36048909348932900514635

theorem tailTrace_210615 : CollatzResearch.WordTrace tailWord_210615 prefixEnd_210615 36048909348932900514635 := by
  unfold tailWord_210615
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681760131985300023377299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5121173421323533348918199 7681760131985300023377299)
  ·
    refine ⟨11522640197977950035065949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7681760131985300023377299 11522640197977950035065949)
    ·
      refine ⟨4320990074241731263149731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11522640197977950035065949 4320990074241731263149731)
      ·
        refine ⟨6481485111362596894724597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4320990074241731263149731 6481485111362596894724597)
        ·
          refine ⟨607639229190243458880431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6481485111362596894724597 607639229190243458880431)
          ·
            refine ⟨911458843785365188320647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607639229190243458880431 911458843785365188320647)
            ·
              refine ⟨1367188265678047782480971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911458843785365188320647 1367188265678047782480971)
              ·
                refine ⟨2050782398517071673721457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367188265678047782480971 2050782398517071673721457)
                ·
                  refine ⟨1538086798887803755291093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2050782398517071673721457 1538086798887803755291093)
                  ·
                    refine ⟨36048909348932900514635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1538086798887803755291093 36048909348932900514635)
                    ·
                      rfl

theorem cell23_210615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_210615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210615 prefixEnd_210615 := by exact prefixLift 210615
  have htrace : WordTrace (prefixWord ++ tailWord_210615) baseStart_210615 baseEnd_210615 := by
    simpa [prefixWord, tailWord_210615, baseEnd_210615] using wordTrace_append hprefix tailTrace_210615
  have hstable : (prefixWord ++ tailWord_210615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210615).length < 2 ^ (prefixWord ++ tailWord_210615).sum := by decide
  have hdescent : baseEnd_210615 < baseStart_210615 := by decide
  rcases family_descends (prefixWord ++ tailWord_210615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210630 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_210630 : Nat := 118140960795 + 210630 * 2 ^ 59
def prefixEnd_210630 : Nat := 4983230072969 + 3 ^ 40 * 210630 * 2
def baseEnd_210630 : Nat := 108154430256616142856337

theorem tailTrace_210630 : CollatzResearch.WordTrace tailWord_210630 prefixEnd_210630 108154430256616142856337 := by
  unfold tailWord_210630
  simp only [CollatzResearch.WordTrace]
  refine ⟨240072100841592424536667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5121538151287305056782229 240072100841592424536667)
  ·
    refine ⟨360108151262388636805001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240072100841592424536667 360108151262388636805001)
    ·
      refine ⟨270081113446791477603751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360108151262388636805001 270081113446791477603751)
      ·
        refine ⟨405121670170187216405627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270081113446791477603751 405121670170187216405627)
        ·
          refine ⟨607682505255280824608441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405121670170187216405627 607682505255280824608441)
          ·
            refine ⟨455761878941460618456331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607682505255280824608441 455761878941460618456331)
            ·
              refine ⟨683642818412190927684497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455761878941460618456331 683642818412190927684497)
              ·
                refine ⟨512732113809143195763373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683642818412190927684497 512732113809143195763373)
                ·
                  refine ⟨192274542678428698411265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 512732113809143195763373 192274542678428698411265)
                  ·
                    refine ⟨144205907008821523808449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 192274542678428698411265 144205907008821523808449)
                    ·
                      refine ⟨108154430256616142856337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144205907008821523808449 108154430256616142856337)
                      ·
                        rfl

theorem cell23_210630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_210630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210630 prefixEnd_210630 := by exact prefixLift 210630
  have htrace : WordTrace (prefixWord ++ tailWord_210630) baseStart_210630 baseEnd_210630 := by
    simpa [prefixWord, tailWord_210630, baseEnd_210630] using wordTrace_append hprefix tailTrace_210630
  have hstable : (prefixWord ++ tailWord_210630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210630).length < 2 ^ (prefixWord ++ tailWord_210630).sum := by decide
  have hdescent : baseEnd_210630 < baseStart_210630 := by decide
  rcases family_descends (prefixWord ++ tailWord_210630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210655 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_210655 : Nat := 118140960795 + 210655 * 2 ^ 59
def prefixEnd_210655 : Nat := 4983230072969 + 3 ^ 40 * 210655 * 2
def baseEnd_210655 : Nat := 108167267272978545043721

theorem tailTrace_210655 : CollatzResearch.WordTrace tailWord_210655 prefixEnd_210655 108167267272978545043721 := by
  unfold tailWord_210655
  simp only [CollatzResearch.WordTrace]
  refine ⟨7683219051840386854833419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5122146034560257903222279 7683219051840386854833419)
  ·
    refine ⟨11524828577760580282250129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7683219051840386854833419 11524828577760580282250129)
    ·
      refine ⟨8643621433320435211687597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11524828577760580282250129 8643621433320435211687597)
      ·
        refine ⟨3241358037495163204382849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8643621433320435211687597 3241358037495163204382849)
        ·
          refine ⟨2431018528121372403287137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3241358037495163204382849 2431018528121372403287137)
          ·
            refine ⟨1823263896091029302465353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2431018528121372403287137 1823263896091029302465353)
            ·
              refine ⟨1367447922068271976849015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823263896091029302465353 1367447922068271976849015)
              ·
                refine ⟨2051171883102407965273523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367447922068271976849015 2051171883102407965273523)
                ·
                  refine ⟨3076757824653611947910285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051171883102407965273523 3076757824653611947910285)
                  ·
                    refine ⟨1153784184245104480466357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3076757824653611947910285 1153784184245104480466357)
                    ·
                      refine ⟨108167267272978545043721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1153784184245104480466357 108167267272978545043721)
                      ·
                        rfl

theorem cell23_210655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_210655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210655 prefixEnd_210655 := by exact prefixLift 210655
  have htrace : WordTrace (prefixWord ++ tailWord_210655) baseStart_210655 baseEnd_210655 := by
    simpa [prefixWord, tailWord_210655, baseEnd_210655] using wordTrace_append hprefix tailTrace_210655
  have hstable : (prefixWord ++ tailWord_210655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210655).length < 2 ^ (prefixWord ++ tailWord_210655).sum := by decide
  have hdescent : baseEnd_210655 < baseStart_210655 := by decide
  rcases family_descends (prefixWord ++ tailWord_210655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210656 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 1, 3, 2]
def baseStart_210656 : Nat := 118140960795 + 210656 * 2 ^ 59
def prefixEnd_210656 : Nat := 4983230072969 + 3 ^ 40 * 210656 * 2
def baseEnd_210656 : Nat := 108167780753633041131217

theorem tailTrace_210656 : CollatzResearch.WordTrace tailWord_210656 prefixEnd_210656 108167780753633041131217 := by
  unfold tailWord_210656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3841627762418382012809911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5122170349891176017079881 3841627762418382012809911)
  ·
    refine ⟨5762441643627573019214867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3841627762418382012809911 5762441643627573019214867)
    ·
      refine ⟨8643662465441359528822301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5762441643627573019214867 8643662465441359528822301)
      ·
        refine ⟨3241373424540509823308363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8643662465441359528822301 3241373424540509823308363)
        ·
          refine ⟨4862060136810764734962545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241373424540509823308363 4862060136810764734962545)
          ·
            refine ⟨3646545102608073551221909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4862060136810764734962545 3646545102608073551221909)
            ·
              refine ⟨170931801684753447713527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3646545102608073551221909 170931801684753447713527)
              ·
                refine ⟨256397702527130171570291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170931801684753447713527 256397702527130171570291)
                ·
                  refine ⟨384596553790695257355437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256397702527130171570291 384596553790695257355437)
                  ·
                    refine ⟨144223707671510721508289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384596553790695257355437 144223707671510721508289)
                    ·
                      refine ⟨108167780753633041131217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144223707671510721508289 108167780753633041131217)
                      ·
                        rfl

theorem cell23_210656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_210656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210656 prefixEnd_210656 := by exact prefixLift 210656
  have htrace : WordTrace (prefixWord ++ tailWord_210656) baseStart_210656 baseEnd_210656 := by
    simpa [prefixWord, tailWord_210656, baseEnd_210656] using wordTrace_append hprefix tailTrace_210656
  have hstable : (prefixWord ++ tailWord_210656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210656).length < 2 ^ (prefixWord ++ tailWord_210656).sum := by decide
  have hdescent : baseEnd_210656 < baseStart_210656 := by decide
  rcases family_descends (prefixWord ++ tailWord_210656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210675 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 7]
def baseStart_210675 : Nat := 118140960795 + 210675 * 2 ^ 59
def prefixEnd_210675 : Nat := 4983230072969 + 3 ^ 40 * 210675 * 2
def baseEnd_210675 : Nat := 12019726320674274088181

theorem tailTrace_210675 : CollatzResearch.WordTrace tailWord_210675 prefixEnd_210675 12019726320674274088181 := by
  unfold tailWord_210675
  simp only [CollatzResearch.WordTrace]
  refine ⟨7683948511767930270561479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5122632341178620180374319 7683948511767930270561479)
  ·
    refine ⟨11525922767651895405842219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7683948511767930270561479 11525922767651895405842219)
    ·
      refine ⟨17288884151477843108763329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11525922767651895405842219 17288884151477843108763329)
      ·
        refine ⟨12966663113608382331572497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17288884151477843108763329 12966663113608382331572497)
        ·
          refine ⟨9724997335206286748679373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12966663113608382331572497 9724997335206286748679373)
          ·
            refine ⟨3646874000702357530754765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9724997335206286748679373 3646874000702357530754765)
            ·
              refine ⟨1367577750263384074033037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3646874000702357530754765 1367577750263384074033037)
              ·
                refine ⟨512841656348769027762389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1367577750263384074033037 512841656348769027762389)
                ·
                  refine ⟨12019726320674274088181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 512841656348769027762389 12019726320674274088181)
                  ·
                    rfl

theorem cell23_210675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 7].length) (baseStart_210675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210675 prefixEnd_210675 := by exact prefixLift 210675
  have htrace : WordTrace (prefixWord ++ tailWord_210675) baseStart_210675 baseEnd_210675 := by
    simpa [prefixWord, tailWord_210675, baseEnd_210675] using wordTrace_append hprefix tailTrace_210675
  have hstable : (prefixWord ++ tailWord_210675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210675).length < 2 ^ (prefixWord ++ tailWord_210675).sum := by decide
  have hdescent : baseEnd_210675 < baseStart_210675 := by decide
  rcases family_descends (prefixWord ++ tailWord_210675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210692 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 7]
def baseStart_210692 : Nat := 118140960795 + 210692 * 2 ^ 59
def prefixEnd_210692 : Nat := 4983230072969 + 3 ^ 40 * 210692 * 2
def baseEnd_210692 : Nat := 12020696228577211142339

theorem tailTrace_210692 : CollatzResearch.WordTrace tailWord_210692 prefixEnd_210692 12020696228577211142339 := by
  unfold tailWord_210692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842284276353171086965165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5123045701804228115953553 3842284276353171086965165)
  ·
    refine ⟨1440856603632439157611937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3842284276353171086965165 1440856603632439157611937)
    ·
      refine ⟨1080642452724329368208953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1440856603632439157611937 1080642452724329368208953)
      ·
        refine ⟨810481839543247026156715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1080642452724329368208953 810481839543247026156715)
        ·
          refine ⟨1215722759314870539235073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810481839543247026156715 1215722759314870539235073)
          ·
            refine ⟨911792069486152904426305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215722759314870539235073 911792069486152904426305)
            ·
              refine ⟨683844052114614678319729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911792069486152904426305 683844052114614678319729)
              ·
                refine ⟨512883039085961008739797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683844052114614678319729 512883039085961008739797)
                ·
                  refine ⟨12020696228577211142339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 512883039085961008739797 12020696228577211142339)
                  ·
                    rfl

theorem cell23_210692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_210692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210692 prefixEnd_210692 := by exact prefixLift 210692
  have htrace : WordTrace (prefixWord ++ tailWord_210692) baseStart_210692 baseEnd_210692 := by
    simpa [prefixWord, tailWord_210692, baseEnd_210692] using wordTrace_append hprefix tailTrace_210692
  have hstable : (prefixWord ++ tailWord_210692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210692).length < 2 ^ (prefixWord ++ tailWord_210692).sum := by decide
  have hdescent : baseEnd_210692 < baseStart_210692 := by decide
  rcases family_descends (prefixWord ++ tailWord_210692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210702 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_210702 : Nat := 118140960795 + 210702 * 2 ^ 59
def prefixEnd_210702 : Nat := 4983230072969 + 3 ^ 40 * 210702 * 2
def baseEnd_210702 : Nat := 108191400863739861156005

theorem tailTrace_210702 : CollatzResearch.WordTrace tailWord_210702 prefixEnd_210702 108191400863739861156005 := by
  unfold tailWord_210702
  simp only [CollatzResearch.WordTrace]
  refine ⟨960616660333764235224295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5123288855113409254529573 960616660333764235224295)
  ·
    refine ⟨1440924990500646352836443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960616660333764235224295 1440924990500646352836443)
    ·
      refine ⟨2161387485750969529254665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1440924990500646352836443 2161387485750969529254665)
      ·
        refine ⟨1621040614313227146940999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2161387485750969529254665 1621040614313227146940999)
        ·
          refine ⟨2431560921469840720411499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621040614313227146940999 2431560921469840720411499)
          ·
            refine ⟨3647341382204761080617249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431560921469840720411499 3647341382204761080617249)
            ·
              refine ⟨2735506036653570810462937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647341382204761080617249 2735506036653570810462937)
              ·
                refine ⟨2051629527490178107847203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735506036653570810462937 2051629527490178107847203)
                ·
                  refine ⟨3077444291235267161770805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051629527490178107847203 3077444291235267161770805)
                  ·
                    refine ⟨288510402303306296416013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3077444291235267161770805 288510402303306296416013)
                    ·
                      refine ⟨108191400863739861156005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 288510402303306296416013 108191400863739861156005)
                      ·
                        rfl

theorem cell23_210702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_210702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210702 prefixEnd_210702 := by exact prefixLift 210702
  have htrace : WordTrace (prefixWord ++ tailWord_210702) baseStart_210702 baseEnd_210702 := by
    simpa [prefixWord, tailWord_210702, baseEnd_210702] using wordTrace_append hprefix tailTrace_210702
  have hstable : (prefixWord ++ tailWord_210702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210702).length < 2 ^ (prefixWord ++ tailWord_210702).sum := by decide
  have hdescent : baseEnd_210702 < baseStart_210702 := by decide
  rcases family_descends (prefixWord ++ tailWord_210702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210709 : List Nat := [1, 3, 2, 1, 2, 3, 3, 3, 5]
def baseStart_210709 : Nat := 118140960795 + 210709 * 2 ^ 59
def prefixEnd_210709 : Nat := 4983230072969 + 3 ^ 40 * 210709 * 2
def baseEnd_210709 : Nat := 12021666136480148196497

theorem tailTrace_210709 : CollatzResearch.WordTrace tailWord_210709 prefixEnd_210709 12021666136480148196497 := by
  unfold tailWord_210709
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685188593644754077299181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5123459062429836051532787 7685188593644754077299181)
  ·
    refine ⟨2881945722616782778987193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7685188593644754077299181 2881945722616782778987193)
    ·
      refine ⟨2161459291962587084240395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2881945722616782778987193 2161459291962587084240395)
      ·
        refine ⟨3242188937943880626360593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161459291962587084240395 3242188937943880626360593)
        ·
          refine ⟨2431641703457910469770445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3242188937943880626360593 2431641703457910469770445)
          ·
            refine ⟨911865638796716426163917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2431641703457910469770445 911865638796716426163917)
            ·
              refine ⟨341949614548768659811469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911865638796716426163917 341949614548768659811469)
              ·
                refine ⟨128231105455788247429301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341949614548768659811469 128231105455788247429301)
                ·
                  refine ⟨12021666136480148196497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128231105455788247429301 12021666136480148196497)
                  ·
                    rfl

theorem cell23_210709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_210709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210709 prefixEnd_210709 := by exact prefixLift 210709
  have htrace : WordTrace (prefixWord ++ tailWord_210709) baseStart_210709 baseEnd_210709 := by
    simpa [prefixWord, tailWord_210709, baseEnd_210709] using wordTrace_append hprefix tailTrace_210709
  have hstable : (prefixWord ++ tailWord_210709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210709).length < 2 ^ (prefixWord ++ tailWord_210709).sum := by decide
  have hdescent : baseEnd_210709 < baseStart_210709 := by decide
  rcases family_descends (prefixWord ++ tailWord_210709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210715 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5]
def baseStart_210715 : Nat := 118140960795 + 210715 * 2 ^ 59
def prefixEnd_210715 : Nat := 4983230072969 + 3 ^ 40 * 210715 * 2
def baseEnd_210715 : Nat := 108198076112248310293445

theorem tailTrace_210715 : CollatzResearch.WordTrace tailWord_210715 prefixEnd_210715 108198076112248310293445 := by
  unfold tailWord_210715
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685407431623017102017599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5123604954415344734678399 7685407431623017102017599)
  ·
    refine ⟨11528111147434525653026399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7685407431623017102017599 11528111147434525653026399)
    ·
      refine ⟨17292166721151788479539599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11528111147434525653026399 17292166721151788479539599)
      ·
        refine ⟨25938250081727682719309399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17292166721151788479539599 25938250081727682719309399)
        ·
          refine ⟨38907375122591524078964099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25938250081727682719309399 38907375122591524078964099)
          ·
            refine ⟨58361062683887286118446149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38907375122591524078964099 58361062683887286118446149)
            ·
              refine ⟨10942699253228866147208653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58361062683887286118446149 10942699253228866147208653)
              ·
                refine ⟨4103512219960824805203245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10942699253228866147208653 4103512219960824805203245)
                ·
                  refine ⟨1538817082485309301951217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4103512219960824805203245 1538817082485309301951217)
                  ·
                    refine ⟨1154112811863981976463413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1538817082485309301951217 1154112811863981976463413)
                    ·
                      refine ⟨108198076112248310293445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1154112811863981976463413 108198076112248310293445)
                      ·
                        rfl

theorem cell23_210715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_210715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210715 prefixEnd_210715 := by exact prefixLift 210715
  have htrace : WordTrace (prefixWord ++ tailWord_210715) baseStart_210715 baseEnd_210715 := by
    simpa [prefixWord, tailWord_210715, baseEnd_210715] using wordTrace_append hprefix tailTrace_210715
  have hstable : (prefixWord ++ tailWord_210715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210715).length < 2 ^ (prefixWord ++ tailWord_210715).sum := by decide
  have hdescent : baseEnd_210715 < baseStart_210715 := by decide
  rcases family_descends (prefixWord ++ tailWord_210715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210732 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_210732 : Nat := 118140960795 + 210732 * 2 ^ 59
def prefixEnd_210732 : Nat := 4983230072969 + 3 ^ 40 * 210732 * 2
def baseEnd_210732 : Nat := 108206805283374743780867

theorem tailTrace_210732 : CollatzResearch.WordTrace tailWord_210732 prefixEnd_210732 108206805283374743780867 := by
  unfold tailWord_210732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843013736280714502693225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5124018315040952670257633 3843013736280714502693225)
  ·
    refine ⟨2882260302210535877019919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3843013736280714502693225 2882260302210535877019919)
    ·
      refine ⟨4323390453315803815529879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882260302210535877019919 4323390453315803815529879)
      ·
        refine ⟨6485085679973705723294819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323390453315803815529879 6485085679973705723294819)
        ·
          refine ⟨9727628519960558584942229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485085679973705723294819 9727628519960558584942229)
          ·
            refine ⟨455982586873151183669167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9727628519960558584942229 455982586873151183669167)
            ·
              refine ⟨683973880309726775503751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455982586873151183669167 683973880309726775503751)
              ·
                refine ⟨1025960820464590163255627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683973880309726775503751 1025960820464590163255627)
                ·
                  refine ⟨1538941230696885244883441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025960820464590163255627 1538941230696885244883441)
                  ·
                    refine ⟨1154205923022663933662581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1538941230696885244883441 1154205923022663933662581)
                    ·
                      refine ⟨108206805283374743780867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1154205923022663933662581 108206805283374743780867)
                      ·
                        rfl

theorem cell23_210732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_210732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210732 prefixEnd_210732 := by exact prefixLift 210732
  have htrace : WordTrace (prefixWord ++ tailWord_210732) baseStart_210732 baseEnd_210732 := by
    simpa [prefixWord, tailWord_210732, baseEnd_210732] using wordTrace_append hprefix tailTrace_210732
  have hstable : (prefixWord ++ tailWord_210732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210732).length < 2 ^ (prefixWord ++ tailWord_210732).sum := by decide
  have hdescent : baseEnd_210732 < baseStart_210732 := by decide
  rcases family_descends (prefixWord ++ tailWord_210732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210872 : List Nat := [2, 1, 2, 1, 2, 3, 3, 9]
def baseStart_210872 : Nat := 118140960795 + 210872 * 2 ^ 59
def prefixEnd_210872 : Nat := 4983230072969 + 3 ^ 40 * 210872 * 2
def baseEnd_210872 : Nat := 4010321947222377630749

theorem tailTrace_210872 : CollatzResearch.WordTrace tailWord_210872 prefixEnd_210872 4010321947222377630749 := by
  unfold tailWord_210872
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845566846027116457741435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5127422461369488610321913 3845566846027116457741435)
  ·
    refine ⟨5768350269040674686612153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3845566846027116457741435 5768350269040674686612153)
    ·
      refine ⟨4326262701780506014959115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5768350269040674686612153 4326262701780506014959115)
      ·
        refine ⟨6489394052670759022438673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326262701780506014959115 6489394052670759022438673)
        ·
          refine ⟨4867045539503069266829005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6489394052670759022438673 4867045539503069266829005)
          ·
            refine ⟨1825142077313650975060877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4867045539503069266829005 1825142077313650975060877)
            ·
              refine ⟨684428278992619115647829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1825142077313650975060877 684428278992619115647829)
              ·
                refine ⟨4010321947222377630749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 684428278992619115647829 4010321947222377630749)
                ·
                  rfl

theorem cell23_210872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 9].length) (baseStart_210872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210872 prefixEnd_210872 := by exact prefixLift 210872
  have htrace : WordTrace (prefixWord ++ tailWord_210872) baseStart_210872 baseEnd_210872 := by
    simpa [prefixWord, tailWord_210872, baseEnd_210872] using wordTrace_append hprefix tailTrace_210872
  have hstable : (prefixWord ++ tailWord_210872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210872).length < 2 ^ (prefixWord ++ tailWord_210872).sum := by decide
  have hdescent : baseEnd_210872 < baseStart_210872 := by decide
  rcases family_descends (prefixWord ++ tailWord_210872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210956 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 3, 4, 2]
def baseStart_210956 : Nat := 118140960795 + 210956 * 2 ^ 59
def prefixEnd_210956 : Nat := 4983230072969 + 3 ^ 40 * 210956 * 2
def baseEnd_210956 : Nat := 108321824949981867379837

theorem tailTrace_210956 : CollatzResearch.WordTrace tailWord_210956 prefixEnd_210956 108321824949981867379837 := by
  unfold tailWord_210956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3847098711874957630770361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5129464949166610174360481 3847098711874957630770361)
  ·
    refine ⟨2885324033906218223077771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3847098711874957630770361 2885324033906218223077771)
    ·
      refine ⟨4327986050859327334616657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885324033906218223077771 4327986050859327334616657)
      ·
        refine ⟨3245989538144495500962493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4327986050859327334616657 3245989538144495500962493)
        ·
          refine ⟨1217246076804185812860935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3245989538144495500962493 1217246076804185812860935)
          ·
            refine ⟨1825869115206278719291403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217246076804185812860935 1825869115206278719291403)
            ·
              refine ⟨2738803672809418078937105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825869115206278719291403 2738803672809418078937105)
              ·
                refine ⟨2054102754607063559202829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2738803672809418078937105 2054102754607063559202829)
                ·
                  refine ⟨770288532977648834701061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2054102754607063559202829 770288532977648834701061)
                  ·
                    refine ⟨144429099933309156506449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770288532977648834701061 144429099933309156506449)
                    ·
                      refine ⟨108321824949981867379837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144429099933309156506449 108321824949981867379837)
                      ·
                        rfl

theorem cell23_210956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_210956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210956 prefixEnd_210956 := by exact prefixLift 210956
  have htrace : WordTrace (prefixWord ++ tailWord_210956) baseStart_210956 baseEnd_210956 := by
    simpa [prefixWord, tailWord_210956, baseEnd_210956] using wordTrace_append hprefix tailTrace_210956
  have hstable : (prefixWord ++ tailWord_210956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210956).length < 2 ^ (prefixWord ++ tailWord_210956).sum := by decide
  have hdescent : baseEnd_210956 < baseStart_210956 := by decide
  rcases family_descends (prefixWord ++ tailWord_210956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210957 : List Nat := [1, 7, 1, 2, 2, 1, 1, 8]
def baseStart_210957 : Nat := 118140960795 + 210957 * 2 ^ 59
def prefixEnd_210957 : Nat := 4983230072969 + 3 ^ 40 * 210957 * 2
def baseEnd_210957 : Nat := 4011938460393939387679

theorem tailTrace_210957 : CollatzResearch.WordTrace tailWord_210957 prefixEnd_210957 4011938460393939387679 := by
  unfold tailWord_210957
  simp only [CollatzResearch.WordTrace]
  refine ⟨7694233896746292432327125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5129489264497528288218083 7694233896746292432327125)
  ·
    refine ⟨180333606954991228882667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7694233896746292432327125 180333606954991228882667)
    ·
      refine ⟨270500410432486843324001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180333606954991228882667 270500410432486843324001)
      ·
        refine ⟨202875307824365132493001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270500410432486843324001 202875307824365132493001)
        ·
          refine ⟨152156480868273849369751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202875307824365132493001 152156480868273849369751)
          ·
            refine ⟨228234721302410774054627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152156480868273849369751 228234721302410774054627)
            ·
              refine ⟨342352081953616161081941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228234721302410774054627 342352081953616161081941)
              ·
                refine ⟨4011938460393939387679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 342352081953616161081941 4011938460393939387679)
                ·
                  rfl

theorem cell23_210957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 8].length) (baseStart_210957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210957 prefixEnd_210957 := by exact prefixLift 210957
  have htrace : WordTrace (prefixWord ++ tailWord_210957) baseStart_210957 baseEnd_210957 := by
    simpa [prefixWord, tailWord_210957, baseEnd_210957] using wordTrace_append hprefix tailTrace_210957
  have hstable : (prefixWord ++ tailWord_210957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210957).length < 2 ^ (prefixWord ++ tailWord_210957).sum := by decide
  have hdescent : baseEnd_210957 < baseStart_210957 := by decide
  rcases family_descends (prefixWord ++ tailWord_210957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210973 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_210973 : Nat := 118140960795 + 210973 * 2 ^ 59
def prefixEnd_210973 : Nat := 4983230072969 + 3 ^ 40 * 210973 * 2
def baseEnd_210973 : Nat := 108330554121108300867259

theorem tailTrace_210973 : CollatzResearch.WordTrace tailWord_210973 prefixEnd_210973 108330554121108300867259 := by
  unfold tailWord_210973
  simp only [CollatzResearch.WordTrace]
  refine ⟨7694817464688327164909573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5129878309792218109939715 7694817464688327164909573)
  ·
    refine ⟨1442778274629061343420545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7694817464688327164909573 1442778274629061343420545)
    ·
      refine ⟨1082083705971796007565409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1442778274629061343420545 1082083705971796007565409)
      ·
        refine ⟨811562779478847005674057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1082083705971796007565409 811562779478847005674057)
        ·
          refine ⟨608672084609135254255543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811562779478847005674057 608672084609135254255543)
          ·
            refine ⟨913008126913702881383315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608672084609135254255543 913008126913702881383315)
            ·
              refine ⟨1369512190370554322074973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913008126913702881383315 1369512190370554322074973)
              ·
                refine ⟨513567071388957870778115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1369512190370554322074973 513567071388957870778115)
                ·
                  refine ⟨770350607083436806167173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513567071388957870778115 770350607083436806167173)
                  ·
                    refine ⟨144440738828144401156345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770350607083436806167173 144440738828144401156345)
                    ·
                      refine ⟨108330554121108300867259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144440738828144401156345 108330554121108300867259)
                      ·
                        rfl

theorem cell23_210973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_210973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210973 prefixEnd_210973 := by exact prefixLift 210973
  have htrace : WordTrace (prefixWord ++ tailWord_210973) baseStart_210973 baseEnd_210973 := by
    simpa [prefixWord, tailWord_210973, baseEnd_210973] using wordTrace_append hprefix tailTrace_210973
  have hstable : (prefixWord ++ tailWord_210973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210973).length < 2 ^ (prefixWord ++ tailWord_210973).sum := by decide
  have hdescent : baseEnd_210973 < baseStart_210973 := by decide
  rcases family_descends (prefixWord ++ tailWord_210973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_210979 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 7]
def baseStart_210979 : Nat := 118140960795 + 210979 * 2 ^ 59
def prefixEnd_210979 : Nat := 4983230072969 + 3 ^ 40 * 210979 * 2
def baseEnd_210979 : Nat := 12037070556115030821359

theorem tailTrace_210979 : CollatzResearch.WordTrace tailWord_210979 prefixEnd_210979 12037070556115030821359 := by
  unfold tailWord_210979
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695036302666590189627991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5130024201777726793085327 7695036302666590189627991)
  ·
    refine ⟨11542554453999885284441987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7695036302666590189627991 11542554453999885284441987)
    ·
      refine ⟨17313831680999827926662981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11542554453999885284441987 17313831680999827926662981)
      ·
        refine ⟨3246343440187467736249309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17313831680999827926662981 3246343440187467736249309)
        ·
          refine ⟨1217378790070300401093491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3246343440187467736249309 1217378790070300401093491)
          ·
            refine ⟨1826068185105450601640237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217378790070300401093491 1826068185105450601640237)
            ·
              refine ⟨684775569414543975615089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1826068185105450601640237 684775569414543975615089)
              ·
                refine ⟨513581677060907981711317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684775569414543975615089 513581677060907981711317)
                ·
                  refine ⟨12037070556115030821359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 513581677060907981711317 12037070556115030821359)
                  ·
                    rfl

theorem cell23_210979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 7].length) (baseStart_210979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_210979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_210979 prefixEnd_210979 := by exact prefixLift 210979
  have htrace : WordTrace (prefixWord ++ tailWord_210979) baseStart_210979 baseEnd_210979 := by
    simpa [prefixWord, tailWord_210979, baseEnd_210979] using wordTrace_append hprefix tailTrace_210979
  have hstable : (prefixWord ++ tailWord_210979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_210979).length < 2 ^ (prefixWord ++ tailWord_210979).sum := by decide
  have hdescent : baseEnd_210979 < baseStart_210979 := by decide
  rcases family_descends (prefixWord ++ tailWord_210979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211016 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_211016 : Nat := 118140960795 + 211016 * 2 ^ 59
def prefixEnd_211016 : Nat := 4983230072969 + 3 ^ 40 * 211016 * 2
def baseEnd_211016 : Nat := 108352633789251632629561

theorem tailTrace_211016 : CollatzResearch.WordTrace tailWord_211016 prefixEnd_211016 108352633789251632629561 := by
  unfold tailWord_211016
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848192901766272754362451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5130923869021697005816601 3848192901766272754362451)
  ·
    refine ⟨5772289352649409131543677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3848192901766272754362451 5772289352649409131543677)
    ·
      refine ⟨2164608507243528424328879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5772289352649409131543677 2164608507243528424328879)
      ·
        refine ⟨3246912760865292636493319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164608507243528424328879 3246912760865292636493319)
        ·
          refine ⟨4870369141297938954739979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246912760865292636493319 4870369141297938954739979)
          ·
            refine ⟨7305553711946908432109969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870369141297938954739979 7305553711946908432109969)
            ·
              refine ⟨5479165283960181324082477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305553711946908432109969 5479165283960181324082477)
              ·
                refine ⟨2054686981485067996530929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5479165283960181324082477 2054686981485067996530929)
                ·
                  refine ⟨1541015236113800997398197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054686981485067996530929 1541015236113800997398197)
                  ·
                    refine ⟨144470178385668843506081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1541015236113800997398197 144470178385668843506081)
                    ·
                      refine ⟨108352633789251632629561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144470178385668843506081 108352633789251632629561)
                      ·
                        rfl

theorem cell23_211016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_211016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211016 prefixEnd_211016 := by exact prefixLift 211016
  have htrace : WordTrace (prefixWord ++ tailWord_211016) baseStart_211016 baseEnd_211016 := by
    simpa [prefixWord, tailWord_211016, baseEnd_211016] using wordTrace_append hprefix tailTrace_211016
  have hstable : (prefixWord ++ tailWord_211016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211016).length < 2 ^ (prefixWord ++ tailWord_211016).sum := by decide
  have hdescent : baseEnd_211016 < baseStart_211016 := by decide
  rcases family_descends (prefixWord ++ tailWord_211016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211176 : List Nat := [2, 1, 4, 1, 2, 3, 10]
def baseStart_211176 : Nat := 118140960795 + 211176 * 2 ^ 59
def prefixEnd_211176 : Nat := 4983230072969 + 3 ^ 40 * 211176 * 2
def baseEnd_211176 : Nat := 1338701119678654402825

theorem tailTrace_211176 : CollatzResearch.WordTrace tailWord_211176 prefixEnd_211176 1338701119678654402825 := by
  unfold tailWord_211176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3851110741476446417274691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5134814321968595223032921 3851110741476446417274691)
  ·
    refine ⟨5776666112214669625912037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3851110741476446417274691 5776666112214669625912037)
    ·
      refine ⟨1083124896040250554858507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5776666112214669625912037 1083124896040250554858507)
      ·
        refine ⟨1624687344060375832287761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083124896040250554858507 1624687344060375832287761)
        ·
          refine ⟨1218515508045281874215821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1624687344060375832287761 1218515508045281874215821)
          ·
            refine ⟨456943315516980702830933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1218515508045281874215821 456943315516980702830933)
            ·
              refine ⟨1338701119678654402825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 456943315516980702830933 1338701119678654402825)
              ·
                rfl

theorem cell23_211176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 10].length) (baseStart_211176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211176 prefixEnd_211176 := by exact prefixLift 211176
  have htrace : WordTrace (prefixWord ++ tailWord_211176) baseStart_211176 baseEnd_211176 := by
    simpa [prefixWord, tailWord_211176, baseEnd_211176] using wordTrace_append hprefix tailTrace_211176
  have hstable : (prefixWord ++ tailWord_211176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211176).length < 2 ^ (prefixWord ++ tailWord_211176).sum := by decide
  have hdescent : baseEnd_211176 < baseStart_211176 := by decide
  rcases family_descends (prefixWord ++ tailWord_211176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211187 : List Nat := [1, 1, 1, 2, 2, 4, 1, 6, 1, 2, 2]
def baseStart_211187 : Nat := 118140960795 + 211187 * 2 ^ 59
def prefixEnd_211187 : Nat := 4983230072969 + 3 ^ 40 * 211187 * 2
def baseEnd_211187 : Nat := 108440438981170463591275

theorem tailTrace_211187 : CollatzResearch.WordTrace tailWord_211187 prefixEnd_211187 108440438981170463591275 := by
  unfold tailWord_211187
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702622685913041713199815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5135081790608694475466543 7702622685913041713199815)
  ·
    refine ⟨11553934028869562569799723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7702622685913041713199815 11553934028869562569799723)
    ·
      refine ⟨17330901043304343854699585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11553934028869562569799723 17330901043304343854699585)
      ·
        refine ⟨12998175782478257891024689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17330901043304343854699585 12998175782478257891024689)
        ·
          refine ⟨9748631836858693418268517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12998175782478257891024689 9748631836858693418268517)
          ·
            refine ⟨1827868469411005015925347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9748631836858693418268517 1827868469411005015925347)
            ·
              refine ⟨2741802704116507523888021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827868469411005015925347 2741802704116507523888021)
              ·
                refine ⟨128522001755461290182251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2741802704116507523888021 128522001755461290182251)
                ·
                  refine ⟨192783002633191935273377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128522001755461290182251 192783002633191935273377)
                  ·
                    refine ⟨144587251974893951455033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 192783002633191935273377 144587251974893951455033)
                    ·
                      refine ⟨108440438981170463591275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144587251974893951455033 108440438981170463591275)
                      ·
                        rfl

theorem cell23_211187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 2, 2].length) (baseStart_211187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211187 prefixEnd_211187 := by exact prefixLift 211187
  have htrace : WordTrace (prefixWord ++ tailWord_211187) baseStart_211187 baseEnd_211187 := by
    simpa [prefixWord, tailWord_211187, baseEnd_211187] using wordTrace_append hprefix tailTrace_211187
  have hstable : (prefixWord ++ tailWord_211187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211187).length < 2 ^ (prefixWord ++ tailWord_211187).sum := by decide
  have hdescent : baseEnd_211187 < baseStart_211187 := by decide
  rcases family_descends (prefixWord ++ tailWord_211187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211260 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_211260 : Nat := 118140960795 + 211260 * 2 ^ 59
def prefixEnd_211260 : Nat := 4983230072969 + 3 ^ 40 * 211260 * 2
def baseEnd_211260 : Nat := 108477923068948677978439

theorem tailTrace_211260 : CollatzResearch.WordTrace tailWord_211260 prefixEnd_211260 108477923068948677978439 := by
  unfold tailWord_211260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852642607324287590303617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5136856809765716787071489 3852642607324287590303617)
  ·
    refine ⟨2889481955493215692727713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3852642607324287590303617 2889481955493215692727713)
    ·
      refine ⟨2167111466619911769545785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2889481955493215692727713 2167111466619911769545785)
      ·
        refine ⟨1625333599964933827159339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2167111466619911769545785 1625333599964933827159339)
        ·
          refine ⟨2438000399947400740739009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625333599964933827159339 2438000399947400740739009)
          ·
            refine ⟨1828500299960550555554257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438000399947400740739009 1828500299960550555554257)
            ·
              refine ⟨1371375224970412916665693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828500299960550555554257 1371375224970412916665693)
              ·
                refine ⟨514265709363904843749635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1371375224970412916665693 514265709363904843749635)
                ·
                  refine ⟨771398564045857265624453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514265709363904843749635 771398564045857265624453)
                  ·
                    refine ⟨144637230758598237304585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771398564045857265624453 144637230758598237304585)
                    ·
                      refine ⟨108477923068948677978439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144637230758598237304585 108477923068948677978439)
                      ·
                        rfl

theorem cell23_211260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_211260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211260 prefixEnd_211260 := by exact prefixLift 211260
  have htrace : WordTrace (prefixWord ++ tailWord_211260) baseStart_211260 baseEnd_211260 := by
    simpa [prefixWord, tailWord_211260, baseEnd_211260] using wordTrace_append hprefix tailTrace_211260
  have hstable : (prefixWord ++ tailWord_211260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211260).length < 2 ^ (prefixWord ++ tailWord_211260).sum := by decide
  have hdescent : baseEnd_211260 < baseStart_211260 := by decide
  rcases family_descends (prefixWord ++ tailWord_211260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211300 : List Nat := [2, 3, 1, 1, 3, 1, 3, 4, 5]
def baseStart_211300 : Nat := 118140960795 + 211300 * 2 ^ 59
def prefixEnd_211300 : Nat := 4983230072969 + 3 ^ 40 * 211300 * 2
def baseEnd_211300 : Nat := 12055384699458724608695

theorem tailTrace_211300 : CollatzResearch.WordTrace tailWord_211300 prefixEnd_211300 12055384699458724608695 := by
  unfold tailWord_211300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853372067251831006031677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5137829423002441341375569 3853372067251831006031677)
  ·
    refine ⟨1445014525219436627261879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3853372067251831006031677 1445014525219436627261879)
    ·
      refine ⟨2167521787829154940892819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445014525219436627261879 2167521787829154940892819)
      ·
        refine ⟨3251282681743732411339229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167521787829154940892819 3251282681743732411339229)
        ·
          refine ⟨1219231005653899654252211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3251282681743732411339229 1219231005653899654252211)
          ·
            refine ⟨1828846508480849481378317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219231005653899654252211 1828846508480849481378317)
            ·
              refine ⟨685817440680318555516869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1828846508480849481378317 685817440680318555516869)
              ·
                refine ⟨128590770127559729159413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685817440680318555516869 128590770127559729159413)
                ·
                  refine ⟨12055384699458724608695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128590770127559729159413 12055384699458724608695)
                  ·
                    rfl

theorem cell23_211300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_211300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211300 prefixEnd_211300 := by exact prefixLift 211300
  have htrace : WordTrace (prefixWord ++ tailWord_211300) baseStart_211300 baseEnd_211300 := by
    simpa [prefixWord, tailWord_211300, baseEnd_211300] using wordTrace_append hprefix tailTrace_211300
  have hstable : (prefixWord ++ tailWord_211300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211300).length < 2 ^ (prefixWord ++ tailWord_211300).sum := by decide
  have hdescent : baseEnd_211300 < baseStart_211300 := by decide
  rcases family_descends (prefixWord ++ tailWord_211300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211360 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 3, 4]
def baseStart_211360 : Nat := 118140960795 + 211360 * 2 ^ 59
def prefixEnd_211360 : Nat := 4983230072969 + 3 ^ 40 * 211360 * 2
def baseEnd_211360 : Nat := 36176423711466095575993

theorem tailTrace_211360 : CollatzResearch.WordTrace tailWord_211360 prefixEnd_211360 36176423711466095575993 := by
  unfold tailWord_211360
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854466257143146129623767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5139288342857528172831689 3854466257143146129623767)
  ·
    refine ⟨5781699385714719194435651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3854466257143146129623767 5781699385714719194435651)
    ·
      refine ⟨8672549078572078791653477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5781699385714719194435651 8672549078572078791653477)
      ·
        refine ⟨1626102952232264773435027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8672549078572078791653477 1626102952232264773435027)
        ·
          refine ⟨2439154428348397160152541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1626102952232264773435027 2439154428348397160152541)
          ·
            refine ⟨914682910630648935057203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2439154428348397160152541 914682910630648935057203)
            ·
              refine ⟨1372024365945973402585805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914682910630648935057203 1372024365945973402585805)
              ·
                refine ⟨514509137229740025969677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1372024365945973402585805 514509137229740025969677)
                ·
                  refine ⟨192940926461152509738629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514509137229740025969677 192940926461152509738629)
                  ·
                    refine ⟨36176423711466095575993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192940926461152509738629 36176423711466095575993)
                    ·
                      rfl

theorem cell23_211360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_211360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211360 prefixEnd_211360 := by exact prefixLift 211360
  have htrace : WordTrace (prefixWord ++ tailWord_211360) baseStart_211360 baseEnd_211360 := by
    simpa [prefixWord, tailWord_211360, baseEnd_211360] using wordTrace_append hprefix tailTrace_211360
  have hstable : (prefixWord ++ tailWord_211360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211360).length < 2 ^ (prefixWord ++ tailWord_211360).sum := by decide
  have hdescent : baseEnd_211360 < baseStart_211360 := by decide
  rcases family_descends (prefixWord ++ tailWord_211360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211367 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_211367 : Nat := 118140960795 + 211367 * 2 ^ 59
def prefixEnd_211367 : Nat := 4983230072969 + 3 ^ 40 * 211367 * 2
def baseEnd_211367 : Nat := 108532865498979759340447

theorem tailTrace_211367 : CollatzResearch.WordTrace tailWord_211367 prefixEnd_211367 108532865498979759340447 := by
  unfold tailWord_211367
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709187825260932454752355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5139458550173954969834903 7709187825260932454752355)
  ·
    refine ⟨11563781737891398682128533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7709187825260932454752355 11563781737891398682128533)
    ·
      refine ⟨542052268963659313224775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11563781737891398682128533 542052268963659313224775)
      ·
        refine ⟨813078403445488969837163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542052268963659313224775 813078403445488969837163)
        ·
          refine ⟨1219617605168233454755745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813078403445488969837163 1219617605168233454755745)
          ·
            refine ⟨914713203876175091066809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219617605168233454755745 914713203876175091066809)
            ·
              refine ⟨686034902907131318300107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914713203876175091066809 686034902907131318300107)
              ·
                refine ⟨1029052354360696977450161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686034902907131318300107 1029052354360696977450161)
                ·
                  refine ⟨771789265770522733087621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029052354360696977450161 771789265770522733087621)
                  ·
                    refine ⟨144710487331973012453929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771789265770522733087621 144710487331973012453929)
                    ·
                      refine ⟨108532865498979759340447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144710487331973012453929 108532865498979759340447)
                      ·
                        rfl

theorem cell23_211367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_211367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211367 prefixEnd_211367 := by exact prefixLift 211367
  have htrace : WordTrace (prefixWord ++ tailWord_211367) baseStart_211367 baseEnd_211367 := by
    simpa [prefixWord, tailWord_211367, baseEnd_211367] using wordTrace_append hprefix tailTrace_211367
  have hstable : (prefixWord ++ tailWord_211367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211367).length < 2 ^ (prefixWord ++ tailWord_211367).sum := by decide
  have hdescent : baseEnd_211367 < baseStart_211367 := by decide
  rcases family_descends (prefixWord ++ tailWord_211367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211403 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 5, 5]
def baseStart_211403 : Nat := 118140960795 + 211403 * 2 ^ 59
def prefixEnd_211403 : Nat := 4983230072969 + 3 ^ 40 * 211403 * 2
def baseEnd_211403 : Nat := 36183783600847206163427

theorem tailTrace_211403 : CollatzResearch.WordTrace tailWord_211403 prefixEnd_211403 36183783600847206163427 := by
  unfold tailWord_211403
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710500853130510603062863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5140333902087007068708575 7710500853130510603062863)
  ·
    refine ⟨11565751279695765904594295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7710500853130510603062863 11565751279695765904594295)
    ·
      refine ⟨17348626919543648856891443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11565751279695765904594295 17348626919543648856891443)
      ·
        refine ⟨26022940379315473285337165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348626919543648856891443 26022940379315473285337165)
        ·
          refine ⟨9758602642243302482001437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26022940379315473285337165 9758602642243302482001437)
          ·
            refine ⟨3659475990841238430750539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9758602642243302482001437 3659475990841238430750539)
            ·
              refine ⟨5489213986261857646125809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659475990841238430750539 5489213986261857646125809)
              ·
                refine ⟨4116910489696393234594357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5489213986261857646125809 4116910489696393234594357)
                ·
                  refine ⟨385960358409036865743221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4116910489696393234594357 385960358409036865743221)
                  ·
                    refine ⟨36183783600847206163427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 385960358409036865743221 36183783600847206163427)
                    ·
                      rfl

theorem cell23_211403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 5].length) (baseStart_211403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211403 prefixEnd_211403 := by exact prefixLift 211403
  have htrace : WordTrace (prefixWord ++ tailWord_211403) baseStart_211403 baseEnd_211403 := by
    simpa [prefixWord, tailWord_211403, baseEnd_211403] using wordTrace_append hprefix tailTrace_211403
  have hstable : (prefixWord ++ tailWord_211403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211403).length < 2 ^ (prefixWord ++ tailWord_211403).sum := by decide
  have hdescent : baseEnd_211403 < baseStart_211403 := by decide
  rcases family_descends (prefixWord ++ tailWord_211403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211437 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_211437 : Nat := 118140960795 + 211437 * 2 ^ 59
def prefixEnd_211437 : Nat := 4983230072969 + 3 ^ 40 * 211437 * 2
def baseEnd_211437 : Nat := 36189603048264828488375

theorem tailTrace_211437 : CollatzResearch.WordTrace tailWord_211437 prefixEnd_211437 36189603048264828488375 := by
  unfold tailWord_211437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711740935007334409800565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5141160623338222939867043 7711740935007334409800565)
  ·
    refine ⟨722975712656937600918803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7711740935007334409800565 722975712656937600918803)
    ·
      refine ⟨1084463568985406401378205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722975712656937600918803 1084463568985406401378205)
      ·
        refine ⟨406673838369527400516827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1084463568985406401378205 406673838369527400516827)
        ·
          refine ⟨610010757554291100775241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406673838369527400516827 610010757554291100775241)
          ·
            refine ⟨457508068165718325581431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610010757554291100775241 457508068165718325581431)
            ·
              refine ⟨686262102248577488372147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457508068165718325581431 686262102248577488372147)
              ·
                refine ⟨1029393153372866232558221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686262102248577488372147 1029393153372866232558221)
                ·
                  refine ⟨386022432514824837209333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029393153372866232558221 386022432514824837209333)
                  ·
                    refine ⟨36189603048264828488375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 386022432514824837209333 36189603048264828488375)
                    ·
                      rfl

theorem cell23_211437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_211437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211437 prefixEnd_211437 := by exact prefixLift 211437
  have htrace : WordTrace (prefixWord ++ tailWord_211437) baseStart_211437 baseEnd_211437 := by
    simpa [prefixWord, tailWord_211437, baseEnd_211437] using wordTrace_append hprefix tailTrace_211437
  have hstable : (prefixWord ++ tailWord_211437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211437).length < 2 ^ (prefixWord ++ tailWord_211437).sum := by decide
  have hdescent : baseEnd_211437 < baseStart_211437 := by decide
  rcases family_descends (prefixWord ++ tailWord_211437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211440 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_211440 : Nat := 118140960795 + 211440 * 2 ^ 59
def prefixEnd_211440 : Nat := 4983230072969 + 3 ^ 40 * 211440 * 2
def baseEnd_211440 : Nat := 108570349586757973727611

theorem tailTrace_211440 : CollatzResearch.WordTrace tailWord_211440 prefixEnd_211440 108570349586757973727611 := by
  unfold tailWord_211440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855925176998232961079887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5141233569330977281439849 3855925176998232961079887)
  ·
    refine ⟨5783887765497349441619831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3855925176998232961079887 5783887765497349441619831)
    ·
      refine ⟨8675831648246024162429747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783887765497349441619831 8675831648246024162429747)
      ·
        refine ⟨13013747472369036243644621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675831648246024162429747 13013747472369036243644621)
        ·
          refine ⟨4880155302138388591366733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13013747472369036243644621 4880155302138388591366733)
          ·
            refine ⟨1830058238301895721762525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4880155302138388591366733 1830058238301895721762525)
            ·
              refine ⟨686271839363210895660947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1830058238301895721762525 686271839363210895660947)
              ·
                refine ⟨1029407759044816343491421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686271839363210895660947 1029407759044816343491421)
                ·
                  refine ⟨386027909641806128809283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029407759044816343491421 386027909641806128809283)
                  ·
                    refine ⟨579041864462709193213925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 386027909641806128809283 579041864462709193213925)
                    ·
                      refine ⟨108570349586757973727611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 579041864462709193213925 108570349586757973727611)
                      ·
                        rfl

theorem cell23_211440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_211440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211440 prefixEnd_211440 := by exact prefixLift 211440
  have htrace : WordTrace (prefixWord ++ tailWord_211440) baseStart_211440 baseEnd_211440 := by
    simpa [prefixWord, tailWord_211440, baseEnd_211440] using wordTrace_append hprefix tailTrace_211440
  have hstable : (prefixWord ++ tailWord_211440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211440).length < 2 ^ (prefixWord ++ tailWord_211440).sum := by decide
  have hdescent : baseEnd_211440 < baseStart_211440 := by decide
  rcases family_descends (prefixWord ++ tailWord_211440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211450 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_211450 : Nat := 118140960795 + 211450 * 2 ^ 59
def prefixEnd_211450 : Nat := 4983230072969 + 3 ^ 40 * 211450 * 2
def baseEnd_211450 : Nat := 36191828131100978200855

theorem tailTrace_211450 : CollatzResearch.WordTrace tailWord_211450 prefixEnd_211450 36191828131100978200855 := by
  unfold tailWord_211450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928053770990059407505951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5141476722640158420015869 1928053770990059407505951)
  ·
    refine ⟨2892080656485089111258927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1928053770990059407505951 2892080656485089111258927)
    ·
      refine ⟨4338120984727633666888391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892080656485089111258927 4338120984727633666888391)
      ·
        refine ⟨6507181477091450500332587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338120984727633666888391 6507181477091450500332587)
        ·
          refine ⟨9760772215637175750498881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507181477091450500332587 9760772215637175750498881)
          ·
            refine ⟨7320579161727881812874161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9760772215637175750498881 7320579161727881812874161)
            ·
              refine ⟨5490434371295911359655621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7320579161727881812874161 5490434371295911359655621)
              ·
                refine ⟨1029456444617983379935429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5490434371295911359655621 1029456444617983379935429)
                ·
                  refine ⟨193023083365871883737893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029456444617983379935429 193023083365871883737893)
                  ·
                    refine ⟨36191828131100978200855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193023083365871883737893 36191828131100978200855)
                    ·
                      rfl

theorem cell23_211450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_211450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211450 prefixEnd_211450 := by exact prefixLift 211450
  have htrace : WordTrace (prefixWord ++ tailWord_211450) baseStart_211450 baseEnd_211450 := by
    simpa [prefixWord, tailWord_211450, baseEnd_211450] using wordTrace_append hprefix tailTrace_211450
  have hstable : (prefixWord ++ tailWord_211450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211450).length < 2 ^ (prefixWord ++ tailWord_211450).sum := by decide
  have hdescent : baseEnd_211450 < baseStart_211450 := by decide
  rcases family_descends (prefixWord ++ tailWord_211450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211462 : List Nat := [6, 2, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_211462 : Nat := 118140960795 + 211462 * 2 ^ 59
def prefixEnd_211462 : Nat := 4983230072969 + 3 ^ 40 * 211462 * 2
def baseEnd_211462 : Nat := 36193882053718962550837

theorem tailTrace_211462 : CollatzResearch.WordTrace tailWord_211462 prefixEnd_211462 36193882053718962550837 := by
  unfold tailWord_211462
  simp only [CollatzResearch.WordTrace]
  refine ⟨241020398747398864983145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5141768506611175786307093 241020398747398864983145)
  ·
    refine ⟨180765299060549148737359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241020398747398864983145 180765299060549148737359)
    ·
      refine ⟨271147948590823723106039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180765299060549148737359 271147948590823723106039)
      ·
        refine ⟨406721922886235584659059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271147948590823723106039 406721922886235584659059)
        ·
          refine ⟨610082884329353376988589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406721922886235584659059 610082884329353376988589)
          ·
            refine ⟨228781081623507516370721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610082884329353376988589 228781081623507516370721)
            ·
              refine ⟨171585811217630637278041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228781081623507516370721 171585811217630637278041)
              ·
                refine ⟨128689358413222977958531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171585811217630637278041 128689358413222977958531)
                ·
                  refine ⟨193034037619834466937797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128689358413222977958531 193034037619834466937797)
                  ·
                    refine ⟨36193882053718962550837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193034037619834466937797 36193882053718962550837)
                    ·
                      rfl

theorem cell23_211462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_211462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211462 prefixEnd_211462 := by exact prefixLift 211462
  have htrace : WordTrace (prefixWord ++ tailWord_211462) baseStart_211462 baseEnd_211462 := by
    simpa [prefixWord, tailWord_211462, baseEnd_211462] using wordTrace_append hprefix tailTrace_211462
  have hstable : (prefixWord ++ tailWord_211462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211462).length < 2 ^ (prefixWord ++ tailWord_211462).sum := by decide
  have hdescent : baseEnd_211462 < baseStart_211462 := by decide
  rcases family_descends (prefixWord ++ tailWord_211462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211463 : List Nat := [1, 1, 4, 3, 14]
def baseStart_211463 : Nat := 118140960795 + 211463 * 2 ^ 59
def prefixEnd_211463 : Nat := 4983230072969 + 3 ^ 40 * 211463 * 2
def baseEnd_211463 : Nat := 148946721045008756845

theorem tailTrace_211463 : CollatzResearch.WordTrace tailWord_211463 prefixEnd_211463 148946721045008756845 := by
  unfold tailWord_211463
  simp only [CollatzResearch.WordTrace]
  refine ⟨7712689232913140850247043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5141792821942093900164695 7712689232913140850247043)
  ·
    refine ⟨11569033849369711275370565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7712689232913140850247043 11569033849369711275370565)
    ·
      refine ⟨2169193846756820864131981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11569033849369711275370565 2169193846756820864131981)
      ·
        refine ⟨813447692533807824049493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2169193846756820864131981 813447692533807824049493)
        ·
          refine ⟨148946721045008756845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 813447692533807824049493 148946721045008756845)
          ·
            rfl

theorem cell23_211463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 14].length) (baseStart_211463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211463 prefixEnd_211463 := by exact prefixLift 211463
  have htrace : WordTrace (prefixWord ++ tailWord_211463) baseStart_211463 baseEnd_211463 := by
    simpa [prefixWord, tailWord_211463, baseEnd_211463] using wordTrace_append hprefix tailTrace_211463
  have hstable : (prefixWord ++ tailWord_211463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211463).length < 2 ^ (prefixWord ++ tailWord_211463).sum := by decide
  have hdescent : baseEnd_211463 < baseStart_211463 := by decide
  rcases family_descends (prefixWord ++ tailWord_211463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211467 : List Nat := [1, 1, 1, 1, 7, 1, 1, 4, 2, 4]
def baseStart_211467 : Nat := 118140960795 + 211467 * 2 ^ 59
def prefixEnd_211467 : Nat := 4983230072969 + 3 ^ 40 * 211467 * 2
def baseEnd_211467 : Nat := 36194737854809789363329

theorem tailTrace_211467 : CollatzResearch.WordTrace tailWord_211467 prefixEnd_211467 36194737854809789363329 := by
  unfold tailWord_211467
  simp only [CollatzResearch.WordTrace]
  refine ⟨7712835124898649533392655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5141890083265766355595103 7712835124898649533392655)
  ·
    refine ⟨11569252687347974300088983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7712835124898649533392655 11569252687347974300088983)
    ·
      refine ⟨17353879031021961450133475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11569252687347974300088983 17353879031021961450133475)
      ·
        refine ⟨26030818546532942175200213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17353879031021961450133475 26030818546532942175200213)
        ·
          refine ⟨610097309684365832231255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26030818546532942175200213 610097309684365832231255)
          ·
            refine ⟨915145964526548748346883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610097309684365832231255 915145964526548748346883)
            ·
              refine ⟨1372718946789823122520325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915145964526548748346883 1372718946789823122520325)
              ·
                refine ⟨257384802523091835472561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1372718946789823122520325 257384802523091835472561)
                ·
                  refine ⟨193038601892318876604421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257384802523091835472561 193038601892318876604421)
                  ·
                    refine ⟨36194737854809789363329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193038601892318876604421 36194737854809789363329)
                    ·
                      rfl

theorem cell23_211467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 4].length) (baseStart_211467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211467 prefixEnd_211467 := by exact prefixLift 211467
  have htrace : WordTrace (prefixWord ++ tailWord_211467) baseStart_211467 baseEnd_211467 := by
    simpa [prefixWord, tailWord_211467, baseEnd_211467] using wordTrace_append hprefix tailTrace_211467
  have hstable : (prefixWord ++ tailWord_211467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211467).length < 2 ^ (prefixWord ++ tailWord_211467).sum := by decide
  have hdescent : baseEnd_211467 < baseStart_211467 := by decide
  rcases family_descends (prefixWord ++ tailWord_211467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211468 : List Nat := [2, 2, 1, 2, 4, 3, 2, 2, 1, 1, 3]
def baseStart_211468 : Nat := 118140960795 + 211468 * 2 ^ 59
def prefixEnd_211468 : Nat := 4983230072969 + 3 ^ 40 * 211468 * 2
def baseEnd_211468 : Nat := 108584727045083864177483

theorem tailTrace_211468 : CollatzResearch.WordTrace tailWord_211468 prefixEnd_211468 108584727045083864177483 := by
  unfold tailWord_211468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856435798947513352089529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5141914398596684469452705 3856435798947513352089529)
  ·
    refine ⟨2892326849210635014067147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3856435798947513352089529 2892326849210635014067147)
    ·
      refine ⟨4338490273815952521100721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2892326849210635014067147 4338490273815952521100721)
      ·
        refine ⟨3253867705361964390825541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4338490273815952521100721 3253867705361964390825541)
        ·
          refine ⟨610100194755368323279789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3253867705361964390825541 610100194755368323279789)
          ·
            refine ⟨228787573033263121229921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610100194755368323279789 228787573033263121229921)
            ·
              refine ⟨171590679774947340922441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228787573033263121229921 171590679774947340922441)
              ·
                refine ⟨128693009831210505691831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171590679774947340922441 128693009831210505691831)
                ·
                  refine ⟨193039514746815758537747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128693009831210505691831 193039514746815758537747)
                  ·
                    refine ⟨289559272120223637806621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193039514746815758537747 289559272120223637806621)
                    ·
                      refine ⟨108584727045083864177483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 289559272120223637806621 108584727045083864177483)
                      ·
                        rfl

theorem cell23_211468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_211468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211468 prefixEnd_211468 := by exact prefixLift 211468
  have htrace : WordTrace (prefixWord ++ tailWord_211468) baseStart_211468 baseEnd_211468 := by
    simpa [prefixWord, tailWord_211468, baseEnd_211468] using wordTrace_append hprefix tailTrace_211468
  have hstable : (prefixWord ++ tailWord_211468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211468).length < 2 ^ (prefixWord ++ tailWord_211468).sum := by decide
  have hdescent : baseEnd_211468 < baseStart_211468 := by decide
  rcases family_descends (prefixWord ++ tailWord_211468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211473 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_211473 : Nat := 118140960795 + 211473 * 2 ^ 59
def prefixEnd_211473 : Nat := 4983230072969 + 3 ^ 40 * 211473 * 2
def baseEnd_211473 : Nat := 108587294448356344614959

theorem tailTrace_211473 : CollatzResearch.WordTrace tailWord_211473 prefixEnd_211473 108587294448356344614959 := by
  unfold tailWord_211473
  simp only [CollatzResearch.WordTrace]
  refine ⟨7713053962876912558111073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5142035975251275038740715 7713053962876912558111073)
  ·
    refine ⟨5784790472157684418583305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7713053962876912558111073 5784790472157684418583305)
    ·
      refine ⟨4338592854118263313937479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5784790472157684418583305 4338592854118263313937479)
      ·
        refine ⟨6507889281177394970906219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4338592854118263313937479 6507889281177394970906219)
        ·
          refine ⟨9761833921766092456359329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507889281177394970906219 9761833921766092456359329)
          ·
            refine ⟨7321375441324569342269497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9761833921766092456359329 7321375441324569342269497)
            ·
              refine ⟨5491031580993427006702123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7321375441324569342269497 5491031580993427006702123)
              ·
                refine ⟨8236547371490140510053185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491031580993427006702123 8236547371490140510053185)
                ·
                  refine ⟨6177410528617605382539889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8236547371490140510053185 6177410528617605382539889)
                  ·
                    refine ⟨4633057896463204036904917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6177410528617605382539889 4633057896463204036904917)
                    ·
                      refine ⟨108587294448356344614959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4633057896463204036904917 108587294448356344614959)
                      ·
                        rfl

theorem cell23_211473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_211473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211473 prefixEnd_211473 := by exact prefixLift 211473
  have htrace : WordTrace (prefixWord ++ tailWord_211473) baseStart_211473 baseEnd_211473 := by
    simpa [prefixWord, tailWord_211473, baseEnd_211473] using wordTrace_append hprefix tailTrace_211473
  have hstable : (prefixWord ++ tailWord_211473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211473).length < 2 ^ (prefixWord ++ tailWord_211473).sum := by decide
  have hdescent : baseEnd_211473 < baseStart_211473 := by decide
  rcases family_descends (prefixWord ++ tailWord_211473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211480 : List Nat := [2, 1, 2, 3, 3, 1, 3, 8]
def baseStart_211480 : Nat := 118140960795 + 211480 * 2 ^ 59
def prefixEnd_211480 : Nat := 4983230072969 + 3 ^ 40 * 211480 * 2
def baseEnd_211480 : Nat := 4021884770849548786201

theorem tailTrace_211480 : CollatzResearch.WordTrace tailWord_211480 prefixEnd_211480 4021884770849548786201 := by
  unfold tailWord_211480
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856654636925776376807947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5142206182567701835743929 3856654636925776376807947)
  ·
    refine ⟨5784981955388664565211921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3856654636925776376807947 5784981955388664565211921)
    ·
      refine ⟨4338736466541498423908941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5784981955388664565211921 4338736466541498423908941)
      ·
        refine ⟨1627026174953061908965853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4338736466541498423908941 1627026174953061908965853)
        ·
          refine ⟨610134815607398215862195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1627026174953061908965853 610134815607398215862195)
          ·
            refine ⟨915202223411097323793293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610134815607398215862195 915202223411097323793293)
            ·
              refine ⟨343200833779161496422485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915202223411097323793293 343200833779161496422485)
              ·
                refine ⟨4021884770849548786201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 343200833779161496422485 4021884770849548786201)
                ·
                  rfl

theorem cell23_211480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 8].length) (baseStart_211480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211480 prefixEnd_211480 := by exact prefixLift 211480
  have htrace : WordTrace (prefixWord ++ tailWord_211480) baseStart_211480 baseEnd_211480 := by
    simpa [prefixWord, tailWord_211480, baseEnd_211480] using wordTrace_append hprefix tailTrace_211480
  have hstable : (prefixWord ++ tailWord_211480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211480).length < 2 ^ (prefixWord ++ tailWord_211480).sum := by decide
  have hdescent : baseEnd_211480 < baseStart_211480 := by decide
  rcases family_descends (prefixWord ++ tailWord_211480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211495 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_211495 : Nat := 118140960795 + 211495 * 2 ^ 59
def prefixEnd_211495 : Nat := 4983230072969 + 3 ^ 40 * 211495 * 2
def baseEnd_211495 : Nat := 108598591022755258539859

theorem tailTrace_211495 : CollatzResearch.WordTrace tailWord_211495 prefixEnd_211495 108598591022755258539859 := by
  unfold tailWord_211495
  simp only [CollatzResearch.WordTrace]
  refine ⟨7713856368797210315411939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5142570912531473543607959 7713856368797210315411939)
  ·
    refine ⟨11570784553195815473117909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7713856368797210315411939 11570784553195815473117909)
    ·
      refine ⟨271190262965526925151201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11570784553195815473117909 271190262965526925151201)
      ·
        refine ⟨203392697224145193863401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271190262965526925151201 203392697224145193863401)
        ·
          refine ⟨152544522918108895397551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203392697224145193863401 152544522918108895397551)
          ·
            refine ⟨228816784377163343096327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152544522918108895397551 228816784377163343096327)
            ·
              refine ⟨343225176565745014644491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228816784377163343096327 343225176565745014644491)
              ·
                refine ⟨514837764848617521966737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343225176565745014644491 514837764848617521966737)
                ·
                  refine ⟨386128323636463141475053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514837764848617521966737 386128323636463141475053)
                  ·
                    refine ⟨144798121363673678053145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386128323636463141475053 144798121363673678053145)
                    ·
                      refine ⟨108598591022755258539859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144798121363673678053145 108598591022755258539859)
                      ·
                        rfl

theorem cell23_211495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_211495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211495 prefixEnd_211495 := by exact prefixLift 211495
  have htrace : WordTrace (prefixWord ++ tailWord_211495) baseStart_211495 baseEnd_211495 := by
    simpa [prefixWord, tailWord_211495, baseEnd_211495] using wordTrace_append hprefix tailTrace_211495
  have hstable : (prefixWord ++ tailWord_211495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211495).length < 2 ^ (prefixWord ++ tailWord_211495).sum := by decide
  have hdescent : baseEnd_211495 < baseStart_211495 := by decide
  rcases family_descends (prefixWord ++ tailWord_211495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211507 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 3]
def baseStart_211507 : Nat := 118140960795 + 211507 * 2 ^ 59
def prefixEnd_211507 : Nat := 4983230072969 + 3 ^ 40 * 211507 * 2
def baseEnd_211507 : Nat := 108604752790609211589803

theorem tailTrace_211507 : CollatzResearch.WordTrace tailWord_211507 prefixEnd_211507 108604752790609211589803 := by
  unfold tailWord_211507
  simp only [CollatzResearch.WordTrace]
  refine ⟨7714294044753736364848775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5142862696502490909899183 7714294044753736364848775)
  ·
    refine ⟨11571441067130604547273163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7714294044753736364848775 11571441067130604547273163)
    ·
      refine ⟨17357161600695906820909745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11571441067130604547273163 17357161600695906820909745)
      ·
        refine ⟨13017871200521930115682309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17357161600695906820909745 13017871200521930115682309)
        ·
          refine ⟨2440850850097861896690433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13017871200521930115682309 2440850850097861896690433)
          ·
            refine ⟨1830638137573396422517825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440850850097861896690433 1830638137573396422517825)
            ·
              refine ⟨1372978603180047316888369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830638137573396422517825 1372978603180047316888369)
              ·
                refine ⟨1029733952385035487666277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372978603180047316888369 1029733952385035487666277)
                ·
                  refine ⟨193075116072194153937427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1029733952385035487666277 193075116072194153937427)
                  ·
                    refine ⟨289612674108291230906141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193075116072194153937427 289612674108291230906141)
                    ·
                      refine ⟨108604752790609211589803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 289612674108291230906141 108604752790609211589803)
                      ·
                        rfl

theorem cell23_211507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 3].length) (baseStart_211507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211507 prefixEnd_211507 := by exact prefixLift 211507
  have htrace : WordTrace (prefixWord ++ tailWord_211507) baseStart_211507 baseEnd_211507 := by
    simpa [prefixWord, tailWord_211507, baseEnd_211507] using wordTrace_append hprefix tailTrace_211507
  have hstable : (prefixWord ++ tailWord_211507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211507).length < 2 ^ (prefixWord ++ tailWord_211507).sum := by decide
  have hdescent : baseEnd_211507 < baseStart_211507 := by decide
  rcases family_descends (prefixWord ++ tailWord_211507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211518 : List Nat := [4, 2, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_211518 : Nat := 118140960795 + 211518 * 2 ^ 59
def prefixEnd_211518 : Nat := 4983230072969 + 3 ^ 40 * 211518 * 2
def baseEnd_211518 : Nat := 36203467025936222850751

theorem tailTrace_211518 : CollatzResearch.WordTrace tailWord_211518 prefixEnd_211518 36203467025936222850751 := by
  unfold tailWord_211518
  simp only [CollatzResearch.WordTrace]
  refine ⟨964336905964235655437401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5143130165142590162332805 964336905964235655437401)
  ·
    refine ⟨723252679473176741578051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 964336905964235655437401 723252679473176741578051)
    ·
      refine ⟨1084879019209765112367077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723252679473176741578051 1084879019209765112367077)
      ·
        refine ⟨203414816101830958568827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1084879019209765112367077 203414816101830958568827)
        ·
          refine ⟨305122224152746437853241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203414816101830958568827 305122224152746437853241)
          ·
            refine ⟨228841668114559828389931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305122224152746437853241 228841668114559828389931)
            ·
              refine ⟨343262502171839742584897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228841668114559828389931 343262502171839742584897)
              ·
                refine ⟨257446876628879806938673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343262502171839742584897 257446876628879806938673)
                ·
                  refine ⟨193085157471659855204005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257446876628879806938673 193085157471659855204005)
                  ·
                    refine ⟨36203467025936222850751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193085157471659855204005 36203467025936222850751)
                    ·
                      rfl

theorem cell23_211518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_211518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211518 prefixEnd_211518 := by exact prefixLift 211518
  have htrace : WordTrace (prefixWord ++ tailWord_211518) baseStart_211518 baseEnd_211518 := by
    simpa [prefixWord, tailWord_211518, baseEnd_211518] using wordTrace_append hprefix tailTrace_211518
  have hstable : (prefixWord ++ tailWord_211518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211518).length < 2 ^ (prefixWord ++ tailWord_211518).sum := by decide
  have hdescent : baseEnd_211518 < baseStart_211518 := by decide
  rcases family_descends (prefixWord ++ tailWord_211518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211564 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 4, 2, 2]
def baseStart_211564 : Nat := 118140960795 + 211564 * 2 ^ 59
def prefixEnd_211564 : Nat := 4983230072969 + 3 ^ 40 * 211564 * 2
def baseEnd_211564 : Nat := 108634021187915488577041

theorem tailTrace_211564 : CollatzResearch.WordTrace tailWord_211564 prefixEnd_211564 108634021187915488577041 := by
  unfold tailWord_211564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858186502773617549836873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5144248670364823399782497 3858186502773617549836873)
  ·
    refine ⟨2893639877080213162377655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3858186502773617549836873 2893639877080213162377655)
    ·
      refine ⟨4340459815620319743566483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2893639877080213162377655 4340459815620319743566483)
      ·
        refine ⟨6510689723430479615349725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340459815620319743566483 6510689723430479615349725)
        ·
          refine ⟨2441508646286429855756147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6510689723430479615349725 2441508646286429855756147)
          ·
            refine ⟨3662262969429644783634221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441508646286429855756147 3662262969429644783634221)
            ·
              refine ⟨1373348613536116793862833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3662262969429644783634221 1373348613536116793862833)
              ·
                refine ⟨1030011460152087595397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373348613536116793862833 1030011460152087595397125)
                ·
                  refine ⟨193127148778516424136961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030011460152087595397125 193127148778516424136961)
                  ·
                    refine ⟨144845361583887318102721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193127148778516424136961 144845361583887318102721)
                    ·
                      refine ⟨108634021187915488577041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144845361583887318102721 108634021187915488577041)
                      ·
                        rfl

theorem cell23_211564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_211564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211564 prefixEnd_211564 := by exact prefixLift 211564
  have htrace : WordTrace (prefixWord ++ tailWord_211564) baseStart_211564 baseEnd_211564 := by
    simpa [prefixWord, tailWord_211564, baseEnd_211564] using wordTrace_append hprefix tailTrace_211564
  have hstable : (prefixWord ++ tailWord_211564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211564).length < 2 ^ (prefixWord ++ tailWord_211564).sum := by decide
  have hdescent : baseEnd_211564 < baseStart_211564 := by decide
  rcases family_descends (prefixWord ++ tailWord_211564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211587 : List Nat := [1, 1, 1, 3, 3, 1, 2, 6, 5]
def baseStart_211587 : Nat := 118140960795 + 211587 * 2 ^ 59
def prefixEnd_211587 : Nat := 4983230072969 + 3 ^ 40 * 211587 * 2
def baseEnd_211587 : Nat := 12071759026996544287715

theorem tailTrace_211587 : CollatzResearch.WordTrace tailWord_211587 prefixEnd_211587 12071759026996544287715 := by
  unfold tailWord_211587
  simp only [CollatzResearch.WordTrace]
  refine ⟨7717211884463910027761015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5144807922975940018507343 7717211884463910027761015)
  ·
    refine ⟨11575817826695865041641523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7717211884463910027761015 11575817826695865041641523)
    ·
      refine ⟨17363726740043797562462285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11575817826695865041641523 17363726740043797562462285)
      ·
        refine ⟨6511397527516424085923357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17363726740043797562462285 6511397527516424085923357)
        ·
          refine ⟨2441774072818659032221259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6511397527516424085923357 2441774072818659032221259)
          ·
            refine ⟨3662661109227988548331889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441774072818659032221259 3662661109227988548331889)
            ·
              refine ⟨2746995831920991411248917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662661109227988548331889 2746995831920991411248917)
              ·
                refine ⟨128765429621296472402293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2746995831920991411248917 128765429621296472402293)
                ·
                  refine ⟨12071759026996544287715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128765429621296472402293 12071759026996544287715)
                  ·
                    rfl

theorem cell23_211587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 5].length) (baseStart_211587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211587 prefixEnd_211587 := by exact prefixLift 211587
  have htrace : WordTrace (prefixWord ++ tailWord_211587) baseStart_211587 baseEnd_211587 := by
    simpa [prefixWord, tailWord_211587, baseEnd_211587] using wordTrace_append hprefix tailTrace_211587
  have hstable : (prefixWord ++ tailWord_211587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211587).length < 2 ^ (prefixWord ++ tailWord_211587).sum := by decide
  have hdescent : baseEnd_211587 < baseStart_211587 := by decide
  rcases family_descends (prefixWord ++ tailWord_211587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211638 : List Nat := [5, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_211638 : Nat := 118140960795 + 211638 * 2 ^ 59
def prefixEnd_211638 : Nat := 4983230072969 + 3 ^ 40 * 211638 * 2
def baseEnd_211638 : Nat := 12074668750705355450189

theorem tailTrace_211638 : CollatzResearch.WordTrace tailWord_211638 prefixEnd_211638 12074668750705355450189 := by
  unfold tailWord_211638
  simp only [CollatzResearch.WordTrace]
  refine ⟨482442000454946608616723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5146048004852763825245045 482442000454946608616723)
  ·
    refine ⟨723663000682419912925085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 482442000454946608616723 723663000682419912925085)
    ·
      refine ⟨271373625255907467346907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 723663000682419912925085 271373625255907467346907)
      ·
        refine ⟨407060437883861201020361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271373625255907467346907 407060437883861201020361)
        ·
          refine ⟨305295328412895900765271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407060437883861201020361 305295328412895900765271)
          ·
            refine ⟨457942992619343851147907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305295328412895900765271 457942992619343851147907)
            ·
              refine ⟨686914488929015776721861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457942992619343851147907 686914488929015776721861)
              ·
                refine ⟨128796466674190458135349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686914488929015776721861 128796466674190458135349)
                ·
                  refine ⟨12074668750705355450189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128796466674190458135349 12074668750705355450189)
                  ·
                    rfl

theorem cell23_211638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_211638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211638 prefixEnd_211638 := by exact prefixLift 211638
  have htrace : WordTrace (prefixWord ++ tailWord_211638) baseStart_211638 baseEnd_211638 := by
    simpa [prefixWord, tailWord_211638, baseEnd_211638] using wordTrace_append hprefix tailTrace_211638
  have hstable : (prefixWord ++ tailWord_211638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211638).length < 2 ^ (prefixWord ++ tailWord_211638).sum := by decide
  have hdescent : baseEnd_211638 < baseStart_211638 := by decide
  rcases family_descends (prefixWord ++ tailWord_211638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211668 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_211668 : Nat := 118140960795 + 211668 * 2 ^ 59
def prefixEnd_211668 : Nat := 4983230072969 + 3 ^ 40 * 211668 * 2
def baseEnd_211668 : Nat := 36229141058661027225521

theorem tailTrace_211668 : CollatzResearch.WordTrace tailWord_211668 prefixEnd_211668 36229141058661027225521 := by
  unfold tailWord_211668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860083098585230430729829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5146777464780307240973105 3860083098585230430729829)
  ·
    refine ⟨723765580984730705761843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3860083098585230430729829 723765580984730705761843)
    ·
      refine ⟨1085648371477096058642765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723765580984730705761843 1085648371477096058642765)
      ·
        refine ⟨407118139303911021991037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1085648371477096058642765 407118139303911021991037)
        ·
          refine ⟨152669302238966633246639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407118139303911021991037 152669302238966633246639)
          ·
            refine ⟨229003953358449949869959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152669302238966633246639 229003953358449949869959)
            ·
              refine ⟨343505930037674924804939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229003953358449949869959 343505930037674924804939)
              ·
                refine ⟨515258895056512387207409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343505930037674924804939 515258895056512387207409)
                ·
                  refine ⟨386444171292384290405557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515258895056512387207409 386444171292384290405557)
                  ·
                    refine ⟨36229141058661027225521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 386444171292384290405557 36229141058661027225521)
                    ·
                      rfl

theorem cell23_211668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_211668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211668 prefixEnd_211668 := by exact prefixLift 211668
  have htrace : WordTrace (prefixWord ++ tailWord_211668) baseStart_211668 baseEnd_211668 := by
    simpa [prefixWord, tailWord_211668, baseEnd_211668] using wordTrace_append hprefix tailTrace_211668
  have hstable : (prefixWord ++ tailWord_211668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211668).length < 2 ^ (prefixWord ++ tailWord_211668).sum := by decide
  have hdescent : baseEnd_211668 < baseStart_211668 := by decide
  rcases family_descends (prefixWord ++ tailWord_211668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211681 : List Nat := [1, 2, 3, 1, 4, 1, 1, 5, 1, 4]
def baseStart_211681 : Nat := 118140960795 + 211681 * 2 ^ 59
def prefixEnd_211681 : Nat := 4983230072969 + 3 ^ 40 * 211681 * 2
def baseEnd_211681 : Nat := 36231366141497176938001

theorem tailTrace_211681 : CollatzResearch.WordTrace tailWord_211681 prefixEnd_211681 36231366141497176938001 := by
  unfold tailWord_211681
  simp only [CollatzResearch.WordTrace]
  refine ⟨7720640346123364081682897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5147093564082242721121931 7720640346123364081682897)
  ·
    refine ⟨5790480259592523061262173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7720640346123364081682897 5790480259592523061262173)
    ·
      refine ⟨2171430097347196147973315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5790480259592523061262173 2171430097347196147973315)
      ·
        refine ⟨3257145146020794221959973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2171430097347196147973315 3257145146020794221959973)
        ·
          refine ⟨610714714878898916617495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3257145146020794221959973 610714714878898916617495)
          ·
            refine ⟨916072072318348374926243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610714714878898916617495 916072072318348374926243)
            ·
              refine ⟨1374108108477522562389365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916072072318348374926243 1374108108477522562389365)
              ·
                refine ⟨128822635169767740224003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1374108108477522562389365 128822635169767740224003)
                ·
                  refine ⟨193233952754651610336005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128822635169767740224003 193233952754651610336005)
                  ·
                    refine ⟨36231366141497176938001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193233952754651610336005 36231366141497176938001)
                    ·
                      rfl

theorem cell23_211681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_211681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211681 prefixEnd_211681 := by exact prefixLift 211681
  have htrace : WordTrace (prefixWord ++ tailWord_211681) baseStart_211681 baseEnd_211681 := by
    simpa [prefixWord, tailWord_211681, baseEnd_211681] using wordTrace_append hprefix tailTrace_211681
  have hstable : (prefixWord ++ tailWord_211681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211681).length < 2 ^ (prefixWord ++ tailWord_211681).sum := by decide
  have hdescent : baseEnd_211681 < baseStart_211681 := by decide
  rcases family_descends (prefixWord ++ tailWord_211681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211694 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_211694 : Nat := 118140960795 + 211694 * 2 ^ 59
def prefixEnd_211694 : Nat := 4983230072969 + 3 ^ 40 * 211694 * 2
def baseEnd_211694 : Nat := 12077863741444442216827

theorem tailTrace_211694 : CollatzResearch.WordTrace tailWord_211694 prefixEnd_211694 12077863741444442216827 := by
  unfold tailWord_211694
  simp only [CollatzResearch.WordTrace]
  refine ⟨965139311884533412738267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5147409663384178201270757 965139311884533412738267)
  ·
    refine ⟨1447708967826800119107401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 965139311884533412738267 1447708967826800119107401)
    ·
      refine ⟨1085781725870100089330551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1447708967826800119107401 1085781725870100089330551)
      ·
        refine ⟨1628672588805150133995827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085781725870100089330551 1628672588805150133995827)
        ·
          refine ⟨2443008883207725200993741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628672588805150133995827 2443008883207725200993741)
          ·
            refine ⟨916128331202896950372653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2443008883207725200993741 916128331202896950372653)
            ·
              refine ⟨343548124201086356389745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 916128331202896950372653 343548124201086356389745)
              ·
                refine ⟨257661093150814767292309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343548124201086356389745 257661093150814767292309)
                ·
                  refine ⟨12077863741444442216827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 257661093150814767292309 12077863741444442216827)
                  ·
                    rfl

theorem cell23_211694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_211694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211694 prefixEnd_211694 := by exact prefixLift 211694
  have htrace : WordTrace (prefixWord ++ tailWord_211694) baseStart_211694 baseEnd_211694 := by
    simpa [prefixWord, tailWord_211694, baseEnd_211694] using wordTrace_append hprefix tailTrace_211694
  have hstable : (prefixWord ++ tailWord_211694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211694).length < 2 ^ (prefixWord ++ tailWord_211694).sum := by decide
  have hdescent : baseEnd_211694 < baseStart_211694 := by decide
  rcases family_descends (prefixWord ++ tailWord_211694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211748 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_211748 : Nat := 118140960795 + 211748 * 2 ^ 59
def prefixEnd_211748 : Nat := 4983230072969 + 3 ^ 40 * 211748 * 2
def baseEnd_211748 : Nat := 108728501628342768676195

theorem tailTrace_211748 : CollatzResearch.WordTrace tailWord_211748 prefixEnd_211748 108728501628342768676195 := by
  unfold tailWord_211748
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861542018440317262185949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5148722691253756349581265 3861542018440317262185949)
  ·
    refine ⟨1448078256915118973319731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3861542018440317262185949 1448078256915118973319731)
    ·
      refine ⟨2172117385372678459979597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448078256915118973319731 2172117385372678459979597)
      ·
        refine ⟨814544019514754422492349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2172117385372678459979597 814544019514754422492349)
        ·
          refine ⟨305454007318032908434631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814544019514754422492349 305454007318032908434631)
          ·
            refine ⟨458181010977049362651947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305454007318032908434631 458181010977049362651947)
            ·
              refine ⟨687271516465574043977921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458181010977049362651947 687271516465574043977921)
              ·
                refine ⟨515453637349180532983441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687271516465574043977921 515453637349180532983441)
                ·
                  refine ⟨386590228011885399737581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515453637349180532983441 386590228011885399737581)
                  ·
                    refine ⟨144971335504457024901593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386590228011885399737581 144971335504457024901593)
                    ·
                      refine ⟨108728501628342768676195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144971335504457024901593 108728501628342768676195)
                      ·
                        rfl

theorem cell23_211748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_211748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211748 prefixEnd_211748 := by exact prefixLift 211748
  have htrace : WordTrace (prefixWord ++ tailWord_211748) baseStart_211748 baseEnd_211748 := by
    simpa [prefixWord, tailWord_211748, baseEnd_211748] using wordTrace_append hprefix tailTrace_211748
  have hstable : (prefixWord ++ tailWord_211748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211748).length < 2 ^ (prefixWord ++ tailWord_211748).sum := by decide
  have hdescent : baseEnd_211748 < baseStart_211748 := by decide
  rcases family_descends (prefixWord ++ tailWord_211748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211767 : List Nat := [1, 1, 3, 1, 2, 1, 6, 8]
def baseStart_211767 : Nat := 118140960795 + 211767 * 2 ^ 59
def prefixEnd_211767 : Nat := 4983230072969 + 3 ^ 40 * 211767 * 2
def baseEnd_211767 : Nat := 4027342880028822012541

theorem tailTrace_211767 : CollatzResearch.WordTrace tailWord_211767 prefixEnd_211767 4027342880028822012541 := by
  unfold tailWord_211767
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723777023811800769313555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5149184682541200512875703 7723777023811800769313555)
  ·
    refine ⟨11585665535717701153970333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7723777023811800769313555 11585665535717701153970333)
    ·
      refine ⟨4344624575894137932738875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11585665535717701153970333 4344624575894137932738875)
      ·
        refine ⟨6516936863841206899108313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344624575894137932738875 6516936863841206899108313)
        ·
          refine ⟨4887702647880905174331235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6516936863841206899108313 4887702647880905174331235)
          ·
            refine ⟨7331553971821357761496853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887702647880905174331235 7331553971821357761496853)
            ·
              refine ⟨343666592429126145070165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7331553971821357761496853 343666592429126145070165)
              ·
                refine ⟨4027342880028822012541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 343666592429126145070165 4027342880028822012541)
                ·
                  rfl

theorem cell23_211767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 8].length) (baseStart_211767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211767 prefixEnd_211767 := by exact prefixLift 211767
  have htrace : WordTrace (prefixWord ++ tailWord_211767) baseStart_211767 baseEnd_211767 := by
    simpa [prefixWord, tailWord_211767, baseEnd_211767] using wordTrace_append hprefix tailTrace_211767
  have hstable : (prefixWord ++ tailWord_211767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211767).length < 2 ^ (prefixWord ++ tailWord_211767).sum := by decide
  have hdescent : baseEnd_211767 < baseStart_211767 := by decide
  rcases family_descends (prefixWord ++ tailWord_211767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211782 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_211782 : Nat := 118140960795 + 211782 * 2 ^ 59
def prefixEnd_211782 : Nat := 4983230072969 + 3 ^ 40 * 211782 * 2
def baseEnd_211782 : Nat := 108745959970595635651039

theorem tailTrace_211782 : CollatzResearch.WordTrace tailWord_211782 prefixEnd_211782 108745959970595635651039 := by
  unfold tailWord_211782
  simp only [CollatzResearch.WordTrace]
  refine ⟨241385128711170572847175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5149549412504972220739733 241385128711170572847175)
  ·
    refine ⟨362077693066755859270763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241385128711170572847175 362077693066755859270763)
    ·
      refine ⟨543116539600133788906145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362077693066755859270763 543116539600133788906145)
      ·
        refine ⟨407337404700100341679609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543116539600133788906145 407337404700100341679609)
        ·
          refine ⟨305503053525075256259707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407337404700100341679609 305503053525075256259707)
          ·
            refine ⟨458254580287612884389561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305503053525075256259707 458254580287612884389561)
            ·
              refine ⟨343690935215709663292171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458254580287612884389561 343690935215709663292171)
              ·
                refine ⟨515536402823564494938257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343690935215709663292171 515536402823564494938257)
                ·
                  refine ⟨386652302117673371203693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515536402823564494938257 386652302117673371203693)
                  ·
                    refine ⟨144994613294127514201385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386652302117673371203693 144994613294127514201385)
                    ·
                      refine ⟨108745959970595635651039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 144994613294127514201385 108745959970595635651039)
                      ·
                        rfl

theorem cell23_211782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_211782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211782 prefixEnd_211782 := by exact prefixLift 211782
  have htrace : WordTrace (prefixWord ++ tailWord_211782) baseStart_211782 baseEnd_211782 := by
    simpa [prefixWord, tailWord_211782, baseEnd_211782] using wordTrace_append hprefix tailTrace_211782
  have hstable : (prefixWord ++ tailWord_211782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211782).length < 2 ^ (prefixWord ++ tailWord_211782).sum := by decide
  have hdescent : baseEnd_211782 < baseStart_211782 := by decide
  rcases family_descends (prefixWord ++ tailWord_211782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211812 : List Nat := [2, 3, 1, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_211812 : Nat := 118140960795 + 211812 * 2 ^ 59
def prefixEnd_211812 : Nat := 4983230072969 + 3 ^ 40 * 211812 * 2
def baseEnd_211812 : Nat := 108761364390230518275901

theorem tailTrace_211812 : CollatzResearch.WordTrace tailWord_211812 prefixEnd_211812 108761364390230518275901 := by
  unfold tailWord_211812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862709154324386727350845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5150278872432515636467793 3862709154324386727350845)
  ·
    refine ⟨1448515932871645022756567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3862709154324386727350845 1448515932871645022756567)
    ·
      refine ⟨2172773899307467534134851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1448515932871645022756567 2172773899307467534134851)
      ·
        refine ⟨3259160848961201301202277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172773899307467534134851 3259160848961201301202277)
        ·
          refine ⟨611092659180225243975427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3259160848961201301202277 611092659180225243975427)
          ·
            refine ⟨916638988770337865963141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611092659180225243975427 916638988770337865963141)
            ·
              refine ⟨171869810394438349868089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 916638988770337865963141 171869810394438349868089)
              ·
                refine ⟨128902357795828762401067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171869810394438349868089 128902357795828762401067)
                ·
                  refine ⟨193353536693743143601601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128902357795828762401067 193353536693743143601601)
                  ·
                    refine ⟨145015152520307357701201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193353536693743143601601 145015152520307357701201)
                    ·
                      refine ⟨108761364390230518275901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145015152520307357701201 108761364390230518275901)
                      ·
                        rfl

theorem cell23_211812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_211812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211812 prefixEnd_211812 := by exact prefixLift 211812
  have htrace : WordTrace (prefixWord ++ tailWord_211812) baseStart_211812 baseEnd_211812 := by
    simpa [prefixWord, tailWord_211812, baseEnd_211812] using wordTrace_append hprefix tailTrace_211812
  have hstable : (prefixWord ++ tailWord_211812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211812).length < 2 ^ (prefixWord ++ tailWord_211812).sum := by decide
  have hdescent : baseEnd_211812 < baseStart_211812 := by decide
  rcases family_descends (prefixWord ++ tailWord_211812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211827 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 1, 8]
def baseStart_211827 : Nat := 118140960795 + 211827 * 2 ^ 59
def prefixEnd_211827 : Nat := 4983230072969 + 3 ^ 40 * 211827 * 2
def baseEnd_211827 : Nat := 36256355533349319862777

theorem tailTrace_211827 : CollatzResearch.WordTrace tailWord_211827 prefixEnd_211827 36256355533349319862777 := by
  unfold tailWord_211827
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725965403594431016497735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5150643602396287344331823 7725965403594431016497735)
  ·
    refine ⟨11588948105391646524746603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7725965403594431016497735 11588948105391646524746603)
    ·
      refine ⟨17383422158087469787119905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588948105391646524746603 17383422158087469787119905)
      ·
        refine ⟨13037566618565602340339929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17383422158087469787119905 13037566618565602340339929)
        ·
          refine ⟨9778174963924201755254947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13037566618565602340339929 9778174963924201755254947)
          ·
            refine ⟨14667262445886302632882421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778174963924201755254947 14667262445886302632882421)
            ·
              refine ⟨1375055854301840871832727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14667262445886302632882421 1375055854301840871832727)
              ·
                refine ⟨2062583781452761307749091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375055854301840871832727 2062583781452761307749091)
                ·
                  refine ⟨3093875672179141961623637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062583781452761307749091 3093875672179141961623637)
                  ·
                    refine ⟨36256355533349319862777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3093875672179141961623637 36256355533349319862777)
                    ·
                      rfl

theorem cell23_211827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 8].length) (baseStart_211827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211827 prefixEnd_211827 := by exact prefixLift 211827
  have htrace : WordTrace (prefixWord ++ tailWord_211827) baseStart_211827 baseEnd_211827 := by
    simpa [prefixWord, tailWord_211827, baseEnd_211827] using wordTrace_append hprefix tailTrace_211827
  have hstable : (prefixWord ++ tailWord_211827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211827).length < 2 ^ (prefixWord ++ tailWord_211827).sum := by decide
  have hdescent : baseEnd_211827 < baseStart_211827 := by decide
  rcases family_descends (prefixWord ++ tailWord_211827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211851 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 1, 4, 2]
def baseStart_211851 : Nat := 118140960795 + 211851 * 2 ^ 59
def prefixEnd_211851 : Nat := 4983230072969 + 3 ^ 40 * 211851 * 2
def baseEnd_211851 : Nat := 108781390135755865688221

theorem tailTrace_211851 : CollatzResearch.WordTrace tailWord_211851 prefixEnd_211851 108781390135755865688221 := by
  unfold tailWord_211851
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726840755507483115371407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5151227170338322076914271 7726840755507483115371407)
  ·
    refine ⟨11590261133261224673057111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7726840755507483115371407 11590261133261224673057111)
    ·
      refine ⟨17385391699891837009585667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11590261133261224673057111 17385391699891837009585667)
      ·
        refine ⟨26078087549837755514378501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17385391699891837009585667 26078087549837755514378501)
        ·
          refine ⟨4889641415594579158945969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26078087549837755514378501 4889641415594579158945969)
          ·
            refine ⟨3667231061695934369209477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4889641415594579158945969 3667231061695934369209477)
            ·
              refine ⟨687605824067987694226777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3667231061695934369209477 687605824067987694226777)
              ·
                refine ⟨515704368050990770670083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687605824067987694226777 515704368050990770670083)
                ·
                  refine ⟨773556552076486156005125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515704368050990770670083 773556552076486156005125)
                  ·
                    refine ⟨145041853514341154250961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773556552076486156005125 145041853514341154250961)
                    ·
                      refine ⟨108781390135755865688221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145041853514341154250961 108781390135755865688221)
                      ·
                        rfl

theorem cell23_211851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 4, 2].length) (baseStart_211851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211851 prefixEnd_211851 := by exact prefixLift 211851
  have htrace : WordTrace (prefixWord ++ tailWord_211851) baseStart_211851 baseEnd_211851 := by
    simpa [prefixWord, tailWord_211851, baseEnd_211851] using wordTrace_append hprefix tailTrace_211851
  have hstable : (prefixWord ++ tailWord_211851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211851).length < 2 ^ (prefixWord ++ tailWord_211851).sum := by decide
  have hdescent : baseEnd_211851 < baseStart_211851 := by decide
  rcases family_descends (prefixWord ++ tailWord_211851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211857 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 11]
def baseStart_211857 : Nat := 118140960795 + 211857 * 2 ^ 59
def prefixEnd_211857 : Nat := 4983230072969 + 3 ^ 40 * 211857 * 2
def baseEnd_211857 : Nat := 12087163446631426912577

theorem tailTrace_211857 : CollatzResearch.WordTrace tailWord_211857 prefixEnd_211857 12087163446631426912577 := by
  unfold tailWord_211857
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727059593485746140089825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5151373062323830760059883 7727059593485746140089825)
  ·
    refine ⟨5795294695114309605067369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7727059593485746140089825 5795294695114309605067369)
    ·
      refine ⟨4346471021335732203800527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5795294695114309605067369 4346471021335732203800527)
      ·
        refine ⟨6519706532003598305700791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346471021335732203800527 6519706532003598305700791)
        ·
          refine ⟨9779559798005397458551187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519706532003598305700791 9779559798005397458551187)
          ·
            refine ⟨14669339697008096187826781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9779559798005397458551187 14669339697008096187826781)
            ·
              refine ⟨5501002386378036070435043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14669339697008096187826781 5501002386378036070435043)
              ·
                refine ⟨8251503579567054105652565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5501002386378036070435043 8251503579567054105652565)
                ·
                  refine ⟨12087163446631426912577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 8251503579567054105652565 12087163446631426912577)
                  ·
                    rfl

theorem cell23_211857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 11].length) (baseStart_211857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211857 prefixEnd_211857 := by exact prefixLift 211857
  have htrace : WordTrace (prefixWord ++ tailWord_211857) baseStart_211857 baseEnd_211857 := by
    simpa [prefixWord, tailWord_211857, baseEnd_211857] using wordTrace_append hprefix tailTrace_211857
  have hstable : (prefixWord ++ tailWord_211857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211857).length < 2 ^ (prefixWord ++ tailWord_211857).sum := by decide
  have hdescent : baseEnd_211857 < baseStart_211857 := by decide
  rcases family_descends (prefixWord ++ tailWord_211857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211862 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_211862 : Nat := 118140960795 + 211862 * 2 ^ 59
def prefixEnd_211862 : Nat := 4983230072969 + 3 ^ 40 * 211862 * 2
def baseEnd_211862 : Nat := 108787038422955322650671

theorem tailTrace_211862 : CollatzResearch.WordTrace tailWord_211862 prefixEnd_211862 108787038422955322650671 := by
  unfold tailWord_211862
  simp only [CollatzResearch.WordTrace]
  refine ⟨482952622404226999626365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5151494638978421329347893 482952622404226999626365)
  ·
    refine ⟨181107233401585124859887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 482952622404226999626365 181107233401585124859887)
    ·
      refine ⟨271660850102377687289831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181107233401585124859887 271660850102377687289831)
      ·
        refine ⟨407491275153566530934747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271660850102377687289831 407491275153566530934747)
        ·
          refine ⟨611236912730349796402121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407491275153566530934747 611236912730349796402121)
          ·
            refine ⟨458427684547762347301591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611236912730349796402121 458427684547762347301591)
            ·
              refine ⟨687641526821643520952387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458427684547762347301591 687641526821643520952387)
              ·
                refine ⟨1031462290232465281428581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687641526821643520952387 1031462290232465281428581)
                ·
                  refine ⟨193399179418587240267859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1031462290232465281428581 193399179418587240267859)
                  ·
                    refine ⟨290098769127880860401789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193399179418587240267859 290098769127880860401789)
                    ·
                      refine ⟨108787038422955322650671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 290098769127880860401789 108787038422955322650671)
                      ·
                        rfl

theorem cell23_211862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_211862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211862 prefixEnd_211862 := by exact prefixLift 211862
  have htrace : WordTrace (prefixWord ++ tailWord_211862) baseStart_211862 baseEnd_211862 := by
    simpa [prefixWord, tailWord_211862, baseEnd_211862] using wordTrace_append hprefix tailTrace_211862
  have hstable : (prefixWord ++ tailWord_211862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211862).length < 2 ^ (prefixWord ++ tailWord_211862).sum := by decide
  have hdescent : baseEnd_211862 < baseStart_211862 := by decide
  rcases family_descends (prefixWord ++ tailWord_211862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211904 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 1, 7]
def baseStart_211904 : Nat := 118140960795 + 211904 * 2 ^ 59
def prefixEnd_211904 : Nat := 4983230072969 + 3 ^ 40 * 211904 * 2
def baseEnd_211904 : Nat := 36269534870148052775159

theorem tailTrace_211904 : CollatzResearch.WordTrace tailWord_211904 prefixEnd_211904 36269534870148052775159 := by
  unfold tailWord_211904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864386912157736583525383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5152515882876982111367177 3864386912157736583525383)
  ·
    refine ⟨5796580368236604875288075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3864386912157736583525383 5796580368236604875288075)
    ·
      refine ⟨8694870552354907312932113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5796580368236604875288075 8694870552354907312932113)
      ·
        refine ⟨6521152914266180484699085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8694870552354907312932113 6521152914266180484699085)
        ·
          refine ⟨2445432342849817681762157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6521152914266180484699085 2445432342849817681762157)
          ·
            refine ⟨917037128568681630660809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2445432342849817681762157 917037128568681630660809)
            ·
              refine ⟨687777846426511222995607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917037128568681630660809 687777846426511222995607)
              ·
                refine ⟨1031666769639766834493411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687777846426511222995607 1031666769639766834493411)
                ·
                  refine ⟨1547500154459650251740117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031666769639766834493411 1547500154459650251740117)
                  ·
                    refine ⟨36269534870148052775159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1547500154459650251740117 36269534870148052775159)
                    ·
                      rfl

theorem cell23_211904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_211904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211904 prefixEnd_211904 := by exact prefixLift 211904
  have htrace : WordTrace (prefixWord ++ tailWord_211904) baseStart_211904 baseEnd_211904 := by
    simpa [prefixWord, tailWord_211904, baseEnd_211904] using wordTrace_append hprefix tailTrace_211904
  have hstable : (prefixWord ++ tailWord_211904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211904).length < 2 ^ (prefixWord ++ tailWord_211904).sum := by decide
  have hdescent : baseEnd_211904 < baseStart_211904 := by decide
  rcases family_descends (prefixWord ++ tailWord_211904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211914 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_211914 : Nat := 118140960795 + 211914 * 2 ^ 59
def prefixEnd_211914 : Nat := 4983230072969 + 3 ^ 40 * 211914 * 2
def baseEnd_211914 : Nat := 108813739416989119200431

theorem tailTrace_211914 : CollatzResearch.WordTrace tailWord_211914 prefixEnd_211914 108813739416989119200431 := by
  unfold tailWord_211914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932284638569811218728699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5152759036186163249943197 1932284638569811218728699)
  ·
    refine ⟨2898426957854716828093049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1932284638569811218728699 2898426957854716828093049)
    ·
      refine ⟨2173820218391037621069787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2898426957854716828093049 2173820218391037621069787)
      ·
        refine ⟨3260730327586556431604681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173820218391037621069787 3260730327586556431604681)
        ·
          refine ⟨2445547745689917323703511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3260730327586556431604681 2445547745689917323703511)
          ·
            refine ⟨3668321618534875985555267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445547745689917323703511 3668321618534875985555267)
            ·
              refine ⟨5502482427802313978332901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668321618534875985555267 5502482427802313978332901)
              ·
                refine ⟨1031715455212933870937419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5502482427802313978332901 1031715455212933870937419)
                ·
                  refine ⟨1547573182819400806406129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1031715455212933870937419 1547573182819400806406129)
                  ·
                    refine ⟨1160679887114550604804597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1547573182819400806406129 1160679887114550604804597)
                    ·
                      refine ⟨108813739416989119200431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1160679887114550604804597 108813739416989119200431)
                      ·
                        rfl

theorem cell23_211914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_211914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211914 prefixEnd_211914 := by exact prefixLift 211914
  have htrace : WordTrace (prefixWord ++ tailWord_211914) baseStart_211914 baseEnd_211914 := by
    simpa [prefixWord, tailWord_211914, baseEnd_211914] using wordTrace_append hprefix tailTrace_211914
  have hstable : (prefixWord ++ tailWord_211914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211914).length < 2 ^ (prefixWord ++ tailWord_211914).sum := by decide
  have hdescent : baseEnd_211914 < baseStart_211914 := by decide
  rcases family_descends (prefixWord ++ tailWord_211914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211925 : List Nat := [1, 3, 2, 3, 3, 1, 3, 2, 5]
def baseStart_211925 : Nat := 118140960795 + 211925 * 2 ^ 59
def prefixEnd_211925 : Nat := 4983230072969 + 3 ^ 40 * 211925 * 2
def baseEnd_211925 : Nat := 12091043078243175129209

theorem tailTrace_211925 : CollatzResearch.WordTrace tailWord_211925 prefixEnd_211925 12091043078243175129209 := by
  unfold tailWord_211925
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729539757239393753565229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5153026504826262502376819 7729539757239393753565229)
  ·
    refine ⟨2898577408964772657586961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7729539757239393753565229 2898577408964772657586961)
    ·
      refine ⟨2173933056723579493190221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2898577408964772657586961 2173933056723579493190221)
      ·
        refine ⟨815224896271342309946333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2173933056723579493190221 815224896271342309946333)
        ·
          refine ⟨305709336101753366229875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 815224896271342309946333 305709336101753366229875)
          ·
            refine ⟨458564004152630049344813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305709336101753366229875 458564004152630049344813)
            ·
              refine ⟨171961501557236268504305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458564004152630049344813 171961501557236268504305)
              ·
                refine ⟨128971126167927201378229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171961501557236268504305 128971126167927201378229)
                ·
                  refine ⟨12091043078243175129209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128971126167927201378229 12091043078243175129209)
                  ·
                    rfl

theorem cell23_211925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_211925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211925 prefixEnd_211925 := by exact prefixLift 211925
  have htrace : WordTrace (prefixWord ++ tailWord_211925) baseStart_211925 baseEnd_211925 := by
    simpa [prefixWord, tailWord_211925, baseEnd_211925] using wordTrace_append hprefix tailTrace_211925
  have hstable : (prefixWord ++ tailWord_211925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211925).length < 2 ^ (prefixWord ++ tailWord_211925).sum := by decide
  have hdescent : baseEnd_211925 < baseStart_211925 := by decide
  rcases family_descends (prefixWord ++ tailWord_211925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211958 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_211958 : Nat := 118140960795 + 211958 * 2 ^ 59
def prefixEnd_211958 : Nat := 4983230072969 + 3 ^ 40 * 211958 * 2
def baseEnd_211958 : Nat := 108836332565786947050229

theorem tailTrace_211958 : CollatzResearch.WordTrace tailWord_211958 prefixEnd_211958 108836332565786947050229 := by
  unfold tailWord_211958
  simp only [CollatzResearch.WordTrace]
  refine ⟨483171460382490024344783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5153828910746560259677685 483171460382490024344783)
  ·
    refine ⟨724757190573735036517175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 483171460382490024344783 724757190573735036517175)
    ·
      refine ⟨1087135785860602554775763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724757190573735036517175 1087135785860602554775763)
      ·
        refine ⟨1630703678790903832163645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087135785860602554775763 1630703678790903832163645)
        ·
          refine ⟨611513879546588937061367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1630703678790903832163645 611513879546588937061367)
          ·
            refine ⟨917270819319883405592051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611513879546588937061367 917270819319883405592051)
            ·
              refine ⟨1375906228979825108388077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917270819319883405592051 1375906228979825108388077)
              ·
                refine ⟨515964835867434415645529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375906228979825108388077 515964835867434415645529)
                ·
                  refine ⟨386973626900575811734147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515964835867434415645529 386973626900575811734147)
                  ·
                    refine ⟨580460440350863717601221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 386973626900575811734147 580460440350863717601221)
                    ·
                      refine ⟨108836332565786947050229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 580460440350863717601221 108836332565786947050229)
                      ·
                        rfl

theorem cell23_211958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_211958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211958 prefixEnd_211958 := by exact prefixLift 211958
  have htrace : WordTrace (prefixWord ++ tailWord_211958) baseStart_211958 baseEnd_211958 := by
    simpa [prefixWord, tailWord_211958, baseEnd_211958] using wordTrace_append hprefix tailTrace_211958
  have hstable : (prefixWord ++ tailWord_211958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211958).length < 2 ^ (prefixWord ++ tailWord_211958).sum := by decide
  have hdescent : baseEnd_211958 < baseStart_211958 := by decide
  rcases family_descends (prefixWord ++ tailWord_211958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211978 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_211978 : Nat := 118140960795 + 211978 * 2 ^ 59
def prefixEnd_211978 : Nat := 4983230072969 + 3 ^ 40 * 211978 * 2
def baseEnd_211978 : Nat := 108846602178876868800137

theorem tailTrace_211978 : CollatzResearch.WordTrace tailWord_211978 prefixEnd_211978 108846602178876868800137 := by
  unfold tailWord_211978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932868206511845951311147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5154315217364922536829725 1932868206511845951311147)
  ·
    refine ⟨2899302309767768926966721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1932868206511845951311147 2899302309767768926966721)
    ·
      refine ⟨2174476732325826695225041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2899302309767768926966721 2174476732325826695225041)
      ·
        refine ⟨1630857549244370021418781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2174476732325826695225041 1630857549244370021418781)
        ·
          refine ⟨611571580966638758032043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1630857549244370021418781 611571580966638758032043)
          ·
            refine ⟨917357371449958137048065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611571580966638758032043 917357371449958137048065)
            ·
              refine ⟨688018028587468602786049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917357371449958137048065 688018028587468602786049)
              ·
                refine ⟨516013521440601452089537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688018028587468602786049 516013521440601452089537)
                ·
                  refine ⟨387010141080451089067153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516013521440601452089537 387010141080451089067153)
                  ·
                    refine ⟨290257605810338316800365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 387010141080451089067153 290257605810338316800365)
                    ·
                      refine ⟨108846602178876868800137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 290257605810338316800365 108846602178876868800137)
                      ·
                        rfl

theorem cell23_211978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_211978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_211978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_211978 prefixEnd_211978 := by exact prefixLift 211978
  have htrace : WordTrace (prefixWord ++ tailWord_211978) baseStart_211978 baseEnd_211978 := by
    simpa [prefixWord, tailWord_211978, baseEnd_211978] using wordTrace_append hprefix tailTrace_211978
  have hstable : (prefixWord ++ tailWord_211978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211978).length < 2 ^ (prefixWord ++ tailWord_211978).sum := by decide
  have hdescent : baseEnd_211978 < baseStart_211978 := by decide
  rcases family_descends (prefixWord ++ tailWord_211978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212011 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 1, 5]
def baseStart_212011 : Nat := 118140960795 + 212011 * 2 ^ 59
def prefixEnd_212011 : Nat := 4983230072969 + 3 ^ 40 * 212011 * 2
def baseEnd_212011 : Nat := 36287849013491746562495

theorem tailTrace_212011 : CollatzResearch.WordTrace tailWord_212011 prefixEnd_212011 36287849013491746562495 := by
  unfold tailWord_212011
  simp only [CollatzResearch.WordTrace]
  refine ⟨7732676434927830441195887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5155117623285220294130591 7732676434927830441195887)
  ·
    refine ⟨11599014652391745661793831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7732676434927830441195887 11599014652391745661793831)
    ·
      refine ⟨17398521978587618492690747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11599014652391745661793831 17398521978587618492690747)
      ·
        refine ⟨26097782967881427739036121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17398521978587618492690747 26097782967881427739036121)
        ·
          refine ⟨19573337225911070804277091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26097782967881427739036121 19573337225911070804277091)
          ·
            refine ⟨29360005838866606206415637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19573337225911070804277091 29360005838866606206415637)
            ·
              refine ⟨1376250273696872165925733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29360005838866606206415637 1376250273696872165925733)
              ·
                refine ⟨258046926318163531111075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1376250273696872165925733 258046926318163531111075)
                ·
                  refine ⟨387070389477245296666613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258046926318163531111075 387070389477245296666613)
                  ·
                    refine ⟨36287849013491746562495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387070389477245296666613 36287849013491746562495)
                    ·
                      rfl

theorem cell23_212011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 5].length) (baseStart_212011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212011 prefixEnd_212011 := by exact prefixLift 212011
  have htrace : WordTrace (prefixWord ++ tailWord_212011) baseStart_212011 baseEnd_212011 := by
    simpa [prefixWord, tailWord_212011, baseEnd_212011] using wordTrace_append hprefix tailTrace_212011
  have hstable : (prefixWord ++ tailWord_212011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212011).length < 2 ^ (prefixWord ++ tailWord_212011).sum := by decide
  have hdescent : baseEnd_212011 < baseStart_212011 := by decide
  rcases family_descends (prefixWord ++ tailWord_212011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212018 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_212018 : Nat := 118140960795 + 212018 * 2 ^ 59
def prefixEnd_212018 : Nat := 4983230072969 + 3 ^ 40 * 212018 * 2
def baseEnd_212018 : Nat := 108867141405056712299953

theorem tailTrace_212018 : CollatzResearch.WordTrace tailWord_212018 prefixEnd_212018 108867141405056712299953 := by
  unfold tailWord_212018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933232936475617659175177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5155287830601647091133805 1933232936475617659175177)
  ·
    refine ⟨1449924702356713244381383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1933232936475617659175177 1449924702356713244381383)
    ·
      refine ⟨2174887053535069866572075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1449924702356713244381383 2174887053535069866572075)
      ·
        refine ⟨3262330580302604799858113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174887053535069866572075 3262330580302604799858113)
        ·
          refine ⟨2446747935226953599893585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3262330580302604799858113 2446747935226953599893585)
          ·
            refine ⟨1835060951420215199920189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446747935226953599893585 1835060951420215199920189)
            ·
              refine ⟨688147856782580699970071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1835060951420215199920189 688147856782580699970071)
              ·
                refine ⟨1032221785173871049955107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688147856782580699970071 1032221785173871049955107)
                ·
                  refine ⟨1548332677760806574932661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1032221785173871049955107 1548332677760806574932661)
                  ·
                    refine ⟨145156188540075616399937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1548332677760806574932661 145156188540075616399937)
                    ·
                      refine ⟨108867141405056712299953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145156188540075616399937 108867141405056712299953)
                      ·
                        rfl

theorem cell23_212018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_212018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212018 prefixEnd_212018 := by exact prefixLift 212018
  have htrace : WordTrace (prefixWord ++ tailWord_212018) baseStart_212018 baseEnd_212018 := by
    simpa [prefixWord, tailWord_212018, baseEnd_212018] using wordTrace_append hprefix tailTrace_212018
  have hstable : (prefixWord ++ tailWord_212018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212018).length < 2 ^ (prefixWord ++ tailWord_212018).sum := by decide
  have hdescent : baseEnd_212018 < baseStart_212018 := by decide
  rcases family_descends (prefixWord ++ tailWord_212018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212028 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_212028 : Nat := 118140960795 + 212028 * 2 ^ 59
def prefixEnd_212028 : Nat := 4983230072969 + 3 ^ 40 * 212028 * 2
def baseEnd_212028 : Nat := 36290758737200557724969

theorem tailTrace_212028 : CollatzResearch.WordTrace tailWord_212028 prefixEnd_212028 36290758737200557724969 := by
  unfold tailWord_212028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866648237933121172282369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5155530983910828229709825 3866648237933121172282369)
  ·
    refine ⟨2899986178449840879211777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3866648237933121172282369 2899986178449840879211777)
    ·
      refine ⟨2174989633837380659408833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2899986178449840879211777 2174989633837380659408833)
      ·
        refine ⟨1631242225378035494556625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2174989633837380659408833 1631242225378035494556625)
        ·
          refine ⟨1223431669033526620917469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1631242225378035494556625 1223431669033526620917469)
          ·
            refine ⟨458786875887572482844051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1223431669033526620917469 458786875887572482844051)
            ·
              refine ⟨688180313831358724266077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458786875887572482844051 688180313831358724266077)
              ·
                refine ⟨258067617686759521599779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 688180313831358724266077 258067617686759521599779)
                ·
                  refine ⟨387101426530139282399669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258067617686759521599779 387101426530139282399669)
                  ·
                    refine ⟨36290758737200557724969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387101426530139282399669 36290758737200557724969)
                    ·
                      rfl

theorem cell23_212028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_212028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212028 prefixEnd_212028 := by exact prefixLift 212028
  have htrace : WordTrace (prefixWord ++ tailWord_212028) baseStart_212028 baseEnd_212028 := by
    simpa [prefixWord, tailWord_212028, baseEnd_212028] using wordTrace_append hprefix tailTrace_212028
  have hstable : (prefixWord ++ tailWord_212028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212028).length < 2 ^ (prefixWord ++ tailWord_212028).sum := by decide
  have hdescent : baseEnd_212028 < baseStart_212028 := by decide
  rcases family_descends (prefixWord ++ tailWord_212028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212062 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_212062 : Nat := 118140960795 + 212062 * 2 ^ 59
def prefixEnd_212062 : Nat := 4983230072969 + 3 ^ 40 * 212062 * 2
def baseEnd_212062 : Nat := 36296578184618180049917

theorem tailTrace_212062 : CollatzResearch.WordTrace tailWord_212062 prefixEnd_212062 36296578184618180049917 := by
  unfold tailWord_212062
  simp only [CollatzResearch.WordTrace]
  refine ⟨966817069717883268912805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5156357705162044100868293 966817069717883268912805)
  ·
    refine ⟨181278200572103112921151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 966817069717883268912805 181278200572103112921151)
    ·
      refine ⟨271917300858154669381727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181278200572103112921151 271917300858154669381727)
      ·
        refine ⟨407875951287232004072591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271917300858154669381727 407875951287232004072591)
        ·
          refine ⟨611813926930848006108887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407875951287232004072591 611813926930848006108887)
          ·
            refine ⟨917720890396272009163331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611813926930848006108887 917720890396272009163331)
            ·
              refine ⟨1376581335594408013744997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917720890396272009163331 1376581335594408013744997)
              ·
                refine ⟨258109000423951502577187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1376581335594408013744997 258109000423951502577187)
                ·
                  refine ⟨387163500635927253865781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258109000423951502577187 387163500635927253865781)
                  ·
                    refine ⟨36296578184618180049917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387163500635927253865781 36296578184618180049917)
                    ·
                      rfl

theorem cell23_212062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_212062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212062 prefixEnd_212062 := by exact prefixLift 212062
  have htrace : WordTrace (prefixWord ++ tailWord_212062) baseStart_212062 baseEnd_212062 := by
    simpa [prefixWord, tailWord_212062, baseEnd_212062] using wordTrace_append hprefix tailTrace_212062
  have hstable : (prefixWord ++ tailWord_212062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212062).length < 2 ^ (prefixWord ++ tailWord_212062).sum := by decide
  have hdescent : baseEnd_212062 < baseStart_212062 := by decide
  rcases family_descends (prefixWord ++ tailWord_212062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212065 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_212065 : Nat := 118140960795 + 212065 * 2 ^ 59
def prefixEnd_212065 : Nat := 4983230072969 + 3 ^ 40 * 212065 * 2
def baseEnd_212065 : Nat := 108891274995818028412237

theorem tailTrace_212065 : CollatzResearch.WordTrace tailWord_212065 prefixEnd_212065 108891274995818028412237 := by
  unfold tailWord_212065
  simp only [CollatzResearch.WordTrace]
  refine ⟨7734645976732197663661649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5156430651154798442441099 7734645976732197663661649)
  ·
    refine ⟨5800984482549148247746237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7734645976732197663661649 5800984482549148247746237)
    ·
      refine ⟨2175369180955930592904839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5800984482549148247746237 2175369180955930592904839)
      ·
        refine ⟨3263053771433895889357259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175369180955930592904839 3263053771433895889357259)
        ·
          refine ⟨4894580657150843834035889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263053771433895889357259 4894580657150843834035889)
          ·
            refine ⟨3670935492863132875526917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4894580657150843834035889 3670935492863132875526917)
            ·
              refine ⟨688300404911837414161297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3670935492863132875526917 688300404911837414161297)
              ·
                refine ⟨516225303683878060620973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688300404911837414161297 516225303683878060620973)
                ·
                  refine ⟨193584488881454272732865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516225303683878060620973 193584488881454272732865)
                  ·
                    refine ⟨145188366661090704549649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193584488881454272732865 145188366661090704549649)
                    ·
                      refine ⟨108891274995818028412237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145188366661090704549649 108891274995818028412237)
                      ·
                        rfl

theorem cell23_212065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_212065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212065 prefixEnd_212065 := by exact prefixLift 212065
  have htrace : WordTrace (prefixWord ++ tailWord_212065) baseStart_212065 baseEnd_212065 := by
    simpa [prefixWord, tailWord_212065, baseEnd_212065] using wordTrace_append hprefix tailTrace_212065
  have hstable : (prefixWord ++ tailWord_212065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212065).length < 2 ^ (prefixWord ++ tailWord_212065).sum := by decide
  have hdescent : baseEnd_212065 < baseStart_212065 := by decide
  rcases family_descends (prefixWord ++ tailWord_212065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212071 : List Nat := [1, 1, 5, 1, 1, 4, 1, 9]
def baseStart_212071 : Nat := 118140960795 + 212071 * 2 ^ 59
def prefixEnd_212071 : Nat := 4983230072969 + 3 ^ 40 * 212071 * 2
def baseEnd_212071 : Nat := 4033124291842407590267

theorem tailTrace_212071 : CollatzResearch.WordTrace tailWord_212071 prefixEnd_212071 4033124291842407590267 := by
  unfold tailWord_212071
  simp only [CollatzResearch.WordTrace]
  refine ⟨7734864814710460688380067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5156576543140307125586711 7734864814710460688380067)
  ·
    refine ⟨11602297222065691032570101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7734864814710460688380067 11602297222065691032570101)
    ·
      refine ⟨1087715364568658534303447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11602297222065691032570101 1087715364568658534303447)
      ·
        refine ⟨1631573046852987801455171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087715364568658534303447 1631573046852987801455171)
        ·
          refine ⟨2447359570279481702182757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631573046852987801455171 2447359570279481702182757)
          ·
            refine ⟨458879919427402819159267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2447359570279481702182757 458879919427402819159267)
            ·
              refine ⟨688319879141104228738901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458879919427402819159267 688319879141104228738901)
              ·
                refine ⟨4033124291842407590267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 688319879141104228738901 4033124291842407590267)
                ·
                  rfl

theorem cell23_212071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 9].length) (baseStart_212071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212071 prefixEnd_212071 := by exact prefixLift 212071
  have htrace : WordTrace (prefixWord ++ tailWord_212071) baseStart_212071 baseEnd_212071 := by
    simpa [prefixWord, tailWord_212071, baseEnd_212071] using wordTrace_append hprefix tailTrace_212071
  have hstable : (prefixWord ++ tailWord_212071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212071).length < 2 ^ (prefixWord ++ tailWord_212071).sum := by decide
  have hdescent : baseEnd_212071 < baseStart_212071 := by decide
  rcases family_descends (prefixWord ++ tailWord_212071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212099 : List Nat := [1, 1, 1, 3, 3, 2, 5, 2, 1, 2, 2]
def baseStart_212099 : Nat := 118140960795 + 212099 * 2 ^ 59
def prefixEnd_212099 : Nat := 4983230072969 + 3 ^ 40 * 212099 * 2
def baseEnd_212099 : Nat := 108908733338070895387081

theorem tailTrace_212099 : CollatzResearch.WordTrace tailWord_212099 prefixEnd_212099 108908733338070895387081 := by
  unfold tailWord_212099
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735886058609021470399351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5157257372406014313599567 7735886058609021470399351)
  ·
    refine ⟨11603829087913532205599027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7735886058609021470399351 11603829087913532205599027)
    ·
      refine ⟨17405743631870298308398541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11603829087913532205599027 17405743631870298308398541)
      ·
        refine ⟨6527153861951361865649453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17405743631870298308398541 6527153861951361865649453)
        ·
          refine ⟨2447682698231760699618545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6527153861951361865649453 2447682698231760699618545)
          ·
            refine ⟨1835762023673820524713909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2447682698231760699618545 1835762023673820524713909)
            ·
              refine ⟨172102689719420674191929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1835762023673820524713909 172102689719420674191929)
              ·
                refine ⟨129077017289565505643947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172102689719420674191929 129077017289565505643947)
                ·
                  refine ⟨193615525934348258465921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129077017289565505643947 193615525934348258465921)
                  ·
                    refine ⟨145211644450761193849441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193615525934348258465921 145211644450761193849441)
                    ·
                      refine ⟨108908733338070895387081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145211644450761193849441 108908733338070895387081)
                      ·
                        rfl

theorem cell23_212099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 2, 2].length) (baseStart_212099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212099 prefixEnd_212099 := by exact prefixLift 212099
  have htrace : WordTrace (prefixWord ++ tailWord_212099) baseStart_212099 baseEnd_212099 := by
    simpa [prefixWord, tailWord_212099, baseEnd_212099] using wordTrace_append hprefix tailTrace_212099
  have hstable : (prefixWord ++ tailWord_212099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212099).length < 2 ^ (prefixWord ++ tailWord_212099).sum := by decide
  have hdescent : baseEnd_212099 < baseStart_212099 := by decide
  rcases family_descends (prefixWord ++ tailWord_212099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212125 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_212125 : Nat := 118140960795 + 212125 * 2 ^ 59
def prefixEnd_212125 : Nat := 4983230072969 + 3 ^ 40 * 212125 * 2
def baseEnd_212125 : Nat := 108922083835087793661961

theorem tailTrace_212125 : CollatzResearch.WordTrace tailWord_212125 prefixEnd_212125 108922083835087793661961 := by
  unfold tailWord_212125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736834356514827910845829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5157889571009885273897219 7736834356514827910845829)
  ·
    refine ⟨1450656441846530233283593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7736834356514827910845829 1450656441846530233283593)
    ·
      refine ⟨1087992331384897674962695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1450656441846530233283593 1087992331384897674962695)
      ·
        refine ⟨1631988497077346512444043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087992331384897674962695 1631988497077346512444043)
        ·
          refine ⟨2447982745616019768666065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631988497077346512444043 2447982745616019768666065)
          ·
            refine ⟨1835987059212014826499549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2447982745616019768666065 1835987059212014826499549)
            ·
              refine ⟨688495147204505559937331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1835987059212014826499549 688495147204505559937331)
              ·
                refine ⟨1032742720806758339905997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688495147204505559937331 1032742720806758339905997)
                ·
                  refine ⟨387278520302534377464749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032742720806758339905997 387278520302534377464749)
                  ·
                    refine ⟨145229445113450391549281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387278520302534377464749 145229445113450391549281)
                    ·
                      refine ⟨108922083835087793661961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145229445113450391549281 108922083835087793661961)
                      ·
                        rfl

theorem cell23_212125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_212125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212125 prefixEnd_212125 := by exact prefixLift 212125
  have htrace : WordTrace (prefixWord ++ tailWord_212125) baseStart_212125 baseEnd_212125 := by
    simpa [prefixWord, tailWord_212125, baseEnd_212125] using wordTrace_append hprefix tailTrace_212125
  have hstable : (prefixWord ++ tailWord_212125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212125).length < 2 ^ (prefixWord ++ tailWord_212125).sum := by decide
  have hdescent : baseEnd_212125 < baseStart_212125 := by decide
  rcases family_descends (prefixWord ++ tailWord_212125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212166 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_212166 : Nat := 118140960795 + 212166 * 2 ^ 59
def prefixEnd_212166 : Nat := 4983230072969 + 3 ^ 40 * 212166 * 2
def baseEnd_212166 : Nat := 108943136541922133249273

theorem tailTrace_212166 : CollatzResearch.WordTrace tailWord_212166 prefixEnd_212166 108943136541922133249273 := by
  unfold tailWord_212166
  simp only [CollatzResearch.WordTrace]
  refine ⟨241822804667696622284011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5158886499577527942058901 241822804667696622284011)
  ·
    refine ⟨362734207001544933426017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241822804667696622284011 362734207001544933426017)
    ·
      refine ⟨272050655251158700069513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362734207001544933426017 272050655251158700069513)
      ·
        refine ⟨204037991438369025052135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272050655251158700069513 204037991438369025052135)
        ·
          refine ⟨306056987157553537578203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204037991438369025052135 306056987157553537578203)
          ·
            refine ⟨459085480736330306367305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306056987157553537578203 459085480736330306367305)
            ·
              refine ⟨344314110552247729775479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459085480736330306367305 344314110552247729775479)
              ·
                refine ⟨516471165828371594663219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344314110552247729775479 516471165828371594663219)
                ·
                  refine ⟨774706748742557391994829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516471165828371594663219 774706748742557391994829)
                  ·
                    refine ⟨290515030778459021998061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774706748742557391994829 290515030778459021998061)
                    ·
                      refine ⟨108943136541922133249273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 290515030778459021998061 108943136541922133249273)
                      ·
                        rfl

theorem cell23_212166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_212166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212166 prefixEnd_212166 := by exact prefixLift 212166
  have htrace : WordTrace (prefixWord ++ tailWord_212166) baseStart_212166 baseEnd_212166 := by
    simpa [prefixWord, tailWord_212166, baseEnd_212166] using wordTrace_append hprefix tailTrace_212166
  have hstable : (prefixWord ++ tailWord_212166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212166).length < 2 ^ (prefixWord ++ tailWord_212166).sum := by decide
  have hdescent : baseEnd_212166 < baseStart_212166 := by decide
  rcases family_descends (prefixWord ++ tailWord_212166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212178 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 7]
def baseStart_212178 : Nat := 118140960795 + 212178 * 2 ^ 59
def prefixEnd_212178 : Nat := 4983230072969 + 3 ^ 40 * 212178 * 2
def baseEnd_212178 : Nat := 12105477589975120699913

theorem tailTrace_212178 : CollatzResearch.WordTrace tailWord_212178 prefixEnd_212178 12105477589975120699913 := by
  unfold tailWord_212178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934691856330704490631297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5159178283548545308350125 1934691856330704490631297)
  ·
    refine ⟨1451018892248028367973473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1934691856330704490631297 1451018892248028367973473)
    ·
      refine ⟨1088264169186021275980105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1451018892248028367973473 1088264169186021275980105)
      ·
        refine ⟨816198126889515956985079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1088264169186021275980105 816198126889515956985079)
        ·
          refine ⟨1224297190334273935477619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816198126889515956985079 1224297190334273935477619)
          ·
            refine ⟨1836445785501410903216429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224297190334273935477619 1836445785501410903216429)
            ·
              refine ⟨688667169563029088706161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1836445785501410903216429 688667169563029088706161)
              ·
                refine ⟨516500377172271816529621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688667169563029088706161 516500377172271816529621)
                ·
                  refine ⟨12105477589975120699913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 516500377172271816529621 12105477589975120699913)
                  ·
                    rfl

theorem cell23_212178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_212178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212178 prefixEnd_212178 := by exact prefixLift 212178
  have htrace : WordTrace (prefixWord ++ tailWord_212178) baseStart_212178 baseEnd_212178 := by
    simpa [prefixWord, tailWord_212178, baseEnd_212178] using wordTrace_append hprefix tailTrace_212178
  have hstable : (prefixWord ++ tailWord_212178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212178).length < 2 ^ (prefixWord ++ tailWord_212178).sum := by decide
  have hdescent : baseEnd_212178 < baseStart_212178 := by decide
  rcases family_descends (prefixWord ++ tailWord_212178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212205 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_212205 : Nat := 118140960795 + 212205 * 2 ^ 59
def prefixEnd_212205 : Nat := 4983230072969 + 3 ^ 40 * 212205 * 2
def baseEnd_212205 : Nat := 108963162287447480661593

theorem tailTrace_212205 : CollatzResearch.WordTrace tailWord_212205 prefixEnd_212205 108963162287447480661593 := by
  unfold tailWord_212205
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739752196225001573758069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5159834797483334382505379 7739752196225001573758069)
  ·
    refine ⟨725601768396093897539819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7739752196225001573758069 725601768396093897539819)
    ·
      refine ⟨1088402652594140846309729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725601768396093897539819 1088402652594140846309729)
      ·
        refine ⟨816301989445605634732297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1088402652594140846309729 816301989445605634732297)
        ·
          refine ⟨612226492084204226049223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816301989445605634732297 612226492084204226049223)
          ·
            refine ⟨918339738126306339073835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612226492084204226049223 918339738126306339073835)
            ·
              refine ⟨1377509607189459508610753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918339738126306339073835 1377509607189459508610753)
              ·
                refine ⟨1033132205392094631458065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377509607189459508610753 1033132205392094631458065)
                ·
                  refine ⟨774849154044070973593549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1033132205392094631458065 774849154044070973593549)
                  ·
                    refine ⟨290568432766526615097581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 774849154044070973593549 290568432766526615097581)
                    ·
                      refine ⟨108963162287447480661593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 290568432766526615097581 108963162287447480661593)
                      ·
                        rfl

theorem cell23_212205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_212205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212205 prefixEnd_212205 := by exact prefixLift 212205
  have htrace : WordTrace (prefixWord ++ tailWord_212205) baseStart_212205 baseEnd_212205 := by
    simpa [prefixWord, tailWord_212205, baseEnd_212205] using wordTrace_append hprefix tailTrace_212205
  have hstable : (prefixWord ++ tailWord_212205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212205).length < 2 ^ (prefixWord ++ tailWord_212205).sum := by decide
  have hdescent : baseEnd_212205 < baseStart_212205 := by decide
  rcases family_descends (prefixWord ++ tailWord_212205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212268 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 6]
def baseStart_212268 : Nat := 118140960795 + 212268 * 2 ^ 59
def prefixEnd_212268 : Nat := 4983230072969 + 3 ^ 40 * 212268 * 2
def baseEnd_212268 : Nat := 12110612396520081574867

theorem tailTrace_212268 : CollatzResearch.WordTrace tailWord_212268 prefixEnd_212268 12110612396520081574867 := by
  unfold tailWord_212268
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871024997498381666650729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5161366663331175555534305 3871024997498381666650729)
  ·
    refine ⟨2903268748123786249988047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3871024997498381666650729 2903268748123786249988047)
    ·
      refine ⟨4354903122185679374982071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903268748123786249988047 4354903122185679374982071)
      ·
        refine ⟨6532354683278519062473107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4354903122185679374982071 6532354683278519062473107)
        ·
          refine ⟨9798532024917778593709661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532354683278519062473107 9798532024917778593709661)
          ·
            refine ⟨3674449509344166972641123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9798532024917778593709661 3674449509344166972641123)
            ·
              refine ⟨5511674264016250458961685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674449509344166972641123 5511674264016250458961685)
              ·
                refine ⟨258359731125761740263829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5511674264016250458961685 258359731125761740263829)
                ·
                  refine ⟨12110612396520081574867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 258359731125761740263829 12110612396520081574867)
                  ·
                    rfl

theorem cell23_212268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_212268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212268 prefixEnd_212268 := by exact prefixLift 212268
  have htrace : WordTrace (prefixWord ++ tailWord_212268) baseStart_212268 baseEnd_212268 := by
    simpa [prefixWord, tailWord_212268, baseEnd_212268] using wordTrace_append hprefix tailTrace_212268
  have hstable : (prefixWord ++ tailWord_212268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212268).length < 2 ^ (prefixWord ++ tailWord_212268).sum := by decide
  have hdescent : baseEnd_212268 < baseStart_212268 := by decide
  rcases family_descends (prefixWord ++ tailWord_212268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212366 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_212366 : Nat := 118140960795 + 212366 * 2 ^ 59
def prefixEnd_212366 : Nat := 4983230072969 + 3 ^ 40 * 212366 * 2
def baseEnd_212366 : Nat := 36348610890940450249451

theorem tailTrace_212366 : CollatzResearch.WordTrace tailWord_212366 prefixEnd_212366 36348610890940450249451 := by
  unfold tailWord_212366
  simp only [CollatzResearch.WordTrace]
  refine ⟨968203043580215758796119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5163749565761150713579301 968203043580215758796119)
  ·
    refine ⟨1452304565370323638194179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 968203043580215758796119 1452304565370323638194179)
    ·
      refine ⟨2178456848055485457291269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452304565370323638194179 2178456848055485457291269)
      ·
        refine ⟨408460659010403523242113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2178456848055485457291269 408460659010403523242113)
        ·
          refine ⟨306345494257802642431585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408460659010403523242113 306345494257802642431585)
          ·
            refine ⟨229759120693351981823689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306345494257802642431585 229759120693351981823689)
            ·
              refine ⟨172319340520013986367767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229759120693351981823689 172319340520013986367767)
              ·
                refine ⟨258479010780020979551651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172319340520013986367767 258479010780020979551651)
                ·
                  refine ⟨387718516170031469327477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258479010780020979551651 387718516170031469327477)
                  ·
                    refine ⟨36348610890940450249451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387718516170031469327477 36348610890940450249451)
                    ·
                      rfl

theorem cell23_212366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_212366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212366 prefixEnd_212366 := by exact prefixLift 212366
  have htrace : WordTrace (prefixWord ++ tailWord_212366) baseStart_212366 baseEnd_212366 := by
    simpa [prefixWord, tailWord_212366, baseEnd_212366] using wordTrace_append hprefix tailTrace_212366
  have hstable : (prefixWord ++ tailWord_212366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212366).length < 2 ^ (prefixWord ++ tailWord_212366).sum := by decide
  have hdescent : baseEnd_212366 < baseStart_212366 := by decide
  rcases family_descends (prefixWord ++ tailWord_212366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212386 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_212386 : Nat := 118140960795 + 212386 * 2 ^ 59
def prefixEnd_212386 : Nat := 4983230072969 + 3 ^ 40 * 212386 * 2
def baseEnd_212386 : Nat := 109056102285911272498261

theorem tailTrace_212386 : CollatzResearch.WordTrace tailWord_212386 prefixEnd_212386 109056102285911272498261 := by
  unfold tailWord_212386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936588452142317371524253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5164235872379512990731341 1936588452142317371524253)
  ·
    refine ⟨726220669553369014321595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1936588452142317371524253 726220669553369014321595)
    ·
      refine ⟨1089331004330053521482393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726220669553369014321595 1089331004330053521482393)
      ·
        refine ⟨816998253247540141111795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1089331004330053521482393 816998253247540141111795)
        ·
          refine ⟨1225497379871310211667693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816998253247540141111795 1225497379871310211667693)
          ·
            refine ⟨459561517451741329375385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1225497379871310211667693 459561517451741329375385)
            ·
              refine ⟨344671138088805997031539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459561517451741329375385 344671138088805997031539)
              ·
                refine ⟨517006707133208995547309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344671138088805997031539 517006707133208995547309)
                ·
                  refine ⟨193877515174953373330241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517006707133208995547309 193877515174953373330241)
                  ·
                    refine ⟨145408136381215029997681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193877515174953373330241 145408136381215029997681)
                    ·
                      refine ⟨109056102285911272498261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145408136381215029997681 109056102285911272498261)
                      ·
                        rfl

theorem cell23_212386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_212386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212386 prefixEnd_212386 := by exact prefixLift 212386
  have htrace : WordTrace (prefixWord ++ tailWord_212386) baseStart_212386 baseEnd_212386 := by
    simpa [prefixWord, tailWord_212386, baseEnd_212386] using wordTrace_append hprefix tailTrace_212386
  have hstable : (prefixWord ++ tailWord_212386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212386).length < 2 ^ (prefixWord ++ tailWord_212386).sum := by decide
  have hdescent : baseEnd_212386 < baseStart_212386 := by decide
  rcases family_descends (prefixWord ++ tailWord_212386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212409 : List Nat := [1, 2, 1, 4, 5, 1, 2, 7]
def baseStart_212409 : Nat := 118140960795 + 212409 * 2 ^ 59
def prefixEnd_212409 : Nat := 4983230072969 + 3 ^ 40 * 212409 * 2
def baseEnd_212409 : Nat := 4039552308924617870765

theorem tailTrace_212409 : CollatzResearch.WordTrace tailWord_212409 prefixEnd_212409 4039552308924617870765 := by
  unfold tailWord_212409
  simp only [CollatzResearch.WordTrace]
  refine ⟨7747192687485944414184281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5164795124990629609456187 7747192687485944414184281)
  ·
    refine ⟨5810394515614458310638211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7747192687485944414184281 5810394515614458310638211)
    ·
      refine ⟨8715591773421687465957317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810394515614458310638211 8715591773421687465957317)
      ·
        refine ⟨1634173457516566399866997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8715591773421687465957317 1634173457516566399866997)
        ·
          refine ⟨153203761642178099987531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1634173457516566399866997 153203761642178099987531)
          ·
            refine ⟨229805642463267149981297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153203761642178099987531 229805642463267149981297)
            ·
              refine ⟨172354231847450362485973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229805642463267149981297 172354231847450362485973)
              ·
                refine ⟨4039552308924617870765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172354231847450362485973 4039552308924617870765)
                ·
                  rfl

theorem cell23_212409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 7].length) (baseStart_212409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212409 prefixEnd_212409 := by exact prefixLift 212409
  have htrace : WordTrace (prefixWord ++ tailWord_212409) baseStart_212409 baseEnd_212409 := by
    simpa [prefixWord, tailWord_212409, baseEnd_212409] using wordTrace_append hprefix tailTrace_212409
  have hstable : (prefixWord ++ tailWord_212409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212409).length < 2 ^ (prefixWord ++ tailWord_212409).sum := by decide
  have hdescent : baseEnd_212409 < baseStart_212409 := by decide
  rcases family_descends (prefixWord ++ tailWord_212409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212420 : List Nat := [2, 3, 3, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_212420 : Nat := 118140960795 + 212420 * 2 ^ 59
def prefixEnd_212420 : Nat := 4983230072969 + 3 ^ 40 * 212420 * 2
def baseEnd_212420 : Nat := 109073560628164139473105

theorem tailTrace_212420 : CollatzResearch.WordTrace tailWord_212420 prefixEnd_212420 109073560628164139473105 := by
  unfold tailWord_212420
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873796945223046646417357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5165062593630728861889809 3873796945223046646417357)
  ·
    refine ⟨1452673854458642492406509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3873796945223046646417357 1452673854458642492406509)
    ·
      refine ⟨544752695421990934652441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1452673854458642492406509 544752695421990934652441)
      ·
        refine ⟨408564521566493200989331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544752695421990934652441 408564521566493200989331)
        ·
          refine ⟨612846782349739801483997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408564521566493200989331 612846782349739801483997)
          ·
            refine ⟨229817543381152425556499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612846782349739801483997 229817543381152425556499)
            ·
              refine ⟨344726315071728638334749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229817543381152425556499 344726315071728638334749)
              ·
                refine ⟨129272368151898239375531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344726315071728638334749 129272368151898239375531)
                ·
                  refine ⟨193908552227847359063297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129272368151898239375531 193908552227847359063297)
                  ·
                    refine ⟨145431414170885519297473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193908552227847359063297 145431414170885519297473)
                    ·
                      refine ⟨109073560628164139473105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145431414170885519297473 109073560628164139473105)
                      ·
                        rfl

theorem cell23_212420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_212420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212420 prefixEnd_212420 := by exact prefixLift 212420
  have htrace : WordTrace (prefixWord ++ tailWord_212420) baseStart_212420 baseEnd_212420 := by
    simpa [prefixWord, tailWord_212420, baseEnd_212420] using wordTrace_append hprefix tailTrace_212420
  have hstable : (prefixWord ++ tailWord_212420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212420).length < 2 ^ (prefixWord ++ tailWord_212420).sum := by decide
  have hdescent : baseEnd_212420 < baseStart_212420 := by decide
  rcases family_descends (prefixWord ++ tailWord_212420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212453 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 2, 1, 3]
def baseStart_212453 : Nat := 118140960795 + 212453 * 2 ^ 59
def prefixEnd_212453 : Nat := 4983230072969 + 3 ^ 40 * 212453 * 2
def baseEnd_212453 : Nat := 109090505489762510360453

theorem tailTrace_212453 : CollatzResearch.WordTrace tailWord_212453 prefixEnd_212453 109090505489762510360453 := by
  unfold tailWord_212453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748797499326539928786013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5165864999551026619190675 7748797499326539928786013)
  ·
    refine ⟨2905799062247452473294755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7748797499326539928786013 2905799062247452473294755)
    ·
      refine ⟨4358698593371178709942133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2905799062247452473294755 4358698593371178709942133)
      ·
        refine ⟨408627993128548004057075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4358698593371178709942133 408627993128548004057075)
        ·
          refine ⟨612941989692822006085613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408627993128548004057075 612941989692822006085613)
          ·
            refine ⟨229853246134808252282105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612941989692822006085613 229853246134808252282105)
            ·
              refine ⟨172389934601106189211579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229853246134808252282105 172389934601106189211579)
              ·
                refine ⟨258584901901659283817369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172389934601106189211579 258584901901659283817369)
                ·
                  refine ⟨193938676426244462863027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258584901901659283817369 193938676426244462863027)
                  ·
                    refine ⟨290908014639366694294541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193938676426244462863027 290908014639366694294541)
                    ·
                      refine ⟨109090505489762510360453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 290908014639366694294541 109090505489762510360453)
                      ·
                        rfl

theorem cell23_212453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_212453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212453 prefixEnd_212453 := by exact prefixLift 212453
  have htrace : WordTrace (prefixWord ++ tailWord_212453) baseStart_212453 baseEnd_212453 := by
    simpa [prefixWord, tailWord_212453, baseEnd_212453] using wordTrace_append hprefix tailTrace_212453
  have hstable : (prefixWord ++ tailWord_212453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212453).length < 2 ^ (prefixWord ++ tailWord_212453).sum := by decide
  have hdescent : baseEnd_212453 < baseStart_212453 := by decide
  rcases family_descends (prefixWord ++ tailWord_212453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212475 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 3]
def baseStart_212475 : Nat := 118140960795 + 212475 * 2 ^ 59
def prefixEnd_212475 : Nat := 4983230072969 + 3 ^ 40 * 212475 * 2
def baseEnd_212475 : Nat := 109101802064161424285351

theorem tailTrace_212475 : CollatzResearch.WordTrace tailWord_212475 prefixEnd_212475 109101802064161424285351 := by
  unfold tailWord_212475
  simp only [CollatzResearch.WordTrace]
  refine ⟨7749599905246837686086879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5166399936831225124057919 7749599905246837686086879)
  ·
    refine ⟨11624399857870256529130319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7749599905246837686086879 11624399857870256529130319)
    ·
      refine ⟨17436599786805384793695479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11624399857870256529130319 17436599786805384793695479)
      ·
        refine ⟨26154899680208077190543219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17436599786805384793695479 26154899680208077190543219)
        ·
          refine ⟨39232349520312115785814829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26154899680208077190543219 39232349520312115785814829)
          ·
            refine ⟨14712131070117043419680561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39232349520312115785814829 14712131070117043419680561)
            ·
              refine ⟨11034098302587782564760421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14712131070117043419680561 11034098302587782564760421)
              ·
                refine ⟨2068893431735209230892579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11034098302587782564760421 2068893431735209230892579)
                ·
                  refine ⟨3103340147602813846338869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068893431735209230892579 3103340147602813846338869)
                  ·
                    refine ⟨290938138837763798094269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3103340147602813846338869 290938138837763798094269)
                    ·
                      refine ⟨109101802064161424285351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 290938138837763798094269 109101802064161424285351)
                      ·
                        rfl

theorem cell23_212475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 3].length) (baseStart_212475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212475 prefixEnd_212475 := by exact prefixLift 212475
  have htrace : WordTrace (prefixWord ++ tailWord_212475) baseStart_212475 baseEnd_212475 := by
    simpa [prefixWord, tailWord_212475, baseEnd_212475] using wordTrace_append hprefix tailTrace_212475
  have hstable : (prefixWord ++ tailWord_212475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212475).length < 2 ^ (prefixWord ++ tailWord_212475).sum := by decide
  have hdescent : baseEnd_212475 < baseStart_212475 := by decide
  rcases family_descends (prefixWord ++ tailWord_212475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212499 : List Nat := [1, 1, 1, 2, 1, 6, 4, 2, 5]
def baseStart_212499 : Nat := 118140960795 + 212499 * 2 ^ 59
def prefixEnd_212499 : Nat := 4983230072969 + 3 ^ 40 * 212499 * 2
def baseEnd_212499 : Nat := 12123791733318814487249

theorem tailTrace_212499 : CollatzResearch.WordTrace tailWord_212499 prefixEnd_212499 12123791733318814487249 := by
  unfold tailWord_212499
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750475257159889784960551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5166983504773259856640367 7750475257159889784960551)
  ·
    refine ⟨11625712885739834677440827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7750475257159889784960551 11625712885739834677440827)
    ·
      refine ⟨17438569328609752016161241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11625712885739834677440827 17438569328609752016161241)
      ·
        refine ⟨13078926996457314012120931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17438569328609752016161241 13078926996457314012120931)
        ·
          refine ⟨19618390494685971018181397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13078926996457314012120931 19618390494685971018181397)
          ·
            refine ⟨919612054438404891477253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19618390494685971018181397 919612054438404891477253)
            ·
              refine ⟨172427260207200917151985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 919612054438404891477253 172427260207200917151985)
              ·
                refine ⟨129320445155400687863989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172427260207200917151985 129320445155400687863989)
                ·
                  refine ⟨12123791733318814487249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129320445155400687863989 12123791733318814487249)
                  ·
                    rfl

theorem cell23_212499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 5].length) (baseStart_212499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212499 prefixEnd_212499 := by exact prefixLift 212499
  have htrace : WordTrace (prefixWord ++ tailWord_212499) baseStart_212499 baseEnd_212499 := by
    simpa [prefixWord, tailWord_212499, baseEnd_212499] using wordTrace_append hprefix tailTrace_212499
  have hstable : (prefixWord ++ tailWord_212499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212499).length < 2 ^ (prefixWord ++ tailWord_212499).sum := by decide
  have hdescent : baseEnd_212499 < baseStart_212499 := by decide
  rcases family_descends (prefixWord ++ tailWord_212499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212595 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7]
def baseStart_212595 : Nat := 118140960795 + 212595 * 2 ^ 59
def prefixEnd_212595 : Nat := 4983230072969 + 3 ^ 40 * 212595 * 2
def baseEnd_212595 : Nat := 109163419742700954784799

theorem tailTrace_212595 : CollatzResearch.WordTrace tailWord_212595 prefixEnd_212595 109163419742700954784799 := by
  unfold tailWord_212595
  simp only [CollatzResearch.WordTrace]
  refine ⟨7753976664812098180455239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5169317776541398786970159 7753976664812098180455239)
  ·
    refine ⟨11630964997218147270682859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7753976664812098180455239 11630964997218147270682859)
    ·
      refine ⟨17446447495827220906024289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11630964997218147270682859 17446447495827220906024289)
      ·
        refine ⟨13084835621870415679518217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17446447495827220906024289 13084835621870415679518217)
        ·
          refine ⟨9813626716402811759638663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13084835621870415679518217 9813626716402811759638663)
          ·
            refine ⟨14720440074604217639457995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813626716402811759638663 14720440074604217639457995)
            ·
              refine ⟨22080660111906326459186993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14720440074604217639457995 22080660111906326459186993)
              ·
                refine ⟨16560495083929744844390245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22080660111906326459186993 16560495083929744844390245)
                ·
                  refine ⟨3105092828236827158323171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16560495083929744844390245 3105092828236827158323171)
                  ·
                    refine ⟨4657639242355240737484757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105092828236827158323171 4657639242355240737484757)
                    ·
                      refine ⟨109163419742700954784799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4657639242355240737484757 109163419742700954784799)
                      ·
                        rfl

theorem cell23_212595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_212595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212595 prefixEnd_212595 := by exact prefixLift 212595
  have htrace : WordTrace (prefixWord ++ tailWord_212595) baseStart_212595 baseEnd_212595 := by
    simpa [prefixWord, tailWord_212595, baseEnd_212595] using wordTrace_append hprefix tailTrace_212595
  have hstable : (prefixWord ++ tailWord_212595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212595).length < 2 ^ (prefixWord ++ tailWord_212595).sum := by decide
  have hdescent : baseEnd_212595 < baseStart_212595 := by decide
  rcases family_descends (prefixWord ++ tailWord_212595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212666 : List Nat := [3, 1, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_212666 : Nat := 118140960795 + 212666 * 2 ^ 59
def prefixEnd_212666 : Nat := 4983230072969 + 3 ^ 40 * 212666 * 2
def baseEnd_212666 : Nat := 36399958956390058998991

theorem tailTrace_212666 : CollatzResearch.WordTrace tailWord_212666 prefixEnd_212666 36399958956390058998991 := by
  unfold tailWord_212666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939141561888719326572463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5171044165036584870859901 1939141561888719326572463)
  ·
    refine ⟨2908712342833078989858695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1939141561888719326572463 2908712342833078989858695)
    ·
      refine ⟨4363068514249618484788043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908712342833078989858695 4363068514249618484788043)
      ·
        refine ⟨6544602771374427727182065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363068514249618484788043 6544602771374427727182065)
        ·
          refine ⟨4908452078530820795386549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6544602771374427727182065 4908452078530820795386549)
          ·
            refine ⟨460167382362264449567489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4908452078530820795386549 460167382362264449567489)
            ·
              refine ⟨345125536771698337175617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460167382362264449567489 345125536771698337175617)
              ·
                refine ⟨258844152578773752881713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345125536771698337175617 258844152578773752881713)
                ·
                  refine ⟨194133114434080314661285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258844152578773752881713 194133114434080314661285)
                  ·
                    refine ⟨36399958956390058998991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194133114434080314661285 36399958956390058998991)
                    ·
                      rfl

theorem cell23_212666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_212666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212666 prefixEnd_212666 := by exact prefixLift 212666
  have htrace : WordTrace (prefixWord ++ tailWord_212666) baseStart_212666 baseEnd_212666 := by
    simpa [prefixWord, tailWord_212666, baseEnd_212666] using wordTrace_append hprefix tailTrace_212666
  have hstable : (prefixWord ++ tailWord_212666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212666).length < 2 ^ (prefixWord ++ tailWord_212666).sum := by decide
  have hdescent : baseEnd_212666 < baseStart_212666 := by decide
  rcases family_descends (prefixWord ++ tailWord_212666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212689 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_212689 : Nat := 118140960795 + 212689 * 2 ^ 59
def prefixEnd_212689 : Nat := 4983230072969 + 3 ^ 40 * 212689 * 2
def baseEnd_212689 : Nat := 109211686924223587009367

theorem tailTrace_212689 : CollatzResearch.WordTrace tailWord_212689 prefixEnd_212689 109211686924223587009367 := by
  unfold tailWord_212689
  simp only [CollatzResearch.WordTrace]
  refine ⟨7757405126471552234377121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5171603417647701489584747 7757405126471552234377121)
  ·
    refine ⟨5818053844853664175782841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7757405126471552234377121 5818053844853664175782841)
    ·
      refine ⟨4363540383640248131837131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5818053844853664175782841 4363540383640248131837131)
      ·
        refine ⟨6545310575460372197755697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363540383640248131837131 6545310575460372197755697)
        ·
          refine ⟨4908982931595279148316773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6545310575460372197755697 4908982931595279148316773)
          ·
            refine ⟨920434299674114840309395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4908982931595279148316773 920434299674114840309395)
            ·
              refine ⟨1380651449511172260464093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920434299674114840309395 1380651449511172260464093)
              ·
                refine ⟨517744293566689597674035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1380651449511172260464093 517744293566689597674035)
                ·
                  refine ⟨776616440350034396511053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 517744293566689597674035 776616440350034396511053)
                  ·
                    refine ⟨291231165131262898691645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 776616440350034396511053 291231165131262898691645)
                    ·
                      refine ⟨109211686924223587009367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 291231165131262898691645 109211686924223587009367)
                      ·
                        rfl

theorem cell23_212689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_212689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212689 prefixEnd_212689 := by exact prefixLift 212689
  have htrace : WordTrace (prefixWord ++ tailWord_212689) baseStart_212689 baseEnd_212689 := by
    simpa [prefixWord, tailWord_212689, baseEnd_212689] using wordTrace_append hprefix tailTrace_212689
  have hstable : (prefixWord ++ tailWord_212689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212689).length < 2 ^ (prefixWord ++ tailWord_212689).sum := by decide
  have hdescent : baseEnd_212689 < baseStart_212689 := by decide
  rcases family_descends (prefixWord ++ tailWord_212689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212694 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_212694 : Nat := 118140960795 + 212694 * 2 ^ 59
def prefixEnd_212694 : Nat := 4983230072969 + 3 ^ 40 * 212694 * 2
def baseEnd_212694 : Nat := 109214254327496067446845

theorem tailTrace_212694 : CollatzResearch.WordTrace tailWord_212694 prefixEnd_212694 109214254327496067446845 := by
  unfold tailWord_212694
  simp only [CollatzResearch.WordTrace]
  refine ⟨484849218215839880519321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5171724994302292058872757 484849218215839880519321)
  ·
    refine ⟨363636913661879910389491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 484849218215839880519321 363636913661879910389491)
    ·
      refine ⟨545455370492819865584237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363636913661879910389491 545455370492819865584237)
      ·
        refine ⟨204545763934807449594089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545455370492819865584237 204545763934807449594089)
        ·
          refine ⟨153409322951105587195567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204545763934807449594089 153409322951105587195567)
          ·
            refine ⟨230113984426658380793351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153409322951105587195567 230113984426658380793351)
            ·
              refine ⟨345170976639987571190027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230113984426658380793351 345170976639987571190027)
              ·
                refine ⟨517756464959981356785041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345170976639987571190027 517756464959981356785041)
                ·
                  refine ⟨388317348719986017588781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517756464959981356785041 388317348719986017588781)
                  ·
                    refine ⟨145619005769994756595793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388317348719986017588781 145619005769994756595793)
                    ·
                      refine ⟨109214254327496067446845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145619005769994756595793 109214254327496067446845)
                      ·
                        rfl

theorem cell23_212694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_212694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212694 prefixEnd_212694 := by exact prefixLift 212694
  have htrace : WordTrace (prefixWord ++ tailWord_212694) baseStart_212694 baseEnd_212694 := by
    simpa [prefixWord, tailWord_212694, baseEnd_212694] using wordTrace_append hprefix tailTrace_212694
  have hstable : (prefixWord ++ tailWord_212694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212694).length < 2 ^ (prefixWord ++ tailWord_212694).sum := by decide
  have hdescent : baseEnd_212694 < baseStart_212694 := by decide
  rcases family_descends (prefixWord ++ tailWord_212694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212707 : List Nat := [1, 1, 1, 7, 2, 1, 2, 3, 1, 2, 2]
def baseStart_212707 : Nat := 118140960795 + 212707 * 2 ^ 59
def prefixEnd_212707 : Nat := 4983230072969 + 3 ^ 40 * 212707 * 2
def baseEnd_212707 : Nat := 109220929576004516584285

theorem tailTrace_212707 : CollatzResearch.WordTrace tailWord_212707 prefixEnd_212707 109220929576004516584285 := by
  unfold tailWord_212707
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758061640406341308532375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5172041093604227539021583 7758061640406341308532375)
  ·
    refine ⟨11637092460609511962798563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7758061640406341308532375 11637092460609511962798563)
    ·
      refine ⟨17455638690914267944197845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11637092460609511962798563 17455638690914267944197845)
      ·
        refine ⟨409116531818303154942137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 17455638690914267944197845 409116531818303154942137)
        ·
          refine ⟨306837398863727366206603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409116531818303154942137 306837398863727366206603)
          ·
            refine ⟨460256098295591049309905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306837398863727366206603 460256098295591049309905)
            ·
              refine ⟨345192073721693286982429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460256098295591049309905 345192073721693286982429)
              ·
                refine ⟨129447027645634982618411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345192073721693286982429 129447027645634982618411)
                ·
                  refine ⟨194170541468452473927617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129447027645634982618411 194170541468452473927617)
                  ·
                    refine ⟨145627906101339355445713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194170541468452473927617 145627906101339355445713)
                    ·
                      refine ⟨109220929576004516584285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145627906101339355445713 109220929576004516584285)
                      ·
                        rfl

theorem cell23_212707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_212707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212707 prefixEnd_212707 := by exact prefixLift 212707
  have htrace : WordTrace (prefixWord ++ tailWord_212707) baseStart_212707 baseEnd_212707 := by
    simpa [prefixWord, tailWord_212707, baseEnd_212707] using wordTrace_append hprefix tailTrace_212707
  have hstable : (prefixWord ++ tailWord_212707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212707).length < 2 ^ (prefixWord ++ tailWord_212707).sum := by decide
  have hdescent : baseEnd_212707 < baseStart_212707 := by decide
  rcases family_descends (prefixWord ++ tailWord_212707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212724 : List Nat := [2, 6, 1, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_212724 : Nat := 118140960795 + 212724 * 2 ^ 59
def prefixEnd_212724 : Nat := 4983230072969 + 3 ^ 40 * 212724 * 2
def baseEnd_212724 : Nat := 109229658747130950071707

theorem tailTrace_212724 : CollatzResearch.WordTrace tailWord_212724 prefixEnd_212724 109229658747130950071707 := by
  unfold tailWord_212724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879340840672376605950613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5172454454229835474600817 3879340840672376605950613)
  ·
    refine ⟨181844101906517653403935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3879340840672376605950613 181844101906517653403935)
    ·
      refine ⟨272766152859776480105903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181844101906517653403935 272766152859776480105903)
      ·
        refine ⟨409149229289664720158855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272766152859776480105903 409149229289664720158855)
        ·
          refine ⟨613723843934497080238283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409149229289664720158855 613723843934497080238283)
          ·
            refine ⟨920585765901745620357425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613723843934497080238283 920585765901745620357425)
            ·
              refine ⟨690439324426309215268069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920585765901745620357425 690439324426309215268069)
              ·
                refine ⟨129457373329932977862763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690439324426309215268069 129457373329932977862763)
                ·
                  refine ⟨194186059994899466794145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129457373329932977862763 194186059994899466794145)
                  ·
                    refine ⟨145639544996174600095609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194186059994899466794145 145639544996174600095609)
                    ·
                      refine ⟨109229658747130950071707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145639544996174600095609 109229658747130950071707)
                      ·
                        rfl

theorem cell23_212724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_212724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212724 prefixEnd_212724 := by exact prefixLift 212724
  have htrace : WordTrace (prefixWord ++ tailWord_212724) baseStart_212724 baseEnd_212724 := by
    simpa [prefixWord, tailWord_212724, baseEnd_212724] using wordTrace_append hprefix tailTrace_212724
  have hstable : (prefixWord ++ tailWord_212724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212724).length < 2 ^ (prefixWord ++ tailWord_212724).sum := by decide
  have hdescent : baseEnd_212724 < baseStart_212724 := by decide
  rcases family_descends (prefixWord ++ tailWord_212724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212729 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 8, 2]
def baseStart_212729 : Nat := 118140960795 + 212729 * 2 ^ 59
def prefixEnd_212729 : Nat := 4983230072969 + 3 ^ 40 * 212729 * 2
def baseEnd_212729 : Nat := 109232226150403430509183

theorem tailTrace_212729 : CollatzResearch.WordTrace tailWord_212729 prefixEnd_212729 109232226150403430509183 := by
  unfold tailWord_212729
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758864046326639065833241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5172576030884426043888827 7758864046326639065833241)
  ·
    refine ⟨5819148034744979299374931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7758864046326639065833241 5819148034744979299374931)
    ·
      refine ⟨8728722052117468949062397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5819148034744979299374931 8728722052117468949062397)
      ·
        refine ⟨3273270769544050855898399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8728722052117468949062397 3273270769544050855898399)
        ·
          refine ⟨4909906154316076283847599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273270769544050855898399 4909906154316076283847599)
          ·
            refine ⟨7364859231474114425771399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4909906154316076283847599 7364859231474114425771399)
            ·
              refine ⟨11047288847211171638657099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7364859231474114425771399 11047288847211171638657099)
              ·
                refine ⟨16570933270816757457985649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11047288847211171638657099 16570933270816757457985649)
                ·
                  refine ⟨12428199953112568093489237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16570933270816757457985649 12428199953112568093489237)
                  ·
                    refine ⟨145642968200537907345577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12428199953112568093489237 145642968200537907345577)
                    ·
                      refine ⟨109232226150403430509183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145642968200537907345577 109232226150403430509183)
                      ·
                        rfl

theorem cell23_212729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_212729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212729 prefixEnd_212729 := by exact prefixLift 212729
  have htrace : WordTrace (prefixWord ++ tailWord_212729) baseStart_212729 baseEnd_212729 := by
    simpa [prefixWord, tailWord_212729, baseEnd_212729] using wordTrace_append hprefix tailTrace_212729
  have hstable : (prefixWord ++ tailWord_212729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212729).length < 2 ^ (prefixWord ++ tailWord_212729).sum := by decide
  have hdescent : baseEnd_212729 < baseStart_212729 := by decide
  rcases family_descends (prefixWord ++ tailWord_212729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212740 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_212740 : Nat := 118140960795 + 212740 * 2 ^ 59
def prefixEnd_212740 : Nat := 4983230072969 + 3 ^ 40 * 212740 * 2
def baseEnd_212740 : Nat := 109237874437602887471633

theorem tailTrace_212740 : CollatzResearch.WordTrace tailWord_212740 prefixEnd_212740 109237874437602887471633 := by
  unfold tailWord_212740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879632624643393972241837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5172843499524525296322449 3879632624643393972241837)
  ·
    refine ⟨1454862234241272739590689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3879632624643393972241837 1454862234241272739590689)
    ·
      refine ⟨1091146675680954554693017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454862234241272739590689 1091146675680954554693017)
      ·
        refine ⟨818360006760715916019763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1091146675680954554693017 818360006760715916019763)
        ·
          refine ⟨1227540010141073874029645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818360006760715916019763 1227540010141073874029645)
          ·
            refine ⟨460327503802902702761117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1227540010141073874029645 460327503802902702761117)
            ·
              refine ⟨172622813926088513535419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460327503802902702761117 172622813926088513535419)
              ·
                refine ⟨258934220889132770303129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172622813926088513535419 258934220889132770303129)
                ·
                  refine ⟨194200665666849577727347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258934220889132770303129 194200665666849577727347)
                  ·
                    refine ⟨291300998500274366591021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194200665666849577727347 291300998500274366591021)
                    ·
                      refine ⟨109237874437602887471633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 291300998500274366591021 109237874437602887471633)
                      ·
                        rfl

theorem cell23_212740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_212740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212740 prefixEnd_212740 := by exact prefixLift 212740
  have htrace : WordTrace (prefixWord ++ tailWord_212740) baseStart_212740 baseEnd_212740 := by
    simpa [prefixWord, tailWord_212740, baseEnd_212740] using wordTrace_append hprefix tailTrace_212740
  have hstable : (prefixWord ++ tailWord_212740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212740).length < 2 ^ (prefixWord ++ tailWord_212740).sum := by decide
  have hdescent : baseEnd_212740 < baseStart_212740 := by decide
  rcases family_descends (prefixWord ++ tailWord_212740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212786 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 7]
def baseStart_212786 : Nat := 118140960795 + 212786 * 2 ^ 59
def prefixEnd_212786 : Nat := 4983230072969 + 3 ^ 40 * 212786 * 2
def baseEnd_212786 : Nat := 12140166060856634166269

theorem tailTrace_212786 : CollatzResearch.WordTrace tailWord_212786 prefixEnd_212786 12140166060856634166269 := by
  unfold tailWord_212786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940235751780034450164553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5173962004746758533772141 1940235751780034450164553)
  ·
    refine ⟨1455176813835025837623415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1940235751780034450164553 1455176813835025837623415)
    ·
      refine ⟨2182765220752538756435123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455176813835025837623415 2182765220752538756435123)
      ·
        refine ⟨3274147831128808134652685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182765220752538756435123 3274147831128808134652685)
        ·
          refine ⟨1227805436673303050494757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3274147831128808134652685 1227805436673303050494757)
          ·
            refine ⟨230213519376244321967767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1227805436673303050494757 230213519376244321967767)
            ·
              refine ⟨345320279064366482951651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230213519376244321967767 345320279064366482951651)
              ·
                refine ⟨517980418596549724427477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345320279064366482951651 517980418596549724427477)
                ·
                  refine ⟨12140166060856634166269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 517980418596549724427477 12140166060856634166269)
                  ·
                    rfl

theorem cell23_212786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_212786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212786 prefixEnd_212786 := by exact prefixLift 212786
  have htrace : WordTrace (prefixWord ++ tailWord_212786) baseStart_212786 baseEnd_212786 := by
    simpa [prefixWord, tailWord_212786, baseEnd_212786] using wordTrace_append hprefix tailTrace_212786
  have hstable : (prefixWord ++ tailWord_212786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212786).length < 2 ^ (prefixWord ++ tailWord_212786).sum := by decide
  have hdescent : baseEnd_212786 < baseStart_212786 := by decide
  rcases family_descends (prefixWord ++ tailWord_212786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212797 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_212797 : Nat := 118140960795 + 212797 * 2 ^ 59
def prefixEnd_212797 : Nat := 4983230072969 + 3 ^ 40 * 212797 * 2
def baseEnd_212797 : Nat := 109267142834909164458871

theorem tailTrace_212797 : CollatzResearch.WordTrace tailWord_212797 prefixEnd_212797 109267142834909164458871 := by
  unfold tailWord_212797
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761344210080286679308645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5174229473386857786205763 7761344210080286679308645)
  ·
    refine ⟨1455252039390053752370371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7761344210080286679308645 1455252039390053752370371)
    ·
      refine ⟨2182878059085080628555557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1455252039390053752370371 2182878059085080628555557)
      ·
        refine ⟨409289636078452617854167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2182878059085080628555557 409289636078452617854167)
        ·
          refine ⟨613934454117678926781251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409289636078452617854167 613934454117678926781251)
          ·
            refine ⟨920901681176518390171877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613934454117678926781251 920901681176518390171877)
            ·
              refine ⟨172669065220597198157227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 920901681176518390171877 172669065220597198157227)
              ·
                refine ⟨259003597830895797235841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172669065220597198157227 259003597830895797235841)
                ·
                  refine ⟨194252698373171847926881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259003597830895797235841 194252698373171847926881)
                  ·
                    refine ⟨145689523779878885945161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194252698373171847926881 145689523779878885945161)
                    ·
                      refine ⟨109267142834909164458871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145689523779878885945161 109267142834909164458871)
                      ·
                        rfl

theorem cell23_212797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_212797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212797 prefixEnd_212797 := by exact prefixLift 212797
  have htrace : WordTrace (prefixWord ++ tailWord_212797) baseStart_212797 baseEnd_212797 := by
    simpa [prefixWord, tailWord_212797, baseEnd_212797] using wordTrace_append hprefix tailTrace_212797
  have hstable : (prefixWord ++ tailWord_212797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212797).length < 2 ^ (prefixWord ++ tailWord_212797).sum := by decide
  have hdescent : baseEnd_212797 < baseStart_212797 := by decide
  rcases family_descends (prefixWord ++ tailWord_212797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212839 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_212839 : Nat := 118140960795 + 212839 * 2 ^ 59
def prefixEnd_212839 : Nat := 4983230072969 + 3 ^ 40 * 212839 * 2
def baseEnd_212839 : Nat := 109288709022398000133677

theorem tailTrace_212839 : CollatzResearch.WordTrace tailWord_212839 prefixEnd_212839 109288709022398000133677 := by
  unfold tailWord_212839
  simp only [CollatzResearch.WordTrace]
  refine ⟨7762876075928127852337571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5175250717285418568225047 7762876075928127852337571)
  ·
    refine ⟨11644314113892191778506357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7762876075928127852337571 11644314113892191778506357)
    ·
      refine ⟨1091654448177392979234971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11644314113892191778506357 1091654448177392979234971)
      ·
        refine ⟨1637481672266089468852457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091654448177392979234971 1637481672266089468852457)
        ·
          refine ⟨1228111254199567101639343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1637481672266089468852457 1228111254199567101639343)
          ·
            refine ⟨1842166881299350652459015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228111254199567101639343 1842166881299350652459015)
            ·
              refine ⟨2763250321949025978688523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842166881299350652459015 2763250321949025978688523)
              ·
                refine ⟨4144875482923538968032785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763250321949025978688523 4144875482923538968032785)
                ·
                  refine ⟨3108656612192654226024589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4144875482923538968032785 3108656612192654226024589)
                  ·
                    refine ⟨1165746229572245334759221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3108656612192654226024589 1165746229572245334759221)
                    ·
                      refine ⟨109288709022398000133677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1165746229572245334759221 109288709022398000133677)
                      ·
                        rfl

theorem cell23_212839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_212839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212839 prefixEnd_212839 := by exact prefixLift 212839
  have htrace : WordTrace (prefixWord ++ tailWord_212839) baseStart_212839 baseEnd_212839 := by
    simpa [prefixWord, tailWord_212839, baseEnd_212839] using wordTrace_append hprefix tailTrace_212839
  have hstable : (prefixWord ++ tailWord_212839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212839).length < 2 ^ (prefixWord ++ tailWord_212839).sum := by decide
  have hdescent : baseEnd_212839 < baseStart_212839 := by decide
  rcases family_descends (prefixWord ++ tailWord_212839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212853 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_212853 : Nat := 118140960795 + 212853 * 2 ^ 59
def prefixEnd_212853 : Nat := 4983230072969 + 3 ^ 40 * 212853 * 2
def baseEnd_212853 : Nat := 109295897751560945358613

theorem tailTrace_212853 : CollatzResearch.WordTrace tailWord_212853 prefixEnd_212853 109295897751560945358613 := by
  unfold tailWord_212853
  simp only [CollatzResearch.WordTrace]
  refine ⟨7763386697877408243347213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5175591131918272162231475 7763386697877408243347213)
  ·
    refine ⟨2911270011704028091255205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7763386697877408243347213 2911270011704028091255205)
    ·
      refine ⟨545863127194505267110351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2911270011704028091255205 545863127194505267110351)
      ·
        refine ⟨818794690791757900665527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545863127194505267110351 818794690791757900665527)
        ·
          refine ⟨1228192036187636850998291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818794690791757900665527 1228192036187636850998291)
          ·
            refine ⟨1842288054281455276497437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228192036187636850998291 1842288054281455276497437)
            ·
              refine ⟨690858020355545728686539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1842288054281455276497437 690858020355545728686539)
              ·
                refine ⟨1036287030533318593029809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690858020355545728686539 1036287030533318593029809)
                ·
                  refine ⟨777215272899988944772357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1036287030533318593029809 777215272899988944772357)
                  ·
                    refine ⟨145727863668747927144817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777215272899988944772357 145727863668747927144817)
                    ·
                      refine ⟨109295897751560945358613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145727863668747927144817 109295897751560945358613)
                      ·
                        rfl

theorem cell23_212853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_212853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212853 prefixEnd_212853 := by exact prefixLift 212853
  have htrace : WordTrace (prefixWord ++ tailWord_212853) baseStart_212853 baseEnd_212853 := by
    simpa [prefixWord, tailWord_212853, baseEnd_212853] using wordTrace_append hprefix tailTrace_212853
  have hstable : (prefixWord ++ tailWord_212853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212853).length < 2 ^ (prefixWord ++ tailWord_212853).sum := by decide
  have hdescent : baseEnd_212853 < baseStart_212853 := by decide
  rcases family_descends (prefixWord ++ tailWord_212853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212893 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 6]
def baseStart_212893 : Nat := 118140960795 + 212893 * 2 ^ 59
def prefixEnd_212893 : Nat := 4983230072969 + 3 ^ 40 * 212893 * 2
def baseEnd_212893 : Nat := 12146270775304532095381

theorem tailTrace_212893 : CollatzResearch.WordTrace tailWord_212893 prefixEnd_212893 12146270775304532095381 := by
  unfold tailWord_212893
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764845617732495074803333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5176563745154996716535555 7764845617732495074803333)
  ·
    refine ⟨1455908553324842826525625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7764845617732495074803333 1455908553324842826525625)
    ·
      refine ⟨1091931414993632119894219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1455908553324842826525625 1091931414993632119894219)
      ·
        refine ⟨1637897122490448179841329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091931414993632119894219 1637897122490448179841329)
        ·
          refine ⟨1228422841867836134880997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1637897122490448179841329 1228422841867836134880997)
          ·
            refine ⟨230329282850219275290187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1228422841867836134880997 230329282850219275290187)
            ·
              refine ⟨345493924275328912935281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230329282850219275290187 345493924275328912935281)
              ·
                refine ⟨259120443206496684701461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345493924275328912935281 259120443206496684701461)
                ·
                  refine ⟨12146270775304532095381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 259120443206496684701461 12146270775304532095381)
                  ·
                    rfl

theorem cell23_212893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_212893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212893 prefixEnd_212893 := by exact prefixLift 212893
  have htrace : WordTrace (prefixWord ++ tailWord_212893) baseStart_212893 baseEnd_212893 := by
    simpa [prefixWord, tailWord_212893, baseEnd_212893] using wordTrace_append hprefix tailTrace_212893
  have hstable : (prefixWord ++ tailWord_212893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212893).length < 2 ^ (prefixWord ++ tailWord_212893).sum := by decide
  have hdescent : baseEnd_212893 < baseStart_212893 := by decide
  rcases family_descends (prefixWord ++ tailWord_212893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212913 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 1, 5, 2]
def baseStart_212913 : Nat := 118140960795 + 212913 * 2 ^ 59
def prefixEnd_212913 : Nat := 4983230072969 + 3 ^ 40 * 212913 * 2
def baseEnd_212913 : Nat := 109326706590830710608337

theorem tailTrace_212913 : CollatzResearch.WordTrace tailWord_212913 prefixEnd_212913 109326706590830710608337 := by
  unfold tailWord_212913
  simp only [CollatzResearch.WordTrace]
  refine ⟨7765575077660038490531393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5177050051773358993687595 7765575077660038490531393)
  ·
    refine ⟨5824181308245028867898545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7765575077660038490531393 5824181308245028867898545)
    ·
      refine ⟨4368135981183771650923909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5824181308245028867898545 4368135981183771650923909)
      ·
        refine ⟨819025496471957184548233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4368135981183771650923909 819025496471957184548233)
        ·
          refine ⟨614269122353967888411175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819025496471957184548233 614269122353967888411175)
          ·
            refine ⟨921403683530951832616763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614269122353967888411175 921403683530951832616763)
            ·
              refine ⟨1382105525296427748925145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921403683530951832616763 1382105525296427748925145)
              ·
                refine ⟨1036579143972320811693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382105525296427748925145 1036579143972320811693859)
                ·
                  refine ⟨1554868715958481217540789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036579143972320811693859 1554868715958481217540789)
                  ·
                    refine ⟨145768942121107614144449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1554868715958481217540789 145768942121107614144449)
                    ·
                      refine ⟨109326706590830710608337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145768942121107614144449 109326706590830710608337)
                      ·
                        rfl

theorem cell23_212913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_212913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212913 prefixEnd_212913 := by exact prefixLift 212913
  have htrace : WordTrace (prefixWord ++ tailWord_212913) baseStart_212913 baseEnd_212913 := by
    simpa [prefixWord, tailWord_212913, baseEnd_212913] using wordTrace_append hprefix tailTrace_212913
  have hstable : (prefixWord ++ tailWord_212913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212913).length < 2 ^ (prefixWord ++ tailWord_212913).sum := by decide
  have hdescent : baseEnd_212913 < baseStart_212913 := by decide
  rcases family_descends (prefixWord ++ tailWord_212913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212954 : List Nat := [3, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3]
def baseStart_212954 : Nat := 118140960795 + 212954 * 2 ^ 59
def prefixEnd_212954 : Nat := 4983230072969 + 3 ^ 40 * 212954 * 2
def baseEnd_212954 : Nat := 109347759297665050195649

theorem tailTrace_212954 : CollatzResearch.WordTrace tailWord_212954 prefixEnd_212954 109347759297665050195649 := by
  unfold tailWord_212954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941767617627875623193479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5178046980341001661849277 1941767617627875623193479)
  ·
    refine ⟨2912651426441813434790219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941767617627875623193479 2912651426441813434790219)
    ·
      refine ⟨4368977139662720152185329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912651426441813434790219 4368977139662720152185329)
      ·
        refine ⟨3276732854747040114138997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368977139662720152185329 3276732854747040114138997)
        ·
          refine ⟨307193705132535010700531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3276732854747040114138997 307193705132535010700531)
          ·
            refine ⟨460790557698802516050797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307193705132535010700531 460790557698802516050797)
            ·
              refine ⟨172796459137050943519049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460790557698802516050797 172796459137050943519049)
              ·
                refine ⟨129597344352788207639287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172796459137050943519049 129597344352788207639287)
                ·
                  refine ⟨194396016529182311458931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129597344352788207639287 194396016529182311458931)
                  ·
                    refine ⟨291594024793773467188397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194396016529182311458931 291594024793773467188397)
                    ·
                      refine ⟨109347759297665050195649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 291594024793773467188397 109347759297665050195649)
                      ·
                        rfl

theorem cell23_212954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_212954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212954 prefixEnd_212954 := by exact prefixLift 212954
  have htrace : WordTrace (prefixWord ++ tailWord_212954) baseStart_212954 baseEnd_212954 := by
    simpa [prefixWord, tailWord_212954, baseEnd_212954] using wordTrace_append hprefix tailTrace_212954
  have hstable : (prefixWord ++ tailWord_212954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212954).length < 2 ^ (prefixWord ++ tailWord_212954).sum := by decide
  have hdescent : baseEnd_212954 < baseStart_212954 := by decide
  rcases family_descends (prefixWord ++ tailWord_212954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212977 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 1, 1, 4]
def baseStart_212977 : Nat := 118140960795 + 212977 * 2 ^ 59
def prefixEnd_212977 : Nat := 4983230072969 + 3 ^ 40 * 212977 * 2
def baseEnd_212977 : Nat := 109359569352718460208043

theorem tailTrace_212977 : CollatzResearch.WordTrace tailWord_212977 prefixEnd_212977 109359569352718460208043 := by
  unfold tailWord_212977
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767909349428177420861185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5178606232952118280574123 7767909349428177420861185)
  ·
    refine ⟨5825932012071133065645889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7767909349428177420861185 5825932012071133065645889)
    ·
      refine ⟨4369449009053349799234417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5825932012071133065645889 4369449009053349799234417)
      ·
        refine ⟨3277086756790012349425813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4369449009053349799234417 3277086756790012349425813)
        ·
          refine ⟨153613441724531828879335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3277086756790012349425813 153613441724531828879335)
          ·
            refine ⟨230420162586797743319003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153613441724531828879335 230420162586797743319003)
            ·
              refine ⟨345630243880196614978505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230420162586797743319003 345630243880196614978505)
              ·
                refine ⟨259222682910147461233879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345630243880196614978505 259222682910147461233879)
                ·
                  refine ⟨388834024365221191850819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259222682910147461233879 388834024365221191850819)
                  ·
                    refine ⟨583251036547831787776229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 388834024365221191850819 583251036547831787776229)
                    ·
                      refine ⟨109359569352718460208043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 583251036547831787776229 109359569352718460208043)
                      ·
                        rfl

theorem cell23_212977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_212977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212977 prefixEnd_212977 := by exact prefixLift 212977
  have htrace : WordTrace (prefixWord ++ tailWord_212977) baseStart_212977 baseEnd_212977 := by
    simpa [prefixWord, tailWord_212977, baseEnd_212977] using wordTrace_append hprefix tailTrace_212977
  have hstable : (prefixWord ++ tailWord_212977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212977).length < 2 ^ (prefixWord ++ tailWord_212977).sum := by decide
  have hdescent : baseEnd_212977 < baseStart_212977 := by decide
  rcases family_descends (prefixWord ++ tailWord_212977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212990 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_212990 : Nat := 118140960795 + 212990 * 2 ^ 59
def prefixEnd_212990 : Nat := 4983230072969 + 3 ^ 40 * 212990 * 2
def baseEnd_212990 : Nat := 109366244601226909345483

theorem tailTrace_212990 : CollatzResearch.WordTrace tailWord_212990 prefixEnd_212990 109366244601226909345483 := by
  unfold tailWord_212990
  simp only [CollatzResearch.WordTrace]
  refine ⟨971047937297635080135553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5178922332254053760722949 971047937297635080135553)
  ·
    refine ⟨728285952973226310101665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 971047937297635080135553 728285952973226310101665)
    ·
      refine ⟨546214464729919732576249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 728285952973226310101665 546214464729919732576249)
      ·
        refine ⟨409660848547439799432187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546214464729919732576249 409660848547439799432187)
        ·
          refine ⟨614491272821159699148281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409660848547439799432187 614491272821159699148281)
          ·
            refine ⟨460868454615869774361211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614491272821159699148281 460868454615869774361211)
            ·
              refine ⟨691302681923804661541817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460868454615869774361211 691302681923804661541817)
              ·
                refine ⟨518477011442853496156363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691302681923804661541817 518477011442853496156363)
                ·
                  refine ⟨777715517164280244234545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518477011442853496156363 777715517164280244234545)
                  ·
                    refine ⟨583286637873210183175909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 777715517164280244234545 583286637873210183175909)
                    ·
                      refine ⟨109366244601226909345483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 583286637873210183175909 109366244601226909345483)
                      ·
                        rfl

theorem cell23_212990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_212990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212990 prefixEnd_212990 := by exact prefixLift 212990
  have htrace : WordTrace (prefixWord ++ tailWord_212990) baseStart_212990 baseEnd_212990 := by
    simpa [prefixWord, tailWord_212990, baseEnd_212990] using wordTrace_append hprefix tailTrace_212990
  have hstable : (prefixWord ++ tailWord_212990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212990).length < 2 ^ (prefixWord ++ tailWord_212990).sum := by decide
  have hdescent : baseEnd_212990 < baseStart_212990 := by decide
  rcases family_descends (prefixWord ++ tailWord_212990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212993 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_212993 : Nat := 118140960795 + 212993 * 2 ^ 59
def prefixEnd_212993 : Nat := 4983230072969 + 3 ^ 40 * 212993 * 2
def baseEnd_212993 : Nat := 109367785043190397607969

theorem tailTrace_212993 : CollatzResearch.WordTrace tailWord_212993 prefixEnd_212993 109367785043190397607969 := by
  unfold tailWord_212993
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768492917370212153443633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5178995278246808102295755 7768492917370212153443633)
  ·
    refine ⟨5826369688027659115082725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7768492917370212153443633 5826369688027659115082725)
    ·
      refine ⟨1092444316505186084078011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5826369688027659115082725 1092444316505186084078011)
      ·
        refine ⟨1638666474757779126117017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092444316505186084078011 1638666474757779126117017)
        ·
          refine ⟨1228999856068334344587763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638666474757779126117017 1228999856068334344587763)
          ·
            refine ⟨1843499784102501516881645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228999856068334344587763 1843499784102501516881645)
            ·
              refine ⟨691312419038438068830617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1843499784102501516881645 691312419038438068830617)
              ·
                refine ⟨518484314278828551622963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691312419038438068830617 518484314278828551622963)
                ·
                  refine ⟨777726471418242827434445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518484314278828551622963 777726471418242827434445)
                  ·
                    refine ⟨291647426781841060287917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 777726471418242827434445 291647426781841060287917)
                    ·
                      refine ⟨109367785043190397607969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 291647426781841060287917 109367785043190397607969)
                      ·
                        rfl

theorem cell23_212993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_212993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_212993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_212993 prefixEnd_212993 := by exact prefixLift 212993
  have htrace : WordTrace (prefixWord ++ tailWord_212993) baseStart_212993 baseEnd_212993 := by
    simpa [prefixWord, tailWord_212993, baseEnd_212993] using wordTrace_append hprefix tailTrace_212993
  have hstable : (prefixWord ++ tailWord_212993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212993).length < 2 ^ (prefixWord ++ tailWord_212993).sum := by decide
  have hdescent : baseEnd_212993 < baseStart_212993 := by decide
  rcases family_descends (prefixWord ++ tailWord_212993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213005 : List Nat := [1, 7, 1, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_213005 : Nat := 118140960795 + 213005 * 2 ^ 59
def prefixEnd_213005 : Nat := 4983230072969 + 3 ^ 40 * 213005 * 2
def baseEnd_213005 : Nat := 109373946811044350657915

theorem tailTrace_213005 : CollatzResearch.WordTrace tailWord_213005 prefixEnd_213005 109373946811044350657915 := by
  unfold tailWord_213005
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768930593326738202880469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5179287062217825468586979 7768930593326738202880469)
  ·
    refine ⟨182084310781095426630011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7768930593326738202880469 182084310781095426630011)
    ·
      refine ⟨273126466171643139945017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182084310781095426630011 273126466171643139945017)
      ·
        refine ⟨204844849628732354958763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273126466171643139945017 204844849628732354958763)
        ·
          refine ⟨307267274443098532438145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204844849628732354958763 307267274443098532438145)
          ·
            refine ⟨230450455832323899328609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307267274443098532438145 230450455832323899328609)
            ·
              refine ⟨172837841874242924496457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230450455832323899328609 172837841874242924496457)
              ·
                refine ⟨129628381405682193372343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172837841874242924496457 129628381405682193372343)
                ·
                  refine ⟨194442572108523290058515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129628381405682193372343 194442572108523290058515)
                  ·
                    refine ⟨291663858162784935087773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194442572108523290058515 291663858162784935087773)
                    ·
                      refine ⟨109373946811044350657915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 291663858162784935087773 109373946811044350657915)
                      ·
                        rfl

theorem cell23_213005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_213005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213005 prefixEnd_213005 := by exact prefixLift 213005
  have htrace : WordTrace (prefixWord ++ tailWord_213005) baseStart_213005 baseEnd_213005 := by
    simpa [prefixWord, tailWord_213005, baseEnd_213005] using wordTrace_append hprefix tailTrace_213005
  have hstable : (prefixWord ++ tailWord_213005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213005).length < 2 ^ (prefixWord ++ tailWord_213005).sum := by decide
  have hdescent : baseEnd_213005 < baseStart_213005 := by decide
  rcases family_descends (prefixWord ++ tailWord_213005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213016 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_213016 : Nat := 118140960795 + 213016 * 2 ^ 59
def prefixEnd_213016 : Nat := 4983230072969 + 3 ^ 40 * 213016 * 2
def baseEnd_213016 : Nat := 109379595098243807620363

theorem tailTrace_213016 : CollatzResearch.WordTrace tailWord_213016 prefixEnd_213016 109379595098243807620363 := by
  unfold tailWord_213016
  simp only [CollatzResearch.WordTrace]
  refine ⟨3884665898143443540765451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5179554530857924721020601 3884665898143443540765451)
  ·
    refine ⟨5826998847215165311148177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3884665898143443540765451 5826998847215165311148177)
    ·
      refine ⟨4370249135411373983361133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5826998847215165311148177 4370249135411373983361133)
      ·
        refine ⟨1638843425779265243760425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4370249135411373983361133 1638843425779265243760425)
        ·
          refine ⟨1229132569334448932820319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638843425779265243760425 1229132569334448932820319)
          ·
            refine ⟨1843698854001673399230479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229132569334448932820319 1843698854001673399230479)
            ·
              refine ⟨2765548281002510098845719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843698854001673399230479 2765548281002510098845719)
              ·
                refine ⟨4148322421503765148268579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765548281002510098845719 4148322421503765148268579)
                ·
                  refine ⟨6222483632255647722402869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148322421503765148268579 6222483632255647722402869)
                  ·
                    refine ⟨583357840523966973975269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6222483632255647722402869 583357840523966973975269)
                    ·
                      refine ⟨109379595098243807620363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 583357840523966973975269 109379595098243807620363)
                      ·
                        rfl

theorem cell23_213016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_213016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213016 prefixEnd_213016 := by exact prefixLift 213016
  have htrace : WordTrace (prefixWord ++ tailWord_213016) baseStart_213016 baseEnd_213016 := by
    simpa [prefixWord, tailWord_213016, baseEnd_213016] using wordTrace_append hprefix tailTrace_213016
  have hstable : (prefixWord ++ tailWord_213016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213016).length < 2 ^ (prefixWord ++ tailWord_213016).sum := by decide
  have hdescent : baseEnd_213016 < baseStart_213016 := by decide
  rcases family_descends (prefixWord ++ tailWord_213016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213020 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_213020 : Nat := 118140960795 + 213020 * 2 ^ 59
def prefixEnd_213020 : Nat := 4983230072969 + 3 ^ 40 * 213020 * 2
def baseEnd_213020 : Nat := 109381649020861791970345

theorem tailTrace_213020 : CollatzResearch.WordTrace tailWord_213020 prefixEnd_213020 109381649020861791970345 := by
  unfold tailWord_213020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3884738844136197882338257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5179651792181597176451009 3884738844136197882338257)
  ·
    refine ⟨2913554133102148411753693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3884738844136197882338257 2913554133102148411753693)
    ·
      refine ⟨1092582799913305654407635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2913554133102148411753693 1092582799913305654407635)
      ·
        refine ⟨1638874199869958481611453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092582799913305654407635 1638874199869958481611453)
        ·
          refine ⟨614577824951234430604295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1638874199869958481611453 614577824951234430604295)
          ·
            refine ⟨921866737426851645906443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614577824951234430604295 921866737426851645906443)
            ·
              refine ⟨1382800106140277468859665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921866737426851645906443 1382800106140277468859665)
              ·
                refine ⟨1037100079605208101644749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382800106140277468859665 1037100079605208101644749)
                ·
                  refine ⟨388912529851953038116781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037100079605208101644749 388912529851953038116781)
                  ·
                    refine ⟨145842198694482389293793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388912529851953038116781 145842198694482389293793)
                    ·
                      refine ⟨109381649020861791970345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145842198694482389293793 109381649020861791970345)
                      ·
                        rfl

theorem cell23_213020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_213020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213020 prefixEnd_213020 := by exact prefixLift 213020
  have htrace : WordTrace (prefixWord ++ tailWord_213020) baseStart_213020 baseEnd_213020 := by
    simpa [prefixWord, tailWord_213020, baseEnd_213020] using wordTrace_append hprefix tailTrace_213020
  have hstable : (prefixWord ++ tailWord_213020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213020).length < 2 ^ (prefixWord ++ tailWord_213020).sum := by decide
  have hdescent : baseEnd_213020 < baseStart_213020 := by decide
  rcases family_descends (prefixWord ++ tailWord_213020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213036 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_213036 : Nat := 118140960795 + 213036 * 2 ^ 59
def prefixEnd_213036 : Nat := 4983230072969 + 3 ^ 40 * 213036 * 2
def baseEnd_213036 : Nat := 109389864711333729370271

theorem tailTrace_213036 : CollatzResearch.WordTrace tailWord_213036 prefixEnd_213036 109389864711333729370271 := by
  unfold tailWord_213036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885030628107215248629481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5180040837476286998172641 3885030628107215248629481)
  ·
    refine ⟨2913772971080411436472111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3885030628107215248629481 2913772971080411436472111)
    ·
      refine ⟨4370659456620617154708167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2913772971080411436472111 4370659456620617154708167)
      ·
        refine ⟨6555989184930925732062251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370659456620617154708167 6555989184930925732062251)
        ·
          refine ⟨9833983777396388598093377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555989184930925732062251 9833983777396388598093377)
          ·
            refine ⟨7375487833047291448570033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9833983777396388598093377 7375487833047291448570033)
            ·
              refine ⟨5531615874785468586427525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7375487833047291448570033 5531615874785468586427525)
              ·
                refine ⟨1037177976522275359955161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5531615874785468586427525 1037177976522275359955161)
                ·
                  refine ⟨777883482391706519966371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037177976522275359955161 777883482391706519966371)
                  ·
                    refine ⟨1166825223587559779949557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 777883482391706519966371 1166825223587559779949557)
                    ·
                      refine ⟨109389864711333729370271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1166825223587559779949557 109389864711333729370271)
                      ·
                        rfl

theorem cell23_213036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_213036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213036 prefixEnd_213036 := by exact prefixLift 213036
  have htrace : WordTrace (prefixWord ++ tailWord_213036) baseStart_213036 baseEnd_213036 := by
    simpa [prefixWord, tailWord_213036, baseEnd_213036] using wordTrace_append hprefix tailTrace_213036
  have hstable : (prefixWord ++ tailWord_213036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213036).length < 2 ^ (prefixWord ++ tailWord_213036).sum := by decide
  have hdescent : baseEnd_213036 < baseStart_213036 := by decide
  rcases family_descends (prefixWord ++ tailWord_213036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213050 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2]
def baseStart_213050 : Nat := 118140960795 + 213050 * 2 ^ 59
def prefixEnd_213050 : Nat := 4983230072969 + 3 ^ 40 * 213050 * 2
def baseEnd_213050 : Nat := 109397053440496674595207

theorem tailTrace_213050 : CollatzResearch.WordTrace tailWord_213050 prefixEnd_213050 109397053440496674595207 := by
  unfold tailWord_213050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942642969540927722067151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5180381252109140592179069 1942642969540927722067151)
  ·
    refine ⟨2913964454311391583100727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1942642969540927722067151 2913964454311391583100727)
    ·
      refine ⟨4370946681467087374651091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2913964454311391583100727 4370946681467087374651091)
      ·
        refine ⟨6556420022200631061976637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370946681467087374651091 6556420022200631061976637)
        ·
          refine ⟨2458657508325236648241239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6556420022200631061976637 2458657508325236648241239)
          ·
            refine ⟨3687986262487854972361859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458657508325236648241239 3687986262487854972361859)
            ·
              refine ⟨5531979393731782458542789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687986262487854972361859 5531979393731782458542789)
              ·
                refine ⟨1037246136324709210976773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5531979393731782458542789 1037246136324709210976773)
                ·
                  refine ⟨194483650560882977058145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1037246136324709210976773 194483650560882977058145)
                  ·
                    refine ⟨145862737920662232793609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194483650560882977058145 145862737920662232793609)
                    ·
                      refine ⟨109397053440496674595207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145862737920662232793609 109397053440496674595207)
                      ·
                        rfl

theorem cell23_213050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_213050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213050 prefixEnd_213050 := by exact prefixLift 213050
  have htrace : WordTrace (prefixWord ++ tailWord_213050) baseStart_213050 baseEnd_213050 := by
    simpa [prefixWord, tailWord_213050, baseEnd_213050] using wordTrace_append hprefix tailTrace_213050
  have hstable : (prefixWord ++ tailWord_213050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213050).length < 2 ^ (prefixWord ++ tailWord_213050).sum := by decide
  have hdescent : baseEnd_213050 < baseStart_213050 := by decide
  rcases family_descends (prefixWord ++ tailWord_213050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213054 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_213054 : Nat := 118140960795 + 213054 * 2 ^ 59
def prefixEnd_213054 : Nat := 4983230072969 + 3 ^ 40 * 213054 * 2
def baseEnd_213054 : Nat := 109399107363114658945189

theorem tailTrace_213054 : CollatzResearch.WordTrace tailWord_213054 prefixEnd_213054 109399107363114658945189 := by
  unfold tailWord_213054
  simp only [CollatzResearch.WordTrace]
  refine ⟨971339721268652446426777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5180478513432813047609477 971339721268652446426777)
  ·
    refine ⟨728504790951489334820083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 971339721268652446426777 728504790951489334820083)
    ·
      refine ⟨1092757186427234002230125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728504790951489334820083 1092757186427234002230125)
      ·
        refine ⟨409783944910212750836297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1092757186427234002230125 409783944910212750836297)
        ·
          refine ⟨307337958682659563127223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409783944910212750836297 307337958682659563127223)
          ·
            refine ⟨461006938023989344690835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307337958682659563127223 461006938023989344690835)
            ·
              refine ⟨691510407035984017036253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461006938023989344690835 691510407035984017036253)
              ·
                refine ⟨259316402638494006388595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691510407035984017036253 259316402638494006388595)
                ·
                  refine ⟨388974603957741009582893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259316402638494006388595 388974603957741009582893)
                  ·
                    refine ⟨145865476484152878593585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388974603957741009582893 145865476484152878593585)
                    ·
                      refine ⟨109399107363114658945189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 145865476484152878593585 109399107363114658945189)
                      ·
                        rfl

theorem cell23_213054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_213054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213054 prefixEnd_213054 := by exact prefixLift 213054
  have htrace : WordTrace (prefixWord ++ tailWord_213054) baseStart_213054 baseEnd_213054 := by
    simpa [prefixWord, tailWord_213054, baseEnd_213054] using wordTrace_append hprefix tailTrace_213054
  have hstable : (prefixWord ++ tailWord_213054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213054).length < 2 ^ (prefixWord ++ tailWord_213054).sum := by decide
  have hdescent : baseEnd_213054 < baseStart_213054 := by decide
  rcases family_descends (prefixWord ++ tailWord_213054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213123 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 4]
def baseStart_213123 : Nat := 118140960795 + 213123 * 2 ^ 59
def prefixEnd_213123 : Nat := 4983230072969 + 3 ^ 40 * 213123 * 2
def baseEnd_213123 : Nat := 109434537528274888982371

theorem tailTrace_213123 : CollatzResearch.WordTrace tailWord_213123 prefixEnd_213123 109434537528274888982371 := by
  unfold tailWord_213123
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773234406899244355676023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5182156271266162903784015 7773234406899244355676023)
  ·
    refine ⟨11659851610348866533514035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7773234406899244355676023 11659851610348866533514035)
    ·
      refine ⟨17489777415523299800271053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659851610348866533514035 17489777415523299800271053)
      ·
        refine ⟨6558666530821237425101645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17489777415523299800271053 6558666530821237425101645)
        ·
          refine ⟨2459499949057964034413117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6558666530821237425101645 2459499949057964034413117)
          ·
            refine ⟨922312480896736512904919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2459499949057964034413117 922312480896736512904919)
            ·
              refine ⟨1383468721345104769357379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922312480896736512904919 1383468721345104769357379)
              ·
                refine ⟨2075203082017657154036069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383468721345104769357379 2075203082017657154036069)
                ·
                  refine ⟨389100577878310716381763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075203082017657154036069 389100577878310716381763)
                  ·
                    refine ⟨583650866817466074572645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 389100577878310716381763 583650866817466074572645)
                    ·
                      refine ⟨109434537528274888982371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 583650866817466074572645 109434537528274888982371)
                      ·
                        rfl

theorem cell23_213123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_213123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213123 prefixEnd_213123 := by exact prefixLift 213123
  have htrace : WordTrace (prefixWord ++ tailWord_213123) baseStart_213123 baseEnd_213123 := by
    simpa [prefixWord, tailWord_213123, baseEnd_213123] using wordTrace_append hprefix tailTrace_213123
  have hstable : (prefixWord ++ tailWord_213123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213123).length < 2 ^ (prefixWord ++ tailWord_213123).sum := by decide
  have hdescent : baseEnd_213123 < baseStart_213123 := by decide
  rcases family_descends (prefixWord ++ tailWord_213123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213184 : List Nat := [2, 1, 1, 2, 5, 1, 4, 2, 1, 4]
def baseStart_213184 : Nat := 118140960795 + 213184 * 2 ^ 59
def prefixEnd_213184 : Nat := 4983230072969 + 3 ^ 40 * 213184 * 2
def baseEnd_213184 : Nat := 36488619949399716773197

theorem tailTrace_213184 : CollatzResearch.WordTrace tailWord_213184 prefixEnd_213184 36488619949399716773197 := by
  unfold tailWord_213184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887729629839125886823303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5183639506452167849097737 3887729629839125886823303)
  ·
    refine ⟨5831594444758688830234955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3887729629839125886823303 5831594444758688830234955)
    ·
      refine ⟨8747391667138033245352433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5831594444758688830234955 8747391667138033245352433)
      ·
        refine ⟨6560543750353524934014325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8747391667138033245352433 6560543750353524934014325)
        ·
          refine ⟨615050976595642962563843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6560543750353524934014325 615050976595642962563843)
          ·
            refine ⟨922576464893464443845765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615050976595642962563843 922576464893464443845765)
            ·
              refine ⟨172983087167524583221081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 922576464893464443845765 172983087167524583221081)
              ·
                refine ⟨129737315375643437415811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172983087167524583221081 129737315375643437415811)
                ·
                  refine ⟨194605973063465156123717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129737315375643437415811 194605973063465156123717)
                  ·
                    refine ⟨36488619949399716773197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194605973063465156123717 36488619949399716773197)
                    ·
                      rfl

theorem cell23_213184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 2, 1, 4].length) (baseStart_213184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213184 prefixEnd_213184 := by exact prefixLift 213184
  have htrace : WordTrace (prefixWord ++ tailWord_213184) baseStart_213184 baseEnd_213184 := by
    simpa [prefixWord, tailWord_213184, baseEnd_213184] using wordTrace_append hprefix tailTrace_213184
  have hstable : (prefixWord ++ tailWord_213184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213184).length < 2 ^ (prefixWord ++ tailWord_213184).sum := by decide
  have hdescent : baseEnd_213184 < baseStart_213184 := by decide
  rcases family_descends (prefixWord ++ tailWord_213184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213224 : List Nat := [2, 1, 4, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_213224 : Nat := 118140960795 + 213224 * 2 ^ 59
def prefixEnd_213224 : Nat := 4983230072969 + 3 ^ 40 * 213224 * 2
def baseEnd_213224 : Nat := 109486399074378993819407

theorem tailTrace_213224 : CollatzResearch.WordTrace tailWord_213224 prefixEnd_213224 109486399074378993819407 := by
  unfold tailWord_213224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888459089766669302551363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5184612119688892403401817 3888459089766669302551363)
  ·
    refine ⟨5832688634650003953827045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3888459089766669302551363 5832688634650003953827045)
    ·
      refine ⟨1093629118996875741342571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5832688634650003953827045 1093629118996875741342571)
      ·
        refine ⟨1640443678495313612013857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093629118996875741342571 1640443678495313612013857)
        ·
          refine ⟨1230332758871485209010393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1640443678495313612013857 1230332758871485209010393)
          ·
            refine ⟨922749569153613906757795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1230332758871485209010393 922749569153613906757795)
            ·
              refine ⟨1384124353730420860136693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922749569153613906757795 1384124353730420860136693)
              ·
                refine ⟨129761658162226955637815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1384124353730420860136693 129761658162226955637815)
                ·
                  refine ⟨194642487243340433456723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129761658162226955637815 194642487243340433456723)
                  ·
                    refine ⟨291963730865010650185085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194642487243340433456723 291963730865010650185085)
                    ·
                      refine ⟨109486399074378993819407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 291963730865010650185085 109486399074378993819407)
                      ·
                        rfl

theorem cell23_213224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_213224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213224 prefixEnd_213224 := by exact prefixLift 213224
  have htrace : WordTrace (prefixWord ++ tailWord_213224) baseStart_213224 baseEnd_213224 := by
    simpa [prefixWord, tailWord_213224, baseEnd_213224] using wordTrace_append hprefix tailTrace_213224
  have hstable : (prefixWord ++ tailWord_213224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213224).length < 2 ^ (prefixWord ++ tailWord_213224).sum := by decide
  have hdescent : baseEnd_213224 < baseStart_213224 := by decide
  rcases family_descends (prefixWord ++ tailWord_213224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213281 : List Nat := [1, 2, 3, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_213281 : Nat := 118140960795 + 213281 * 2 ^ 59
def prefixEnd_213281 : Nat := 4983230072969 + 3 ^ 40 * 213281 * 2
def baseEnd_213281 : Nat := 109515667471685270806645

theorem tailTrace_213281 : CollatzResearch.WordTrace tailWord_213281 prefixEnd_213281 109515667471685270806645 := by
  unfold tailWord_213281
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778997140326837339927697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5185998093551224893285131 7778997140326837339927697)
  ·
    refine ⟨5834247855245128004945773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7778997140326837339927697 5834247855245128004945773)
    ·
      refine ⟨2187842945716923001854665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5834247855245128004945773 2187842945716923001854665)
      ·
        refine ⟨1640882209287692251390999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2187842945716923001854665 1640882209287692251390999)
        ·
          refine ⟨2461323313931538377086499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640882209287692251390999 2461323313931538377086499)
          ·
            refine ⟨3691984970897307565629749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461323313931538377086499 3691984970897307565629749)
            ·
              refine ⟨346123591021622584277789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3691984970897307565629749 346123591021622584277789)
              ·
                refine ⟨129796346633108469104171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346123591021622584277789 129796346633108469104171)
                ·
                  refine ⟨194694519949662703656257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129796346633108469104171 194694519949662703656257)
                  ·
                    refine ⟨146020889962247027742193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194694519949662703656257 146020889962247027742193)
                    ·
                      refine ⟨109515667471685270806645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146020889962247027742193 109515667471685270806645)
                      ·
                        rfl

theorem cell23_213281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_213281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213281 prefixEnd_213281 := by exact prefixLift 213281
  have htrace : WordTrace (prefixWord ++ tailWord_213281) baseStart_213281 baseEnd_213281 := by
    simpa [prefixWord, tailWord_213281, baseEnd_213281] using wordTrace_append hprefix tailTrace_213281
  have hstable : (prefixWord ++ tailWord_213281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213281).length < 2 ^ (prefixWord ++ tailWord_213281).sum := by decide
  have hdescent : baseEnd_213281 < baseStart_213281 := by decide
  rcases family_descends (prefixWord ++ tailWord_213281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213298 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_213298 : Nat := 118140960795 + 213298 * 2 ^ 59
def prefixEnd_213298 : Nat := 4983230072969 + 3 ^ 40 * 213298 * 2
def baseEnd_213298 : Nat := 109524396642811704294067

theorem tailTrace_213298 : CollatzResearch.WordTrace tailWord_213298 prefixEnd_213298 109524396642811704294067 := by
  unfold tailWord_213298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944904295316312310824137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5186411454176832828864365 1944904295316312310824137)
  ·
    refine ⟨1458678221487234233118103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1944904295316312310824137 1458678221487234233118103)
    ·
      refine ⟨2188017332230851349677155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458678221487234233118103 2188017332230851349677155)
      ·
        refine ⟨3282025998346277024515733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188017332230851349677155 3282025998346277024515733)
        ·
          refine ⟨153844968672481735524175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3282025998346277024515733 153844968672481735524175)
          ·
            refine ⟨230767453008722603286263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153844968672481735524175 230767453008722603286263)
            ·
              refine ⟨346151179513083904929395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230767453008722603286263 346151179513083904929395)
              ·
                refine ⟨519226769269625857394093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346151179513083904929395 519226769269625857394093)
                ·
                  refine ⟨194710038476109696522785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 519226769269625857394093 194710038476109696522785)
                  ·
                    refine ⟨146032528857082272392089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194710038476109696522785 146032528857082272392089)
                    ·
                      refine ⟨109524396642811704294067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146032528857082272392089 109524396642811704294067)
                      ·
                        rfl

theorem cell23_213298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_213298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213298 prefixEnd_213298 := by exact prefixLift 213298
  have htrace : WordTrace (prefixWord ++ tailWord_213298) baseStart_213298 baseEnd_213298 := by
    simpa [prefixWord, tailWord_213298, baseEnd_213298] using wordTrace_append hprefix tailTrace_213298
  have hstable : (prefixWord ++ tailWord_213298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213298).length < 2 ^ (prefixWord ++ tailWord_213298).sum := by decide
  have hdescent : baseEnd_213298 < baseStart_213298 := by decide
  rcases family_descends (prefixWord ++ tailWord_213298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213377 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 7]
def baseStart_213377 : Nat := 118140960795 + 213377 * 2 ^ 59
def prefixEnd_213377 : Nat := 4983230072969 + 3 ^ 40 * 213377 * 2
def baseEnd_213377 : Nat := 12173884623835210578467

theorem tailTrace_213377 : CollatzResearch.WordTrace tailWord_213377 prefixEnd_213377 12173884623835210578467 := by
  unfold tailWord_213377
  simp only [CollatzResearch.WordTrace]
  refine ⟨7782498547979045735422385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5188332365319363823614923 7782498547979045735422385)
  ·
    refine ⟨5836873910984284301566789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7782498547979045735422385 5836873910984284301566789)
    ·
      refine ⟨1094413858309553306543773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5836873910984284301566789 1094413858309553306543773)
      ·
        refine ⟨410405196866082489953915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1094413858309553306543773 410405196866082489953915)
        ·
          refine ⟨615607795299123734930873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410405196866082489953915 615607795299123734930873)
          ·
            refine ⟨461705846474342801198155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615607795299123734930873 461705846474342801198155)
            ·
              refine ⟨692558769711514201797233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461705846474342801198155 692558769711514201797233)
              ·
                refine ⟨519419077283635651347925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692558769711514201797233 519419077283635651347925)
                ·
                  refine ⟨12173884623835210578467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 519419077283635651347925 12173884623835210578467)
                  ·
                    rfl

theorem cell23_213377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 7].length) (baseStart_213377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213377 prefixEnd_213377 := by exact prefixLift 213377
  have htrace : WordTrace (prefixWord ++ tailWord_213377) baseStart_213377 baseEnd_213377 := by
    simpa [prefixWord, tailWord_213377, baseEnd_213377] using wordTrace_append hprefix tailTrace_213377
  have hstable : (prefixWord ++ tailWord_213377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213377).length < 2 ^ (prefixWord ++ tailWord_213377).sum := by decide
  have hdescent : baseEnd_213377 < baseStart_213377 := by decide
  rcases family_descends (prefixWord ++ tailWord_213377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213405 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_213405 : Nat := 118140960795 + 213405 * 2 ^ 59
def prefixEnd_213405 : Nat := 4983230072969 + 3 ^ 40 * 213405 * 2
def baseEnd_213405 : Nat := 109579339072842785656075

theorem tailTrace_213405 : CollatzResearch.WordTrace tailWord_213405 prefixEnd_213405 109579339072842785656075 := by
  unfold tailWord_213405
  simp only [CollatzResearch.WordTrace]
  refine ⟨7783519791877606517441669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5189013194585071011627779 7783519791877606517441669)
  ·
    refine ⟨1459409960977051222020313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7783519791877606517441669 1459409960977051222020313)
    ·
      refine ⟨1094557470732788416515235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1459409960977051222020313 1094557470732788416515235)
      ·
        refine ⟨1641836206099182624772853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094557470732788416515235 1641836206099182624772853)
        ·
          refine ⟨153922144321798371072455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1641836206099182624772853 153922144321798371072455)
          ·
            refine ⟨230883216482697556608683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153922144321798371072455 230883216482697556608683)
            ·
              refine ⟨346324824724046334913025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230883216482697556608683 346324824724046334913025)
              ·
                refine ⟨259743618543034751184769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346324824724046334913025 259743618543034751184769)
                ·
                  refine ⟨194807713907276063388577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259743618543034751184769 194807713907276063388577)
                  ·
                    refine ⟨146105785430457047541433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194807713907276063388577 146105785430457047541433)
                    ·
                      refine ⟨109579339072842785656075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146105785430457047541433 109579339072842785656075)
                      ·
                        rfl

theorem cell23_213405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_213405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213405 prefixEnd_213405 := by exact prefixLift 213405
  have htrace : WordTrace (prefixWord ++ tailWord_213405) baseStart_213405 baseEnd_213405 := by
    simpa [prefixWord, tailWord_213405, baseEnd_213405] using wordTrace_append hprefix tailTrace_213405
  have hstable : (prefixWord ++ tailWord_213405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213405).length < 2 ^ (prefixWord ++ tailWord_213405).sum := by decide
  have hdescent : baseEnd_213405 < baseStart_213405 := by decide
  rcases family_descends (prefixWord ++ tailWord_213405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213440 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_213440 : Nat := 118140960795 + 213440 * 2 ^ 59
def prefixEnd_213440 : Nat := 4983230072969 + 3 ^ 40 * 213440 * 2
def baseEnd_213440 : Nat := 109597310895750148718413

theorem tailTrace_213440 : CollatzResearch.WordTrace tailWord_213440 prefixEnd_213440 109597310895750148718413 := by
  unfold tailWord_213440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892398173375403747482887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5189864231167204996643849 3892398173375403747482887)
  ·
    refine ⟨5838597260063105621224331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3892398173375403747482887 5838597260063105621224331)
    ·
      refine ⟨8757895890094658431836497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5838597260063105621224331 8757895890094658431836497)
      ·
        refine ⟨6568421917570993823877373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8757895890094658431836497 6568421917570993823877373)
        ·
          refine ⟨2463158219089122683954015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6568421917570993823877373 2463158219089122683954015)
          ·
            refine ⟨3694737328633684025931023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463158219089122683954015 3694737328633684025931023)
            ·
              refine ⟨5542105992950526038896535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694737328633684025931023 5542105992950526038896535)
              ·
                refine ⟨8313158989425789058344803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542105992950526038896535 8313158989425789058344803)
                ·
                  refine ⟨12469738484138683587517205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313158989425789058344803 12469738484138683587517205)
                  ·
                    refine ⟨584518991444000793164869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12469738484138683587517205 584518991444000793164869)
                    ·
                      refine ⟨109597310895750148718413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 584518991444000793164869 109597310895750148718413)
                      ·
                        rfl

theorem cell23_213440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_213440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213440 prefixEnd_213440 := by exact prefixLift 213440
  have htrace : WordTrace (prefixWord ++ tailWord_213440) baseStart_213440 baseEnd_213440 := by
    simpa [prefixWord, tailWord_213440, baseEnd_213440] using wordTrace_append hprefix tailTrace_213440
  have hstable : (prefixWord ++ tailWord_213440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213440).length < 2 ^ (prefixWord ++ tailWord_213440).sum := by decide
  have hdescent : baseEnd_213440 < baseStart_213440 := by decide
  rcases family_descends (prefixWord ++ tailWord_213440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213447 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_213447 : Nat := 118140960795 + 213447 * 2 ^ 59
def prefixEnd_213447 : Nat := 4983230072969 + 3 ^ 40 * 213447 * 2
def baseEnd_213447 : Nat := 109600905260331621330881

theorem tailTrace_213447 : CollatzResearch.WordTrace tailWord_213447 prefixEnd_213447 109600905260331621330881 := by
  unfold tailWord_213447
  simp only [CollatzResearch.WordTrace]
  refine ⟨7785051657725447690470595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5190034438483631793647063 7785051657725447690470595)
  ·
    refine ⟨11677577486588171535705893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7785051657725447690470595 11677577486588171535705893)
    ·
      refine ⟨2189545778735282162944855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11677577486588171535705893 2189545778735282162944855)
      ·
        refine ⟨3284318668102923244417283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189545778735282162944855 3284318668102923244417283)
        ·
          refine ⟨4926478002154384866625925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284318668102923244417283 4926478002154384866625925)
          ·
            refine ⟨923714625403947162492361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4926478002154384866625925 923714625403947162492361)
            ·
              refine ⟨692785969052960371869271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923714625403947162492361 692785969052960371869271)
              ·
                refine ⟨1039178953579440557803907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692785969052960371869271 1039178953579440557803907)
                ·
                  refine ⟨1558768430369160836705861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039178953579440557803907 1558768430369160836705861)
                  ·
                    refine ⟨292269080694217656882349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1558768430369160836705861 292269080694217656882349)
                    ·
                      refine ⟨109600905260331621330881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 292269080694217656882349 109600905260331621330881)
                      ·
                        rfl

theorem cell23_213447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_213447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213447 prefixEnd_213447 := by exact prefixLift 213447
  have htrace : WordTrace (prefixWord ++ tailWord_213447) baseStart_213447 baseEnd_213447 := by
    simpa [prefixWord, tailWord_213447, baseEnd_213447] using wordTrace_append hprefix tailTrace_213447
  have hstable : (prefixWord ++ tailWord_213447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213447).length < 2 ^ (prefixWord ++ tailWord_213447).sum := by decide
  have hdescent : baseEnd_213447 < baseStart_213447 := by decide
  rcases family_descends (prefixWord ++ tailWord_213447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213450 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 10]
def baseStart_213450 : Nat := 118140960795 + 213450 * 2 ^ 59
def prefixEnd_213450 : Nat := 4983230072969 + 3 ^ 40 * 213450 * 2
def baseEnd_213450 : Nat := 12178049522477234399263

theorem tailTrace_213450 : CollatzResearch.WordTrace tailWord_213450 prefixEnd_213450 12178049522477234399263 := by
  unfold tailWord_213450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946290269178644800707451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5190107384476386135219869 1946290269178644800707451)
  ·
    refine ⟨2919435403767967201061177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1946290269178644800707451 2919435403767967201061177)
    ·
      refine ⟨2189576552825975400795883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2919435403767967201061177 2189576552825975400795883)
      ·
        refine ⟨3284364829238963101193825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189576552825975400795883 3284364829238963101193825)
        ·
          refine ⟨2463273621929222325895369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3284364829238963101193825 2463273621929222325895369)
          ·
            refine ⟨1847455216446916744421527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463273621929222325895369 1847455216446916744421527)
            ·
              refine ⟨2771182824670375116632291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847455216446916744421527 2771182824670375116632291)
              ·
                refine ⟨4156774237005562674948437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771182824670375116632291 4156774237005562674948437)
                ·
                  refine ⟨12178049522477234399263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 4156774237005562674948437 12178049522477234399263)
                  ·
                    rfl

theorem cell23_213450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_213450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213450 prefixEnd_213450 := by exact prefixLift 213450
  have htrace : WordTrace (prefixWord ++ tailWord_213450) baseStart_213450 baseEnd_213450 := by
    simpa [prefixWord, tailWord_213450, baseEnd_213450] using wordTrace_append hprefix tailTrace_213450
  have hstable : (prefixWord ++ tailWord_213450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213450).length < 2 ^ (prefixWord ++ tailWord_213450).sum := by decide
  have hdescent : baseEnd_213450 < baseStart_213450 := by decide
  rcases family_descends (prefixWord ++ tailWord_213450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213528 : List Nat := [2, 1, 2, 3, 3, 2, 1, 4, 1, 1, 3]
def baseStart_213528 : Nat := 118140960795 + 213528 * 2 ^ 59
def prefixEnd_213528 : Nat := 4983230072969 + 3 ^ 40 * 213528 * 2
def baseEnd_213528 : Nat := 109642497193345804418009

theorem tailTrace_213528 : CollatzResearch.WordTrace tailWord_213528 prefixEnd_213528 109642497193345804418009 := by
  unfold tailWord_213528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894002985215999262084619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5192003980287999016112825 3894002985215999262084619)
  ·
    refine ⟨5841004477823998893126929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894002985215999262084619 5841004477823998893126929)
    ·
      refine ⟨4380753358367999169845197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5841004477823998893126929 4380753358367999169845197)
      ·
        refine ⟨1642782509387999688691949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4380753358367999169845197 1642782509387999688691949)
        ·
          refine ⟨616043441020499883259481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1642782509387999688691949 616043441020499883259481)
          ·
            refine ⟨462032580765374912444611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616043441020499883259481 462032580765374912444611)
            ·
              refine ⟨693048871148062368666917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462032580765374912444611 693048871148062368666917)
              ·
                refine ⟨129946663340261694125047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693048871148062368666917 129946663340261694125047)
                ·
                  refine ⟨194919995010392541187571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129946663340261694125047 194919995010392541187571)
                  ·
                    refine ⟨292379992515588811781357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194919995010392541187571 292379992515588811781357)
                    ·
                      refine ⟨109642497193345804418009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 292379992515588811781357 109642497193345804418009)
                      ·
                        rfl

theorem cell23_213528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_213528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213528 prefixEnd_213528 := by exact prefixLift 213528
  have htrace : WordTrace (prefixWord ++ tailWord_213528) baseStart_213528 baseEnd_213528 := by
    simpa [prefixWord, tailWord_213528, baseEnd_213528] using wordTrace_append hprefix tailTrace_213528
  have hstable : (prefixWord ++ tailWord_213528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213528).length < 2 ^ (prefixWord ++ tailWord_213528).sum := by decide
  have hdescent : baseEnd_213528 < baseStart_213528 := by decide
  rcases family_descends (prefixWord ++ tailWord_213528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213537 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_213537 : Nat := 118140960795 + 213537 * 2 ^ 59
def prefixEnd_213537 : Nat := 4983230072969 + 3 ^ 40 * 213537 * 2
def baseEnd_213537 : Nat := 109647118519236269205467

theorem tailTrace_213537 : CollatzResearch.WordTrace tailWord_213537 prefixEnd_213537 109647118519236269205467 := by
  unfold tailWord_213537
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788334227399393061246865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5192222818266262040831243 7788334227399393061246865)
  ·
    refine ⟨5841250670549544795935149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7788334227399393061246865 5841250670549544795935149)
    ·
      refine ⟨2190469001456079298475681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5841250670549544795935149 2190469001456079298475681)
      ·
        refine ⟨1642851751092059473856761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2190469001456079298475681 1642851751092059473856761)
        ·
          refine ⟨1232138813319044605392571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642851751092059473856761 1232138813319044605392571)
          ·
            refine ⟨1848208219978566908088857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232138813319044605392571 1848208219978566908088857)
            ·
              refine ⟨1386156164983925181066643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848208219978566908088857 1386156164983925181066643)
              ·
                refine ⟨2079234247475887771599965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386156164983925181066643 2079234247475887771599965)
                ·
                  refine ⟨779712842803457914349987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2079234247475887771599965 779712842803457914349987)
                  ·
                    refine ⟨1169569264205186871524981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 779712842803457914349987 1169569264205186871524981)
                    ·
                      refine ⟨109647118519236269205467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1169569264205186871524981 109647118519236269205467)
                      ·
                        rfl

theorem cell23_213537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_213537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213537 prefixEnd_213537 := by exact prefixLift 213537
  have htrace : WordTrace (prefixWord ++ tailWord_213537) baseStart_213537 baseEnd_213537 := by
    simpa [prefixWord, tailWord_213537, baseEnd_213537] using wordTrace_append hprefix tailTrace_213537
  have hstable : (prefixWord ++ tailWord_213537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213537).length < 2 ^ (prefixWord ++ tailWord_213537).sum := by decide
  have hdescent : baseEnd_213537 < baseStart_213537 := by decide
  rcases family_descends (prefixWord ++ tailWord_213537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213544 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 1, 6]
def baseStart_213544 : Nat := 118140960795 + 213544 * 2 ^ 59
def prefixEnd_213544 : Nat := 4983230072969 + 3 ^ 40 * 213544 * 2
def baseEnd_213544 : Nat := 36550237627939247272645

theorem tailTrace_213544 : CollatzResearch.WordTrace tailWord_213544 prefixEnd_213544 36550237627939247272645 := by
  unfold tailWord_213544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894294769187016628375843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5192393025582688837834457 3894294769187016628375843)
  ·
    refine ⟨5841442153780524942563765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894294769187016628375843 5841442153780524942563765)
    ·
      refine ⟨547635201916924213365353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5841442153780524942563765 547635201916924213365353)
      ·
        refine ⟨410726401437693160024015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547635201916924213365353 410726401437693160024015)
        ·
          refine ⟨616089602156539740036023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410726401437693160024015 616089602156539740036023)
          ·
            refine ⟨924134403234809610054035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616089602156539740036023 924134403234809610054035)
            ·
              refine ⟨1386201604852214415081053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924134403234809610054035 1386201604852214415081053)
              ·
                refine ⟨519825601819580405655395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1386201604852214415081053 519825601819580405655395)
                ·
                  refine ⟨779738402729370608483093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519825601819580405655395 779738402729370608483093)
                  ·
                    refine ⟨36550237627939247272645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 779738402729370608483093 36550237627939247272645)
                    ·
                      rfl

theorem cell23_213544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_213544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213544 prefixEnd_213544 := by exact prefixLift 213544
  have htrace : WordTrace (prefixWord ++ tailWord_213544) baseStart_213544 baseEnd_213544 := by
    simpa [prefixWord, tailWord_213544, baseEnd_213544] using wordTrace_append hprefix tailTrace_213544
  have hstable : (prefixWord ++ tailWord_213544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213544).length < 2 ^ (prefixWord ++ tailWord_213544).sum := by decide
  have hdescent : baseEnd_213544 < baseStart_213544 := by decide
  rcases family_descends (prefixWord ++ tailWord_213544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213554 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_213554 : Nat := 118140960795 + 213554 * 2 ^ 59
def prefixEnd_213554 : Nat := 4983230072969 + 3 ^ 40 * 213554 * 2
def baseEnd_213554 : Nat := 109655847690362702692889

theorem tailTrace_213554 : CollatzResearch.WordTrace tailWord_213554 prefixEnd_213554 109655847690362702692889 := by
  unfold tailWord_213554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947238567084451241153929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5192636178891869976410477 1947238567084451241153929)
  ·
    refine ⟨1460428925313338430865447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1947238567084451241153929 1460428925313338430865447)
    ·
      refine ⟨2190643387970007646298171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460428925313338430865447 2190643387970007646298171)
      ·
        refine ⟨3285965081955011469447257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190643387970007646298171 3285965081955011469447257)
        ·
          refine ⟨2464473811466258602085443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3285965081955011469447257 2464473811466258602085443)
          ·
            refine ⟨3696710717199387903128165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464473811466258602085443 3696710717199387903128165)
            ·
              refine ⟨693133259474885231836531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3696710717199387903128165 693133259474885231836531)
              ·
                refine ⟨1039699889212327847754797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693133259474885231836531 1039699889212327847754797)
                ·
                  refine ⟨389887458454622942908049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039699889212327847754797 389887458454622942908049)
                  ·
                    refine ⟨292415593840967207181037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389887458454622942908049 292415593840967207181037)
                    ·
                      refine ⟨109655847690362702692889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 292415593840967207181037 109655847690362702692889)
                      ·
                        rfl

theorem cell23_213554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_213554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213554 prefixEnd_213554 := by exact prefixLift 213554
  have htrace : WordTrace (prefixWord ++ tailWord_213554) baseStart_213554 baseEnd_213554 := by
    simpa [prefixWord, tailWord_213554, baseEnd_213554] using wordTrace_append hprefix tailTrace_213554
  have hstable : (prefixWord ++ tailWord_213554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213554).length < 2 ^ (prefixWord ++ tailWord_213554).sum := by decide
  have hdescent : baseEnd_213554 < baseStart_213554 := by decide
  rcases family_descends (prefixWord ++ tailWord_213554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213564 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_213564 : Nat := 118140960795 + 213564 * 2 ^ 59
def prefixEnd_213564 : Nat := 4983230072969 + 3 ^ 40 * 213564 * 2
def baseEnd_213564 : Nat := 109660982496907663567843

theorem tailTrace_213564 : CollatzResearch.WordTrace tailWord_213564 prefixEnd_213564 109660982496907663567843 := by
  unfold tailWord_213564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894659499150788336239873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5192879332201051114986497 3894659499150788336239873)
  ·
    refine ⟨2920994624363091252179905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3894659499150788336239873 2920994624363091252179905)
    ·
      refine ⟨2190745968272318439134929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2920994624363091252179905 2190745968272318439134929)
      ·
        refine ⟨1643059476204238829351197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2190745968272318439134929 1643059476204238829351197)
        ·
          refine ⟨616147303576589561006699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1643059476204238829351197 616147303576589561006699)
          ·
            refine ⟨924220955364884341510049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616147303576589561006699 924220955364884341510049)
            ·
              refine ⟨693165716523663256132537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924220955364884341510049 693165716523663256132537)
              ·
                refine ⟨519874287392747442099403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693165716523663256132537 519874287392747442099403)
                ·
                  refine ⟨779811431089121163149105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519874287392747442099403 779811431089121163149105)
                  ·
                    refine ⟨584858573316840872361829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 779811431089121163149105 584858573316840872361829)
                    ·
                      refine ⟨109660982496907663567843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 584858573316840872361829 109660982496907663567843)
                      ·
                        rfl

theorem cell23_213564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_213564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213564 prefixEnd_213564 := by exact prefixLift 213564
  have htrace : WordTrace (prefixWord ++ tailWord_213564) baseStart_213564 baseEnd_213564 := by
    simpa [prefixWord, tailWord_213564, baseEnd_213564] using wordTrace_append hprefix tailTrace_213564
  have hstable : (prefixWord ++ tailWord_213564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213564).length < 2 ^ (prefixWord ++ tailWord_213564).sum := by decide
  have hdescent : baseEnd_213564 < baseStart_213564 := by decide
  rcases family_descends (prefixWord ++ tailWord_213564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213568 : List Nat := [2, 1, 1, 2, 2, 2, 3, 5, 1, 2, 2]
def baseStart_213568 : Nat := 118140960795 + 213568 * 2 ^ 59
def prefixEnd_213568 : Nat := 4983230072969 + 3 ^ 40 * 213568 * 2
def baseEnd_213568 : Nat := 109663036419525647917825

theorem tailTrace_213568 : CollatzResearch.WordTrace tailWord_213568 prefixEnd_213568 109663036419525647917825 := by
  unfold tailWord_213568
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894732445143542677812679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5192976593524723570416905 3894732445143542677812679)
  ·
    refine ⟨5842098667715314016719019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894732445143542677812679 5842098667715314016719019)
    ·
      refine ⟨8763148001572971025078529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5842098667715314016719019 8763148001572971025078529)
      ·
        refine ⟨6572361001179728268808897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8763148001572971025078529 6572361001179728268808897)
        ·
          refine ⟨4929270750884796201606673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6572361001179728268808897 4929270750884796201606673)
          ·
            refine ⟨3696953063163597151205005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4929270750884796201606673 3696953063163597151205005)
            ·
              refine ⟨1386357398686348931701877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3696953063163597151205005 1386357398686348931701877)
              ·
                refine ⟨129971006126845212347051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1386357398686348931701877 129971006126845212347051)
                ·
                  refine ⟨194956509190267818520577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129971006126845212347051 194956509190267818520577)
                  ·
                    refine ⟨146217381892700863890433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194956509190267818520577 146217381892700863890433)
                    ·
                      refine ⟨109663036419525647917825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146217381892700863890433 109663036419525647917825)
                      ·
                        rfl

theorem cell23_213568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_213568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213568 prefixEnd_213568 := by exact prefixLift 213568
  have htrace : WordTrace (prefixWord ++ tailWord_213568) baseStart_213568 baseEnd_213568 := by
    simpa [prefixWord, tailWord_213568, baseEnd_213568] using wordTrace_append hprefix tailTrace_213568
  have hstable : (prefixWord ++ tailWord_213568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213568).length < 2 ^ (prefixWord ++ tailWord_213568).sum := by decide
  have hdescent : baseEnd_213568 < baseStart_213568 := by decide
  rcases family_descends (prefixWord ++ tailWord_213568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213601 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_213601 : Nat := 118140960795 + 213601 * 2 ^ 59
def prefixEnd_213601 : Nat := 4983230072969 + 3 ^ 40 * 213601 * 2
def baseEnd_213601 : Nat := 109679981281124018805173

theorem tailTrace_213601 : CollatzResearch.WordTrace tailWord_213601 prefixEnd_213601 109679981281124018805173 := by
  unfold tailWord_213601
  simp only [CollatzResearch.WordTrace]
  refine ⟨7790668499167531991576657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5193778999445021327717771 7790668499167531991576657)
  ·
    refine ⟨5843001374375648993682493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7790668499167531991576657 5843001374375648993682493)
    ·
      refine ⟨2191125515390868372630935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5843001374375648993682493 2191125515390868372630935)
      ·
        refine ⟨3286688273086302558946403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191125515390868372630935 3286688273086302558946403)
        ·
          refine ⟨4930032409629453838419605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286688273086302558946403 4930032409629453838419605)
          ·
            refine ⟨231095269201380648675919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4930032409629453838419605 231095269201380648675919)
            ·
              refine ⟨346642903802070973013879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231095269201380648675919 346642903802070973013879)
              ·
                refine ⟨519964355703106459520819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346642903802070973013879 519964355703106459520819)
                ·
                  refine ⟨779946533554659689281229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519964355703106459520819 779946533554659689281229)
                  ·
                    refine ⟨292479950082997383480461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779946533554659689281229 292479950082997383480461)
                    ·
                      refine ⟨109679981281124018805173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 292479950082997383480461 109679981281124018805173)
                      ·
                        rfl

theorem cell23_213601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_213601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213601 prefixEnd_213601 := by exact prefixLift 213601
  have htrace : WordTrace (prefixWord ++ tailWord_213601) baseStart_213601 baseEnd_213601 := by
    simpa [prefixWord, tailWord_213601, baseEnd_213601] using wordTrace_append hprefix tailTrace_213601
  have hstable : (prefixWord ++ tailWord_213601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213601).length < 2 ^ (prefixWord ++ tailWord_213601).sum := by decide
  have hdescent : baseEnd_213601 < baseStart_213601 := by decide
  rcases family_descends (prefixWord ++ tailWord_213601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213608 : List Nat := [2, 1, 4, 3, 3, 1, 2, 7]
def baseStart_213608 : Nat := 118140960795 + 213608 * 2 ^ 59
def prefixEnd_213608 : Nat := 4983230072969 + 3 ^ 40 * 213608 * 2
def baseEnd_213608 : Nat := 4062354653544647830283

theorem tailTrace_213608 : CollatzResearch.WordTrace tailWord_213608 prefixEnd_213608 4062354653544647830283 := by
  unfold tailWord_213608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895461905071086093540739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5193949206761448124720985 3895461905071086093540739)
  ·
    refine ⟨5843192857606629140311109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3895461905071086093540739 5843192857606629140311109)
    ·
      refine ⟨1095598660801242963808333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5843192857606629140311109 1095598660801242963808333)
      ·
        refine ⟨410849497800466111428125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1095598660801242963808333 410849497800466111428125)
        ·
          refine ⟨154068561675174791785547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410849497800466111428125 154068561675174791785547)
          ·
            refine ⟨231102842512762187678321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154068561675174791785547 231102842512762187678321)
            ·
              refine ⟨173327131884571640758741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231102842512762187678321 173327131884571640758741)
              ·
                refine ⟨4062354653544647830283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173327131884571640758741 4062354653544647830283)
                ·
                  rfl

theorem cell23_213608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 7].length) (baseStart_213608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213608 prefixEnd_213608 := by exact prefixLift 213608
  have htrace : WordTrace (prefixWord ++ tailWord_213608) baseStart_213608 baseEnd_213608 := by
    simpa [prefixWord, tailWord_213608, baseEnd_213608] using wordTrace_append hprefix tailTrace_213608
  have hstable : (prefixWord ++ tailWord_213608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213608).length < 2 ^ (prefixWord ++ tailWord_213608).sum := by decide
  have hdescent : baseEnd_213608 < baseStart_213608 := by decide
  rcases family_descends (prefixWord ++ tailWord_213608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213614 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_213614 : Nat := 118140960795 + 213614 * 2 ^ 59
def prefixEnd_213614 : Nat := 4983230072969 + 3 ^ 40 * 213614 * 2
def baseEnd_213614 : Nat := 109686656529632467942613

theorem tailTrace_213614 : CollatzResearch.WordTrace tailWord_213614 prefixEnd_213614 109686656529632467942613 := by
  unfold tailWord_213614
  simp only [CollatzResearch.WordTrace]
  refine ⟨973892831015054401474987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5194095098746956807866597 973892831015054401474987)
  ·
    refine ⟨1460839246522581602212481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 973892831015054401474987 1460839246522581602212481)
    ·
      refine ⟨1095629434891936201659361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1460839246522581602212481 1095629434891936201659361)
      ·
        refine ⟨821722076168952151244521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1095629434891936201659361 821722076168952151244521)
        ·
          refine ⟨616291557126714113433391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821722076168952151244521 616291557126714113433391)
          ·
            refine ⟨924437335690071170150087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616291557126714113433391 924437335690071170150087)
            ·
              refine ⟨1386656003535106755225131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924437335690071170150087 1386656003535106755225131)
              ·
                refine ⟨2079984005302660132837697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386656003535106755225131 2079984005302660132837697)
                ·
                  refine ⟨1559988003976995099628273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079984005302660132837697 1559988003976995099628273)
                  ·
                    refine ⟨1169991002982746324721205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1559988003976995099628273 1169991002982746324721205)
                    ·
                      refine ⟨109686656529632467942613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1169991002982746324721205 109686656529632467942613)
                      ·
                        rfl

theorem cell23_213614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_213614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213614 prefixEnd_213614 := by exact prefixLift 213614
  have htrace : WordTrace (prefixWord ++ tailWord_213614) baseStart_213614 baseEnd_213614 := by
    simpa [prefixWord, tailWord_213614, baseEnd_213614] using wordTrace_append hprefix tailTrace_213614
  have hstable : (prefixWord ++ tailWord_213614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213614).length < 2 ^ (prefixWord ++ tailWord_213614).sum := by decide
  have hdescent : baseEnd_213614 < baseStart_213614 := by decide
  rcases family_descends (prefixWord ++ tailWord_213614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213652 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_213652 : Nat := 118140960795 + 213652 * 2 ^ 59
def prefixEnd_213652 : Nat := 4983230072969 + 3 ^ 40 * 213652 * 2
def baseEnd_213652 : Nat := 109706168794503319267439

theorem tailTrace_213652 : CollatzResearch.WordTrace tailWord_213652 prefixEnd_213652 109706168794503319267439 := by
  unfold tailWord_213652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3896264310991383850841605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5195019081321845134455473 3896264310991383850841605)
  ·
    refine ⟨730549558310884472032801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3896264310991383850841605 730549558310884472032801)
    ·
      refine ⟨547912168733163354024601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 730549558310884472032801 547912168733163354024601)
      ·
        refine ⟨410934126549872515518451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547912168733163354024601 410934126549872515518451)
        ·
          refine ⟨616401189824808773277677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410934126549872515518451 616401189824808773277677)
          ·
            refine ⟨231150446184303289979129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 616401189824808773277677 231150446184303289979129)
            ·
              refine ⟨173362834638227467484347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231150446184303289979129 173362834638227467484347)
              ·
                refine ⟨260044251957341201226521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173362834638227467484347 260044251957341201226521)
                ·
                  refine ⟨195033188968005900919891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260044251957341201226521 195033188968005900919891)
                  ·
                    refine ⟨292549783452008851379837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195033188968005900919891 292549783452008851379837)
                    ·
                      refine ⟨109706168794503319267439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 292549783452008851379837 109706168794503319267439)
                      ·
                        rfl

theorem cell23_213652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_213652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213652 prefixEnd_213652 := by exact prefixLift 213652
  have htrace : WordTrace (prefixWord ++ tailWord_213652) baseStart_213652 baseEnd_213652 := by
    simpa [prefixWord, tailWord_213652, baseEnd_213652] using wordTrace_append hprefix tailTrace_213652
  have hstable : (prefixWord ++ tailWord_213652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213652).length < 2 ^ (prefixWord ++ tailWord_213652).sum := by decide
  have hdescent : baseEnd_213652 < baseStart_213652 := by decide
  rcases family_descends (prefixWord ++ tailWord_213652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213704 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_213704 : Nat := 118140960795 + 213704 * 2 ^ 59
def prefixEnd_213704 : Nat := 4983230072969 + 3 ^ 40 * 213704 * 2
def baseEnd_213704 : Nat := 109732869788537115817199

theorem tailTrace_213704 : CollatzResearch.WordTrace tailWord_213704 prefixEnd_213704 109732869788537115817199 := by
  unfold tailWord_213704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3897212608897190291288083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5196283478529587055050777 3897212608897190291288083)
  ·
    refine ⟨5845818913345785436932125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3897212608897190291288083 5845818913345785436932125)
    ·
      refine ⟨2192182092504669538849547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5845818913345785436932125 2192182092504669538849547)
      ·
        refine ⟨3288273138757004308274321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192182092504669538849547 3288273138757004308274321)
        ·
          refine ⟨2466204854067753231205741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3288273138757004308274321 2466204854067753231205741)
          ·
            refine ⟨924826820275407461702153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2466204854067753231205741 924826820275407461702153)
            ·
              refine ⟨693620115206555596276615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924826820275407461702153 693620115206555596276615)
              ·
                refine ⟨1040430172809833394414923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693620115206555596276615 1040430172809833394414923)
                ·
                  refine ⟨1560645259214750091622385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040430172809833394414923 1560645259214750091622385)
                  ·
                    refine ⟨1170483944411062568716789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1560645259214750091622385 1170483944411062568716789)
                    ·
                      refine ⟨109732869788537115817199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1170483944411062568716789 109732869788537115817199)
                      ·
                        rfl

theorem cell23_213704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_213704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213704 prefixEnd_213704 := by exact prefixLift 213704
  have htrace : WordTrace (prefixWord ++ tailWord_213704) baseStart_213704 baseEnd_213704 := by
    simpa [prefixWord, tailWord_213704, baseEnd_213704] using wordTrace_append hprefix tailTrace_213704
  have hstable : (prefixWord ++ tailWord_213704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213704).length < 2 ^ (prefixWord ++ tailWord_213704).sum := by decide
  have hdescent : baseEnd_213704 < baseStart_213704 := by decide
  rcases family_descends (prefixWord ++ tailWord_213704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213707 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 4, 8]
def baseStart_213707 : Nat := 118140960795 + 213707 * 2 ^ 59
def prefixEnd_213707 : Nat := 4983230072969 + 3 ^ 40 * 213707 * 2
def baseEnd_213707 : Nat := 36578136743500201359895

theorem tailTrace_213707 : CollatzResearch.WordTrace tailWord_213707 prefixEnd_213707 36578136743500201359895 := by
  unfold tailWord_213707
  simp only [CollatzResearch.WordTrace]
  refine ⟨7794534636783512094935375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5196356424522341396623583 7794534636783512094935375)
  ·
    refine ⟨11691801955175268142403063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7794534636783512094935375 11691801955175268142403063)
    ·
      refine ⟨17537702932762902213604595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11691801955175268142403063 17537702932762902213604595)
      ·
        refine ⟨26306554399144353320406893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17537702932762902213604595 26306554399144353320406893)
        ·
          refine ⟨9864957899679132495152585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26306554399144353320406893 9864957899679132495152585)
          ·
            refine ⟨7398718424759349371364439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9864957899679132495152585 7398718424759349371364439)
            ·
              refine ⟨11098077637139024057046659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398718424759349371364439 11098077637139024057046659)
              ·
                refine ⟨16647116455708536085569989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11098077637139024057046659 16647116455708536085569989)
                ·
                  refine ⟨3121334335445350516044373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16647116455708536085569989 3121334335445350516044373)
                  ·
                    refine ⟨36578136743500201359895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3121334335445350516044373 36578136743500201359895)
                    ·
                      rfl

theorem cell23_213707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_213707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213707 prefixEnd_213707 := by exact prefixLift 213707
  have htrace : WordTrace (prefixWord ++ tailWord_213707) baseStart_213707 baseEnd_213707 := by
    simpa [prefixWord, tailWord_213707, baseEnd_213707] using wordTrace_append hprefix tailTrace_213707
  have hstable : (prefixWord ++ tailWord_213707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213707).length < 2 ^ (prefixWord ++ tailWord_213707).sum := by decide
  have hdescent : baseEnd_213707 < baseStart_213707 := by decide
  rcases family_descends (prefixWord ++ tailWord_213707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213731 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 4]
def baseStart_213731 : Nat := 118140960795 + 213731 * 2 ^ 59
def prefixEnd_213731 : Nat := 4983230072969 + 3 ^ 40 * 213731 * 2
def baseEnd_213731 : Nat := 109746733766208510179575

theorem tailTrace_213731 : CollatzResearch.WordTrace tailWord_213731 prefixEnd_213731 109746733766208510179575 := by
  unfold tailWord_213731
  simp only [CollatzResearch.WordTrace]
  refine ⟨7795409988696564193809047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5196939992464376129206031 7795409988696564193809047)
  ·
    refine ⟨11693114983044846290713571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7795409988696564193809047 11693114983044846290713571)
    ·
      refine ⟨17539672474567269436070357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11693114983044846290713571 17539672474567269436070357)
      ·
        refine ⟨411086073622670377407899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 17539672474567269436070357 411086073622670377407899)
        ·
          refine ⟨616629110434005566111849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411086073622670377407899 616629110434005566111849)
          ·
            refine ⟨462471832825504174583887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616629110434005566111849 462471832825504174583887)
            ·
              refine ⟨693707749238256261875831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462471832825504174583887 693707749238256261875831)
              ·
                refine ⟨1040561623857384392813747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693707749238256261875831 1040561623857384392813747)
                ·
                  refine ⟨1560842435786076589220621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040561623857384392813747 1560842435786076589220621)
                  ·
                    refine ⟨585315913419778720957733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1560842435786076589220621 585315913419778720957733)
                    ·
                      refine ⟨109746733766208510179575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 585315913419778720957733 109746733766208510179575)
                      ·
                        rfl

theorem cell23_213731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_213731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213731 prefixEnd_213731 := by exact prefixLift 213731
  have htrace : WordTrace (prefixWord ++ tailWord_213731) baseStart_213731 baseEnd_213731 := by
    simpa [prefixWord, tailWord_213731, baseEnd_213731] using wordTrace_append hprefix tailTrace_213731
  have hstable : (prefixWord ++ tailWord_213731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213731).length < 2 ^ (prefixWord ++ tailWord_213731).sum := by decide
  have hdescent : baseEnd_213731 < baseStart_213731 := by decide
  rcases family_descends (prefixWord ++ tailWord_213731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213741 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_213741 : Nat := 118140960795 + 213741 * 2 ^ 59
def prefixEnd_213741 : Nat := 4983230072969 + 3 ^ 40 * 213741 * 2
def baseEnd_213741 : Nat := 36583956190917823684843

theorem tailTrace_213741 : CollatzResearch.WordTrace tailWord_213741 prefixEnd_213741 36583956190917823684843 := by
  unfold tailWord_213741
  simp only [CollatzResearch.WordTrace]
  refine ⟨7795774718660335901673077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5197183145773557267782051 7795774718660335901673077)
  ·
    refine ⟨730853879874406490781851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7795774718660335901673077 730853879874406490781851)
    ·
      refine ⟨1096280819811609736172777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730853879874406490781851 1096280819811609736172777)
      ·
        refine ⟨822210614858707302129583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1096280819811609736172777 822210614858707302129583)
        ·
          refine ⟨1233315922288060953194375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822210614858707302129583 1233315922288060953194375)
          ·
            refine ⟨1849973883432091429791563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233315922288060953194375 1849973883432091429791563)
            ·
              refine ⟨2774960825148137144687345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849973883432091429791563 2774960825148137144687345)
              ·
                refine ⟨2081220618861102858515509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2774960825148137144687345 2081220618861102858515509)
                ·
                  refine ⟨195114433018228392985829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2081220618861102858515509 195114433018228392985829)
                  ·
                    refine ⟨36583956190917823684843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195114433018228392985829 36583956190917823684843)
                    ·
                      rfl

theorem cell23_213741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_213741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213741 prefixEnd_213741 := by exact prefixLift 213741
  have htrace : WordTrace (prefixWord ++ tailWord_213741) baseStart_213741 baseEnd_213741 := by
    simpa [prefixWord, tailWord_213741, baseEnd_213741] using wordTrace_append hprefix tailTrace_213741
  have hstable : (prefixWord ++ tailWord_213741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213741).length < 2 ^ (prefixWord ++ tailWord_213741).sum := by decide
  have hdescent : baseEnd_213741 < baseStart_213741 := by decide
  rcases family_descends (prefixWord ++ tailWord_213741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213758 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_213758 : Nat := 118140960795 + 213758 * 2 ^ 59
def prefixEnd_213758 : Nat := 4983230072969 + 3 ^ 40 * 213758 * 2
def baseEnd_213758 : Nat := 36586865914626634847317

theorem tailTrace_213758 : CollatzResearch.WordTrace tailWord_213758 prefixEnd_213758 36586865914626634847317 := by
  unfold tailWord_213758
  simp only [CollatzResearch.WordTrace]
  refine ⟨974549344949843475630241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5197596506399165203361285 974549344949843475630241)
  ·
    refine ⟨730912008712382606722681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 974549344949843475630241 730912008712382606722681)
    ·
      refine ⟨548184006534286955042011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 730912008712382606722681 548184006534286955042011)
      ·
        refine ⟨822276009801430432563017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548184006534286955042011 822276009801430432563017)
        ·
          refine ⟨616707007351072824422263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822276009801430432563017 616707007351072824422263)
          ·
            refine ⟨925060511026609236633395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616707007351072824422263 925060511026609236633395)
            ·
              refine ⟨1387590766539913854950093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925060511026609236633395 1387590766539913854950093)
              ·
                refine ⟨520346537452467695606285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1387590766539913854950093 520346537452467695606285)
                ·
                  refine ⟨195129951544675385852357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 520346537452467695606285 195129951544675385852357)
                  ·
                    refine ⟨36586865914626634847317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195129951544675385852357 36586865914626634847317)
                    ·
                      rfl

theorem cell23_213758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_213758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213758 prefixEnd_213758 := by exact prefixLift 213758
  have htrace : WordTrace (prefixWord ++ tailWord_213758) baseStart_213758 baseEnd_213758 := by
    simpa [prefixWord, tailWord_213758, baseEnd_213758] using wordTrace_append hprefix tailTrace_213758
  have hstable : (prefixWord ++ tailWord_213758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213758).length < 2 ^ (prefixWord ++ tailWord_213758).sum := by decide
  have hdescent : baseEnd_213758 < baseStart_213758 := by decide
  rcases family_descends (prefixWord ++ tailWord_213758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213774 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_213774 : Nat := 118140960795 + 213774 * 2 ^ 59
def prefixEnd_213774 : Nat := 4983230072969 + 3 ^ 40 * 213774 * 2
def baseEnd_213774 : Nat := 109768813434351841941877

theorem tailTrace_213774 : CollatzResearch.WordTrace tailWord_213774 prefixEnd_213774 109768813434351841941877 := by
  unfold tailWord_213774
  simp only [CollatzResearch.WordTrace]
  refine ⟨974622290942597817203047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5197985551693855025082917 974622290942597817203047)
  ·
    refine ⟨1461933436413896725804571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 974622290942597817203047 1461933436413896725804571)
    ·
      refine ⟨2192900154620845088706857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461933436413896725804571 2192900154620845088706857)
      ·
        refine ⟨1644675115965633816530143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2192900154620845088706857 1644675115965633816530143)
        ·
          refine ⟨2467012673948450724795215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644675115965633816530143 2467012673948450724795215)
          ·
            refine ⟨3700519010922676087192823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467012673948450724795215 3700519010922676087192823)
            ·
              refine ⟨5550778516384014130789235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700519010922676087192823 5550778516384014130789235)
              ·
                refine ⟨8326167774576021196183853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550778516384014130789235 8326167774576021196183853)
                ·
                  refine ⟨3122312915466007948568945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8326167774576021196183853 3122312915466007948568945)
                  ·
                    refine ⟨2341734686599505961426709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122312915466007948568945 2341734686599505961426709)
                    ·
                      refine ⟨109768813434351841941877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2341734686599505961426709 109768813434351841941877)
                      ·
                        rfl

theorem cell23_213774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_213774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213774 prefixEnd_213774 := by exact prefixLift 213774
  have htrace : WordTrace (prefixWord ++ tailWord_213774) baseStart_213774 baseEnd_213774 := by
    simpa [prefixWord, tailWord_213774, baseEnd_213774] using wordTrace_append hprefix tailTrace_213774
  have hstable : (prefixWord ++ tailWord_213774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213774).length < 2 ^ (prefixWord ++ tailWord_213774).sum := by decide
  have hdescent : baseEnd_213774 < baseStart_213774 := by decide
  rcases family_descends (prefixWord ++ tailWord_213774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213822 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_213822 : Nat := 118140960795 + 213822 * 2 ^ 59
def prefixEnd_213822 : Nat := 4983230072969 + 3 ^ 40 * 213822 * 2
def baseEnd_213822 : Nat := 12199273389529739349073

theorem tailTrace_213822 : CollatzResearch.WordTrace tailWord_213822 prefixEnd_213822 12199273389529739349073 := by
  unfold tailWord_213822
  simp only [CollatzResearch.WordTrace]
  refine ⟨974841128920860841921465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5199152687577924490247813 974841128920860841921465)
  ·
    refine ⟨731130846690645631441099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 974841128920860841921465 731130846690645631441099)
    ·
      refine ⟨1096696270035968447161649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731130846690645631441099 1096696270035968447161649)
      ·
        refine ⟨822522202526976335371237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1096696270035968447161649 822522202526976335371237)
        ·
          refine ⟨154222912973808062882107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 822522202526976335371237 154222912973808062882107)
          ·
            refine ⟨231334369460712094323161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154222912973808062882107 231334369460712094323161)
            ·
              refine ⟨173500777095534070742371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231334369460712094323161 173500777095534070742371)
              ·
                refine ⟨260251165643301106113557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173500777095534070742371 260251165643301106113557)
                ·
                  refine ⟨12199273389529739349073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260251165643301106113557 12199273389529739349073)
                  ·
                    rfl

theorem cell23_213822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_213822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213822 prefixEnd_213822 := by exact prefixLift 213822
  have htrace : WordTrace (prefixWord ++ tailWord_213822) baseStart_213822 baseEnd_213822 := by
    simpa [prefixWord, tailWord_213822, baseEnd_213822] using wordTrace_append hprefix tailTrace_213822
  have hstable : (prefixWord ++ tailWord_213822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213822).length < 2 ^ (prefixWord ++ tailWord_213822).sum := by decide
  have hdescent : baseEnd_213822 < baseStart_213822 := by decide
  rcases family_descends (prefixWord ++ tailWord_213822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213878 : List Nat := [5, 1, 1, 3, 1, 1, 3, 8]
def baseStart_213878 : Nat := 118140960795 + 213878 * 2 ^ 59
def prefixEnd_213878 : Nat := 4983230072969 + 3 ^ 40 * 213878 * 2
def baseEnd_213878 : Nat := 4067489460089608705237

theorem tailTrace_213878 : CollatzResearch.WordTrace tailWord_213878 prefixEnd_213878 4067489460089608705237 := by
  unfold tailWord_213878
  simp only [CollatzResearch.WordTrace]
  refine ⟨487548219947750518713143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5200514346109338866273525 487548219947750518713143)
  ·
    refine ⟨731322329921625778069715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 487548219947750518713143 731322329921625778069715)
    ·
      refine ⟨1096983494882438667104573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731322329921625778069715 1096983494882438667104573)
      ·
        refine ⟨411368810580914500164215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1096983494882438667104573 411368810580914500164215)
        ·
          refine ⟨617053215871371750246323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411368810580914500164215 617053215871371750246323)
          ·
            refine ⟨925579823807057625369485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617053215871371750246323 925579823807057625369485)
            ·
              refine ⟨347092433927646609513557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925579823807057625369485 347092433927646609513557)
              ·
                refine ⟨4067489460089608705237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 347092433927646609513557 4067489460089608705237)
                ·
                  rfl

theorem cell23_213878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_213878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213878 prefixEnd_213878 := by exact prefixLift 213878
  have htrace : WordTrace (prefixWord ++ tailWord_213878) baseStart_213878 baseEnd_213878 := by
    simpa [prefixWord, tailWord_213878, baseEnd_213878] using wordTrace_append hprefix tailTrace_213878
  have hstable : (prefixWord ++ tailWord_213878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213878).length < 2 ^ (prefixWord ++ tailWord_213878).sum := by decide
  have hdescent : baseEnd_213878 < baseStart_213878 := by decide
  rcases family_descends (prefixWord ++ tailWord_213878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213906 : List Nat := [3, 2, 3, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_213906 : Nat := 118140960795 + 213906 * 2 ^ 59
def prefixEnd_213906 : Nat := 4983230072969 + 3 ^ 40 * 213906 * 2
def baseEnd_213906 : Nat := 109836592880745325491271

theorem tailTrace_213906 : CollatzResearch.WordTrace tailWord_213906 prefixEnd_213906 109836592880745325491271 := by
  unfold tailWord_213906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950448190765642270357393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5201195175375046054286381 1950448190765642270357393)
  ·
    refine ⟨1462836143074231702768045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1950448190765642270357393 1462836143074231702768045)
    ·
      refine ⟨548563553652836888538017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1462836143074231702768045 548563553652836888538017)
      ·
        refine ⟨411422665239627666403513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548563553652836888538017 411422665239627666403513)
        ·
          refine ⟨308566998929720749802635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411422665239627666403513 308566998929720749802635)
          ·
            refine ⟨462850498394581124703953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308566998929720749802635 462850498394581124703953)
            ·
              refine ⟨347137873795935843527965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462850498394581124703953 347137873795935843527965)
              ·
                refine ⟨130176702673475941322987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347137873795935843527965 130176702673475941322987)
                ·
                  refine ⟨195265054010213911984481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130176702673475941322987 195265054010213911984481)
                  ·
                    refine ⟨146448790507660433988361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 195265054010213911984481 146448790507660433988361)
                    ·
                      refine ⟨109836592880745325491271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146448790507660433988361 109836592880745325491271)
                      ·
                        rfl

theorem cell23_213906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_213906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213906 prefixEnd_213906 := by exact prefixLift 213906
  have htrace : WordTrace (prefixWord ++ tailWord_213906) baseStart_213906 baseEnd_213906 := by
    simpa [prefixWord, tailWord_213906, baseEnd_213906] using wordTrace_append hprefix tailTrace_213906
  have hstable : (prefixWord ++ tailWord_213906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213906).length < 2 ^ (prefixWord ++ tailWord_213906).sum := by decide
  have hdescent : baseEnd_213906 < baseStart_213906 := by decide
  rcases family_descends (prefixWord ++ tailWord_213906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213922 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_213922 : Nat := 118140960795 + 213922 * 2 ^ 59
def prefixEnd_213922 : Nat := 4983230072969 + 3 ^ 40 * 213922 * 2
def baseEnd_213922 : Nat := 109844808571217262891197

theorem tailTrace_213922 : CollatzResearch.WordTrace tailWord_213922 prefixEnd_213922 109844808571217262891197 := by
  unfold tailWord_213922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950594082751150953503005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5201584220669735876008013 1950594082751150953503005)
  ·
    refine ⟨731472781031681607563627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1950594082751150953503005 731472781031681607563627)
    ·
      refine ⟨1097209171547522411345441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731472781031681607563627 1097209171547522411345441)
      ·
        refine ⟨822906878660641808509081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097209171547522411345441 822906878660641808509081)
        ·
          refine ⟨617180158995481356381811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822906878660641808509081 617180158995481356381811)
          ·
            refine ⟨925770238493222034572717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617180158995481356381811 925770238493222034572717)
            ·
              refine ⟨347163839434958262964769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925770238493222034572717 347163839434958262964769)
              ·
                refine ⟨260372879576218697223577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347163839434958262964769 260372879576218697223577)
                ·
                  refine ⟨195279659682164022917683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260372879576218697223577 195279659682164022917683)
                  ·
                    refine ⟨292919489523246034376525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195279659682164022917683 292919489523246034376525)
                    ·
                      refine ⟨109844808571217262891197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 292919489523246034376525 109844808571217262891197)
                      ·
                        rfl

theorem cell23_213922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_213922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213922 prefixEnd_213922 := by exact prefixLift 213922
  have htrace : WordTrace (prefixWord ++ tailWord_213922) baseStart_213922 baseEnd_213922 := by
    simpa [prefixWord, tailWord_213922, baseEnd_213922] using wordTrace_append hprefix tailTrace_213922
  have hstable : (prefixWord ++ tailWord_213922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213922).length < 2 ^ (prefixWord ++ tailWord_213922).sum := by decide
  have hdescent : baseEnd_213922 < baseStart_213922 := by decide
  rcases family_descends (prefixWord ++ tailWord_213922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213945 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 1, 4, 2]
def baseStart_213945 : Nat := 118140960795 + 213945 * 2 ^ 59
def prefixEnd_213945 : Nat := 4983230072969 + 3 ^ 40 * 213945 * 2
def baseEnd_213945 : Nat := 109856618626270672903591

theorem tailTrace_213945 : CollatzResearch.WordTrace tailWord_213945 prefixEnd_213945 109856618626270672903591 := by
  unfold tailWord_213945
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803215209921278742099289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5202143473280852494732859 7803215209921278742099289)
  ·
    refine ⟨5852411407440959056574467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7803215209921278742099289 5852411407440959056574467)
    ·
      refine ⟨8778617111161438584861701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5852411407440959056574467 8778617111161438584861701)
      ·
        refine ⟨1645990708342769734661569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8778617111161438584861701 1645990708342769734661569)
        ·
          refine ⟨1234493031257077300996177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645990708342769734661569 1234493031257077300996177)
          ·
            refine ⟨925869773442807975747133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1234493031257077300996177 925869773442807975747133)
            ·
              refine ⟨347201165041052990905175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925869773442807975747133 347201165041052990905175)
              ·
                refine ⟨520801747561579486357763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347201165041052990905175 520801747561579486357763)
                ·
                  refine ⟨781202621342369229536645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520801747561579486357763 781202621342369229536645)
                  ·
                    refine ⟨146475491501694230538121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 781202621342369229536645 146475491501694230538121)
                    ·
                      refine ⟨109856618626270672903591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146475491501694230538121 109856618626270672903591)
                      ·
                        rfl

theorem cell23_213945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_213945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_213945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_213945 prefixEnd_213945 := by exact prefixLift 213945
  have htrace : WordTrace (prefixWord ++ tailWord_213945) baseStart_213945 baseEnd_213945 := by
    simpa [prefixWord, tailWord_213945, baseEnd_213945] using wordTrace_append hprefix tailTrace_213945
  have hstable : (prefixWord ++ tailWord_213945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213945).length < 2 ^ (prefixWord ++ tailWord_213945).sum := by decide
  have hdescent : baseEnd_213945 < baseStart_213945 := by decide
  rcases family_descends (prefixWord ++ tailWord_213945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214031 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_214031 : Nat := 118140960795 + 214031 * 2 ^ 59
def prefixEnd_214031 : Nat := 4983230072969 + 3 ^ 40 * 214031 * 2
def baseEnd_214031 : Nat := 109900777962557336428195

theorem tailTrace_214031 : CollatzResearch.WordTrace tailWord_214031 prefixEnd_214031 109900777962557336428195 := by
  unfold tailWord_214031
  simp only [CollatzResearch.WordTrace]
  refine ⟨7806351887609715429729947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5204234591739810286486631 7806351887609715429729947)
  ·
    refine ⟨11709527831414573144594921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7806351887609715429729947 11709527831414573144594921)
    ·
      refine ⟨8782145873560929858446191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11709527831414573144594921 8782145873560929858446191)
      ·
        refine ⟨13173218810341394787669287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8782145873560929858446191 13173218810341394787669287)
        ·
          refine ⟨19759828215512092181503931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13173218810341394787669287 19759828215512092181503931)
          ·
            refine ⟨29639742323268138272255897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19759828215512092181503931 29639742323268138272255897)
            ·
              refine ⟨22229806742451103704191923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29639742323268138272255897 22229806742451103704191923)
              ·
                refine ⟨33344710113676655556287885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22229806742451103704191923 33344710113676655556287885)
                ·
                  refine ⟨12504266292628745833607957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33344710113676655556287885 12504266292628745833607957)
                  ·
                    refine ⟨586137482466972460950373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12504266292628745833607957 586137482466972460950373)
                    ·
                      refine ⟨109900777962557336428195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 586137482466972460950373 109900777962557336428195)
                      ·
                        rfl

theorem cell23_214031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_214031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214031 prefixEnd_214031 := by exact prefixLift 214031
  have htrace : WordTrace (prefixWord ++ tailWord_214031) baseStart_214031 baseEnd_214031 := by
    simpa [prefixWord, tailWord_214031, baseEnd_214031] using wordTrace_append hprefix tailTrace_214031
  have hstable : (prefixWord ++ tailWord_214031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214031).length < 2 ^ (prefixWord ++ tailWord_214031).sum := by decide
  have hdescent : baseEnd_214031 < baseStart_214031 := by decide
  rcases family_descends (prefixWord ++ tailWord_214031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214041 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 8]
def baseStart_214041 : Nat := 118140960795 + 214041 * 2 ^ 59
def prefixEnd_214041 : Nat := 4983230072969 + 3 ^ 40 * 214041 * 2
def baseEnd_214041 : Nat := 12211768085455810811461

theorem tailTrace_214041 : CollatzResearch.WordTrace tailWord_214041 prefixEnd_214041 12211768085455810811461 := by
  unfold tailWord_214041
  simp only [CollatzResearch.WordTrace]
  refine ⟨7806716617573487137593977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5204477745048991425062651 7806716617573487137593977)
  ·
    refine ⟨5855037463180115353195483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7806716617573487137593977 5855037463180115353195483)
    ·
      refine ⟨8782556194770173029793225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855037463180115353195483 8782556194770173029793225)
      ·
        refine ⟨6586917146077629772344919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8782556194770173029793225 6586917146077629772344919)
        ·
          refine ⟨9880375719116444658517379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586917146077629772344919 9880375719116444658517379)
          ·
            refine ⟨14820563578674666987776069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9880375719116444658517379 14820563578674666987776069)
            ·
              refine ⟨2778855671001500060208013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14820563578674666987776069 2778855671001500060208013)
              ·
                refine ⟨1042070876625562522578005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2778855671001500060208013 1042070876625562522578005)
                ·
                  refine ⟨12211768085455810811461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1042070876625562522578005 12211768085455810811461)
                  ·
                    rfl

theorem cell23_214041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_214041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214041 prefixEnd_214041 := by exact prefixLift 214041
  have htrace : WordTrace (prefixWord ++ tailWord_214041) baseStart_214041 baseEnd_214041 := by
    simpa [prefixWord, tailWord_214041, baseEnd_214041] using wordTrace_append hprefix tailTrace_214041
  have hstable : (prefixWord ++ tailWord_214041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214041).length < 2 ^ (prefixWord ++ tailWord_214041).sum := by decide
  have hdescent : baseEnd_214041 < baseStart_214041 := by decide
  rcases family_descends (prefixWord ++ tailWord_214041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214052 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_214052 : Nat := 118140960795 + 214052 * 2 ^ 59
def prefixEnd_214052 : Nat := 4983230072969 + 3 ^ 40 * 214052 * 2
def baseEnd_214052 : Nat := 109911561056301754265599

theorem tailTrace_214052 : CollatzResearch.WordTrace tailWord_214052 prefixEnd_214052 109911561056301754265599 := by
  unfold tailWord_214052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903558910266818008122205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5204745213689090677496273 3903558910266818008122205)
  ·
    refine ⟨1463834591350056753045827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3903558910266818008122205 1463834591350056753045827)
    ·
      refine ⟨2195751887025085129568741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463834591350056753045827 2195751887025085129568741)
      ·
        refine ⟨411703478817203461794139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2195751887025085129568741 411703478817203461794139)
        ·
          refine ⟨617555218225805192691209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411703478817203461794139 617555218225805192691209)
          ·
            refine ⟨463166413669353894518407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617555218225805192691209 463166413669353894518407)
            ·
              refine ⟨694749620504030841777611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463166413669353894518407 694749620504030841777611)
              ·
                refine ⟨1042124430756046262666417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694749620504030841777611 1042124430756046262666417)
                ·
                  refine ⟨781593323067034696999813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042124430756046262666417 781593323067034696999813)
                  ·
                    refine ⟨146548748075069005687465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 781593323067034696999813 146548748075069005687465)
                    ·
                      refine ⟨109911561056301754265599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 146548748075069005687465 109911561056301754265599)
                      ·
                        rfl

theorem cell23_214052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_214052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214052 prefixEnd_214052 := by exact prefixLift 214052
  have htrace : WordTrace (prefixWord ++ tailWord_214052) baseStart_214052 baseEnd_214052 := by
    simpa [prefixWord, tailWord_214052, baseEnd_214052] using wordTrace_append hprefix tailTrace_214052
  have hstable : (prefixWord ++ tailWord_214052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214052).length < 2 ^ (prefixWord ++ tailWord_214052).sum := by decide
  have hdescent : baseEnd_214052 < baseStart_214052 := by decide
  rcases family_descends (prefixWord ++ tailWord_214052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214072 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_214072 : Nat := 118140960795 + 214072 * 2 ^ 59
def prefixEnd_214072 : Nat := 4983230072969 + 3 ^ 40 * 214072 * 2
def baseEnd_214072 : Nat := 109921830669391676015507

theorem tailTrace_214072 : CollatzResearch.WordTrace tailWord_214072 prefixEnd_214072 109921830669391676015507 := by
  unfold tailWord_214072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903923640230589715986235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5205231520307452954648313 3903923640230589715986235)
  ·
    refine ⟨5855885460345884573979353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903923640230589715986235 5855885460345884573979353)
    ·
      refine ⟨4391914095259413430484515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5855885460345884573979353 4391914095259413430484515)
      ·
        refine ⟨6587871142889120145726773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4391914095259413430484515 6587871142889120145726773)
        ·
          refine ⟨617612919645855013661885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6587871142889120145726773 617612919645855013661885)
          ·
            refine ⟨231604844867195630123207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617612919645855013661885 231604844867195630123207)
            ·
              refine ⟨347407267300793445184811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231604844867195630123207 347407267300793445184811)
              ·
                refine ⟨521110900951190167777217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347407267300793445184811 521110900951190167777217)
                ·
                  refine ⟨390833175713392625832913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521110900951190167777217 390833175713392625832913)
                  ·
                    refine ⟨293124881785044469374685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 390833175713392625832913 293124881785044469374685)
                    ·
                      refine ⟨109921830669391676015507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 293124881785044469374685 109921830669391676015507)
                      ·
                        rfl

theorem cell23_214072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_214072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214072 prefixEnd_214072 := by exact prefixLift 214072
  have htrace : WordTrace (prefixWord ++ tailWord_214072) baseStart_214072 baseEnd_214072 := by
    simpa [prefixWord, tailWord_214072, baseEnd_214072] using wordTrace_append hprefix tailTrace_214072
  have hstable : (prefixWord ++ tailWord_214072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214072).length < 2 ^ (prefixWord ++ tailWord_214072).sum := by decide
  have hdescent : baseEnd_214072 < baseStart_214072 := by decide
  rcases family_descends (prefixWord ++ tailWord_214072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214109 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 6]
def baseStart_214109 : Nat := 118140960795 + 214109 * 2 ^ 59
def prefixEnd_214109 : Nat := 4983230072969 + 3 ^ 40 * 214109 * 2
def baseEnd_214109 : Nat := 12215647717067559028093

theorem tailTrace_214109 : CollatzResearch.WordTrace tailWord_214109 prefixEnd_214109 12215647717067559028093 := by
  unfold tailWord_214109
  simp only [CollatzResearch.WordTrace]
  refine ⟨7809196781327134751069381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5206131187551423167379587 7809196781327134751069381)
  ·
    refine ⟨1464224396498837765825509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7809196781327134751069381 1464224396498837765825509)
    ·
      refine ⟨274542074343532081092283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1464224396498837765825509 274542074343532081092283)
      ·
        refine ⟨411813111515298121638425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274542074343532081092283 411813111515298121638425)
        ·
          refine ⟨308859833636473591228819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411813111515298121638425 308859833636473591228819)
          ·
            refine ⟨463289750454710386843229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308859833636473591228819 463289750454710386843229)
            ·
              refine ⟨173733656420516395066211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463289750454710386843229 173733656420516395066211)
              ·
                refine ⟨260600484630774592599317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173733656420516395066211 260600484630774592599317)
                ·
                  refine ⟨12215647717067559028093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260600484630774592599317 12215647717067559028093)
                  ·
                    rfl

theorem cell23_214109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_214109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214109 prefixEnd_214109 := by exact prefixLift 214109
  have htrace : WordTrace (prefixWord ++ tailWord_214109) baseStart_214109 baseEnd_214109 := by
    simpa [prefixWord, tailWord_214109, baseEnd_214109] using wordTrace_append hprefix tailTrace_214109
  have hstable : (prefixWord ++ tailWord_214109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214109).length < 2 ^ (prefixWord ++ tailWord_214109).sum := by decide
  have hdescent : baseEnd_214109 < baseStart_214109 := by decide
  rcases family_descends (prefixWord ++ tailWord_214109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214122 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_214122 : Nat := 118140960795 + 214122 * 2 ^ 59
def prefixEnd_214122 : Nat := 4983230072969 + 3 ^ 40 * 214122 * 2
def baseEnd_214122 : Nat := 36649168234038826796759

theorem tailTrace_214122 : CollatzResearch.WordTrace tailWord_214122 prefixEnd_214122 36649168234038826796759 := by
  unfold tailWord_214122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952417732570009492823155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5206447286853358647528413 1952417732570009492823155)
  ·
    refine ⟨2928626598855014239234733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1952417732570009492823155 2928626598855014239234733)
    ·
      refine ⟨1098234974570630339713025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2928626598855014239234733 1098234974570630339713025)
      ·
        refine ⟨823676230927972754784769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098234974570630339713025 823676230927972754784769)
        ·
          refine ⟨617757173195979566088577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823676230927972754784769 617757173195979566088577)
          ·
            refine ⟨463317879896984674566433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617757173195979566088577 463317879896984674566433)
            ·
              refine ⟨347488409922738505924825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463317879896984674566433 347488409922738505924825)
              ·
                refine ⟨260616307442053879443619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347488409922738505924825 260616307442053879443619)
                ·
                  refine ⟨390924461163080819165429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260616307442053879443619 390924461163080819165429)
                  ·
                    refine ⟨36649168234038826796759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 390924461163080819165429 36649168234038826796759)
                    ·
                      rfl

theorem cell23_214122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_214122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214122 prefixEnd_214122 := by exact prefixLift 214122
  have htrace : WordTrace (prefixWord ++ tailWord_214122) baseStart_214122 baseEnd_214122 := by
    simpa [prefixWord, tailWord_214122, baseEnd_214122] using wordTrace_append hprefix tailTrace_214122
  have hstable : (prefixWord ++ tailWord_214122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214122).length < 2 ^ (prefixWord ++ tailWord_214122).sum := by decide
  have hdescent : baseEnd_214122 < baseStart_214122 := by decide
  rcases family_descends (prefixWord ++ tailWord_214122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214128 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_214128 : Nat := 118140960795 + 214128 * 2 ^ 59
def prefixEnd_214128 : Nat := 4983230072969 + 3 ^ 40 * 214128 * 2
def baseEnd_214128 : Nat := 109950585586043456915249

theorem tailTrace_214128 : CollatzResearch.WordTrace tailWord_214128 prefixEnd_214128 109950585586043456915249 := by
  unfold tailWord_214128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904944884129150498005519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5206593178838867330674025 3904944884129150498005519)
  ·
    refine ⟨5857417326193725747008279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3904944884129150498005519 5857417326193725747008279)
    ·
      refine ⟨8786125989290588620512419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5857417326193725747008279 8786125989290588620512419)
      ·
        refine ⟨13179188983935882930768629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8786125989290588620512419 13179188983935882930768629)
        ·
          refine ⟨1235548967243989024759559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13179188983935882930768629 1235548967243989024759559)
          ·
            refine ⟨1853323450865983537139339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235548967243989024759559 1853323450865983537139339)
            ·
              refine ⟨2779985176298975305709009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853323450865983537139339 2779985176298975305709009)
              ·
                refine ⟨2084988882224231479281757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779985176298975305709009 2084988882224231479281757)
                ·
                  refine ⟨781870830834086804730659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2084988882224231479281757 781870830834086804730659)
                  ·
                    refine ⟨1172806246251130207095989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 781870830834086804730659 1172806246251130207095989)
                    ·
                      refine ⟨109950585586043456915249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1172806246251130207095989 109950585586043456915249)
                      ·
                        rfl

theorem cell23_214128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_214128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214128 prefixEnd_214128 := by exact prefixLift 214128
  have htrace : WordTrace (prefixWord ++ tailWord_214128) baseStart_214128 baseEnd_214128 := by
    simpa [prefixWord, tailWord_214128, baseEnd_214128] using wordTrace_append hprefix tailTrace_214128
  have hstable : (prefixWord ++ tailWord_214128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214128).length < 2 ^ (prefixWord ++ tailWord_214128).sum := by decide
  have hdescent : baseEnd_214128 < baseStart_214128 := by decide
  rcases family_descends (prefixWord ++ tailWord_214128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214145 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_214145 : Nat := 118140960795 + 214145 * 2 ^ 59
def prefixEnd_214145 : Nat := 4983230072969 + 3 ^ 40 * 214145 * 2
def baseEnd_214145 : Nat := 109959314757169890402671

theorem tailTrace_214145 : CollatzResearch.WordTrace tailWord_214145 prefixEnd_214145 109959314757169890402671 := by
  unfold tailWord_214145
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810509809196712899379889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5207006539464475266253259 7810509809196712899379889)
  ·
    refine ⟨5857882356897534674534917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7810509809196712899379889 5857882356897534674534917)
    ·
      refine ⟨1098352941918287751475297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5857882356897534674534917 1098352941918287751475297)
      ·
        refine ⟨823764706438715813606473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098352941918287751475297 823764706438715813606473)
        ·
          refine ⟨617823529829036860204855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823764706438715813606473 617823529829036860204855)
          ·
            refine ⟨926735294743555290307283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617823529829036860204855 926735294743555290307283)
            ·
              refine ⟨1390102942115332935460925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926735294743555290307283 1390102942115332935460925)
              ·
                refine ⟨521288603293249850797847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1390102942115332935460925 521288603293249850797847)
                ·
                  refine ⟨781932904939874776196771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521288603293249850797847 781932904939874776196771)
                  ·
                    refine ⟨1172899357409812164295157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 781932904939874776196771 1172899357409812164295157)
                    ·
                      refine ⟨109959314757169890402671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1172899357409812164295157 109959314757169890402671)
                      ·
                        rfl

theorem cell23_214145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_214145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214145 prefixEnd_214145 := by exact prefixLift 214145
  have htrace : WordTrace (prefixWord ++ tailWord_214145) baseStart_214145 baseEnd_214145 := by
    simpa [prefixWord, tailWord_214145, baseEnd_214145] using wordTrace_append hprefix tailTrace_214145
  have hstable : (prefixWord ++ tailWord_214145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214145).length < 2 ^ (prefixWord ++ tailWord_214145).sum := by decide
  have hdescent : baseEnd_214145 < baseStart_214145 := by decide
  rcases family_descends (prefixWord ++ tailWord_214145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214148 : List Nat := [2, 3, 2, 1, 2, 2, 11]
def baseStart_214148 : Nat := 118140960795 + 214148 * 2 ^ 59
def prefixEnd_214148 : Nat := 4983230072969 + 3 ^ 40 * 214148 * 2
def baseEnd_214148 : Nat := 1357541422211523193397

theorem tailTrace_214148 : CollatzResearch.WordTrace tailWord_214148 prefixEnd_214148 1357541422211523193397 := by
  unfold tailWord_214148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905309614092922205869549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5207079485457229607826065 3905309614092922205869549)
  ·
    refine ⟨1464491105284845827201081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3905309614092922205869549 1464491105284845827201081)
    ·
      refine ⟨1098368328963634370400811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464491105284845827201081 1098368328963634370400811)
      ·
        refine ⟨1647552493445451555601217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098368328963634370400811 1647552493445451555601217)
        ·
          refine ⟨1235664370084088666700913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647552493445451555601217 1235664370084088666700913)
          ·
            refine ⟨926748277563066500025685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235664370084088666700913 926748277563066500025685)
            ·
              refine ⟨1357541422211523193397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 926748277563066500025685 1357541422211523193397)
              ·
                rfl

theorem cell23_214148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 11].length) (baseStart_214148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214148 prefixEnd_214148 := by exact prefixLift 214148
  have htrace : WordTrace (prefixWord ++ tailWord_214148) baseStart_214148 baseEnd_214148 := by
    simpa [prefixWord, tailWord_214148, baseEnd_214148] using wordTrace_append hprefix tailTrace_214148
  have hstable : (prefixWord ++ tailWord_214148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214148).length < 2 ^ (prefixWord ++ tailWord_214148).sum := by decide
  have hdescent : baseEnd_214148 < baseStart_214148 := by decide
  rcases family_descends (prefixWord ++ tailWord_214148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214188 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_214188 : Nat := 118140960795 + 214188 * 2 ^ 59
def prefixEnd_214188 : Nat := 4983230072969 + 3 ^ 40 * 214188 * 2
def baseEnd_214188 : Nat := 109981394425313222164973

theorem tailTrace_214188 : CollatzResearch.WordTrace tailWord_214188 prefixEnd_214188 109981394425313222164973 := by
  unfold tailWord_214188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906039074020465621597609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5208052098693954162130145 3906039074020465621597609)
  ·
    refine ⟨2929529305515349216198207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3906039074020465621597609 2929529305515349216198207)
    ·
      refine ⟨4394293958273023824297311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929529305515349216198207 4394293958273023824297311)
      ·
        refine ⟨6591440937409535736445967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394293958273023824297311 6591440937409535736445967)
        ·
          refine ⟨9887161406114303604668951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591440937409535736445967 9887161406114303604668951)
          ·
            refine ⟨14830742109171455407003427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9887161406114303604668951 14830742109171455407003427)
            ·
              refine ⟨22246113163757183110505141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14830742109171455407003427 22246113163757183110505141)
              ·
                refine ⟨2085573109102235916609857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22246113163757183110505141 2085573109102235916609857)
                ·
                  refine ⟨1564179831826676937457393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085573109102235916609857 1564179831826676937457393)
                  ·
                    refine ⟨1173134873870007703093045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564179831826676937457393 1173134873870007703093045)
                    ·
                      refine ⟨109981394425313222164973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1173134873870007703093045 109981394425313222164973)
                      ·
                        rfl

theorem cell23_214188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_214188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_214188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_214188 prefixEnd_214188 := by exact prefixLift 214188
  have htrace : WordTrace (prefixWord ++ tailWord_214188) baseStart_214188 baseEnd_214188 := by
    simpa [prefixWord, tailWord_214188, baseEnd_214188] using wordTrace_append hprefix tailTrace_214188
  have hstable : (prefixWord ++ tailWord_214188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214188).length < 2 ^ (prefixWord ++ tailWord_214188).sum := by decide
  have hdescent : baseEnd_214188 < baseStart_214188 := by decide
  rcases family_descends (prefixWord ++ tailWord_214188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
