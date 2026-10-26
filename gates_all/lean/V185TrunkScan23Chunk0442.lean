import V185TrunkScan23Chunk0441

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2612824 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_2612824 : Nat := 118140960795 + 2612824 * 2 ^ 59
def prefixEnd_2612824 : Nat := 4983230072969 + 3 ^ 40 * 2612824 * 2
def baseEnd_2612824 : Nat := 1341634577603190547783847

theorem tailTrace_2612824 : CollatzResearch.WordTrace tailWord_2612824 prefixEnd_2612824 1341634577603190547783847 := by
  unfold tailWord_2612824
  simp only [CollatzResearch.WordTrace]
  refine ⟨47648760143096178828870763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63531680190794905105161017 47648760143096178828870763)
  ·
    refine ⟨71473140214644268243306145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47648760143096178828870763 71473140214644268243306145)
    ·
      refine ⟨53604855160983201182479609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71473140214644268243306145 53604855160983201182479609)
      ·
        refine ⟨40203641370737400886859707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53604855160983201182479609 40203641370737400886859707)
        ·
          refine ⟨60305462056106101330289561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40203641370737400886859707 60305462056106101330289561)
          ·
            refine ⟨45229096542079575997717171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60305462056106101330289561 45229096542079575997717171)
            ·
              refine ⟨67843644813119363996575757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45229096542079575997717171 67843644813119363996575757)
              ·
                refine ⟨25441366804919761498715909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67843644813119363996575757 25441366804919761498715909)
                ·
                  refine ⟨4770256275922455281009233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25441366804919761498715909 4770256275922455281009233)
                  ·
                    refine ⟨3577692206941841460756925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4770256275922455281009233 3577692206941841460756925)
                    ·
                      refine ⟨1341634577603190547783847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3577692206941841460756925 1341634577603190547783847)
                      ·
                        rfl

theorem cell23_2612824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_2612824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612824 prefixEnd_2612824 := by exact prefixLift 2612824
  have htrace : WordTrace (prefixWord ++ tailWord_2612824) baseStart_2612824 baseEnd_2612824 := by
    simpa [prefixWord, tailWord_2612824, baseEnd_2612824] using wordTrace_append hprefix tailTrace_2612824
  have hstable : (prefixWord ++ tailWord_2612824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612824).length < 2 ^ (prefixWord ++ tailWord_2612824).sum := by decide
  have hdescent : baseEnd_2612824 < baseStart_2612824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612847 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_2612847 : Nat := 118140960795 + 2612847 * 2 ^ 59
def prefixEnd_2612847 : Nat := 4983230072969 + 3 ^ 40 * 2612847 * 2
def baseEnd_2612847 : Nat := 1341646387658243957796241

theorem tailTrace_2612847 : CollatzResearch.WordTrace tailWord_2612847 prefixEnd_2612847 1341646387658243957796241 := by
  unfold tailWord_2612847
  simp only [CollatzResearch.WordTrace]
  refine ⟨95298359165109032585828795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63532239443406021723885863 95298359165109032585828795)
  ·
    refine ⟨142947538747663548878743193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95298359165109032585828795 142947538747663548878743193)
    ·
      refine ⟨107210654060747661659057395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142947538747663548878743193 107210654060747661659057395)
      ·
        refine ⟨160815981091121492488586093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107210654060747661659057395 160815981091121492488586093)
        ·
          refine ⟨60305992909170559683219785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160815981091121492488586093 60305992909170559683219785)
          ·
            refine ⟨45229494681877919762414839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60305992909170559683219785 45229494681877919762414839)
            ·
              refine ⟨67844242022816879643622259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45229494681877919762414839 67844242022816879643622259)
              ·
                refine ⟨101766363034225319465433389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67844242022816879643622259 101766363034225319465433389)
                ·
                  refine ⟨38162386137834494799537521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101766363034225319465433389 38162386137834494799537521)
                  ·
                    refine ⟨28621789603375871099653141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38162386137834494799537521 28621789603375871099653141)
                    ·
                      refine ⟨1341646387658243957796241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28621789603375871099653141 1341646387658243957796241)
                      ·
                        rfl

theorem cell23_2612847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_2612847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612847 prefixEnd_2612847 := by exact prefixLift 2612847
  have htrace : WordTrace (prefixWord ++ tailWord_2612847) baseStart_2612847 baseEnd_2612847 := by
    simpa [prefixWord, tailWord_2612847, baseEnd_2612847] using wordTrace_append hprefix tailTrace_2612847
  have hstable : (prefixWord ++ tailWord_2612847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612847).length < 2 ^ (prefixWord ++ tailWord_2612847).sum := by decide
  have hdescent : baseEnd_2612847 < baseStart_2612847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612865 : List Nat := [1, 2, 4, 2, 1, 4, 1, 3, 1, 4]
def baseStart_2612865 : Nat := 118140960795 + 2612865 * 2 ^ 59
def prefixEnd_2612865 : Nat := 4983230072969 + 3 ^ 40 * 2612865 * 2
def baseEnd_2612865 : Nat := 447218543436674962457053

theorem tailTrace_2612865 : CollatzResearch.WordTrace tailWord_2612865 prefixEnd_2612865 447218543436674962457053 := by
  unfold tailWord_2612865
  simp only [CollatzResearch.WordTrace]
  refine ⟨95299015679043821659984049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63532677119362547773322699 95299015679043821659984049)
  ·
    refine ⟨71474261759282866244988037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95299015679043821659984049 71474261759282866244988037)
    ·
      refine ⟨13401424079865537420935257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71474261759282866244988037 13401424079865537420935257)
      ·
        refine ⟨10051068059899153065701443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13401424079865537420935257 10051068059899153065701443)
        ·
          refine ⟨15076602089848729598552165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10051068059899153065701443 15076602089848729598552165)
          ·
            refine ⟨2826862891846636799728531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15076602089848729598552165 2826862891846636799728531)
            ·
              refine ⟨4240294337769955199592797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826862891846636799728531 4240294337769955199592797)
              ·
                refine ⟨1590110376663733199847299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4240294337769955199592797 1590110376663733199847299)
                ·
                  refine ⟨2385165564995599799770949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590110376663733199847299 2385165564995599799770949)
                  ·
                    refine ⟨447218543436674962457053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2385165564995599799770949 447218543436674962457053)
                    ·
                      rfl

theorem cell23_2612865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_2612865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612865 prefixEnd_2612865 := by exact prefixLift 2612865
  have htrace : WordTrace (prefixWord ++ tailWord_2612865) baseStart_2612865 baseEnd_2612865 := by
    simpa [prefixWord, tailWord_2612865, baseEnd_2612865] using wordTrace_append hprefix tailTrace_2612865
  have hstable : (prefixWord ++ tailWord_2612865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612865).length < 2 ^ (prefixWord ++ tailWord_2612865).sum := by decide
  have hdescent : baseEnd_2612865 < baseStart_2612865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612882 : List Nat := [3, 2, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_2612882 : Nat := 118140960795 + 2612882 * 2 ^ 59
def prefixEnd_2612882 : Nat := 4983230072969 + 3 ^ 40 * 2612882 * 2
def baseEnd_2612882 : Nat := 447221453160383773619527

theorem tailTrace_2612882 : CollatzResearch.WordTrace tailWord_2612882 prefixEnd_2612882 447221453160383773619527 := by
  unfold tailWord_2612882
  simp only [CollatzResearch.WordTrace]
  refine ⟨23824908929995558390838225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63533090479988155708901933 23824908929995558390838225)
  ·
    refine ⟨17868681697496668793128669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23824908929995558390838225 17868681697496668793128669)
    ·
      refine ⟨6700755636561250797423251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17868681697496668793128669 6700755636561250797423251)
      ·
        refine ⟨10051133454841876196134877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6700755636561250797423251 10051133454841876196134877)
        ·
          refine ⟨3769175045565703573550579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10051133454841876196134877 3769175045565703573550579)
          ·
            refine ⟨5653762568348555360325869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769175045565703573550579 5653762568348555360325869)
            ·
              refine ⟨2120160963130708260122201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5653762568348555360325869 2120160963130708260122201)
              ·
                refine ⟨1590120722348031195091651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2120160963130708260122201 1590120722348031195091651)
                ·
                  refine ⟨2385181083522046792637477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590120722348031195091651 2385181083522046792637477)
                  ·
                    refine ⟨447221453160383773619527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2385181083522046792637477 447221453160383773619527)
                    ·
                      rfl

theorem cell23_2612882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_2612882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612882 prefixEnd_2612882 := by exact prefixLift 2612882
  have htrace : WordTrace (prefixWord ++ tailWord_2612882) baseStart_2612882 baseEnd_2612882 := by
    simpa [prefixWord, tailWord_2612882, baseEnd_2612882] using wordTrace_append hprefix tailTrace_2612882
  have hstable : (prefixWord ++ tailWord_2612882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612882).length < 2 ^ (prefixWord ++ tailWord_2612882).sum := by decide
  have hdescent : baseEnd_2612882 < baseStart_2612882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612888 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2612888 : Nat := 118140960795 + 2612888 * 2 ^ 59
def prefixEnd_2612888 : Nat := 4983230072969 + 3 ^ 40 * 2612888 * 2
def baseEnd_2612888 : Nat := 1341667440365078297383553

theorem tailTrace_2612888 : CollatzResearch.WordTrace tailWord_2612888 prefixEnd_2612888 1341667440365078297383553 := by
  unfold tailWord_2612888
  simp only [CollatzResearch.WordTrace]
  refine ⟨47649927278980248294035659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63533236371973664392047545 47649927278980248294035659)
  ·
    refine ⟨71474890918470372441053489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47649927278980248294035659 71474890918470372441053489)
    ·
      refine ⟨53606168188852779330790117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71474890918470372441053489 53606168188852779330790117)
      ·
        refine ⟨10051156535409896124523147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53606168188852779330790117 10051156535409896124523147)
        ·
          refine ⟨15076734803114844186784721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10051156535409896124523147 15076734803114844186784721)
          ·
            refine ⟨11307551102336133140088541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15076734803114844186784721 11307551102336133140088541)
            ·
              refine ⟨4240331663376049927533203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11307551102336133140088541 4240331663376049927533203)
              ·
                refine ⟨6360497495064074891299805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4240331663376049927533203 6360497495064074891299805)
                ·
                  refine ⟨2385186560649028084237427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6360497495064074891299805 2385186560649028084237427)
                  ·
                    refine ⟨3577779840973542126356141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2385186560649028084237427 3577779840973542126356141)
                    ·
                      refine ⟨1341667440365078297383553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3577779840973542126356141 1341667440365078297383553)
                      ·
                        rfl

theorem cell23_2612888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2612888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612888 prefixEnd_2612888 := by exact prefixLift 2612888
  have htrace : WordTrace (prefixWord ++ tailWord_2612888) baseStart_2612888 baseEnd_2612888 := by
    simpa [prefixWord, tailWord_2612888, baseEnd_2612888] using wordTrace_append hprefix tailTrace_2612888
  have hstable : (prefixWord ++ tailWord_2612888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612888).length < 2 ^ (prefixWord ++ tailWord_2612888).sum := by decide
  have hdescent : baseEnd_2612888 < baseStart_2612888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612895 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 6]
def baseStart_2612895 : Nat := 118140960795 + 2612895 * 2 ^ 59
def prefixEnd_2612895 : Nat := 4983230072969 + 3 ^ 40 * 2612895 * 2
def baseEnd_2612895 : Nat := 149074559414406641110669

theorem tailTrace_2612895 : CollatzResearch.WordTrace tailWord_2612895 prefixEnd_2612895 149074559414406641110669 := by
  unfold tailWord_2612895
  simp only [CollatzResearch.WordTrace]
  refine ⟨95300109868935136783576139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63533406579290091189050759 95300109868935136783576139)
  ·
    refine ⟨142950164803402705175364209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95300109868935136783576139 142950164803402705175364209)
    ·
      refine ⟨107212623602552028881523157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142950164803402705175364209 107212623602552028881523157)
      ·
        refine ⟨2512795865684813176910699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 107212623602552028881523157 2512795865684813176910699)
        ·
          refine ⟨3769193798527219765366049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512795865684813176910699 3769193798527219765366049)
          ·
            refine ⟨2826895348895414824024537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3769193798527219765366049 2826895348895414824024537)
            ·
              refine ⟨2120171511671561118018403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2826895348895414824024537 2120171511671561118018403)
              ·
                refine ⟨3180257267507341677027605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120171511671561118018403 3180257267507341677027605)
                ·
                  refine ⟨149074559414406641110669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3180257267507341677027605 149074559414406641110669)
                  ·
                    rfl

theorem cell23_2612895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 6].length) (baseStart_2612895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612895 prefixEnd_2612895 := by exact prefixLift 2612895
  have htrace : WordTrace (prefixWord ++ tailWord_2612895) baseStart_2612895 baseEnd_2612895 := by
    simpa [prefixWord, tailWord_2612895, baseEnd_2612895] using wordTrace_append hprefix tailTrace_2612895
  have hstable : (prefixWord ++ tailWord_2612895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612895).length < 2 ^ (prefixWord ++ tailWord_2612895).sum := by decide
  have hdescent : baseEnd_2612895 < baseStart_2612895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612914 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2612914 : Nat := 118140960795 + 2612914 * 2 ^ 59
def prefixEnd_2612914 : Nat := 4983230072969 + 3 ^ 40 * 2612914 * 2
def baseEnd_2612914 : Nat := 1341680790862095195658433

theorem tailTrace_2612914 : CollatzResearch.WordTrace tailWord_2612914 prefixEnd_2612914 1341680790862095195658433 := by
  unfold tailWord_2612914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23825200713966575757129449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63533868570577535352345197 23825200713966575757129449)
  ·
    refine ⟨17868900535474931817847087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23825200713966575757129449 17868900535474931817847087)
    ·
      refine ⟨26803350803212397726770631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17868900535474931817847087 26803350803212397726770631)
      ·
        refine ⟨40205026204818596590155947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26803350803212397726770631 40205026204818596590155947)
        ·
          refine ⟨60307539307227894885233921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40205026204818596590155947 60307539307227894885233921)
          ·
            refine ⟨45230654480420921163925441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60307539307227894885233921 45230654480420921163925441)
            ·
              refine ⟨33922990860315690872944081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45230654480420921163925441 33922990860315690872944081)
              ·
                refine ⟨25442243145236768154708061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33922990860315690872944081 25442243145236768154708061)
                ·
                  refine ⟨9540841179463788058015523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25442243145236768154708061 9540841179463788058015523)
                  ·
                    refine ⟨14311261769195682087023285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9540841179463788058015523 14311261769195682087023285)
                    ·
                      refine ⟨1341680790862095195658433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14311261769195682087023285 1341680790862095195658433)
                      ·
                        rfl

theorem cell23_2612914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2612914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612914 prefixEnd_2612914 := by exact prefixLift 2612914
  have htrace : WordTrace (prefixWord ++ tailWord_2612914) baseStart_2612914 baseEnd_2612914 := by
    simpa [prefixWord, tailWord_2612914, baseEnd_2612914] using wordTrace_append hprefix tailTrace_2612914
  have hstable : (prefixWord ++ tailWord_2612914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612914).length < 2 ^ (prefixWord ++ tailWord_2612914).sum := by decide
  have hdescent : baseEnd_2612914 < baseStart_2612914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612928 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 1, 1, 4]
def baseStart_2612928 : Nat := 118140960795 + 2612928 * 2 ^ 59
def prefixEnd_2612928 : Nat := 4983230072969 + 3 ^ 40 * 2612928 * 2
def baseEnd_2612928 : Nat := 1341687979591258140883369

theorem tailTrace_2612928 : CollatzResearch.WordTrace tailWord_2612928 prefixEnd_2612928 1341687979591258140883369 := by
  unfold tailWord_2612928
  simp only [CollatzResearch.WordTrace]
  refine ⟨47650656738907791709763719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63534208985210388946351625 47650656738907791709763719)
  ·
    refine ⟨71475985108361687564645579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47650656738907791709763719 71475985108361687564645579)
    ·
      refine ⟨107213977662542531346968369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71475985108361687564645579 107213977662542531346968369)
      ·
        refine ⟨80410483246906898510226277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107213977662542531346968369 80410483246906898510226277)
        ·
          refine ⟨15076965608795043470667427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80410483246906898510226277 15076965608795043470667427)
          ·
            refine ⟨22615448413192565206001141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15076965608795043470667427 22615448413192565206001141)
            ·
              refine ⟨2120198288736802988062607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22615448413192565206001141 2120198288736802988062607)
              ·
                refine ⟨3180297433105204482093911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120198288736802988062607 3180297433105204482093911)
                ·
                  refine ⟨4770446149657806723140867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180297433105204482093911 4770446149657806723140867)
                  ·
                    refine ⟨7155669224486710084711301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770446149657806723140867 7155669224486710084711301)
                    ·
                      refine ⟨1341687979591258140883369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7155669224486710084711301 1341687979591258140883369)
                      ·
                        rfl

theorem cell23_2612928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_2612928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612928 prefixEnd_2612928 := by exact prefixLift 2612928
  have htrace : WordTrace (prefixWord ++ tailWord_2612928) baseStart_2612928 baseEnd_2612928 := by
    simpa [prefixWord, tailWord_2612928, baseEnd_2612928] using wordTrace_append hprefix tailTrace_2612928
  have hstable : (prefixWord ++ tailWord_2612928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612928).length < 2 ^ (prefixWord ++ tailWord_2612928).sum := by decide
  have hdescent : baseEnd_2612928 < baseStart_2612928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612948 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2612948 : Nat := 118140960795 + 2612948 * 2 ^ 59
def prefixEnd_2612948 : Nat := 4983230072969 + 3 ^ 40 * 2612948 * 2
def baseEnd_2612948 : Nat := 1341698249204348062633277

theorem tailTrace_2612948 : CollatzResearch.WordTrace tailWord_2612948 prefixEnd_2612948 1341698249204348062633277 := by
  unfold tailWord_2612948
  simp only [CollatzResearch.WordTrace]
  refine ⟨47651021468871563417627749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63534695291828751223503665 47651021468871563417627749)
  ·
    refine ⟨8934566525413418140805203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47651021468871563417627749 8934566525413418140805203)
    ·
      refine ⟨13401849788120127211207805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8934566525413418140805203 13401849788120127211207805)
      ·
        refine ⟨5025693670545047704202927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13401849788120127211207805 5025693670545047704202927)
        ·
          refine ⟨7538540505817571556304391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5025693670545047704202927 7538540505817571556304391)
          ·
            refine ⟨11307810758726357334456587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7538540505817571556304391 11307810758726357334456587)
            ·
              refine ⟨16961716138089536001684881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11307810758726357334456587 16961716138089536001684881)
              ·
                refine ⟨12721287103567152001263661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16961716138089536001684881 12721287103567152001263661)
                ·
                  refine ⟨4770482663837682000473873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12721287103567152001263661 4770482663837682000473873)
                  ·
                    refine ⟨3577861997878261500355405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4770482663837682000473873 3577861997878261500355405)
                    ·
                      refine ⟨1341698249204348062633277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3577861997878261500355405 1341698249204348062633277)
                      ·
                        rfl

theorem cell23_2612948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2612948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612948 prefixEnd_2612948 := by exact prefixLift 2612948
  have htrace : WordTrace (prefixWord ++ tailWord_2612948) baseStart_2612948 baseEnd_2612948 := by
    simpa [prefixWord, tailWord_2612948, baseEnd_2612948] using wordTrace_append hprefix tailTrace_2612948
  have hstable : (prefixWord ++ tailWord_2612948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612948).length < 2 ^ (prefixWord ++ tailWord_2612948).sum := by decide
  have hdescent : baseEnd_2612948 < baseStart_2612948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612964 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_2612964 : Nat := 118140960795 + 2612964 * 2 ^ 59
def prefixEnd_2612964 : Nat := 4983230072969 + 3 ^ 40 * 2612964 * 2
def baseEnd_2612964 : Nat := 447235488298273333344401

theorem tailTrace_2612964 : CollatzResearch.WordTrace tailWord_2612964 prefixEnd_2612964 447235488298273333344401 := by
  unfold tailWord_2612964
  simp only [CollatzResearch.WordTrace]
  refine ⟨47651313252842580783918973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63535084337123441045225297 47651313252842580783918973)
  ·
    refine ⟨17869242469815967793969615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47651313252842580783918973 17869242469815967793969615)
    ·
      refine ⟨26803863704723951690954423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17869242469815967793969615 26803863704723951690954423)
      ·
        refine ⟨40205795557085927536431635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26803863704723951690954423 40205795557085927536431635)
        ·
          refine ⟨60308693335628891304647453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40205795557085927536431635 60308693335628891304647453)
          ·
            refine ⟨22615760000860834239242795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60308693335628891304647453 22615760000860834239242795)
            ·
              refine ⟨33923640001291251358864193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22615760000860834239242795 33923640001291251358864193)
              ·
                refine ⟨25442730000968438519148145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33923640001291251358864193 25442730000968438519148145)
                ·
                  refine ⟨19082047500726328889361109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25442730000968438519148145 19082047500726328889361109)
                  ·
                    refine ⟨447235488298273333344401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19082047500726328889361109 447235488298273333344401)
                    ·
                      rfl

theorem cell23_2612964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_2612964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612964 prefixEnd_2612964 := by exact prefixLift 2612964
  have htrace : WordTrace (prefixWord ++ tailWord_2612964) baseStart_2612964 baseEnd_2612964 := by
    simpa [prefixWord, tailWord_2612964, baseEnd_2612964] using wordTrace_append hprefix tailTrace_2612964
  have hstable : (prefixWord ++ tailWord_2612964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612964).length < 2 ^ (prefixWord ++ tailWord_2612964).sum := by decide
  have hdescent : baseEnd_2612964 < baseStart_2612964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612978 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2612978 : Nat := 118140960795 + 2612978 * 2 ^ 59
def prefixEnd_2612978 : Nat := 4983230072969 + 3 ^ 40 * 2612978 * 2
def baseEnd_2612978 : Nat := 1341713653623982945258139

theorem tailTrace_2612978 : CollatzResearch.WordTrace tailWord_2612978 prefixEnd_2612978 1341713653623982945258139 := by
  unfold tailWord_2612978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23825784281908610489711897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63535424751756294639231725 23825784281908610489711897)
  ·
    refine ⟨17869338211431457867283923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23825784281908610489711897 17869338211431457867283923)
    ·
      refine ⟨26804007317147186800925885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17869338211431457867283923 26804007317147186800925885)
      ·
        refine ⟨10051502743930195050347207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26804007317147186800925885 10051502743930195050347207)
        ·
          refine ⟨15077254115895292575520811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10051502743930195050347207 15077254115895292575520811)
          ·
            refine ⟨22615881173842938863281217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15077254115895292575520811 22615881173842938863281217)
            ·
              refine ⟨16961910880382204147460913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22615881173842938863281217 16961910880382204147460913)
              ·
                refine ⟨12721433160286653110595685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16961910880382204147460913 12721433160286653110595685)
                ·
                  refine ⟨2385268717553747458236691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12721433160286653110595685 2385268717553747458236691)
                  ·
                    refine ⟨3577903076330621187355037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2385268717553747458236691 3577903076330621187355037)
                    ·
                      refine ⟨1341713653623982945258139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3577903076330621187355037 1341713653623982945258139)
                      ·
                        rfl

theorem cell23_2612978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2612978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612978 prefixEnd_2612978 := by exact prefixLift 2612978
  have htrace : WordTrace (prefixWord ++ tailWord_2612978) baseStart_2612978 baseEnd_2612978 := by
    simpa [prefixWord, tailWord_2612978, baseEnd_2612978] using wordTrace_append hprefix tailTrace_2612978
  have hstable : (prefixWord ++ tailWord_2612978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612978).length < 2 ^ (prefixWord ++ tailWord_2612978).sum := by decide
  have hdescent : baseEnd_2612978 < baseStart_2612978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612982 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_2612982 : Nat := 118140960795 + 2612982 * 2 ^ 59
def prefixEnd_2612982 : Nat := 4983230072969 + 3 ^ 40 * 2612982 * 2
def baseEnd_2612982 : Nat := 1341715707546600929608121

theorem tailTrace_2612982 : CollatzResearch.WordTrace tailWord_2612982 prefixEnd_2612982 1341715707546600929608121 := by
  unfold tailWord_2612982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956455188726246915124575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63535522013079967094662133 5956455188726246915124575)
  ·
    refine ⟨8934682783089370372686863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5956455188726246915124575 8934682783089370372686863)
    ·
      refine ⟨13402024174634055559030295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8934682783089370372686863 13402024174634055559030295)
      ·
        refine ⟨20103036261951083338545443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13402024174634055559030295 20103036261951083338545443)
        ·
          refine ⟨30154554392926625007818165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20103036261951083338545443 30154554392926625007818165)
          ·
            refine ⟨2826989474336871094482953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30154554392926625007818165 2826989474336871094482953)
            ·
              refine ⟨2120242105752653320862215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2826989474336871094482953 2120242105752653320862215)
              ·
                refine ⟨3180363158628979981293323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120242105752653320862215 3180363158628979981293323)
                ·
                  refine ⟨4770544737943469971939985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180363158628979981293323 4770544737943469971939985)
                  ·
                    refine ⟨3577908553457602478954989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4770544737943469971939985 3577908553457602478954989)
                    ·
                      refine ⟨1341715707546600929608121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3577908553457602478954989 1341715707546600929608121)
                      ·
                        rfl

theorem cell23_2612982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_2612982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612982 prefixEnd_2612982 := by exact prefixLift 2612982
  have htrace : WordTrace (prefixWord ++ tailWord_2612982) baseStart_2612982 baseEnd_2612982 := by
    simpa [prefixWord, tailWord_2612982, baseEnd_2612982] using wordTrace_append hprefix tailTrace_2612982
  have hstable : (prefixWord ++ tailWord_2612982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612982).length < 2 ^ (prefixWord ++ tailWord_2612982).sum := by decide
  have hdescent : baseEnd_2612982 < baseStart_2612982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612984 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_2612984 : Nat := 118140960795 + 2612984 * 2 ^ 59
def prefixEnd_2612984 : Nat := 4983230072969 + 3 ^ 40 * 2612984 * 2
def baseEnd_2612984 : Nat := 1341716734507909921783111

theorem tailTrace_2612984 : CollatzResearch.WordTrace tailWord_2612984 prefixEnd_2612984 1341716734507909921783111 := by
  unfold tailWord_2612984
  simp only [CollatzResearch.WordTrace]
  refine ⟨47651677982806352491783003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63535570643741803322377337 47651677982806352491783003)
  ·
    refine ⟨71477516974209528737674505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47651677982806352491783003 71477516974209528737674505)
    ·
      refine ⟨53608137730657146553255879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71477516974209528737674505 53608137730657146553255879)
      ·
        refine ⟨80412206595985719829883819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53608137730657146553255879 80412206595985719829883819)
        ·
          refine ⟨120618309893978579744825729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80412206595985719829883819 120618309893978579744825729)
          ·
            refine ⟨90463732420483934808619297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120618309893978579744825729 90463732420483934808619297)
            ·
              refine ⟨67847799315362951106464473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90463732420483934808619297 67847799315362951106464473)
              ·
                refine ⟨50885849486522213329848355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67847799315362951106464473 50885849486522213329848355)
                ·
                  refine ⟨76328774229783319994772533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50885849486522213329848355 76328774229783319994772533)
                  ·
                    refine ⟨7155822584042186249509925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76328774229783319994772533 7155822584042186249509925)
                    ·
                      refine ⟨1341716734507909921783111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7155822584042186249509925 1341716734507909921783111)
                      ·
                        rfl

theorem cell23_2612984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_2612984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612984 prefixEnd_2612984 := by exact prefixLift 2612984
  have htrace : WordTrace (prefixWord ++ tailWord_2612984) baseStart_2612984 baseEnd_2612984 := by
    simpa [prefixWord, tailWord_2612984, baseEnd_2612984] using wordTrace_append hprefix tailTrace_2612984
  have hstable : (prefixWord ++ tailWord_2612984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612984).length < 2 ^ (prefixWord ++ tailWord_2612984).sum := by decide
  have hdescent : baseEnd_2612984 < baseStart_2612984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613069 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2613069 : Nat := 118140960795 + 2613069 * 2 ^ 59
def prefixEnd_2613069 : Nat := 4983230072969 + 3 ^ 40 * 2613069 * 2
def baseEnd_2613069 : Nat := 1341760380363542089220221

theorem tailTrace_2613069 : CollatzResearch.WordTrace tailWord_2613069 prefixEnd_2613069 1341760380363542089220221 := by
  unfold tailWord_2613069
  simp only [CollatzResearch.WordTrace]
  refine ⟨95306456170304764500410261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63537637446869843000273507 95306456170304764500410261)
  ·
    refine ⟨4467490132983035835956731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95306456170304764500410261 4467490132983035835956731)
    ·
      refine ⟨6701235199474553753935097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4467490132983035835956731 6701235199474553753935097)
      ·
        refine ⟨5025926399605915315451323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6701235199474553753935097 5025926399605915315451323)
        ·
          refine ⟨7538889599408872973176985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5025926399605915315451323 7538889599408872973176985)
          ·
            refine ⟨5654167199556654729882739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7538889599408872973176985 5654167199556654729882739)
            ·
              refine ⟨8481250799334982094824109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5654167199556654729882739 8481250799334982094824109)
              ·
                refine ⟨3180469049750618285559041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8481250799334982094824109 3180469049750618285559041)
                ·
                  refine ⟨2385351787312963714169281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3180469049750618285559041 2385351787312963714169281)
                  ·
                    refine ⟨1789013840484722785626961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385351787312963714169281 1789013840484722785626961)
                    ·
                      refine ⟨1341760380363542089220221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789013840484722785626961 1341760380363542089220221)
                      ·
                        rfl

theorem cell23_2613069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2613069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613069 prefixEnd_2613069 := by exact prefixLift 2613069
  have htrace : WordTrace (prefixWord ++ tailWord_2613069) baseStart_2613069 baseEnd_2613069 := by
    simpa [prefixWord, tailWord_2613069, baseEnd_2613069] using wordTrace_append hprefix tailTrace_2613069
  have hstable : (prefixWord ++ tailWord_2613069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613069).length < 2 ^ (prefixWord ++ tailWord_2613069).sum := by decide
  have hdescent : baseEnd_2613069 < baseStart_2613069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613088 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 2, 5]
def baseStart_2613088 : Nat := 118140960795 + 2613088 * 2 ^ 59
def prefixEnd_2613088 : Nat := 4983230072969 + 3 ^ 40 * 2613088 * 2
def baseEnd_2613088 : Nat := 447256712165325838294211

theorem tailTrace_2613088 : CollatzResearch.WordTrace tailWord_2613088 prefixEnd_2613088 447256712165325838294211 := by
  unfold tailWord_2613088
  simp only [CollatzResearch.WordTrace]
  refine ⟨47653574578617965372675959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63538099438157287163567945 47653574578617965372675959)
  ·
    refine ⟨71480361867926948059013939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47653574578617965372675959 71480361867926948059013939)
    ·
      refine ⟨107220542801890422088520909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71480361867926948059013939 107220542801890422088520909)
      ·
        refine ⟨40207703550708908283195341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107220542801890422088520909 40207703550708908283195341)
        ·
          refine ⟨15077888831515840606198253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40207703550708908283195341 15077888831515840606198253)
          ·
            refine ⟨5654208311818440227324345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15077888831515840606198253 5654208311818440227324345)
            ·
              refine ⟨4240656233863830170493259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5654208311818440227324345 4240656233863830170493259)
              ·
                refine ⟨6360984350795745255739889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4240656233863830170493259 6360984350795745255739889)
                ·
                  refine ⟨4770738263096808941804917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6360984350795745255739889 4770738263096808941804917)
                  ·
                    refine ⟨447256712165325838294211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4770738263096808941804917 447256712165325838294211)
                    ·
                      rfl

theorem cell23_2613088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_2613088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613088 prefixEnd_2613088 := by exact prefixLift 2613088
  have htrace : WordTrace (prefixWord ++ tailWord_2613088) baseStart_2613088 baseEnd_2613088 := by
    simpa [prefixWord, tailWord_2613088, baseEnd_2613088] using wordTrace_append hprefix tailTrace_2613088
  have hstable : (prefixWord ++ tailWord_2613088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613088).length < 2 ^ (prefixWord ++ tailWord_2613088).sum := by decide
  have hdescent : baseEnd_2613088 < baseStart_2613088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613111 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_2613111 : Nat := 118140960795 + 2613111 * 2 ^ 59
def prefixEnd_2613111 : Nat := 4983230072969 + 3 ^ 40 * 2613111 * 2
def baseEnd_2613111 : Nat := 1341781946551030924895027

theorem tailTrace_2613111 : CollatzResearch.WordTrace tailWord_2613111 prefixEnd_2613111 1341781946551030924895027 := by
  unfold tailWord_2613111
  simp only [CollatzResearch.WordTrace]
  refine ⟨95307988036152605673439187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63538658690768403782292791 95307988036152605673439187)
  ·
    refine ⟨142961982054228908510158781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95307988036152605673439187 142961982054228908510158781)
    ·
      refine ⟨53610743270335840691309543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142961982054228908510158781 53610743270335840691309543)
      ·
        refine ⟨80416114905503761036964315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53610743270335840691309543 80416114905503761036964315)
        ·
          refine ⟨120624172358255641555446473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80416114905503761036964315 120624172358255641555446473)
          ·
            refine ⟨90468129268691731166584855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120624172358255641555446473 90468129268691731166584855)
            ·
              refine ⟨135702193903037596749877283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90468129268691731166584855 135702193903037596749877283)
              ·
                refine ⟨203553290854556395124815925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135702193903037596749877283 203553290854556395124815925)
                ·
                  refine ⟨19083121017614662042951493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203553290854556395124815925 19083121017614662042951493)
                  ·
                    refine ⟨3578085190802749133053405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19083121017614662042951493 3578085190802749133053405)
                    ·
                      refine ⟨1341781946551030924895027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3578085190802749133053405 1341781946551030924895027)
                      ·
                        rfl

theorem cell23_2613111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_2613111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613111 prefixEnd_2613111 := by exact prefixLift 2613111
  have htrace : WordTrace (prefixWord ++ tailWord_2613111) baseStart_2613111 baseEnd_2613111 := by
    simpa [prefixWord, tailWord_2613111, baseEnd_2613111] using wordTrace_append hprefix tailTrace_2613111
  have hstable : (prefixWord ++ tailWord_2613111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613111).length < 2 ^ (prefixWord ++ tailWord_2613111).sum := by decide
  have hdescent : baseEnd_2613111 < baseStart_2613111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613161 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 5, 5]
def baseStart_2613161 : Nat := 118140960795 + 2613161 * 2 ^ 59
def prefixEnd_2613161 : Nat := 4983230072969 + 3 ^ 40 * 2613161 * 2
def baseEnd_2613161 : Nat := 447269206861251909756599

theorem tailTrace_2613161 : CollatzResearch.WordTrace tailWord_2613161 prefixEnd_2613161 447269206861251909756599 := by
  unfold tailWord_2613161
  simp only [CollatzResearch.WordTrace]
  refine ⟨95309811685971464212759337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63539874457314309475172891 95309811685971464212759337)
  ·
    refine ⟨71482358764478598159569503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95309811685971464212759337 71482358764478598159569503)
    ·
      refine ⟨107223538146717897239354255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71482358764478598159569503 107223538146717897239354255)
      ·
        refine ⟨160835307220076845859031383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107223538146717897239354255 160835307220076845859031383)
        ·
          refine ⟨241252960830115268788547075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160835307220076845859031383 241252960830115268788547075)
          ·
            refine ⟨361879441245172903182820613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241252960830115268788547075 361879441245172903182820613)
            ·
              refine ⟨67852395233469919346778865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 361879441245172903182820613 67852395233469919346778865)
              ·
                refine ⟨50889296425102439510084149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67852395233469919346778865 50889296425102439510084149)
                ·
                  refine ⟨4770871539853353704070389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50889296425102439510084149 4770871539853353704070389)
                  ·
                    refine ⟨447269206861251909756599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4770871539853353704070389 447269206861251909756599)
                    ·
                      rfl

theorem cell23_2613161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_2613161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613161 prefixEnd_2613161 := by exact prefixLift 2613161
  have htrace : WordTrace (prefixWord ++ tailWord_2613161) baseStart_2613161 baseEnd_2613161 := by
    simpa [prefixWord, tailWord_2613161, baseEnd_2613161] using wordTrace_append hprefix tailTrace_2613161
  have hstable : (prefixWord ++ tailWord_2613161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613161).length < 2 ^ (prefixWord ++ tailWord_2613161).sum := by decide
  have hdescent : baseEnd_2613161 < baseStart_2613161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613208 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 6, 4]
def baseStart_2613208 : Nat := 118140960795 + 2613208 * 2 ^ 59
def prefixEnd_2613208 : Nat := 4983230072969 + 3 ^ 40 * 2613208 * 2
def baseEnd_2613208 : Nat := 447277251391505681794027

theorem tailTrace_2613208 : CollatzResearch.WordTrace tailWord_2613208 prefixEnd_2613208 447277251391505681794027 := by
  unfold tailWord_2613208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47655762958400595619860139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63541017277867460826480185 47655762958400595619860139)
  ·
    refine ⟨71483644437600893429790209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47655762958400595619860139 71483644437600893429790209)
    ·
      refine ⟨53612733328200670072342657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71483644437600893429790209 53612733328200670072342657)
      ·
        refine ⟨40209549996150502554256993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53612733328200670072342657 40209549996150502554256993)
        ·
          refine ⟨30157162497112876915692745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40209549996150502554256993 30157162497112876915692745)
          ·
            refine ⟨22617871872834657686769559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30157162497112876915692745 22617871872834657686769559)
            ·
              refine ⟨33926807809251986530154339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22617871872834657686769559 33926807809251986530154339)
              ·
                refine ⟨50890211713877979795231509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33926807809251986530154339 50890211713877979795231509)
                ·
                  refine ⟨2385478674088030302901477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50890211713877979795231509 2385478674088030302901477)
                  ·
                    refine ⟨447277251391505681794027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2385478674088030302901477 447277251391505681794027)
                    ·
                      rfl

theorem cell23_2613208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_2613208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613208 prefixEnd_2613208 := by exact prefixLift 2613208
  have htrace : WordTrace (prefixWord ++ tailWord_2613208) baseStart_2613208 baseEnd_2613208 := by
    simpa [prefixWord, tailWord_2613208, baseEnd_2613208] using wordTrace_append hprefix tailTrace_2613208
  have hstable : (prefixWord ++ tailWord_2613208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613208).length < 2 ^ (prefixWord ++ tailWord_2613208).sum := by decide
  have hdescent : baseEnd_2613208 < baseStart_2613208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613215 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 4]
def baseStart_2613215 : Nat := 118140960795 + 2613215 * 2 ^ 59
def prefixEnd_2613215 : Nat := 4983230072969 + 3 ^ 40 * 2613215 * 2
def baseEnd_2613215 : Nat := 1341835348539098517994549

theorem tailTrace_2613215 : CollatzResearch.WordTrace tailWord_2613215 prefixEnd_2613215 1341835348539098517994549 := by
  unfold tailWord_2613215
  simp only [CollatzResearch.WordTrace]
  refine ⟨95311781227775831435225099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63541187485183887623483399 95311781227775831435225099)
  ·
    refine ⟨142967671841663747152837649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95311781227775831435225099 142967671841663747152837649)
    ·
      refine ⟨107225753881247810364628237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142967671841663747152837649 107225753881247810364628237)
      ·
        refine ⟨40209657705467928886735589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107225753881247810364628237 40209657705467928886735589)
        ·
          refine ⟨7539310819775236666262923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40209657705467928886735589 7539310819775236666262923)
          ·
            refine ⟨11308966229662854999394385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7539310819775236666262923 11308966229662854999394385)
            ·
              refine ⟨8481724672247141249545789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11308966229662854999394385 8481724672247141249545789)
              ·
                refine ⟨3180646752092677968579671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8481724672247141249545789 3180646752092677968579671)
                ·
                  refine ⟨4770970128139016952869507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180646752092677968579671 4770970128139016952869507)
                  ·
                    refine ⟨7156455192208525429304261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770970128139016952869507 7156455192208525429304261)
                    ·
                      refine ⟨1341835348539098517994549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7156455192208525429304261 1341835348539098517994549)
                      ·
                        rfl

theorem cell23_2613215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_2613215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613215 prefixEnd_2613215 := by exact prefixLift 2613215
  have htrace : WordTrace (prefixWord ++ tailWord_2613215) baseStart_2613215 baseEnd_2613215 := by
    simpa [prefixWord, tailWord_2613215, baseEnd_2613215] using wordTrace_append hprefix tailTrace_2613215
  have hstable : (prefixWord ++ tailWord_2613215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613215).length < 2 ^ (prefixWord ++ tailWord_2613215).sum := by decide
  have hdescent : baseEnd_2613215 < baseStart_2613215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613232 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 3, 2, 2]
def baseStart_2613232 : Nat := 118140960795 + 2613232 * 2 ^ 59
def prefixEnd_2613232 : Nat := 4983230072969 + 3 ^ 40 * 2613232 * 2
def baseEnd_2613232 : Nat := 1341844077710224951481971

theorem tailTrace_2613232 : CollatzResearch.WordTrace tailWord_2613232 prefixEnd_2613232 1341844077710224951481971 := by
  unfold tailWord_2613232
  simp only [CollatzResearch.WordTrace]
  refine ⟨47656200634357121669296975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63541600845809495559062633 47656200634357121669296975)
  ·
    refine ⟨71484300951535682503945463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47656200634357121669296975 71484300951535682503945463)
    ·
      refine ⟨107226451427303523755918195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71484300951535682503945463 107226451427303523755918195)
      ·
        refine ⟨160839677140955285633877293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107226451427303523755918195 160839677140955285633877293)
        ·
          refine ⟨60314878927858232112703985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160839677140955285633877293 60314878927858232112703985)
          ·
            refine ⟨45236159195893674084527989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60314878927858232112703985 45236159195893674084527989)
            ·
              refine ⟨4240889924615031945424499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45236159195893674084527989 4240889924615031945424499)
              ·
                refine ⟨6361334886922547918136749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4240889924615031945424499 6361334886922547918136749)
                ·
                  refine ⟨2385500582595955469301281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6361334886922547918136749 2385500582595955469301281)
                  ·
                    refine ⟨1789125436946966601975961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385500582595955469301281 1789125436946966601975961)
                    ·
                      refine ⟨1341844077710224951481971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789125436946966601975961 1341844077710224951481971)
                      ·
                        rfl

theorem cell23_2613232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 2, 2].length) (baseStart_2613232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613232 prefixEnd_2613232 := by exact prefixLift 2613232
  have htrace : WordTrace (prefixWord ++ tailWord_2613232) baseStart_2613232 baseEnd_2613232 := by
    simpa [prefixWord, tailWord_2613232, baseEnd_2613232] using wordTrace_append hprefix tailTrace_2613232
  have hstable : (prefixWord ++ tailWord_2613232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613232).length < 2 ^ (prefixWord ++ tailWord_2613232).sum := by decide
  have hdescent : baseEnd_2613232 < baseStart_2613232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613269 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_2613269 : Nat := 118140960795 + 2613269 * 2 ^ 59
def prefixEnd_2613269 : Nat := 4983230072969 + 3 ^ 40 * 2613269 * 2
def baseEnd_2613269 : Nat := 1341863076494441306719301

theorem tailTrace_2613269 : CollatzResearch.WordTrace tailWord_2613269 prefixEnd_2613269 1341863076494441306719301 := by
  unfold tailWord_2613269
  simp only [CollatzResearch.WordTrace]
  refine ⟨95313750769580198657690861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63542500513053465771793907 95313750769580198657690861)
  ·
    refine ⟨35742656538592574496634073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95313750769580198657690861 35742656538592574496634073)
    ·
      refine ⟨26806992403944430872475555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35742656538592574496634073 26806992403944430872475555)
      ·
        refine ⟨40210488605916646308713333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26806992403944430872475555 40210488605916646308713333)
        ·
          refine ⟨3769733306804685591441875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40210488605916646308713333 3769733306804685591441875)
          ·
            refine ⟨5654599960207028387162813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769733306804685591441875 5654599960207028387162813)
            ·
              refine ⟨2120474985077635645186055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5654599960207028387162813 2120474985077635645186055)
              ·
                refine ⟨3180712477616453467779083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120474985077635645186055 3180712477616453467779083)
                ·
                  refine ⟨4771068716424680201668625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180712477616453467779083 4771068716424680201668625)
                  ·
                    refine ⟨3578301537318510151251469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771068716424680201668625 3578301537318510151251469)
                    ·
                      refine ⟨1341863076494441306719301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3578301537318510151251469 1341863076494441306719301)
                      ·
                        rfl

theorem cell23_2613269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_2613269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613269 prefixEnd_2613269 := by exact prefixLift 2613269
  have htrace : WordTrace (prefixWord ++ tailWord_2613269) baseStart_2613269 baseEnd_2613269 := by
    simpa [prefixWord, tailWord_2613269, baseEnd_2613269] using wordTrace_append hprefix tailTrace_2613269
  have hstable : (prefixWord ++ tailWord_2613269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613269).length < 2 ^ (prefixWord ++ tailWord_2613269).sum := by decide
  have hdescent : baseEnd_2613269 < baseStart_2613269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613298 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_2613298 : Nat := 118140960795 + 2613298 * 2 ^ 59
def prefixEnd_2613298 : Nat := 4983230072969 + 3 ^ 40 * 2613298 * 2
def baseEnd_2613298 : Nat := 447292655811140564418889

theorem tailTrace_2613298 : CollatzResearch.WordTrace tailWord_2613298 prefixEnd_2613298 447292655811140564418889 := by
  unfold tailWord_2613298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23828702121618784152624137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63543205657650091073664365 23828702121618784152624137)
  ·
    refine ⟨17871526591214088114468103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23828702121618784152624137 17871526591214088114468103)
    ·
      refine ⟨26807289886821132171702155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17871526591214088114468103 26807289886821132171702155)
      ·
        refine ⟨40210934830231698257553233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26807289886821132171702155 40210934830231698257553233)
        ·
          refine ⟨30158201122673773693164925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40210934830231698257553233 30158201122673773693164925)
          ·
            refine ⟨11309325421002665134936847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30158201122673773693164925 11309325421002665134936847)
            ·
              refine ⟨16963988131503997702405271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11309325421002665134936847 16963988131503997702405271)
              ·
                refine ⟨25445982197255996553607907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16963988131503997702405271 25445982197255996553607907)
                ·
                  refine ⟨38168973295883994830411861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25445982197255996553607907 38168973295883994830411861)
                  ·
                    refine ⟨447292655811140564418889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38168973295883994830411861 447292655811140564418889)
                    ·
                      rfl

theorem cell23_2613298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_2613298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613298 prefixEnd_2613298 := by exact prefixLift 2613298
  have htrace : WordTrace (prefixWord ++ tailWord_2613298) baseStart_2613298 baseEnd_2613298 := by
    simpa [prefixWord, tailWord_2613298, baseEnd_2613298] using wordTrace_append hprefix tailTrace_2613298
  have hstable : (prefixWord ++ tailWord_2613298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613298).length < 2 ^ (prefixWord ++ tailWord_2613298).sum := by decide
  have hdescent : baseEnd_2613298 < baseStart_2613298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613322 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_2613322 : Nat := 118140960795 + 2613322 * 2 ^ 59
def prefixEnd_2613322 : Nat := 4983230072969 + 3 ^ 40 * 2613322 * 2
def baseEnd_2613322 : Nat := 1341890290969129599356557

theorem tailTrace_2613322 : CollatzResearch.WordTrace tailWord_2613322 prefixEnd_2613322 1341890290969129599356557 := by
  unfold tailWord_2613322
  simp only [CollatzResearch.WordTrace]
  refine ⟨23828920959597047177342555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63543789225592125806246813 23828920959597047177342555)
  ·
    refine ⟨35743381439395570766013833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23828920959597047177342555 35743381439395570766013833)
    ·
      refine ⟨26807536079546678074510375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35743381439395570766013833 26807536079546678074510375)
      ·
        refine ⟨40211304119320017111765563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26807536079546678074510375 40211304119320017111765563)
        ·
          refine ⟨60316956178980025667648345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40211304119320017111765563 60316956178980025667648345)
          ·
            refine ⟨45237717134235019250736259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60316956178980025667648345 45237717134235019250736259)
            ·
              refine ⟨67856575701352528876104389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45237717134235019250736259 67856575701352528876104389)
              ·
                refine ⟨12723107944003599164269573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67856575701352528876104389 12723107944003599164269573)
                ·
                  refine ⟨2385582739500674843300545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12723107944003599164269573 2385582739500674843300545)
                  ·
                    refine ⟨1789187054625506132475409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385582739500674843300545 1789187054625506132475409)
                    ·
                      refine ⟨1341890290969129599356557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789187054625506132475409 1341890290969129599356557)
                      ·
                        rfl

theorem cell23_2613322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_2613322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613322 prefixEnd_2613322 := by exact prefixLift 2613322
  have htrace : WordTrace (prefixWord ++ tailWord_2613322) baseStart_2613322 baseEnd_2613322 := by
    simpa [prefixWord, tailWord_2613322, baseEnd_2613322] using wordTrace_append hprefix tailTrace_2613322
  have hstable : (prefixWord ++ tailWord_2613322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613322).length < 2 ^ (prefixWord ++ tailWord_2613322).sum := by decide
  have hdescent : baseEnd_2613322 < baseStart_2613322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613325 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2613325 : Nat := 118140960795 + 2613325 * 2 ^ 59
def prefixEnd_2613325 : Nat := 4983230072969 + 3 ^ 40 * 2613325 * 2
def baseEnd_2613325 : Nat := 1341891831411093087619043

theorem tailTrace_2613325 : CollatzResearch.WordTrace tailWord_2613325 prefixEnd_2613325 1341891831411093087619043 := by
  unfold tailWord_2613325
  simp only [CollatzResearch.WordTrace]
  refine ⟨95315793257377320221729429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63543862171584880147819619 95315793257377320221729429)
  ·
    refine ⟨4467927808939561885393567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95315793257377320221729429 4467927808939561885393567)
    ·
      refine ⟨6701891713409342828090351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4467927808939561885393567 6701891713409342828090351)
      ·
        refine ⟨10052837570114014242135527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701891713409342828090351 10052837570114014242135527)
        ·
          refine ⟨15079256355171021363203291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10052837570114014242135527 15079256355171021363203291)
          ·
            refine ⟨22618884532756532044804937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15079256355171021363203291 22618884532756532044804937)
            ·
              refine ⟨16964163399567399033603703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22618884532756532044804937 16964163399567399033603703)
              ·
                refine ⟨25446245099351098550405555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16964163399567399033603703 25446245099351098550405555)
                ·
                  refine ⟨38169367649026647825608333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25446245099351098550405555 38169367649026647825608333)
                  ·
                    refine ⟨14313512868384992934603125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38169367649026647825608333 14313512868384992934603125)
                    ·
                      refine ⟨1341891831411093087619043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14313512868384992934603125 1341891831411093087619043)
                      ·
                        rfl

theorem cell23_2613325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2613325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613325 prefixEnd_2613325 := by exact prefixLift 2613325
  have htrace : WordTrace (prefixWord ++ tailWord_2613325) baseStart_2613325 baseEnd_2613325 := by
    simpa [prefixWord, tailWord_2613325, baseEnd_2613325] using wordTrace_append hprefix tailTrace_2613325
  have hstable : (prefixWord ++ tailWord_2613325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613325).length < 2 ^ (prefixWord ++ tailWord_2613325).sum := by decide
  have hdescent : baseEnd_2613325 < baseStart_2613325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613326 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_2613326 : Nat := 118140960795 + 2613326 * 2 ^ 59
def prefixEnd_2613326 : Nat := 4983230072969 + 3 ^ 40 * 2613326 * 2
def baseEnd_2613326 : Nat := 1341892344891747583706539

theorem tailTrace_2613326 : CollatzResearch.WordTrace tailWord_2613326 prefixEnd_2613326 1341892344891747583706539 := by
  unfold tailWord_2613326
  simp only [CollatzResearch.WordTrace]
  refine ⟨11914478716296712174064479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63543886486915798261677221 11914478716296712174064479)
  ·
    refine ⟨17871718074445068261096719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11914478716296712174064479 17871718074445068261096719)
    ·
      refine ⟨26807577111667602391645079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17871718074445068261096719 26807577111667602391645079)
      ·
        refine ⟨40211365667501403587467619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26807577111667602391645079 40211365667501403587467619)
        ·
          refine ⟨60317048501252105381201429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40211365667501403587467619 60317048501252105381201429)
          ·
            refine ⟨2827361648496192439743817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60317048501252105381201429 2827361648496192439743817)
            ·
              refine ⟨2120521236372144329807863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827361648496192439743817 2120521236372144329807863)
              ·
                refine ⟨3180781854558216494711795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120521236372144329807863 3180781854558216494711795)
                ·
                  refine ⟨4771172781837324742067693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180781854558216494711795 4771172781837324742067693)
                  ·
                    refine ⟨1789189793188996778275385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4771172781837324742067693 1789189793188996778275385)
                    ·
                      refine ⟨1341892344891747583706539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789189793188996778275385 1341892344891747583706539)
                      ·
                        rfl

theorem cell23_2613326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_2613326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613326 prefixEnd_2613326 := by exact prefixLift 2613326
  have htrace : WordTrace (prefixWord ++ tailWord_2613326) baseStart_2613326 baseEnd_2613326 := by
    simpa [prefixWord, tailWord_2613326, baseEnd_2613326] using wordTrace_append hprefix tailTrace_2613326
  have hstable : (prefixWord ++ tailWord_2613326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613326).length < 2 ^ (prefixWord ++ tailWord_2613326).sum := by decide
  have hdescent : baseEnd_2613326 < baseStart_2613326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613356 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 2, 2, 2]
def baseStart_2613356 : Nat := 118140960795 + 2613356 * 2 ^ 59
def prefixEnd_2613356 : Nat := 4983230072969 + 3 ^ 40 * 2613356 * 2
def baseEnd_2613356 : Nat := 1341907749311382466331401

theorem tailTrace_2613356 : CollatzResearch.WordTrace tailWord_2613356 prefixEnd_2613356 1341907749311382466331401 := by
  unfold tailWord_2613356
  simp only [CollatzResearch.WordTrace]
  refine ⟨47658461960132506258053961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63544615946843341677405281 47658461960132506258053961)
  ·
    refine ⟨35743846470099379693540471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47658461960132506258053961 35743846470099379693540471)
    ·
      refine ⟨53615769705149069540310707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35743846470099379693540471 53615769705149069540310707)
      ·
        refine ⟨80423654557723604310466061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53615769705149069540310707 80423654557723604310466061)
        ·
          refine ⟨30158870459146351616424773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80423654557723604310466061 30158870459146351616424773)
          ·
            refine ⟨5654788211089940928079645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30158870459146351616424773 5654788211089940928079645)
            ·
              refine ⟨2120545579158727848029867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5654788211089940928079645 2120545579158727848029867)
              ·
                refine ⟨3180818368738091772044801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120545579158727848029867 3180818368738091772044801)
                ·
                  refine ⟨2385613776553568829033601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3180818368738091772044801 2385613776553568829033601)
                  ·
                    refine ⟨1789210332415176621775201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385613776553568829033601 1789210332415176621775201)
                    ·
                      refine ⟨1341907749311382466331401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789210332415176621775201 1341907749311382466331401)
                      ·
                        rfl

theorem cell23_2613356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_2613356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613356 prefixEnd_2613356 := by exact prefixLift 2613356
  have htrace : WordTrace (prefixWord ++ tailWord_2613356) baseStart_2613356 baseEnd_2613356 := by
    simpa [prefixWord, tailWord_2613356, baseEnd_2613356] using wordTrace_append hprefix tailTrace_2613356
  have hstable : (prefixWord ++ tailWord_2613356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613356).length < 2 ^ (prefixWord ++ tailWord_2613356).sum := by decide
  have hdescent : baseEnd_2613356 < baseStart_2613356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613368 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_2613368 : Nat := 118140960795 + 2613368 * 2 ^ 59
def prefixEnd_2613368 : Nat := 4983230072969 + 3 ^ 40 * 2613368 * 2
def baseEnd_2613368 : Nat := 1341913911079236419381345

theorem tailTrace_2613368 : CollatzResearch.WordTrace tailWord_2613368 prefixEnd_2613368 1341913911079236419381345 := by
  unfold tailWord_2613368
  simp only [CollatzResearch.WordTrace]
  refine ⟨47658680798110769282772379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63544907730814359043696505 47658680798110769282772379)
  ·
    refine ⟨71488021197166153924158569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47658680798110769282772379 71488021197166153924158569)
    ·
      refine ⟨53616015897874615443118927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71488021197166153924158569 53616015897874615443118927)
      ·
        refine ⟨80424023846811923164678391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53616015897874615443118927 80424023846811923164678391)
        ·
          refine ⟨120636035770217884747017587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80424023846811923164678391 120636035770217884747017587)
          ·
            refine ⟨180954053655326827120526381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120636035770217884747017587 180954053655326827120526381)
            ·
              refine ⟨67857770120747560170197393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180954053655326827120526381 67857770120747560170197393)
              ·
                refine ⟨50893327590560670127648045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67857770120747560170197393 50893327590560670127648045)
                ·
                  refine ⟨19084997846460251297868017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50893327590560670127648045 19084997846460251297868017)
                  ·
                    refine ⟨14313748384845188473401013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19084997846460251297868017 14313748384845188473401013)
                    ·
                      refine ⟨1341913911079236419381345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14313748384845188473401013 1341913911079236419381345)
                      ·
                        rfl

theorem cell23_2613368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_2613368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613368 prefixEnd_2613368 := by exact prefixLift 2613368
  have htrace : WordTrace (prefixWord ++ tailWord_2613368) baseStart_2613368 baseEnd_2613368 := by
    simpa [prefixWord, tailWord_2613368, baseEnd_2613368] using wordTrace_append hprefix tailTrace_2613368
  have hstable : (prefixWord ++ tailWord_2613368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613368).length < 2 ^ (prefixWord ++ tailWord_2613368).sum := by decide
  have hdescent : baseEnd_2613368 < baseStart_2613368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613396 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 7]
def baseStart_2613396 : Nat := 118140960795 + 2613396 * 2 ^ 59
def prefixEnd_2613396 : Nat := 4983230072969 + 3 ^ 40 * 2613396 * 2
def baseEnd_2613396 : Nat := 149103143170840256647913

theorem tailTrace_2613396 : CollatzResearch.WordTrace tailWord_2613396 prefixEnd_2613396 149103143170840256647913 := by
  unfold tailWord_2613396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47659191420060049673782021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63545588560080066231709361 47659191420060049673782021)
  ·
    refine ⟨8936098391261259313834129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47659191420060049673782021 8936098391261259313834129)
    ·
      refine ⟨6702073793445944485375597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8936098391261259313834129 6702073793445944485375597)
      ·
        refine ⟨2513277672542229182015849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6702073793445944485375597 2513277672542229182015849)
        ·
          refine ⟨1884958254406671886511887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2513277672542229182015849 1884958254406671886511887)
          ·
            refine ⟨2827437381610007829767831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884958254406671886511887 2827437381610007829767831)
            ·
              refine ⟨4241156072415011744651747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827437381610007829767831 4241156072415011744651747)
              ·
                refine ⟨6361734108622517616977621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241156072415011744651747 6361734108622517616977621)
                ·
                  refine ⟨149103143170840256647913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6361734108622517616977621 149103143170840256647913)
                  ·
                    rfl

theorem cell23_2613396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_2613396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613396 prefixEnd_2613396 := by exact prefixLift 2613396
  have htrace : WordTrace (prefixWord ++ tailWord_2613396) baseStart_2613396 baseEnd_2613396 := by
    simpa [prefixWord, tailWord_2613396, baseEnd_2613396] using wordTrace_append hprefix tailTrace_2613396
  have hstable : (prefixWord ++ tailWord_2613396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613396).length < 2 ^ (prefixWord ++ tailWord_2613396).sum := by decide
  have hdescent : baseEnd_2613396 < baseStart_2613396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613402 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2613402 : Nat := 118140960795 + 2613402 * 2 ^ 59
def prefixEnd_2613402 : Nat := 4983230072969 + 3 ^ 40 * 2613402 * 2
def baseEnd_2613402 : Nat := 1341931369421489286356189

theorem tailTrace_2613402 : CollatzResearch.WordTrace tailWord_2613402 prefixEnd_2613402 1341931369421489286356189 := by
  unfold tailWord_2613402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23829650419524590593070615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63545734452065574914854973 23829650419524590593070615)
  ·
    refine ⟨35744475629286885889605923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23829650419524590593070615 35744475629286885889605923)
    ·
      refine ⟨53616713443930328834408885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35744475629286885889605923 53616713443930328834408885)
      ·
        refine ⟨5026566885368468328225833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53616713443930328834408885 5026566885368468328225833)
        ·
          refine ⟨3769925164026351246169375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5026566885368468328225833 3769925164026351246169375)
          ·
            refine ⟨5654887746039526869254063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769925164026351246169375 5654887746039526869254063)
            ·
              refine ⟨8482331619059290303881095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5654887746039526869254063 8482331619059290303881095)
              ·
                refine ⟨12723497428588935455821643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8482331619059290303881095 12723497428588935455821643)
                ·
                  refine ⟨19085246142883403183732465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12723497428588935455821643 19085246142883403183732465)
                  ·
                    refine ⟨14313934607162552387799349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19085246142883403183732465 14313934607162552387799349)
                    ·
                      refine ⟨1341931369421489286356189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14313934607162552387799349 1341931369421489286356189)
                      ·
                        rfl

theorem cell23_2613402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2613402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613402 prefixEnd_2613402 := by exact prefixLift 2613402
  have htrace : WordTrace (prefixWord ++ tailWord_2613402) baseStart_2613402 baseEnd_2613402 := by
    simpa [prefixWord, tailWord_2613402, baseEnd_2613402] using wordTrace_append hprefix tailTrace_2613402
  have hstable : (prefixWord ++ tailWord_2613402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613402).length < 2 ^ (prefixWord ++ tailWord_2613402).sum := by decide
  have hdescent : baseEnd_2613402 < baseStart_2613402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613432 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_2613432 : Nat := 118140960795 + 2613432 * 2 ^ 59
def prefixEnd_2613432 : Nat := 4983230072969 + 3 ^ 40 * 2613432 * 2
def baseEnd_2613432 : Nat := 1341946773841124168981051

theorem tailTrace_2613432 : CollatzResearch.WordTrace tailWord_2613432 prefixEnd_2613432 1341946773841124168981051 := by
  unfold tailWord_2613432
  simp only [CollatzResearch.WordTrace]
  refine ⟨47659847933994838747937275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63546463911993118330583033 47659847933994838747937275)
  ·
    refine ⟨71489771900992258121905913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47659847933994838747937275 71489771900992258121905913)
    ·
      refine ⟨53617328925744193591429435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71489771900992258121905913 53617328925744193591429435)
      ·
        refine ⟨80425993388616290387144153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53617328925744193591429435 80425993388616290387144153)
        ·
          refine ⟨60319495041462217790358115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80425993388616290387144153 60319495041462217790358115)
          ·
            refine ⟨90479242562193326685537173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60319495041462217790358115 90479242562193326685537173)
            ·
              refine ⟨4241214495102812188384555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90479242562193326685537173 4241214495102812188384555)
              ·
                refine ⟨6361821742654218282576833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241214495102812188384555 6361821742654218282576833)
                ·
                  refine ⟨4771366306990663711932625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6361821742654218282576833 4771366306990663711932625)
                  ·
                    refine ⟨3578524730242997783949469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771366306990663711932625 3578524730242997783949469)
                    ·
                      refine ⟨1341946773841124168981051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3578524730242997783949469 1341946773841124168981051)
                      ·
                        rfl

theorem cell23_2613432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_2613432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613432 prefixEnd_2613432 := by exact prefixLift 2613432
  have htrace : WordTrace (prefixWord ++ tailWord_2613432) baseStart_2613432 baseEnd_2613432 := by
    simpa [prefixWord, tailWord_2613432, baseEnd_2613432] using wordTrace_append hprefix tailTrace_2613432
  have hstable : (prefixWord ++ tailWord_2613432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613432).length < 2 ^ (prefixWord ++ tailWord_2613432).sum := by decide
  have hdescent : baseEnd_2613432 < baseStart_2613432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613465 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 3, 5]
def baseStart_2613465 : Nat := 118140960795 + 2613465 * 2 ^ 59
def prefixEnd_2613465 : Nat := 4983230072969 + 3 ^ 40 * 2613465 * 2
def baseEnd_2613465 : Nat := 447321239567574179956133

theorem tailTrace_2613465 : CollatzResearch.WordTrace tailWord_2613465 prefixEnd_2613465 447321239567574179956133 := by
  unfold tailWord_2613465
  simp only [CollatzResearch.WordTrace]
  refine ⟨95320899476870124131825849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63547266317913416087883899 95320899476870124131825849)
  ·
    refine ⟨71490674607652593098869387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95320899476870124131825849 71490674607652593098869387)
    ·
      refine ⟨107236011911478889648304081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71490674607652593098869387 107236011911478889648304081)
      ·
        refine ⟨80427008933609167236228061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107236011911478889648304081 80427008933609167236228061)
        ·
          refine ⟨30160128350103437713585523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80427008933609167236228061 30160128350103437713585523)
          ·
            refine ⟨45240192525155156570378285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30160128350103437713585523 45240192525155156570378285)
            ·
              refine ⟨16965072196933183713891857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45240192525155156570378285 16965072196933183713891857)
              ·
                refine ⟨12723804147699887785418893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16965072196933183713891857 12723804147699887785418893)
                ·
                  refine ⟨4771426555387457919532085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12723804147699887785418893 4771426555387457919532085)
                  ·
                    refine ⟨447321239567574179956133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4771426555387457919532085 447321239567574179956133)
                    ·
                      rfl

theorem cell23_2613465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_2613465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613465 prefixEnd_2613465 := by exact prefixLift 2613465
  have htrace : WordTrace (prefixWord ++ tailWord_2613465) baseStart_2613465 baseEnd_2613465 := by
    simpa [prefixWord, tailWord_2613465, baseEnd_2613465] using wordTrace_append hprefix tailTrace_2613465
  have hstable : (prefixWord ++ tailWord_2613465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613465).length < 2 ^ (prefixWord ++ tailWord_2613465).sum := by decide
  have hdescent : baseEnd_2613465 < baseStart_2613465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613472 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 1, 5, 2]
def baseStart_2613472 : Nat := 118140960795 + 2613472 * 2 ^ 59
def prefixEnd_2613472 : Nat := 4983230072969 + 3 ^ 40 * 2613472 * 2
def baseEnd_2613472 : Nat := 1341967313067304012480867

theorem tailTrace_2613472 : CollatzResearch.WordTrace tailWord_2613472 prefixEnd_2613472 1341967313067304012480867 := by
  unfold tailWord_2613472
  simp only [CollatzResearch.WordTrace]
  refine ⟨47660577393922382163665335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63547436525229842884887113 47660577393922382163665335)
  ·
    refine ⟨71490866090883573245498003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47660577393922382163665335 71490866090883573245498003)
    ·
      refine ⟨107236299136325359868247005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71490866090883573245498003 107236299136325359868247005)
      ·
        refine ⟨40213612176122009950592627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107236299136325359868247005 40213612176122009950592627)
        ·
          refine ⟨60320418264183014925888941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40213612176122009950592627 60320418264183014925888941)
          ·
            refine ⟨22620156849068630597208353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60320418264183014925888941 22620156849068630597208353)
            ·
              refine ⟨16965117636801472947906265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22620156849068630597208353 16965117636801472947906265)
              ·
                refine ⟨12723838227601104710929699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16965117636801472947906265 12723838227601104710929699)
                ·
                  refine ⟨19085757341401657066394549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12723838227601104710929699 19085757341401657066394549)
                  ·
                    refine ⟨1789289750756405349974489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19085757341401657066394549 1789289750756405349974489)
                    ·
                      refine ⟨1341967313067304012480867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789289750756405349974489 1341967313067304012480867)
                      ·
                        rfl

theorem cell23_2613472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_2613472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613472 prefixEnd_2613472 := by exact prefixLift 2613472
  have htrace : WordTrace (prefixWord ++ tailWord_2613472) baseStart_2613472 baseEnd_2613472 := by
    simpa [prefixWord, tailWord_2613472, baseEnd_2613472] using wordTrace_append hprefix tailTrace_2613472
  have hstable : (prefixWord ++ tailWord_2613472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613472).length < 2 ^ (prefixWord ++ tailWord_2613472).sum := by decide
  have hdescent : baseEnd_2613472 < baseStart_2613472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613479 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2613479 : Nat := 118140960795 + 2613479 * 2 ^ 59
def prefixEnd_2613479 : Nat := 4983230072969 + 3 ^ 40 * 2613479 * 2
def baseEnd_2613479 : Nat := 1341970907431885485093335

theorem tailTrace_2613479 : CollatzResearch.WordTrace tailWord_2613479 prefixEnd_2613479 1341970907431885485093335 := by
  unfold tailWord_2613479
  simp only [CollatzResearch.WordTrace]
  refine ⟨95321410098819404522835491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63547606732546269681890327 95321410098819404522835491)
  ·
    refine ⟨142982115148229106784253237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95321410098819404522835491 142982115148229106784253237)
    ·
      refine ⟨13404573295146478761023741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142982115148229106784253237 13404573295146478761023741)
      ·
        refine ⟨5026714985679929535383903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13404573295146478761023741 5026714985679929535383903)
        ·
          refine ⟨7540072478519894303075855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026714985679929535383903 7540072478519894303075855)
          ·
            refine ⟨11310108717779841454613783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540072478519894303075855 11310108717779841454613783)
            ·
              refine ⟨16965163076669762181920675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11310108717779841454613783 16965163076669762181920675)
              ·
                refine ⟨25447744615004643272881013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16965163076669762181920675 25447744615004643272881013)
                ·
                  refine ⟨2385726057656685306832595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25447744615004643272881013 2385726057656685306832595)
                  ·
                    refine ⟨3578589086485027960248893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2385726057656685306832595 3578589086485027960248893)
                    ·
                      refine ⟨1341970907431885485093335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3578589086485027960248893 1341970907431885485093335)
                      ·
                        rfl

theorem cell23_2613479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2613479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613479 prefixEnd_2613479 := by exact prefixLift 2613479
  have htrace : WordTrace (prefixWord ++ tailWord_2613479) baseStart_2613479 baseEnd_2613479 := by
    simpa [prefixWord, tailWord_2613479, baseEnd_2613479] using wordTrace_append hprefix tailTrace_2613479
  have hstable : (prefixWord ++ tailWord_2613479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613479).length < 2 ^ (prefixWord ++ tailWord_2613479).sum := by decide
  have hdescent : baseEnd_2613479 < baseStart_2613479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613482 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_2613482 : Nat := 118140960795 + 2613482 * 2 ^ 59
def prefixEnd_2613482 : Nat := 4983230072969 + 3 ^ 40 * 2613482 * 2
def baseEnd_2613482 : Nat := 447324149291282991118607

theorem tailTrace_2613482 : CollatzResearch.WordTrace tailWord_2613482 prefixEnd_2613482 447324149291282991118607 := by
  unfold tailWord_2613482
  simp only [CollatzResearch.WordTrace]
  refine ⟨23830379879452134008798675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63547679678539024023463133 23830379879452134008798675)
  ·
    refine ⟨35745569819178201013198013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23830379879452134008798675 35745569819178201013198013)
    ·
      refine ⟨13404588682191825379949255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35745569819178201013198013 13404588682191825379949255)
      ·
        refine ⟨20106883023287738069923883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13404588682191825379949255 20106883023287738069923883)
        ·
          refine ⟨30160324534931607104885825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20106883023287738069923883 30160324534931607104885825)
          ·
            refine ⟨22620243401198705328664369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30160324534931607104885825 22620243401198705328664369)
            ·
              refine ⟨16965182550899028996498277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22620243401198705328664369 16965182550899028996498277)
              ·
                refine ⟨3180971728293567936843427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16965182550899028996498277 3180971728293567936843427)
                ·
                  refine ⟨4771457592440351905265141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180971728293567936843427 4771457592440351905265141)
                  ·
                    refine ⟨447324149291282991118607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4771457592440351905265141 447324149291282991118607)
                    ·
                      rfl

theorem cell23_2613482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_2613482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613482 prefixEnd_2613482 := by exact prefixLift 2613482
  have htrace : WordTrace (prefixWord ++ tailWord_2613482) baseStart_2613482 baseEnd_2613482 := by
    simpa [prefixWord, tailWord_2613482, baseEnd_2613482] using wordTrace_append hprefix tailTrace_2613482
  have hstable : (prefixWord ++ tailWord_2613482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613482).length < 2 ^ (prefixWord ++ tailWord_2613482).sum := by decide
  have hdescent : baseEnd_2613482 < baseStart_2613482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613489 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 2, 3, 2]
def baseStart_2613489 : Nat := 118140960795 + 2613489 * 2 ^ 59
def prefixEnd_2613489 : Nat := 4983230072969 + 3 ^ 40 * 2613489 * 2
def baseEnd_2613489 : Nat := 1341976042238430445968289

theorem tailTrace_2613489 : CollatzResearch.WordTrace tailWord_2613489 prefixEnd_2613489 1341976042238430445968289 := by
  unfold tailWord_2613489
  simp only [CollatzResearch.WordTrace]
  refine ⟨95321774828783176230699521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63547849885855450820466347 95321774828783176230699521)
  ·
    refine ⟨71491331121587382173024641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95321774828783176230699521 71491331121587382173024641)
    ·
      refine ⟨53618498341190536629768481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71491331121587382173024641 53618498341190536629768481)
      ·
        refine ⟨40213873755892902472326361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53618498341190536629768481 40213873755892902472326361)
        ·
          refine ⟨30160405316919676854244771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40213873755892902472326361 30160405316919676854244771)
          ·
            refine ⟨45240607975379515281367157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30160405316919676854244771 45240607975379515281367157)
            ·
              refine ⟨4241306997691829557628171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45240607975379515281367157 4241306997691829557628171)
              ·
                refine ⟨6361960496537744336442257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241306997691829557628171 6361960496537744336442257)
                ·
                  refine ⟨4771470372403308252331693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6361960496537744336442257 4771470372403308252331693)
                  ·
                    refine ⟨1789301389651240594624385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4771470372403308252331693 1789301389651240594624385)
                    ·
                      refine ⟨1341976042238430445968289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789301389651240594624385 1341976042238430445968289)
                      ·
                        rfl

theorem cell23_2613489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_2613489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613489 prefixEnd_2613489 := by exact prefixLift 2613489
  have htrace : WordTrace (prefixWord ++ tailWord_2613489) baseStart_2613489 baseEnd_2613489 := by
    simpa [prefixWord, tailWord_2613489, baseEnd_2613489] using wordTrace_append hprefix tailTrace_2613489
  have hstable : (prefixWord ++ tailWord_2613489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613489).length < 2 ^ (prefixWord ++ tailWord_2613489).sum := by decide
  have hdescent : baseEnd_2613489 < baseStart_2613489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613515 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6]
def baseStart_2613515 : Nat := 118140960795 + 2613515 * 2 ^ 59
def prefixEnd_2613515 : Nat := 4983230072969 + 3 ^ 40 * 2613515 * 2
def baseEnd_2613515 : Nat := 1341989392735447344243169

theorem tailTrace_2613515 : CollatzResearch.WordTrace tailWord_2613515 prefixEnd_2613515 1341989392735447344243169 := by
  unfold tailWord_2613515
  simp only [CollatzResearch.WordTrace]
  refine ⟨95322723126688982671145999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63548482084459321780763999 95322723126688982671145999)
  ·
    refine ⟨142984084690033474006718999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95322723126688982671145999 142984084690033474006718999)
    ·
      refine ⟨214476127035050211010078499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142984084690033474006718999 214476127035050211010078499)
      ·
        refine ⟨321714190552575316515117749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214476127035050211010078499 321714190552575316515117749)
        ·
          refine ⟨30160705364303935923292289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 321714190552575316515117749 30160705364303935923292289)
          ·
            refine ⟨22620529023227951942469217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30160705364303935923292289 22620529023227951942469217)
            ·
              refine ⟨16965396767420963956851913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22620529023227951942469217 16965396767420963956851913)
              ·
                refine ⟨12724047575565722967638935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16965396767420963956851913 12724047575565722967638935)
                ·
                  refine ⟨19086071363348584451458403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12724047575565722967638935 19086071363348584451458403)
                  ·
                    refine ⟨28629107045022876677187605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19086071363348584451458403 28629107045022876677187605)
                    ·
                      refine ⟨1341989392735447344243169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28629107045022876677187605 1341989392735447344243169)
                      ·
                        rfl

theorem cell23_2613515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_2613515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613515 prefixEnd_2613515 := by exact prefixLift 2613515
  have htrace : WordTrace (prefixWord ++ tailWord_2613515) baseStart_2613515 baseEnd_2613515 := by
    simpa [prefixWord, tailWord_2613515, baseEnd_2613515] using wordTrace_append hprefix tailTrace_2613515
  have hstable : (prefixWord ++ tailWord_2613515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613515).length < 2 ^ (prefixWord ++ tailWord_2613515).sum := by decide
  have hdescent : baseEnd_2613515 < baseStart_2613515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613536 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 3, 2, 2]
def baseStart_2613536 : Nat := 118140960795 + 2613536 * 2 ^ 59
def prefixEnd_2613536 : Nat := 4983230072969 + 3 ^ 40 * 2613536 * 2
def baseEnd_2613536 : Nat := 1342000175829191762080573

theorem tailTrace_2613536 : CollatzResearch.WordTrace tailWord_2613536 prefixEnd_2613536 1342000175829191762080573 := by
  unfold tailWord_2613536
  simp only [CollatzResearch.WordTrace]
  refine ⟨47661744529806451628830231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63548992706408602171773641 47661744529806451628830231)
  ·
    refine ⟨71492616794709677443245347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47661744529806451628830231 71492616794709677443245347)
    ·
      refine ⟨107238925192064516164868021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71492616794709677443245347 107238925192064516164868021)
      ·
        refine ⟨10053649236756048390456377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107238925192064516164868021 10053649236756048390456377)
        ·
          refine ⟨7540236927567036292842283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10053649236756048390456377 7540236927567036292842283)
          ·
            refine ⟨11310355391350554439263425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540236927567036292842283 11310355391350554439263425)
            ·
              refine ⟨8482766543512915829447569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11310355391350554439263425 8482766543512915829447569)
              ·
                refine ⟨6362074907634686872085677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8482766543512915829447569 6362074907634686872085677)
                ·
                  refine ⟨2385778090363007577032129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6362074907634686872085677 2385778090363007577032129)
                  ·
                    refine ⟨1789333567772255682774097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385778090363007577032129 1789333567772255682774097)
                    ·
                      refine ⟨1342000175829191762080573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789333567772255682774097 1342000175829191762080573)
                      ·
                        rfl

theorem cell23_2613536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_2613536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613536 prefixEnd_2613536 := by exact prefixLift 2613536
  have htrace : WordTrace (prefixWord ++ tailWord_2613536) baseStart_2613536 baseEnd_2613536 := by
    simpa [prefixWord, tailWord_2613536, baseEnd_2613536] using wordTrace_append hprefix tailTrace_2613536
  have hstable : (prefixWord ++ tailWord_2613536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613536).length < 2 ^ (prefixWord ++ tailWord_2613536).sum := by decide
  have hdescent : baseEnd_2613536 < baseStart_2613536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613539 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 3]
def baseStart_2613539 : Nat := 118140960795 + 2613539 * 2 ^ 59
def prefixEnd_2613539 : Nat := 4983230072969 + 3 ^ 40 * 2613539 * 2
def baseEnd_2613539 : Nat := 1342001716271155250343059

theorem tailTrace_2613539 : CollatzResearch.WordTrace tailWord_2613539 prefixEnd_2613539 1342001716271155250343059 := by
  unfold tailWord_2613539
  simp only [CollatzResearch.WordTrace]
  refine ⟨95323598478602034770019671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63549065652401356513346447 95323598478602034770019671)
  ·
    refine ⟨142985397717903052155029507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95323598478602034770019671 142985397717903052155029507)
    ·
      refine ⟨214478096576854578232544261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142985397717903052155029507 214478096576854578232544261)
      ·
        refine ⟨40214643108160233418602049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214478096576854578232544261 40214643108160233418602049)
        ·
          refine ⟨30160982331120175063951537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40214643108160233418602049 30160982331120175063951537)
          ·
            refine ⟨22620736748340131297963653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30160982331120175063951537 22620736748340131297963653)
            ·
              refine ⟨4241388140313774618368185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22620736748340131297963653 4241388140313774618368185)
              ·
                refine ⟨3181041105235330963776139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4241388140313774618368185 3181041105235330963776139)
                ·
                  refine ⟨4771561657852996445664209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181041105235330963776139 4771561657852996445664209)
                  ·
                    refine ⟨3578671243389747334248157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771561657852996445664209 3578671243389747334248157)
                    ·
                      refine ⟨1342001716271155250343059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3578671243389747334248157 1342001716271155250343059)
                      ·
                        rfl

theorem cell23_2613539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_2613539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613539 prefixEnd_2613539 := by exact prefixLift 2613539
  have htrace : WordTrace (prefixWord ++ tailWord_2613539) baseStart_2613539 baseEnd_2613539 := by
    simpa [prefixWord, tailWord_2613539, baseEnd_2613539] using wordTrace_append hprefix tailTrace_2613539
  have hstable : (prefixWord ++ tailWord_2613539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613539).length < 2 ^ (prefixWord ++ tailWord_2613539).sum := by decide
  have hdescent : baseEnd_2613539 < baseStart_2613539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613556 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2613556 : Nat := 118140960795 + 2613556 * 2 ^ 59
def prefixEnd_2613556 : Nat := 4983230072969 + 3 ^ 40 * 2613556 * 2
def baseEnd_2613556 : Nat := 1342010445442281683830481

theorem tailTrace_2613556 : CollatzResearch.WordTrace tailWord_2613556 prefixEnd_2613556 1342010445442281683830481 := by
  unfold tailWord_2613556
  simp only [CollatzResearch.WordTrace]
  refine ⟨47662109259770223336694261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63549479013026964448925681 47662109259770223336694261)
  ·
    refine ⟨4468322743103458437815087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47662109259770223336694261 4468322743103458437815087)
    ·
      refine ⟨6702484114655187656722631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4468322743103458437815087 6702484114655187656722631)
      ·
        refine ⟨10053726171982781485083947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6702484114655187656722631 10053726171982781485083947)
        ·
          refine ⟨15080589257974172227625921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10053726171982781485083947 15080589257974172227625921)
          ·
            refine ⟨11310441943480629170719441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15080589257974172227625921 11310441943480629170719441)
            ·
              refine ⟨8482831457610471878039581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11310441943480629170719441 8482831457610471878039581)
              ·
                refine ⟨3181061796603926954264843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8482831457610471878039581 3181061796603926954264843)
                ·
                  refine ⟨4771592694905890431397265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181061796603926954264843 4771592694905890431397265)
                  ·
                    refine ⟨3578694521179417823547949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771592694905890431397265 3578694521179417823547949)
                    ·
                      refine ⟨1342010445442281683830481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3578694521179417823547949 1342010445442281683830481)
                      ·
                        rfl

theorem cell23_2613556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2613556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613556 prefixEnd_2613556 := by exact prefixLift 2613556
  have htrace : WordTrace (prefixWord ++ tailWord_2613556) baseStart_2613556 baseEnd_2613556 := by
    simpa [prefixWord, tailWord_2613556, baseEnd_2613556] using wordTrace_append hprefix tailTrace_2613556
  have hstable : (prefixWord ++ tailWord_2613556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613556).length < 2 ^ (prefixWord ++ tailWord_2613556).sum := by decide
  have hdescent : baseEnd_2613556 < baseStart_2613556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613609 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 1, 4, 2]
def baseStart_2613609 : Nat := 118140960795 + 2613609 * 2 ^ 59
def prefixEnd_2613609 : Nat := 4983230072969 + 3 ^ 40 * 2613609 * 2
def baseEnd_2613609 : Nat := 1342037659916969976467737

theorem tailTrace_2613609 : CollatzResearch.WordTrace tailWord_2613609 prefixEnd_2613609 1342037659916969976467737 := by
  unfold tailWord_2613609
  simp only [CollatzResearch.WordTrace]
  refine ⟨95326151588348436725067881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63550767725565624483378587 95326151588348436725067881)
  ·
    refine ⟨71494613691261327543800911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95326151588348436725067881 71494613691261327543800911)
    ·
      refine ⟨107241920536891991315701367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71494613691261327543800911 107241920536891991315701367)
      ·
        refine ⟨160862880805337986973552051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107241920536891991315701367 160862880805337986973552051)
        ·
          refine ⟨241294321208006980460328077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160862880805337986973552051 241294321208006980460328077)
          ·
            refine ⟨90485370453002617672623029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241294321208006980460328077 90485370453002617672623029)
            ·
              refine ⟨8483003479968995406808409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90485370453002617672623029 8483003479968995406808409)
              ·
                refine ⟨6362252609976746555106307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8483003479968995406808409 6362252609976746555106307)
                ·
                  refine ⟨9543378914965119832659461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6362252609976746555106307 9543378914965119832659461)
                  ·
                    refine ⟨1789383546555959968623649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9543378914965119832659461 1789383546555959968623649)
                    ·
                      refine ⟨1342037659916969976467737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789383546555959968623649 1342037659916969976467737)
                      ·
                        rfl

theorem cell23_2613609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 4, 2].length) (baseStart_2613609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613609 prefixEnd_2613609 := by exact prefixLift 2613609
  have htrace : WordTrace (prefixWord ++ tailWord_2613609) baseStart_2613609 baseEnd_2613609 := by
    simpa [prefixWord, tailWord_2613609, baseEnd_2613609] using wordTrace_append hprefix tailTrace_2613609
  have hstable : (prefixWord ++ tailWord_2613609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613609).length < 2 ^ (prefixWord ++ tailWord_2613609).sum := by decide
  have hdescent : baseEnd_2613609 < baseStart_2613609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613613 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_2613613 : Nat := 118140960795 + 2613613 * 2 ^ 59
def prefixEnd_2613613 : Nat := 4983230072969 + 3 ^ 40 * 2613613 * 2
def baseEnd_2613613 : Nat := 1342039713839587960817719

theorem tailTrace_2613613 : CollatzResearch.WordTrace tailWord_2613613 prefixEnd_2613613 1342039713839587960817719 := by
  unfold tailWord_2613613
  simp only [CollatzResearch.WordTrace]
  refine ⟨95326297480333945408213493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63550864986889296938808995 95326297480333945408213493)
  ·
    refine ⟨8936840388781307382020015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95326297480333945408213493 8936840388781307382020015)
    ·
      refine ⟨13405260583171961073030023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936840388781307382020015 13405260583171961073030023)
      ·
        refine ⟨20107890874757941609545035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13405260583171961073030023 20107890874757941609545035)
        ·
          refine ⟨30161836312136912414317553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20107890874757941609545035 30161836312136912414317553)
          ·
            refine ⟨22621377234102684310738165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30161836312136912414317553 22621377234102684310738165)
            ·
              refine ⟨2120754115697126654131703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22621377234102684310738165 2120754115697126654131703)
              ·
                refine ⟨3181131173545689981197555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120754115697126654131703 3181131173545689981197555)
                ·
                  refine ⟨4771696760318534971796333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181131173545689981197555 4771696760318534971796333)
                  ·
                    refine ⟨1789386285119450614423625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4771696760318534971796333 1789386285119450614423625)
                    ·
                      refine ⟨1342039713839587960817719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789386285119450614423625 1342039713839587960817719)
                      ·
                        rfl

theorem cell23_2613613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_2613613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613613 prefixEnd_2613613 := by exact prefixLift 2613613
  have htrace : WordTrace (prefixWord ++ tailWord_2613613) baseStart_2613613 baseEnd_2613613 := by
    simpa [prefixWord, tailWord_2613613, baseEnd_2613613] using wordTrace_append hprefix tailTrace_2613613
  have hstable : (prefixWord ++ tailWord_2613613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613613).length < 2 ^ (prefixWord ++ tailWord_2613613).sum := by decide
  have hdescent : baseEnd_2613613 < baseStart_2613613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613615 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 11]
def baseStart_2613615 : Nat := 118140960795 + 2613615 * 2 ^ 59
def prefixEnd_2613615 : Nat := 4983230072969 + 3 ^ 40 * 2613615 * 2
def baseEnd_2613615 : Nat := 149115637866766328110301

theorem tailTrace_2613615 : CollatzResearch.WordTrace tailWord_2613615 prefixEnd_2613615 149115637866766328110301 := by
  unfold tailWord_2613615
  simp only [CollatzResearch.WordTrace]
  refine ⟨95326370426326699749786299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63550913617551133166524199 95326370426326699749786299)
  ·
    refine ⟨142989555639490049624679449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95326370426326699749786299 142989555639490049624679449)
    ·
      refine ⟨107242166729617537218509587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142989555639490049624679449 107242166729617537218509587)
      ·
        refine ⟨160863250094426305827764381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107242166729617537218509587 160863250094426305827764381)
        ·
          refine ⟨60323718785409864685411643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160863250094426305827764381 60323718785409864685411643)
          ·
            refine ⟨90485578178114797028117465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60323718785409864685411643 90485578178114797028117465)
            ·
              refine ⟨67864183633586097771088099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90485578178114797028117465 67864183633586097771088099)
              ·
                refine ⟨101796275450379146656632149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67864183633586097771088099 101796275450379146656632149)
                ·
                  refine ⟨149115637866766328110301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 101796275450379146656632149 149115637866766328110301)
                  ·
                    rfl

theorem cell23_2613615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 11].length) (baseStart_2613615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613615 prefixEnd_2613615 := by exact prefixLift 2613615
  have htrace : WordTrace (prefixWord ++ tailWord_2613615) baseStart_2613615 baseEnd_2613615 := by
    simpa [prefixWord, tailWord_2613615, baseEnd_2613615] using wordTrace_append hprefix tailTrace_2613615
  have hstable : (prefixWord ++ tailWord_2613615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613615).length < 2 ^ (prefixWord ++ tailWord_2613615).sum := by decide
  have hdescent : baseEnd_2613615 < baseStart_2613615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613666 : List Nat := [3, 3, 1, 2, 1, 1, 4, 3, 5]
def baseStart_2613666 : Nat := 118140960795 + 2613666 * 2 ^ 59
def prefixEnd_2613666 : Nat := 4983230072969 + 3 ^ 40 * 2613666 * 2
def baseEnd_2613666 : Nat := 149118547590475139272775

theorem tailTrace_2613666 : CollatzResearch.WordTrace tailWord_2613666 prefixEnd_2613666 149118547590475139272775 := by
  unfold tailWord_2613666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23832057637285483864973213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63552153699427956973261901 23832057637285483864973213)
  ·
    refine ⟨8937021613982056449364955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23832057637285483864973213 8937021613982056449364955)
    ·
      refine ⟨13405532420973084674047433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8937021613982056449364955 13405532420973084674047433)
      ·
        refine ⟨10054149315729813505535575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13405532420973084674047433 10054149315729813505535575)
        ·
          refine ⟨15081223973594720258303363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10054149315729813505535575 15081223973594720258303363)
          ·
            refine ⟨22621835960392080387455045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15081223973594720258303363 22621835960392080387455045)
            ·
              refine ⟨4241594242573515072647821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22621835960392080387455045 4241594242573515072647821)
              ·
                refine ⟨1590597840965068152242933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4241594242573515072647821 1590597840965068152242933)
                ·
                  refine ⟨149118547590475139272775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1590597840965068152242933 149118547590475139272775)
                  ·
                    rfl

theorem cell23_2613666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_2613666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613666 prefixEnd_2613666 := by exact prefixLift 2613666
  have htrace : WordTrace (prefixWord ++ tailWord_2613666) baseStart_2613666 baseEnd_2613666 := by
    simpa [prefixWord, tailWord_2613666, baseEnd_2613666] using wordTrace_append hprefix tailTrace_2613666
  have hstable : (prefixWord ++ tailWord_2613666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613666).length < 2 ^ (prefixWord ++ tailWord_2613666).sum := by decide
  have hdescent : baseEnd_2613666 < baseStart_2613666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613677 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2613677 : Nat := 118140960795 + 2613677 * 2 ^ 59
def prefixEnd_2613677 : Nat := 4983230072969 + 3 ^ 40 * 2613677 * 2
def baseEnd_2613677 : Nat := 1342072576601475710417425

theorem tailTrace_2613677 : CollatzResearch.WordTrace tailWord_2613677 prefixEnd_2613677 1342072576601475710417425 := by
  unfold tailWord_2613677
  simp only [CollatzResearch.WordTrace]
  refine ⟨95328631752102084338543285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63552421168068056225695523 95328631752102084338543285)
  ·
    refine ⟨8937059226759570406738433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95328631752102084338543285 8937059226759570406738433)
    ·
      refine ⟨6702794420069677805053825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8937059226759570406738433 6702794420069677805053825)
      ·
        refine ⟨5027095815052258353790369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6702794420069677805053825 5027095815052258353790369)
        ·
          refine ⟨3770321861289193765342777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5027095815052258353790369 3770321861289193765342777)
          ·
            refine ⟨2827741395966895324007083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3770321861289193765342777 2827741395966895324007083)
            ·
              refine ⟨4241612093950342986010625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827741395966895324007083 4241612093950342986010625)
              ·
                refine ⟨3181209070462757239507969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4241612093950342986010625 3181209070462757239507969)
                ·
                  refine ⟨2385906802847067929630977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3181209070462757239507969 2385906802847067929630977)
                  ·
                    refine ⟨1789430102135300947223233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385906802847067929630977 1789430102135300947223233)
                    ·
                      refine ⟨1342072576601475710417425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789430102135300947223233 1342072576601475710417425)
                      ·
                        rfl

theorem cell23_2613677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2613677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613677 prefixEnd_2613677 := by exact prefixLift 2613677
  have htrace : WordTrace (prefixWord ++ tailWord_2613677) baseStart_2613677 baseEnd_2613677 := by
    simpa [prefixWord, tailWord_2613677, baseEnd_2613677] using wordTrace_append hprefix tailTrace_2613677
  have hstable : (prefixWord ++ tailWord_2613677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613677).length < 2 ^ (prefixWord ++ tailWord_2613677).sum := by decide
  have hdescent : baseEnd_2613677 < baseStart_2613677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613722 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 10]
def baseStart_2613722 : Nat := 118140960795 + 2613722 * 2 ^ 59
def prefixEnd_2613722 : Nat := 4983230072969 + 3 ^ 40 * 2613722 * 2
def baseEnd_2613722 : Nat := 149121742581214226039413

theorem tailTrace_2613722 : CollatzResearch.WordTrace tailWord_2613722 prefixEnd_2613722 149121742581214226039413 := by
  unfold tailWord_2613722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23832568259234764255982855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63553515357959371349287613 23832568259234764255982855)
  ·
    refine ⟨35748852388852146383974283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23832568259234764255982855 35748852388852146383974283)
    ·
      refine ⟨53623278583278219575961425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35748852388852146383974283 53623278583278219575961425)
      ·
        refine ⟨40217458937458664681971069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53623278583278219575961425 40217458937458664681971069)
        ·
          refine ⟨15081547101546999255739151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40217458937458664681971069 15081547101546999255739151)
          ·
            refine ⟨22622320652320498883608727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15081547101546999255739151 22622320652320498883608727)
            ·
              refine ⟨33933480978480748325413091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22622320652320498883608727 33933480978480748325413091)
              ·
                refine ⟨50900221467721122488119637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33933480978480748325413091 50900221467721122488119637)
                ·
                  refine ⟨149121742581214226039413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50900221467721122488119637 149121742581214226039413)
                  ·
                    rfl

theorem cell23_2613722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_2613722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613722 prefixEnd_2613722 := by exact prefixLift 2613722
  have htrace : WordTrace (prefixWord ++ tailWord_2613722) baseStart_2613722 baseEnd_2613722 := by
    simpa [prefixWord, tailWord_2613722, baseEnd_2613722] using wordTrace_append hprefix tailTrace_2613722
  have hstable : (prefixWord ++ tailWord_2613722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613722).length < 2 ^ (prefixWord ++ tailWord_2613722).sum := by decide
  have hdescent : baseEnd_2613722 < baseStart_2613722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613736 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2613736 : Nat := 118140960795 + 2613736 * 2 ^ 59
def prefixEnd_2613736 : Nat := 4983230072969 + 3 ^ 40 * 2613736 * 2
def baseEnd_2613736 : Nat := 1342102871960090979579653

theorem tailTrace_2613736 : CollatzResearch.WordTrace tailWord_2613736 prefixEnd_2613736 1342102871960090979579653 := by
  unfold tailWord_2613736
  simp only [CollatzResearch.WordTrace]
  refine ⟨47665391829444168707470531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63553855772592224943294041 47665391829444168707470531)
  ·
    refine ⟨71498087744166253061205797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47665391829444168707470531 71498087744166253061205797)
    ·
      refine ⟨13405891452031172448976087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71498087744166253061205797 13405891452031172448976087)
      ·
        refine ⟨20108837178046758673464131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13405891452031172448976087 20108837178046758673464131)
        ·
          refine ⟨30163255767070138010196197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20108837178046758673464131 30163255767070138010196197)
          ·
            refine ⟨5655610456325650876911787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30163255767070138010196197 5655610456325650876911787)
            ·
              refine ⟨8483415684488476315367681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5655610456325650876911787 8483415684488476315367681)
              ·
                refine ⟨6362561763366357236525761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8483415684488476315367681 6362561763366357236525761)
                ·
                  refine ⟨4771921322524767927394321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6362561763366357236525761 4771921322524767927394321)
                  ·
                    refine ⟨3578940991893575945545741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4771921322524767927394321 3578940991893575945545741)
                    ·
                      refine ⟨1342102871960090979579653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3578940991893575945545741 1342102871960090979579653)
                      ·
                        rfl

theorem cell23_2613736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2613736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613736 prefixEnd_2613736 := by exact prefixLift 2613736
  have htrace : WordTrace (prefixWord ++ tailWord_2613736) baseStart_2613736 baseEnd_2613736 := by
    simpa [prefixWord, tailWord_2613736, baseEnd_2613736] using wordTrace_append hprefix tailTrace_2613736
  have hstable : (prefixWord ++ tailWord_2613736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613736).length < 2 ^ (prefixWord ++ tailWord_2613736).sum := by decide
  have hdescent : baseEnd_2613736 < baseStart_2613736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613769 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 1, 5]
def baseStart_2613769 : Nat := 118140960795 + 2613769 * 2 ^ 59
def prefixEnd_2613769 : Nat := 4983230072969 + 3 ^ 40 * 2613769 * 2
def baseEnd_2613769 : Nat := 447373272273896450155667

theorem tailTrace_2613769 : CollatzResearch.WordTrace tailWord_2613769 prefixEnd_2613769 447373272273896450155667 := by
  unfold tailWord_2613769
  simp only [CollatzResearch.WordTrace]
  refine ⟨95331987267768784050892361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63554658178512522700594907 95331987267768784050892361)
  ·
    refine ⟨71498990450826588038169271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95331987267768784050892361 71498990450826588038169271)
    ·
      refine ⟨107248485676239882057253907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71498990450826588038169271 107248485676239882057253907)
      ·
        refine ⟨160872728514359823085880861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107248485676239882057253907 160872728514359823085880861)
        ·
          refine ⟨60327273192884933657205323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160872728514359823085880861 60327273192884933657205323)
          ·
            refine ⟨90490909789327400485807985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60327273192884933657205323 90490909789327400485807985)
            ·
              refine ⟨67868182341995550364355989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90490909789327400485807985 67868182341995550364355989)
              ·
                refine ⟨3181321047281041423329187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67868182341995550364355989 3181321047281041423329187)
                ·
                  refine ⟨4771981570921562134993781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181321047281041423329187 4771981570921562134993781)
                  ·
                    refine ⟨447373272273896450155667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4771981570921562134993781 447373272273896450155667)
                    ·
                      rfl

theorem cell23_2613769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_2613769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613769 prefixEnd_2613769 := by exact prefixLift 2613769
  have htrace : WordTrace (prefixWord ++ tailWord_2613769) baseStart_2613769 baseEnd_2613769 := by
    simpa [prefixWord, tailWord_2613769, baseEnd_2613769] using wordTrace_append hprefix tailTrace_2613769
  have hstable : (prefixWord ++ tailWord_2613769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613769).length < 2 ^ (prefixWord ++ tailWord_2613769).sum := by decide
  have hdescent : baseEnd_2613769 < baseStart_2613769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613809 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2613809 : Nat := 118140960795 + 2613809 * 2 ^ 59
def prefixEnd_2613809 : Nat := 4983230072969 + 3 ^ 40 * 2613809 * 2
def baseEnd_2613809 : Nat := 1342140356047869193966817

theorem tailTrace_2613809 : CollatzResearch.WordTrace tailWord_2613809 prefixEnd_2613809 1342140356047869193966817 := by
  unfold tailWord_2613809
  simp only [CollatzResearch.WordTrace]
  refine ⟨95333446187623870882348481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63555630791749247254898987 95333446187623870882348481)
  ·
    refine ⟨71500084640717903161761361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95333446187623870882348481 71500084640717903161761361)
    ·
      refine ⟨53625063480538427371321021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71500084640717903161761361 53625063480538427371321021)
      ·
        refine ⟨20109398805201910264245383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53625063480538427371321021 20109398805201910264245383)
        ·
          refine ⟨30164098207802865396368075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20109398805201910264245383 30164098207802865396368075)
          ·
            refine ⟨45246147311704298094552113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30164098207802865396368075 45246147311704298094552113)
            ·
              refine ⟨33934610483778223570914085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45246147311704298094552113 33934610483778223570914085)
              ·
                refine ⟨6362739465708416919546391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33934610483778223570914085 6362739465708416919546391)
                ·
                  refine ⟨9544109198562625379319587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6362739465708416919546391 9544109198562625379319587)
                  ·
                    refine ⟨14316163797843938068979381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9544109198562625379319587 14316163797843938068979381)
                    ·
                      refine ⟨1342140356047869193966817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14316163797843938068979381 1342140356047869193966817)
                      ·
                        rfl

theorem cell23_2613809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2613809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613809 prefixEnd_2613809 := by exact prefixLift 2613809
  have htrace : WordTrace (prefixWord ++ tailWord_2613809) baseStart_2613809 baseEnd_2613809 := by
    simpa [prefixWord, tailWord_2613809, baseEnd_2613809] using wordTrace_append hprefix tailTrace_2613809
  have hstable : (prefixWord ++ tailWord_2613809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613809).length < 2 ^ (prefixWord ++ tailWord_2613809).sum := by decide
  have hdescent : baseEnd_2613809 < baseStart_2613809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613816 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 2, 4]
def baseStart_2613816 : Nat := 118140960795 + 2613816 * 2 ^ 59
def prefixEnd_2613816 : Nat := 4983230072969 + 3 ^ 40 * 2613816 * 2
def baseEnd_2613816 : Nat := 447381316804150222193095

theorem tailTrace_2613816 : CollatzResearch.WordTrace tailWord_2613816 prefixEnd_2613816 447381316804150222193095 := by
  unfold tailWord_2613816
  simp only [CollatzResearch.WordTrace]
  refine ⟨47666850749299255538926651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63555800999065674051902201 47666850749299255538926651)
  ·
    refine ⟨71500276123948883308389977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47666850749299255538926651 71500276123948883308389977)
    ·
      refine ⟨53625207092961662481292483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71500276123948883308389977 53625207092961662481292483)
      ·
        refine ⟨80437810639442493721938725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53625207092961662481292483 80437810639442493721938725)
        ·
          refine ⟨15082089494895467572863511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80437810639442493721938725 15082089494895467572863511)
          ·
            refine ⟨22623134242343201359295267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15082089494895467572863511 22623134242343201359295267)
            ·
              refine ⟨33934701363514802038942901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22623134242343201359295267 33934701363514802038942901)
              ·
                refine ⟨3181378252829512691150897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33934701363514802038942901 3181378252829512691150897)
                ·
                  refine ⟨2386033689622134518363173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3181378252829512691150897 2386033689622134518363173)
                  ·
                    refine ⟨447381316804150222193095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2386033689622134518363173 447381316804150222193095)
                    ·
                      rfl

theorem cell23_2613816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_2613816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613816 prefixEnd_2613816 := by exact prefixLift 2613816
  have htrace : WordTrace (prefixWord ++ tailWord_2613816) baseStart_2613816 baseEnd_2613816 := by
    simpa [prefixWord, tailWord_2613816, baseEnd_2613816] using wordTrace_append hprefix tailTrace_2613816
  have hstable : (prefixWord ++ tailWord_2613816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613816).length < 2 ^ (prefixWord ++ tailWord_2613816).sum := by decide
  have hdescent : baseEnd_2613816 < baseStart_2613816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613823 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 3, 2, 2]
def baseStart_2613823 : Nat := 118140960795 + 2613823 * 2 ^ 59
def prefixEnd_2613823 : Nat := 4983230072969 + 3 ^ 40 * 2613823 * 2
def baseEnd_2613823 : Nat := 1342147544777032139191753

theorem tailTrace_2613823 : CollatzResearch.WordTrace tailWord_2613823 prefixEnd_2613823 1342147544777032139191753 := by
  unfold tailWord_2613823
  simp only [CollatzResearch.WordTrace]
  refine ⟨95333956809573151273358123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63555971206382100848905415 95333956809573151273358123)
  ·
    refine ⟨143000935214359726910037185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95333956809573151273358123 143000935214359726910037185)
    ·
      refine ⟨107250701410769795182527889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143000935214359726910037185 107250701410769795182527889)
      ·
        refine ⟨80438026058077346386895917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107250701410769795182527889 80438026058077346386895917)
        ·
          refine ⟨30164259771779004895085969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80438026058077346386895917 30164259771779004895085969)
          ·
            refine ⟨22623194828834253671314477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30164259771779004895085969 22623194828834253671314477)
            ·
              refine ⟨8483698060812845126742929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22623194828834253671314477 8483698060812845126742929)
              ·
                refine ⟨6362773545609633845057197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8483698060812845126742929 6362773545609633845057197)
                ·
                  refine ⟨2386040079603612691896449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6362773545609633845057197 2386040079603612691896449)
                  ·
                    refine ⟨1789530059702709518922337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2386040079603612691896449 1789530059702709518922337)
                    ·
                      refine ⟨1342147544777032139191753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789530059702709518922337 1342147544777032139191753)
                      ·
                        rfl

theorem cell23_2613823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_2613823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613823 prefixEnd_2613823 := by exact prefixLift 2613823
  have htrace : WordTrace (prefixWord ++ tailWord_2613823) baseStart_2613823 baseEnd_2613823 := by
    simpa [prefixWord, tailWord_2613823, baseEnd_2613823] using wordTrace_append hprefix tailTrace_2613823
  have hstable : (prefixWord ++ tailWord_2613823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613823).length < 2 ^ (prefixWord ++ tailWord_2613823).sum := by decide
  have hdescent : baseEnd_2613823 < baseStart_2613823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613879 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_2613879 : Nat := 118140960795 + 2613879 * 2 ^ 59
def prefixEnd_2613879 : Nat := 4983230072969 + 3 ^ 40 * 2613879 * 2
def baseEnd_2613879 : Nat := 1342176299693683920091495

theorem tailTrace_2613879 : CollatzResearch.WordTrace tailWord_2613879 prefixEnd_2613879 1342176299693683920091495 := by
  unfold tailWord_2613879
  simp only [CollatzResearch.WordTrace]
  refine ⟨95335999297370272837396691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63557332864913515224931127 95335999297370272837396691)
  ·
    refine ⟨143003998946055409256095037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95335999297370272837396691 143003998946055409256095037)
    ·
      refine ⟨53626499604770778471035639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143003998946055409256095037 53626499604770778471035639)
      ·
        refine ⟨80439749407156167706553459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53626499604770778471035639 80439749407156167706553459)
        ·
          refine ⟨120659624110734251559830189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80439749407156167706553459 120659624110734251559830189)
          ·
            refine ⟨45247359041525344334936321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120659624110734251559830189 45247359041525344334936321)
            ·
              refine ⟨33935519281144008251202241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45247359041525344334936321 33935519281144008251202241)
              ·
                refine ⟨25451639460858006188401681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33935519281144008251202241 25451639460858006188401681)
                ·
                  refine ⟨19088729595643504641301261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25451639460858006188401681 19088729595643504641301261)
                  ·
                    refine ⟨7158273598366314240487973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19088729595643504641301261 7158273598366314240487973)
                    ·
                      refine ⟨1342176299693683920091495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7158273598366314240487973 1342176299693683920091495)
                      ·
                        rfl

theorem cell23_2613879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_2613879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613879 prefixEnd_2613879 := by exact prefixLift 2613879
  have htrace : WordTrace (prefixWord ++ tailWord_2613879) baseStart_2613879 baseEnd_2613879 := by
    simpa [prefixWord, tailWord_2613879, baseEnd_2613879] using wordTrace_append hprefix tailTrace_2613879
  have hstable : (prefixWord ++ tailWord_2613879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613879).length < 2 ^ (prefixWord ++ tailWord_2613879).sum := by decide
  have hdescent : baseEnd_2613879 < baseStart_2613879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613913 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 4, 2, 2]
def baseStart_2613913 : Nat := 118140960795 + 2613913 * 2 ^ 59
def prefixEnd_2613913 : Nat := 4983230072969 + 3 ^ 40 * 2613913 * 2
def baseEnd_2613913 : Nat := 1342193758035936787066339

theorem tailTrace_2613913 : CollatzResearch.WordTrace tailWord_2613913 prefixEnd_2613913 1342193758035936787066339 := by
  unfold tailWord_2613913
  simp only [CollatzResearch.WordTrace]
  refine ⟨95337239379247096644134393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63558159586164731096089595 95337239379247096644134393)
  ·
    refine ⟨71502929534435322483100795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95337239379247096644134393 71502929534435322483100795)
    ·
      refine ⟨107254394301652983724651193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71502929534435322483100795 107254394301652983724651193)
      ·
        refine ⟨80440795726239737793488395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107254394301652983724651193 80440795726239737793488395)
        ·
          refine ⟨120661193589359606690232593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80440795726239737793488395 120661193589359606690232593)
          ·
            refine ⟨90495895192019705017674445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120661193589359606690232593 90495895192019705017674445)
            ·
              refine ⟨33935960697007389381627917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90495895192019705017674445 33935960697007389381627917)
              ·
                refine ⟨12725985261377771018110469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33935960697007389381627917 12725985261377771018110469)
                ·
                  refine ⟨2386122236508332065895713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12725985261377771018110469 2386122236508332065895713)
                  ·
                    refine ⟨1789591677381249049421785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2386122236508332065895713 1789591677381249049421785)
                    ·
                      refine ⟨1342193758035936787066339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789591677381249049421785 1342193758035936787066339)
                      ·
                        rfl

theorem cell23_2613913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_2613913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613913 prefixEnd_2613913 := by exact prefixLift 2613913
  have htrace : WordTrace (prefixWord ++ tailWord_2613913) baseStart_2613913 baseEnd_2613913 := by
    simpa [prefixWord, tailWord_2613913, baseEnd_2613913] using wordTrace_append hprefix tailTrace_2613913
  have hstable : (prefixWord ++ tailWord_2613913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613913).length < 2 ^ (prefixWord ++ tailWord_2613913).sum := by decide
  have hdescent : baseEnd_2613913 < baseStart_2613913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613934 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2613934 : Nat := 118140960795 + 2613934 * 2 ^ 59
def prefixEnd_2613934 : Nat := 4983230072969 + 3 ^ 40 * 2613934 * 2
def baseEnd_2613934 : Nat := 1342204541129681204903743

theorem tailTrace_2613934 : CollatzResearch.WordTrace tailWord_2613934 prefixEnd_2613934 1342204541129681204903743 := by
  unfold tailWord_2613934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11917250664021377153831107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63558670208114011487099237 11917250664021377153831107)
  ·
    refine ⟨17875875996032065730746661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11917250664021377153831107 17875875996032065730746661)
    ·
      refine ⟨3351726749256012324514999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17875875996032065730746661 3351726749256012324514999)
      ·
        refine ⟨5027590123884018486772499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351726749256012324514999 5027590123884018486772499)
        ·
          refine ⟨7541385185826027730158749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027590123884018486772499 7541385185826027730158749)
          ·
            refine ⟨2828019444684760398809531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7541385185826027730158749 2828019444684760398809531)
            ·
              refine ⟨4242029167027140598214297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2828019444684760398809531 4242029167027140598214297)
              ·
                refine ⟨3181521875270355448660723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4242029167027140598214297 3181521875270355448660723)
                ·
                  refine ⟨4772282812905533172991085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181521875270355448660723 4772282812905533172991085)
                  ·
                    refine ⟨1789606054839574939871657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4772282812905533172991085 1789606054839574939871657)
                    ·
                      refine ⟨1342204541129681204903743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789606054839574939871657 1342204541129681204903743)
                      ·
                        rfl

theorem cell23_2613934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2613934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613934 prefixEnd_2613934 := by exact prefixLift 2613934
  have htrace : WordTrace (prefixWord ++ tailWord_2613934) baseStart_2613934 baseEnd_2613934 := by
    simpa [prefixWord, tailWord_2613934, baseEnd_2613934] using wordTrace_append hprefix tailTrace_2613934
  have hstable : (prefixWord ++ tailWord_2613934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613934).length < 2 ^ (prefixWord ++ tailWord_2613934).sum := by decide
  have hdescent : baseEnd_2613934 < baseStart_2613934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613970 : List Nat := [3, 2, 2, 2, 3, 1, 1, 4, 5]
def baseStart_2613970 : Nat := 118140960795 + 2613970 * 2 ^ 59
def prefixEnd_2613970 : Nat := 4983230072969 + 3 ^ 40 * 2613970 * 2
def baseEnd_2613970 : Nat := 149135891825915896005953

theorem tailTrace_2613970 : CollatzResearch.WordTrace tailWord_2613970 prefixEnd_2613970 149135891825915896005953 := by
  unfold tailWord_2613970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23834829585010148844739841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63559545560027063585972909 23834829585010148844739841)
  ·
    refine ⟨17876122188757611633554881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23834829585010148844739841 17876122188757611633554881)
    ·
      refine ⟨13407091641568208725166161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17876122188757611633554881 13407091641568208725166161)
      ·
        refine ⟨10055318731176156543874621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13407091641568208725166161 10055318731176156543874621)
        ·
          refine ⟨3770744524191058703952983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10055318731176156543874621 3770744524191058703952983)
          ·
            refine ⟨5656116786286588055929475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770744524191058703952983 5656116786286588055929475)
            ·
              refine ⟨8484175179429882083894213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656116786286588055929475 8484175179429882083894213)
              ·
                refine ⟨1590782846143102890730165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8484175179429882083894213 1590782846143102890730165)
                ·
                  refine ⟨149135891825915896005953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1590782846143102890730165 149135891825915896005953)
                  ·
                    rfl

theorem cell23_2613970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_2613970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613970 prefixEnd_2613970 := by exact prefixLift 2613970
  have htrace : WordTrace (prefixWord ++ tailWord_2613970) baseStart_2613970 baseEnd_2613970 := by
    simpa [prefixWord, tailWord_2613970, baseEnd_2613970] using wordTrace_append hprefix tailTrace_2613970
  have hstable : (prefixWord ++ tailWord_2613970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613970).length < 2 ^ (prefixWord ++ tailWord_2613970).sum := by decide
  have hdescent : baseEnd_2613970 < baseStart_2613970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613976 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2613976 : Nat := 118140960795 + 2613976 * 2 ^ 59
def prefixEnd_2613976 : Nat := 4983230072969 + 3 ^ 40 * 2613976 * 2
def baseEnd_2613976 : Nat := 1342226107317170040578549

theorem tailTrace_2613976 : CollatzResearch.WordTrace tailWord_2613976 prefixEnd_2613976 1342226107317170040578549 := by
  unfold tailWord_2613976
  simp only [CollatzResearch.WordTrace]
  refine ⟨47669768589009429201838891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63559691452012572269118521 47669768589009429201838891)
  ·
    refine ⟨71504652883514143802758337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47669768589009429201838891 71504652883514143802758337)
    ·
      refine ⟨53628489662635607852068753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71504652883514143802758337 53628489662635607852068753)
      ·
        refine ⟨40221367246976705889051565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53628489662635607852068753 40221367246976705889051565)
        ·
          refine ⟨15083012717616264708394337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40221367246976705889051565 15083012717616264708394337)
          ·
            refine ⟨11312259538212198531295753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15083012717616264708394337 11312259538212198531295753)
            ·
              refine ⟨8484194653659148898471815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11312259538212198531295753 8484194653659148898471815)
              ·
                refine ⟨12726291980488723347707723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8484194653659148898471815 12726291980488723347707723)
                ·
                  refine ⟨19089437970733085021561585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12726291980488723347707723 19089437970733085021561585)
                  ·
                    refine ⟨14317078478049813766171189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19089437970733085021561585 14317078478049813766171189)
                    ·
                      refine ⟨1342226107317170040578549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14317078478049813766171189 1342226107317170040578549)
                      ·
                        rfl

theorem cell23_2613976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2613976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613976 prefixEnd_2613976 := by exact prefixLift 2613976
  have htrace : WordTrace (prefixWord ++ tailWord_2613976) baseStart_2613976 baseEnd_2613976 := by
    simpa [prefixWord, tailWord_2613976, baseEnd_2613976] using wordTrace_append hprefix tailTrace_2613976
  have hstable : (prefixWord ++ tailWord_2613976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613976).length < 2 ^ (prefixWord ++ tailWord_2613976).sum := by decide
  have hdescent : baseEnd_2613976 < baseStart_2613976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613980 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2613980 : Nat := 118140960795 + 2613980 * 2 ^ 59
def prefixEnd_2613980 : Nat := 4983230072969 + 3 ^ 40 * 2613980 * 2
def baseEnd_2613980 : Nat := 1342228161239788024928531

theorem tailTrace_2613980 : CollatzResearch.WordTrace tailWord_2613980 prefixEnd_2613980 1342228161239788024928531 := by
  unfold tailWord_2613980
  simp only [CollatzResearch.WordTrace]
  refine ⟨47669841535002183543411697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63559788713336244724548929 47669841535002183543411697)
  ·
    refine ⟨35752381151251637657558773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47669841535002183543411697 35752381151251637657558773)
    ·
      refine ⟨3351785732929841030396135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35752381151251637657558773 3351785732929841030396135)
      ·
        refine ⟨5027678599394761545594203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351785732929841030396135 5027678599394761545594203)
        ·
          refine ⟨7541517899092142318391305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027678599394761545594203 7541517899092142318391305)
          ·
            refine ⟨5656138424319106738793479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7541517899092142318391305 5656138424319106738793479)
            ·
              refine ⟨8484207636478660108190219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656138424319106738793479 8484207636478660108190219)
              ·
                refine ⟨12726311454717990162285329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8484207636478660108190219 12726311454717990162285329)
                ·
                  refine ⟨9544733591038492621713997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12726311454717990162285329 9544733591038492621713997)
                  ·
                    refine ⟨3579275096639434733142749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9544733591038492621713997 3579275096639434733142749)
                    ·
                      refine ⟨1342228161239788024928531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3579275096639434733142749 1342228161239788024928531)
                      ·
                        rfl

theorem cell23_2613980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2613980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2613980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2613980 prefixEnd_2613980 := by exact prefixLift 2613980
  have htrace : WordTrace (prefixWord ++ tailWord_2613980) baseStart_2613980 baseEnd_2613980 := by
    simpa [prefixWord, tailWord_2613980, baseEnd_2613980] using wordTrace_append hprefix tailTrace_2613980
  have hstable : (prefixWord ++ tailWord_2613980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613980).length < 2 ^ (prefixWord ++ tailWord_2613980).sum := by decide
  have hdescent : baseEnd_2613980 < baseStart_2613980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614004 : List Nat := [2, 6, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2614004 : Nat := 118140960795 + 2614004 * 2 ^ 59
def prefixEnd_2614004 : Nat := 4983230072969 + 3 ^ 40 * 2614004 * 2
def baseEnd_2614004 : Nat := 149137831641721770114269

theorem tailTrace_2614004 : CollatzResearch.WordTrace tailWord_2614004 prefixEnd_2614004 149137831641721770114269 := by
  unfold tailWord_2614004
  simp only [CollatzResearch.WordTrace]
  refine ⟨47670279210958709592848533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63560372281278279457131377 47670279210958709592848533)
  ·
    refine ⟨2234544338013689512164775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47670279210958709592848533 2234544338013689512164775)
    ·
      refine ⟨3351816507020534268247163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234544338013689512164775 3351816507020534268247163)
      ·
        refine ⟨5027724760530801402370745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351816507020534268247163 5027724760530801402370745)
        ·
          refine ⟨3770793570398101051778059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5027724760530801402370745 3770793570398101051778059)
          ·
            refine ⟨5656190355597151577667089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770793570398101051778059 5656190355597151577667089)
            ·
              refine ⟨4242142766697863683250317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5656190355597151577667089 4242142766697863683250317)
              ·
                refine ⟨1590803537511698881218869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4242142766697863683250317 1590803537511698881218869)
                ·
                  refine ⟨149137831641721770114269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1590803537511698881218869 149137831641721770114269)
                  ·
                    rfl

theorem cell23_2614004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2614004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614004 prefixEnd_2614004 := by exact prefixLift 2614004
  have htrace : WordTrace (prefixWord ++ tailWord_2614004) baseStart_2614004 baseEnd_2614004 := by
    simpa [prefixWord, tailWord_2614004, baseEnd_2614004] using wordTrace_append hprefix tailTrace_2614004
  have hstable : (prefixWord ++ tailWord_2614004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614004).length < 2 ^ (prefixWord ++ tailWord_2614004).sum := by decide
  have hdescent : baseEnd_2614004 < baseStart_2614004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614026 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 8]
def baseStart_2614026 : Nat := 118140960795 + 2614026 * 2 ^ 59
def prefixEnd_2614026 : Nat := 4983230072969 + 3 ^ 40 * 2614026 * 2
def baseEnd_2614026 : Nat := 149139086816654982772591

theorem tailTrace_2614026 : CollatzResearch.WordTrace tailWord_2614026 prefixEnd_2614026 149139086816654982772591 := by
  unfold tailWord_2614026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23835340206959429235749483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63560907218558477961998621 23835340206959429235749483)
  ·
    refine ⟨35753010310439143853624225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23835340206959429235749483 35753010310439143853624225)
    ·
      refine ⟨26814757732829357890218169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35753010310439143853624225 26814757732829357890218169)
      ·
        refine ⟨20111068299622018417663627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26814757732829357890218169 20111068299622018417663627)
        ·
          refine ⟨30166602449433027626495441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20111068299622018417663627 30166602449433027626495441)
          ·
            refine ⟨22624951837074770719871581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30166602449433027626495441 22624951837074770719871581)
            ·
              refine ⟨8484356938903039019951843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22624951837074770719871581 8484356938903039019951843)
              ·
                refine ⟨12726535408354558529927765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8484356938903039019951843 12726535408354558529927765)
                ·
                  refine ⟨149139086816654982772591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12726535408354558529927765 149139086816654982772591)
                  ·
                    rfl

theorem cell23_2614026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_2614026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614026 prefixEnd_2614026 := by exact prefixLift 2614026
  have htrace : WordTrace (prefixWord ++ tailWord_2614026) baseStart_2614026 baseEnd_2614026 := by
    simpa [prefixWord, tailWord_2614026, baseEnd_2614026] using wordTrace_append hprefix tailTrace_2614026
  have hstable : (prefixWord ++ tailWord_2614026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614026).length < 2 ^ (prefixWord ++ tailWord_2614026).sum := by decide
  have hdescent : baseEnd_2614026 < baseStart_2614026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614081 : List Nat := [1, 2, 5, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2614081 : Nat := 118140960795 + 2614081 * 2 ^ 59
def prefixEnd_2614081 : Nat := 4983230072969 + 3 ^ 40 * 2614081 * 2
def baseEnd_2614081 : Nat := 447426674261964043255189

theorem tailTrace_2614081 : CollatzResearch.WordTrace tailWord_2614081 prefixEnd_2614081 447426674261964043255189 := by
  unfold tailWord_2614081
  simp only [CollatzResearch.WordTrace]
  refine ⟨95343366842638461336250097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63562244561758974224166731 95343366842638461336250097)
  ·
    refine ⟨71507525131978846002187573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95343366842638461336250097 71507525131978846002187573)
    ·
      refine ⟨6703830481123016812705085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71507525131978846002187573 6703830481123016812705085)
      ·
        refine ⟨2513936430421131304764407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6703830481123016812705085 2513936430421131304764407)
        ·
          refine ⟨3770904645631696957146611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2513936430421131304764407 3770904645631696957146611)
          ·
            refine ⟨5656356968447545435719917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770904645631696957146611 5656356968447545435719917)
            ·
              refine ⟨2121133863167829538394969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5656356968447545435719917 2121133863167829538394969)
              ·
                refine ⟨1590850397375872153796227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2121133863167829538394969 1590850397375872153796227)
                ·
                  refine ⟨2386275596063808230694341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590850397375872153796227 2386275596063808230694341)
                  ·
                    refine ⟨447426674261964043255189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2386275596063808230694341 447426674261964043255189)
                    ·
                      rfl

theorem cell23_2614081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2614081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614081 prefixEnd_2614081 := by exact prefixLift 2614081
  have htrace : WordTrace (prefixWord ++ tailWord_2614081) baseStart_2614081 baseEnd_2614081 := by
    simpa [prefixWord, tailWord_2614081, baseEnd_2614081] using wordTrace_append hprefix tailTrace_2614081
  have hstable : (prefixWord ++ tailWord_2614081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614081).length < 2 ^ (prefixWord ++ tailWord_2614081).sum := by decide
  have hdescent : baseEnd_2614081 < baseStart_2614081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614114 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_2614114 : Nat := 118140960795 + 2614114 * 2 ^ 59
def prefixEnd_2614114 : Nat := 4983230072969 + 3 ^ 40 * 2614114 * 2
def baseEnd_2614114 : Nat := 1342296967647490500652915

theorem tailTrace_2614114 : CollatzResearch.WordTrace tailWord_2614114 prefixEnd_2614114 1342296967647490500652915 := by
  unfold tailWord_2614114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23836142612879726993050349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63563046967679271981467597 23836142612879726993050349)
  ·
    refine ⟨8938553479829897622393881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23836142612879726993050349 8938553479829897622393881)
    ·
      refine ⟨6703915109872423216795411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8938553479829897622393881 6703915109872423216795411)
      ·
        refine ⟨10055872664808634825193117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6703915109872423216795411 10055872664808634825193117)
        ·
          refine ⟨3770952249303238059447419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10055872664808634825193117 3770952249303238059447419)
          ·
            refine ⟨5656428373954857089171129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770952249303238059447419 5656428373954857089171129)
            ·
              refine ⟨4242321280466142816878347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5656428373954857089171129 4242321280466142816878347)
              ·
                refine ⟨6363481920699214225317521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4242321280466142816878347 6363481920699214225317521)
                ·
                  refine ⟨4772611440524410668988141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6363481920699214225317521 4772611440524410668988141)
                  ·
                    refine ⟨1789729290196654000870553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4772611440524410668988141 1789729290196654000870553)
                    ·
                      refine ⟨1342296967647490500652915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789729290196654000870553 1342296967647490500652915)
                      ·
                        rfl

theorem cell23_2614114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_2614114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614114 prefixEnd_2614114 := by exact prefixLift 2614114
  have htrace : WordTrace (prefixWord ++ tailWord_2614114) baseStart_2614114 baseEnd_2614114 := by
    simpa [prefixWord, tailWord_2614114, baseEnd_2614114] using wordTrace_append hprefix tailTrace_2614114
  have hstable : (prefixWord ++ tailWord_2614114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614114).length < 2 ^ (prefixWord ++ tailWord_2614114).sum := by decide
  have hdescent : baseEnd_2614114 < baseStart_2614114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614130 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2614130 : Nat := 118140960795 + 2614130 * 2 ^ 59
def prefixEnd_2614130 : Nat := 4983230072969 + 3 ^ 40 * 2614130 * 2
def baseEnd_2614130 : Nat := 1342305183337962438052841

theorem tailTrace_2614130 : CollatzResearch.WordTrace tailWord_2614130 prefixEnd_2614130 1342305183337962438052841 := by
  unfold tailWord_2614130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23836288504865235676195961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63563436012973961803189229 23836288504865235676195961)
  ·
    refine ⟨17877216378648926757146971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23836288504865235676195961 17877216378648926757146971)
    ·
      refine ⟨26815824567973390135720457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17877216378648926757146971 26815824567973390135720457)
      ·
        refine ⟨20111868425980042601790343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26815824567973390135720457 20111868425980042601790343)
        ·
          refine ⟨30167802638970063902685515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20111868425980042601790343 30167802638970063902685515)
          ·
            refine ⟨45251703958455095854028273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30167802638970063902685515 45251703958455095854028273)
            ·
              refine ⟨33938777968841321890521205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45251703958455095854028273 33938777968841321890521205)
              ·
                refine ⟨3181760434578873927236363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33938777968841321890521205 3181760434578873927236363)
                ·
                  refine ⟨4772640651868310890854545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3181760434578873927236363 4772640651868310890854545)
                  ·
                    refine ⟨3579480488901233168140909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4772640651868310890854545 3579480488901233168140909)
                    ·
                      refine ⟨1342305183337962438052841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3579480488901233168140909 1342305183337962438052841)
                      ·
                        rfl

theorem cell23_2614130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2614130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614130 prefixEnd_2614130 := by exact prefixLift 2614130
  have htrace : WordTrace (prefixWord ++ tailWord_2614130) baseStart_2614130 baseEnd_2614130 := by
    simpa [prefixWord, tailWord_2614130, baseEnd_2614130] using wordTrace_append hprefix tailTrace_2614130
  have hstable : (prefixWord ++ tailWord_2614130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614130).length < 2 ^ (prefixWord ++ tailWord_2614130).sum := by decide
  have hdescent : baseEnd_2614130 < baseStart_2614130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614136 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_2614136 : Nat := 118140960795 + 2614136 * 2 ^ 59
def prefixEnd_2614136 : Nat := 4983230072969 + 3 ^ 40 * 2614136 * 2
def baseEnd_2614136 : Nat := 1342308264221889414577813

theorem tailTrace_2614136 : CollatzResearch.WordTrace tailWord_2614136 prefixEnd_2614136 1342308264221889414577813 := by
  unfold tailWord_2614136
  simp only [CollatzResearch.WordTrace]
  refine ⟨47672686428719602864751131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63563581904959470486334841 47672686428719602864751131)
  ·
    refine ⟨71509029643079404297126697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47672686428719602864751131 71509029643079404297126697)
    ·
      refine ⟨53631772232309553222845023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71509029643079404297126697 53631772232309553222845023)
      ·
        refine ⟨80447658348464329834267535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53631772232309553222845023 80447658348464329834267535)
        ·
          refine ⟨120671487522696494751401303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80447658348464329834267535 120671487522696494751401303)
          ·
            refine ⟨181007231284044742127101955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120671487522696494751401303 181007231284044742127101955)
            ·
              refine ⟨271510846926067113190652933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181007231284044742127101955 271510846926067113190652933)
              ·
                refine ⟨50908283798637583723247425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271510846926067113190652933 50908283798637583723247425)
                ·
                  refine ⟨38181212848978187792435569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50908283798637583723247425 38181212848978187792435569)
                  ·
                    refine ⟨28635909636733640844326677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38181212848978187792435569 28635909636733640844326677)
                    ·
                      refine ⟨1342308264221889414577813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28635909636733640844326677 1342308264221889414577813)
                      ·
                        rfl

theorem cell23_2614136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_2614136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614136 prefixEnd_2614136 := by exact prefixLift 2614136
  have htrace : WordTrace (prefixWord ++ tailWord_2614136) baseStart_2614136 baseEnd_2614136 := by
    simpa [prefixWord, tailWord_2614136, baseEnd_2614136] using wordTrace_append hprefix tailTrace_2614136
  have hstable : (prefixWord ++ tailWord_2614136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614136).length < 2 ^ (prefixWord ++ tailWord_2614136).sum := by decide
  have hdescent : baseEnd_2614136 < baseStart_2614136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614173 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2614173 : Nat := 118140960795 + 2614173 * 2 ^ 59
def prefixEnd_2614173 : Nat := 4983230072969 + 3 ^ 40 * 2614173 * 2
def baseEnd_2614173 : Nat := 1342327263006105769815143

theorem tailTrace_2614173 : CollatzResearch.WordTrace tailWord_2614173 prefixEnd_2614173 1342327263006105769815143 := by
  unfold tailWord_2614173
  simp only [CollatzResearch.WordTrace]
  refine ⟨95346722358305161048599173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63564481572203440699066115 95346722358305161048599173)
  ·
    refine ⟨17877510442182217696612345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95346722358305161048599173 17877510442182217696612345)
    ·
      refine ⟨13408132831636663272459259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17877510442182217696612345 13408132831636663272459259)
      ·
        refine ⟨20112199247454994908688889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13408132831636663272459259 20112199247454994908688889)
        ·
          refine ⟨15084149435591246181516667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20112199247454994908688889 15084149435591246181516667)
          ·
            refine ⟨22626224153386869272275001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15084149435591246181516667 22626224153386869272275001)
            ·
              refine ⟨16969668115040151954206251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22626224153386869272275001 16969668115040151954206251)
              ·
                refine ⟨25454502172560227931309377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16969668115040151954206251 25454502172560227931309377)
                ·
                  refine ⟨19090876629420170948482033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25454502172560227931309377 19090876629420170948482033)
                  ·
                    refine ⟨14318157472065128211361525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19090876629420170948482033 14318157472065128211361525)
                    ·
                      refine ⟨1342327263006105769815143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14318157472065128211361525 1342327263006105769815143)
                      ·
                        rfl

theorem cell23_2614173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2614173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614173 prefixEnd_2614173 := by exact prefixLift 2614173
  have htrace : WordTrace (prefixWord ++ tailWord_2614173) baseStart_2614173 baseEnd_2614173 := by
    simpa [prefixWord, tailWord_2614173, baseEnd_2614173] using wordTrace_append hprefix tailTrace_2614173
  have hstable : (prefixWord ++ tailWord_2614173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614173).length < 2 ^ (prefixWord ++ tailWord_2614173).sum := by decide
  have hdescent : baseEnd_2614173 < baseStart_2614173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614223 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 7]
def baseStart_2614223 : Nat := 118140960795 + 2614223 * 2 ^ 59
def prefixEnd_2614223 : Nat := 4983230072969 + 3 ^ 40 * 2614223 * 2
def baseEnd_2614223 : Nat := 149150326337647841576657

theorem tailTrace_2614223 : CollatzResearch.WordTrace tailWord_2614223 prefixEnd_2614223 149150326337647841576657 := by
  unfold tailWord_2614223
  simp only [CollatzResearch.WordTrace]
  refine ⟨95348546008124019587919323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63565697338749346391946215 95348546008124019587919323)
  ·
    refine ⟨143022819012186029381878985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95348546008124019587919323 143022819012186029381878985)
    ·
      refine ⟨107267114259139522036409239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143022819012186029381878985 107267114259139522036409239)
      ·
        refine ⟨160900671388709283054613859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107267114259139522036409239 160900671388709283054613859)
        ·
          refine ⟨241351007083063924581920789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160900671388709283054613859 241351007083063924581920789)
          ·
            refine ⟨11313328457018621464777537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 241351007083063924581920789 11313328457018621464777537)
            ·
              refine ⟨8484996342763966098583153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11313328457018621464777537 8484996342763966098583153)
              ·
                refine ⟨6363747257072974573937365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8484996342763966098583153 6363747257072974573937365)
                ·
                  refine ⟨149150326337647841576657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6363747257072974573937365 149150326337647841576657)
                  ·
                    rfl

theorem cell23_2614223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 7].length) (baseStart_2614223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614223 prefixEnd_2614223 := by exact prefixLift 2614223
  have htrace : WordTrace (prefixWord ++ tailWord_2614223) baseStart_2614223 baseEnd_2614223 := by
    simpa [prefixWord, tailWord_2614223, baseEnd_2614223] using wordTrace_append hprefix tailTrace_2614223
  have hstable : (prefixWord ++ tailWord_2614223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614223).length < 2 ^ (prefixWord ++ tailWord_2614223).sum := by decide
  have hdescent : baseEnd_2614223 < baseStart_2614223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614324 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_2614324 : Nat := 118140960795 + 2614324 * 2 ^ 59
def prefixEnd_2614324 : Nat := 4983230072969 + 3 ^ 40 * 2614324 * 2
def baseEnd_2614324 : Nat := 1342404798584934679026949

theorem tailTrace_2614324 : CollatzResearch.WordTrace tailWord_2614324 prefixEnd_2614324 1342404798584934679026949 := by
  unfold tailWord_2614324
  simp only [CollatzResearch.WordTrace]
  refine ⟨47676114890379056918673013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63568153187172075891564017 47676114890379056918673013)
  ·
    refine ⟨4469635770973036586125595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47676114890379056918673013 4469635770973036586125595)
    ·
      refine ⟨6704453656459554879188393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469635770973036586125595 6704453656459554879188393)
      ·
        refine ⟨5028340242344666159391295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6704453656459554879188393 5028340242344666159391295)
        ·
          refine ⟨7542510363516999239086943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028340242344666159391295 7542510363516999239086943)
          ·
            refine ⟨11313765545275498858630415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7542510363516999239086943 11313765545275498858630415)
            ·
              refine ⟨16970648317913248287945623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11313765545275498858630415 16970648317913248287945623)
              ·
                refine ⟨25455972476869872431918435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16970648317913248287945623 25455972476869872431918435)
                ·
                  refine ⟨38183958715304808647877653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25455972476869872431918435 38183958715304808647877653)
                  ·
                    refine ⟨1789873064779912905369265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38183958715304808647877653 1789873064779912905369265)
                    ·
                      refine ⟨1342404798584934679026949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789873064779912905369265 1342404798584934679026949)
                      ·
                        rfl

theorem cell23_2614324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_2614324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614324 prefixEnd_2614324 := by exact prefixLift 2614324
  have htrace : WordTrace (prefixWord ++ tailWord_2614324) baseStart_2614324 baseEnd_2614324 := by
    simpa [prefixWord, tailWord_2614324, baseEnd_2614324] using wordTrace_append hprefix tailTrace_2614324
  have hstable : (prefixWord ++ tailWord_2614324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614324).length < 2 ^ (prefixWord ++ tailWord_2614324).sum := by decide
  have hdescent : baseEnd_2614324 < baseStart_2614324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614330 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 6]
def baseStart_2614330 : Nat := 118140960795 + 2614330 * 2 ^ 59
def prefixEnd_2614330 : Nat := 4983230072969 + 3 ^ 40 * 2614330 * 2
def baseEnd_2614330 : Nat := 149156431052095739505769

theorem tailTrace_2614330 : CollatzResearch.WordTrace tailWord_2614330 prefixEnd_2614330 149156431052095739505769 := by
  unfold tailWord_2614330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23838112154684094215516111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63568299079157584574709629 23838112154684094215516111)
  ·
    refine ⟨35757168232026141323274167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23838112154684094215516111 35757168232026141323274167)
    ·
      refine ⟨53635752348039211984911251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35757168232026141323274167 53635752348039211984911251)
      ·
        refine ⟨80453628522058817977366877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53635752348039211984911251 80453628522058817977366877)
        ·
          refine ⟨30170110695772056741512579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80453628522058817977366877 30170110695772056741512579)
          ·
            refine ⟨45255166043658085112268869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30170110695772056741512579 45255166043658085112268869)
            ·
              refine ⟨8485343633185890958550413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45255166043658085112268869 8485343633185890958550413)
              ·
                refine ⟨3182003862444709109456405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8485343633185890958550413 3182003862444709109456405)
                ·
                  refine ⟨149156431052095739505769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3182003862444709109456405 149156431052095739505769)
                  ·
                    rfl

theorem cell23_2614330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_2614330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614330 prefixEnd_2614330 := by exact prefixLift 2614330
  have htrace : WordTrace (prefixWord ++ tailWord_2614330) baseStart_2614330 baseEnd_2614330 := by
    simpa [prefixWord, tailWord_2614330, baseEnd_2614330] using wordTrace_append hprefix tailTrace_2614330
  have hstable : (prefixWord ++ tailWord_2614330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614330).length < 2 ^ (prefixWord ++ tailWord_2614330).sum := by decide
  have hdescent : baseEnd_2614330 < baseStart_2614330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614334 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2614334 : Nat := 118140960795 + 2614334 * 2 ^ 59
def prefixEnd_2614334 : Nat := 4983230072969 + 3 ^ 40 * 2614334 * 2
def baseEnd_2614334 : Nat := 447469977797159879967301

theorem tailTrace_2614334 : CollatzResearch.WordTrace tailWord_2614334 prefixEnd_2614334 447469977797159879967301 := by
  unfold tailWord_2614334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11919074313840235693151257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63568396340481257030140037 11919074313840235693151257)
  ·
    refine ⟨8939305735380176769863443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11919074313840235693151257 8939305735380176769863443)
    ·
      refine ⟨13408958603070265154795165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8939305735380176769863443 13408958603070265154795165)
      ·
        refine ⟨5028359476151349433048187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13408958603070265154795165 5028359476151349433048187)
        ·
          refine ⟨7542539214227024149572281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5028359476151349433048187 7542539214227024149572281)
          ·
            refine ⟨5656904410670268112179211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7542539214227024149572281 5656904410670268112179211)
            ·
              refine ⟨8485356616005402168268817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656904410670268112179211 8485356616005402168268817)
              ·
                refine ⟨6364017462004051626201613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8485356616005402168268817 6364017462004051626201613)
                ·
                  refine ⟨2386506548251519359825605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6364017462004051626201613 2386506548251519359825605)
                  ·
                    refine ⟨447469977797159879967301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2386506548251519359825605 447469977797159879967301)
                    ·
                      rfl

theorem cell23_2614334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2614334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614334 prefixEnd_2614334 := by exact prefixLift 2614334
  have htrace : WordTrace (prefixWord ++ tailWord_2614334) baseStart_2614334 baseEnd_2614334 := by
    simpa [prefixWord, tailWord_2614334, baseEnd_2614334] using wordTrace_append hprefix tailTrace_2614334
  have hstable : (prefixWord ++ tailWord_2614334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614334).length < 2 ^ (prefixWord ++ tailWord_2614334).sum := by decide
  have hdescent : baseEnd_2614334 < baseStart_2614334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614357 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_2614357 : Nat := 118140960795 + 2614357 * 2 ^ 59
def prefixEnd_2614357 : Nat := 4983230072969 + 3 ^ 40 * 2614357 * 2
def baseEnd_2614357 : Nat := 1342421743446533049914297

theorem tailTrace_2614357 : CollatzResearch.WordTrace tailWord_2614357 prefixEnd_2614357 1342421743446533049914297 := by
  unfold tailWord_2614357
  simp only [CollatzResearch.WordTrace]
  refine ⟨95353433389638560473297325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63568955593092373648864883 95353433389638560473297325)
  ·
    refine ⟨35757537521114460177486497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95353433389638560473297325 35757537521114460177486497)
    ·
      refine ⟨26818153140835845133114873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35757537521114460177486497 26818153140835845133114873)
      ·
        refine ⟨20113614855626883849836155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26818153140835845133114873 20113614855626883849836155)
        ·
          refine ⟨30170422283440325774754233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20113614855626883849836155 30170422283440325774754233)
          ·
            refine ⟨22627816712580244331065675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30170422283440325774754233 22627816712580244331065675)
            ·
              refine ⟨33941725068870366496598513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22627816712580244331065675 33941725068870366496598513)
              ·
                refine ⟨25456293801652774872448885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33941725068870366496598513 25456293801652774872448885)
                ·
                  refine ⟨2386527543904947644292083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25456293801652774872448885 2386527543904947644292083)
                  ·
                    refine ⟨3579791315857421466438125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2386527543904947644292083 3579791315857421466438125)
                    ·
                      refine ⟨1342421743446533049914297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3579791315857421466438125 1342421743446533049914297)
                      ·
                        rfl

theorem cell23_2614357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_2614357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614357 prefixEnd_2614357 := by exact prefixLift 2614357
  have htrace : WordTrace (prefixWord ++ tailWord_2614357) baseStart_2614357 baseEnd_2614357 := by
    simpa [prefixWord, tailWord_2614357, baseEnd_2614357] using wordTrace_append hprefix tailTrace_2614357
  have hstable : (prefixWord ++ tailWord_2614357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614357).length < 2 ^ (prefixWord ++ tailWord_2614357).sum := by decide
  have hdescent : baseEnd_2614357 < baseStart_2614357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614367 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 4, 3, 2]
def baseStart_2614367 : Nat := 118140960795 + 2614367 * 2 ^ 59
def prefixEnd_2614367 : Nat := 4983230072969 + 3 ^ 40 * 2614367 * 2
def baseEnd_2614367 : Nat := 1342426878253078010789251

theorem tailTrace_2614367 : CollatzResearch.WordTrace tailWord_2614367 prefixEnd_2614367 1342426878253078010789251 := by
  unfold tailWord_2614367
  simp only [CollatzResearch.WordTrace]
  refine ⟨95353798119602332181161355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63569198746401554787440903 95353798119602332181161355)
  ·
    refine ⟨143030697179403498271742033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95353798119602332181161355 143030697179403498271742033)
    ·
      refine ⟨107273022884552623703806525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143030697179403498271742033 107273022884552623703806525)
      ·
        refine ⟨40227383581707233888927447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107273022884552623703806525 40227383581707233888927447)
        ·
          refine ⟨60341075372560850833391171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40227383581707233888927447 60341075372560850833391171)
          ·
            refine ⟨90511613058841276250086757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60341075372560850833391171 90511613058841276250086757)
            ·
              refine ⟨16970927448532739296891267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90511613058841276250086757 16970927448532739296891267)
              ·
                refine ⟨25456391172799108945336901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16970927448532739296891267 25456391172799108945336901)
                ·
                  refine ⟨4773073344899832927250669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25456391172799108945336901 4773073344899832927250669)
                  ·
                    refine ⟨1789902504337437347719001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4773073344899832927250669 1789902504337437347719001)
                    ·
                      refine ⟨1342426878253078010789251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789902504337437347719001 1342426878253078010789251)
                      ·
                        rfl

theorem cell23_2614367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_2614367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614367 prefixEnd_2614367 := by exact prefixLift 2614367
  have htrace : WordTrace (prefixWord ++ tailWord_2614367) baseStart_2614367 baseEnd_2614367 := by
    simpa [prefixWord, tailWord_2614367, baseEnd_2614367] using wordTrace_append hprefix tailTrace_2614367
  have hstable : (prefixWord ++ tailWord_2614367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614367).length < 2 ^ (prefixWord ++ tailWord_2614367).sum := by decide
  have hdescent : baseEnd_2614367 < baseStart_2614367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614397 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_2614397 : Nat := 118140960795 + 2614397 * 2 ^ 59
def prefixEnd_2614397 : Nat := 4983230072969 + 3 ^ 40 * 2614397 * 2
def baseEnd_2614397 : Nat := 1342442282672712893414113

theorem tailTrace_2614397 : CollatzResearch.WordTrace tailWord_2614397 prefixEnd_2614397 1342442282672712893414113 := by
  unfold tailWord_2614397
  simp only [CollatzResearch.WordTrace]
  refine ⟨95354892309493647304753445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63569928206329098203168963 95354892309493647304753445)
  ·
    refine ⟨17879042308030058869641271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95354892309493647304753445 17879042308030058869641271)
    ·
      refine ⟨26818563462045088304461907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17879042308030058869641271 26818563462045088304461907)
      ·
        refine ⟨40227845193067632456692861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26818563462045088304461907 40227845193067632456692861)
        ·
          refine ⟨15085441947400362171259823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40227845193067632456692861 15085441947400362171259823)
          ·
            refine ⟨22628162921100543256889735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15085441947400362171259823 22628162921100543256889735)
            ·
              refine ⟨33942244381650814885334603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22628162921100543256889735 33942244381650814885334603)
              ·
                refine ⟨50913366572476222328001905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33942244381650814885334603 50913366572476222328001905)
                ·
                  refine ⟨38185024929357166746001429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50913366572476222328001905 38185024929357166746001429)
                  ·
                    refine ⟨1789923043563617191218817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38185024929357166746001429 1789923043563617191218817)
                    ·
                      refine ⟨1342442282672712893414113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1789923043563617191218817 1342442282672712893414113)
                      ·
                        rfl

theorem cell23_2614397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_2614397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614397 prefixEnd_2614397 := by exact prefixLift 2614397
  have htrace : WordTrace (prefixWord ++ tailWord_2614397) baseStart_2614397 baseEnd_2614397 := by
    simpa [prefixWord, tailWord_2614397, baseEnd_2614397] using wordTrace_append hprefix tailTrace_2614397
  have hstable : (prefixWord ++ tailWord_2614397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614397).length < 2 ^ (prefixWord ++ tailWord_2614397).sum := by decide
  have hdescent : baseEnd_2614397 < baseStart_2614397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614414 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2614414 : Nat := 118140960795 + 2614414 * 2 ^ 59
def prefixEnd_2614414 : Nat := 4983230072969 + 3 ^ 40 * 2614414 * 2
def baseEnd_2614414 : Nat := 1342451011843839326901535

theorem tailTrace_2614414 : CollatzResearch.WordTrace tailWord_2614414 prefixEnd_2614414 1342451011843839326901535 := by
  unfold tailWord_2614414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11919439043804007401015287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63570341566954706138748197 11919439043804007401015287)
  ·
    refine ⟨17879158565706011101522931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11919439043804007401015287 17879158565706011101522931)
    ·
      refine ⟨26818737848559016652284397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17879158565706011101522931 26818737848559016652284397)
      ·
        refine ⟨10057026693209631244606649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26818737848559016652284397 10057026693209631244606649)
        ·
          refine ⟨7542770019907223433454987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10057026693209631244606649 7542770019907223433454987)
          ·
            refine ⟨11314155029860835150182481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7542770019907223433454987 11314155029860835150182481)
            ·
              refine ⟨8485616272395626362636861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11314155029860835150182481 8485616272395626362636861)
              ·
                refine ⟨3182106102148359885988823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8485616272395626362636861 3182106102148359885988823)
                ·
                  refine ⟨4773159153222539828983235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182106102148359885988823 4773159153222539828983235)
                  ·
                    refine ⟨7159738729833809743474853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4773159153222539828983235 7159738729833809743474853)
                    ·
                      refine ⟨1342451011843839326901535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7159738729833809743474853 1342451011843839326901535)
                      ·
                        rfl

theorem cell23_2614414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2614414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614414 prefixEnd_2614414 := by exact prefixLift 2614414
  have htrace : WordTrace (prefixWord ++ tailWord_2614414) baseStart_2614414 baseEnd_2614414 := by
    simpa [prefixWord, tailWord_2614414, baseEnd_2614414] using wordTrace_append hprefix tailTrace_2614414
  have hstable : (prefixWord ++ tailWord_2614414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614414).length < 2 ^ (prefixWord ++ tailWord_2614414).sum := by decide
  have hdescent : baseEnd_2614414 < baseStart_2614414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614464 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3]
def baseStart_2614464 : Nat := 118140960795 + 2614464 * 2 ^ 59
def prefixEnd_2614464 : Nat := 4983230072969 + 3 ^ 40 * 2614464 * 2
def baseEnd_2614464 : Nat := 1342476685876564131276305

theorem tailTrace_2614464 : CollatzResearch.WordTrace tailWord_2614464 prefixEnd_2614464 1342476685876564131276305 := by
  unfold tailWord_2614464
  simp only [CollatzResearch.WordTrace]
  refine ⟨47678668000125458873721223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63571557333500611831628297 47678668000125458873721223)
  ·
    refine ⟨71518002000188188310581835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47678668000125458873721223 71518002000188188310581835)
    ·
      refine ⟨107277003000282282465872753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71518002000188188310581835 107277003000282282465872753)
      ·
        refine ⟨80457752250211711849404565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107277003000282282465872753 80457752250211711849404565)
        ·
          refine ⟨3771457136728673992940839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80457752250211711849404565 3771457136728673992940839)
          ·
            refine ⟨5657185705093010989411259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771457136728673992940839 5657185705093010989411259)
            ·
              refine ⟨8485778557639516484116889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657185705093010989411259 8485778557639516484116889)
              ·
                refine ⟨6364333918229637363087667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8485778557639516484116889 6364333918229637363087667)
                ·
                  refine ⟨9546500877344456044631501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6364333918229637363087667 9546500877344456044631501)
                  ·
                    refine ⟨3579937829004171016736813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9546500877344456044631501 3579937829004171016736813)
                    ·
                      refine ⟨1342476685876564131276305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3579937829004171016736813 1342476685876564131276305)
                      ·
                        rfl

theorem cell23_2614464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_2614464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614464 prefixEnd_2614464 := by exact prefixLift 2614464
  have htrace : WordTrace (prefixWord ++ tailWord_2614464) baseStart_2614464 baseEnd_2614464 := by
    simpa [prefixWord, tailWord_2614464, baseEnd_2614464] using wordTrace_append hprefix tailTrace_2614464
  have hstable : (prefixWord ++ tailWord_2614464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614464).length < 2 ^ (prefixWord ++ tailWord_2614464).sum := by decide
  have hdescent : baseEnd_2614464 < baseStart_2614464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614468 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_2614468 : Nat := 118140960795 + 2614468 * 2 ^ 59
def prefixEnd_2614468 : Nat := 4983230072969 + 3 ^ 40 * 2614468 * 2
def baseEnd_2614468 : Nat := 1342478739799182115626287

theorem tailTrace_2614468 : CollatzResearch.WordTrace tailWord_2614468 prefixEnd_2614468 1342478739799182115626287 := by
  unfold tailWord_2614468
  simp only [CollatzResearch.WordTrace]
  refine ⟨47678740946118213215294029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63571654594824284287058705 47678740946118213215294029)
  ·
    refine ⟨17879527854794329955735261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47678740946118213215294029 17879527854794329955735261)
    ·
      refine ⟨6704822945547873733400723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17879527854794329955735261 6704822945547873733400723)
      ·
        refine ⟨10057234418321810600101085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6704822945547873733400723 10057234418321810600101085)
        ·
          refine ⟨3771462906870678975037907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10057234418321810600101085 3771462906870678975037907)
          ·
            refine ⟨5657194360306018462556861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771462906870678975037907 5657194360306018462556861)
            ·
              refine ⟨2121447885114756923458823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5657194360306018462556861 2121447885114756923458823)
              ·
                refine ⟨3182171827672135385188235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121447885114756923458823 3182171827672135385188235)
                ·
                  refine ⟨4773257741508203077782353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182171827672135385188235 4773257741508203077782353)
                  ·
                    refine ⟨3579943306131152308336765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4773257741508203077782353 3579943306131152308336765)
                    ·
                      refine ⟨1342478739799182115626287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3579943306131152308336765 1342478739799182115626287)
                      ·
                        rfl

theorem cell23_2614468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_2614468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614468 prefixEnd_2614468 := by exact prefixLift 2614468
  have htrace : WordTrace (prefixWord ++ tailWord_2614468) baseStart_2614468 baseEnd_2614468 := by
    simpa [prefixWord, tailWord_2614468, baseEnd_2614468] using wordTrace_append hprefix tailTrace_2614468
  have hstable : (prefixWord ++ tailWord_2614468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614468).length < 2 ^ (prefixWord ++ tailWord_2614468).sum := by decide
  have hdescent : baseEnd_2614468 < baseStart_2614468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614497 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 2, 6]
def baseStart_2614497 : Nat := 118140960795 + 2614497 * 2 ^ 59
def prefixEnd_2614497 : Nat := 4983230072969 + 3 ^ 40 * 2614497 * 2
def baseEnd_2614497 : Nat := 447497876912720834054551

theorem tailTrace_2614497 : CollatzResearch.WordTrace tailWord_2614497 prefixEnd_2614497 447497876912720834054551 := by
  unfold tailWord_2614497
  simp only [CollatzResearch.WordTrace]
  refine ⟨95358539609131364383393745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63572359739420909588929163 95358539609131364383393745)
  ·
    refine ⟨71518904706848523287545309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95358539609131364383393745 71518904706848523287545309)
    ·
      refine ⟨26819589265068196232829491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71518904706848523287545309 26819589265068196232829491)
      ·
        refine ⟨40229383897602294349244237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26819589265068196232829491 40229383897602294349244237)
        ·
          refine ⟨15086018961600860380966589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40229383897602294349244237 15086018961600860380966589)
          ·
            refine ⟨5657257110600322642862471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15086018961600860380966589 5657257110600322642862471)
            ·
              refine ⟨8485885665900483964293707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657257110600322642862471 8485885665900483964293707)
              ·
                refine ⟨12728828498850725946440561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8485885665900483964293707 12728828498850725946440561)
                ·
                  refine ⟨9546621374138044459830421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12728828498850725946440561 9546621374138044459830421)
                  ·
                    refine ⟨447497876912720834054551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9546621374138044459830421 447497876912720834054551)
                    ·
                      rfl

theorem cell23_2614497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_2614497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614497 prefixEnd_2614497 := by exact prefixLift 2614497
  have htrace : WordTrace (prefixWord ++ tailWord_2614497) baseStart_2614497 baseEnd_2614497 := by
    simpa [prefixWord, tailWord_2614497, baseEnd_2614497] using wordTrace_append hprefix tailTrace_2614497
  have hstable : (prefixWord ++ tailWord_2614497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614497).length < 2 ^ (prefixWord ++ tailWord_2614497).sum := by decide
  have hdescent : baseEnd_2614497 < baseStart_2614497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614520 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_2614520 : Nat := 118140960795 + 2614520 * 2 ^ 59
def prefixEnd_2614520 : Nat := 4983230072969 + 3 ^ 40 * 2614520 * 2
def baseEnd_2614520 : Nat := 1342505440793215912176047

theorem tailTrace_2614520 : CollatzResearch.WordTrace tailWord_2614520 prefixEnd_2614520 1342505440793215912176047 := by
  unfold tailWord_2614520
  simp only [CollatzResearch.WordTrace]
  refine ⟨47679689244024019655740507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63572918992032026207654009 47679689244024019655740507)
  ·
    refine ⟨71519533866036029483610761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47679689244024019655740507 71519533866036029483610761)
    ·
      refine ⟨53639650399527022112708071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71519533866036029483610761 53639650399527022112708071)
      ·
        refine ⟨80459475599290533169062107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53639650399527022112708071 80459475599290533169062107)
        ·
          refine ⟨120689213398935799753593161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80459475599290533169062107 120689213398935799753593161)
          ·
            refine ⟨90516910049201849815194871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120689213398935799753593161 90516910049201849815194871)
            ·
              refine ⟨135775365073802774722792307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90516910049201849815194871 135775365073802774722792307)
              ·
                refine ⟨203663047610704162084188461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135775365073802774722792307 203663047610704162084188461)
                ·
                  refine ⟨76373642854014060781570673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203663047610704162084188461 76373642854014060781570673)
                  ·
                    refine ⟨57280232140510545586178005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76373642854014060781570673 57280232140510545586178005)
                    ·
                      refine ⟨1342505440793215912176047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57280232140510545586178005 1342505440793215912176047)
                      ·
                        rfl

theorem cell23_2614520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_2614520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614520 prefixEnd_2614520 := by exact prefixLift 2614520
  have htrace : WordTrace (prefixWord ++ tailWord_2614520) baseStart_2614520 baseEnd_2614520 := by
    simpa [prefixWord, tailWord_2614520, baseEnd_2614520] using wordTrace_append hprefix tailTrace_2614520
  have hstable : (prefixWord ++ tailWord_2614520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614520).length < 2 ^ (prefixWord ++ tailWord_2614520).sum := by decide
  have hdescent : baseEnd_2614520 < baseStart_2614520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614537 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 3]
def baseStart_2614537 : Nat := 118140960795 + 2614537 * 2 ^ 59
def prefixEnd_2614537 : Nat := 4983230072969 + 3 ^ 40 * 2614537 * 2
def baseEnd_2614537 : Nat := 1342514169964342345663469

theorem tailTrace_2614537 : CollatzResearch.WordTrace tailWord_2614537 prefixEnd_2614537 1342514169964342345663469 := by
  unfold tailWord_2614537
  simp only [CollatzResearch.WordTrace]
  refine ⟨95359998528986451214849865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63573332352657634143233243 95359998528986451214849865)
  ·
    refine ⟨71519998896739838411137399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95359998528986451214849865 71519998896739838411137399)
    ·
      refine ⟨107279998345109757616706099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71519998896739838411137399 107279998345109757616706099)
      ·
        refine ⟨160919997517664636425059149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107279998345109757616706099 160919997517664636425059149)
        ·
          refine ⟨60344999069124238659397181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160919997517664636425059149 60344999069124238659397181)
          ·
            refine ⟨22629374650921589497273943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60344999069124238659397181 22629374650921589497273943)
            ·
              refine ⟨33944061976382384245910915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22629374650921589497273943 33944061976382384245910915)
              ·
                refine ⟨50916092964573576368866373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33944061976382384245910915 50916092964573576368866373)
                ·
                  refine ⟨9546767430857545569162445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50916092964573576368866373 9546767430857545569162445)
                  ·
                    refine ⟨3580037786571579588435917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9546767430857545569162445 3580037786571579588435917)
                    ·
                      refine ⟨1342514169964342345663469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580037786571579588435917 1342514169964342345663469)
                      ·
                        rfl

theorem cell23_2614537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_2614537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614537 prefixEnd_2614537 := by exact prefixLift 2614537
  have htrace : WordTrace (prefixWord ++ tailWord_2614537) baseStart_2614537 baseEnd_2614537 := by
    simpa [prefixWord, tailWord_2614537, baseEnd_2614537] using wordTrace_append hprefix tailTrace_2614537
  have hstable : (prefixWord ++ tailWord_2614537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614537).length < 2 ^ (prefixWord ++ tailWord_2614537).sum := by decide
  have hdescent : baseEnd_2614537 < baseStart_2614537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614554 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_2614554 : Nat := 118140960795 + 2614554 * 2 ^ 59
def prefixEnd_2614554 : Nat := 4983230072969 + 3 ^ 40 * 2614554 * 2
def baseEnd_2614554 : Nat := 1342522899135468779150891

theorem tailTrace_2614554 : CollatzResearch.WordTrace tailWord_2614554 prefixEnd_2614554 1342522899135468779150891 := by
  unfold tailWord_2614554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23840154642481215779554679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63573745713283242078812477 23840154642481215779554679)
  ·
    refine ⟨35760231963721823669332019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23840154642481215779554679 35760231963721823669332019)
    ·
      refine ⟨53640347945582735503998029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35760231963721823669332019 53640347945582735503998029)
      ·
        refine ⟨20115130479593525813999261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53640347945582735503998029 20115130479593525813999261)
        ·
          refine ⟨7543173929847572180249723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20115130479593525813999261 7543173929847572180249723)
          ·
            refine ⟨11314760894771358270374585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7543173929847572180249723 11314760894771358270374585)
            ·
              refine ⟨8486070671078518702780939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11314760894771358270374585 8486070671078518702780939)
              ·
                refine ⟨12729106006617778054171409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8486070671078518702780939 12729106006617778054171409)
                ·
                  refine ⟨9546829504963333540628557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12729106006617778054171409 9546829504963333540628557)
                  ·
                    refine ⟨3580061064361250077735709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9546829504963333540628557 3580061064361250077735709)
                    ·
                      refine ⟨1342522899135468779150891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580061064361250077735709 1342522899135468779150891)
                      ·
                        rfl

theorem cell23_2614554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_2614554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614554 prefixEnd_2614554 := by exact prefixLift 2614554
  have htrace : WordTrace (prefixWord ++ tailWord_2614554) baseStart_2614554 baseEnd_2614554 := by
    simpa [prefixWord, tailWord_2614554, baseEnd_2614554] using wordTrace_append hprefix tailTrace_2614554
  have hstable : (prefixWord ++ tailWord_2614554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614554).length < 2 ^ (prefixWord ++ tailWord_2614554).sum := by decide
  have hdescent : baseEnd_2614554 < baseStart_2614554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614664 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 3, 5]
def baseStart_2614664 : Nat := 118140960795 + 2614664 * 2 ^ 59
def prefixEnd_2614664 : Nat := 4983230072969 + 3 ^ 40 * 2614664 * 2
def baseEnd_2614664 : Nat := 447526460669154449591795

theorem tailTrace_2614664 : CollatzResearch.WordTrace tailWord_2614664 prefixEnd_2614664 447526460669154449591795 := by
  unfold tailWord_2614664
  simp only [CollatzResearch.WordTrace]
  refine ⟨47682315299763175952361523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63576420399684234603148697 47682315299763175952361523)
  ·
    refine ⟨71523472949644763928542285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47682315299763175952361523 71523472949644763928542285)
    ·
      refine ⟨26821302356116786473203357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71523472949644763928542285 26821302356116786473203357)
      ·
        refine ⟨10057988383543794927451259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26821302356116786473203357 10057988383543794927451259)
        ·
          refine ⟨15086982575315692391176889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10057988383543794927451259 15086982575315692391176889)
          ·
            refine ⟨11315236931486769293382667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15086982575315692391176889 11315236931486769293382667)
            ·
              refine ⟨16972855397230153940074001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11315236931486769293382667 16972855397230153940074001)
              ·
                refine ⟨12729641547922615455055501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16972855397230153940074001 12729641547922615455055501)
                ·
                  refine ⟨4773615580470980795645813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12729641547922615455055501 4773615580470980795645813)
                  ·
                    refine ⟨447526460669154449591795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4773615580470980795645813 447526460669154449591795)
                    ·
                      rfl

theorem cell23_2614664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_2614664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614664 prefixEnd_2614664 := by exact prefixLift 2614664
  have htrace : WordTrace (prefixWord ++ tailWord_2614664) baseStart_2614664 baseEnd_2614664 := by
    simpa [prefixWord, tailWord_2614664, baseEnd_2614664] using wordTrace_append hprefix tailTrace_2614664
  have hstable : (prefixWord ++ tailWord_2614664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614664).length < 2 ^ (prefixWord ++ tailWord_2614664).sum := by decide
  have hdescent : baseEnd_2614664 < baseStart_2614664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614695 : List Nat := [1, 1, 6, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2614695 : Nat := 118140960795 + 2614695 * 2 ^ 59
def prefixEnd_2614695 : Nat := 4983230072969 + 3 ^ 40 * 2614695 * 2
def baseEnd_2614695 : Nat := 1342595299907752727487743

theorem tailTrace_2614695 : CollatzResearch.WordTrace tailWord_2614695 prefixEnd_2614695 1342595299907752727487743 := by
  unfold tailWord_2614695
  simp only [CollatzResearch.WordTrace]
  refine ⟨95365761262414044199101539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63577174174942696132734359 95365761262414044199101539)
  ·
    refine ⟨143048641893621066298652309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95365761262414044199101539 143048641893621066298652309)
    ·
      refine ⟨6705405088763487482749327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 143048641893621066298652309 6705405088763487482749327)
      ·
        refine ⟨10058107633145231224123991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6705405088763487482749327 10058107633145231224123991)
        ·
          refine ⟨15087161449717846836185987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10058107633145231224123991 15087161449717846836185987)
          ·
            refine ⟨22630742174576770254278981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15087161449717846836185987 22630742174576770254278981)
            ·
              refine ⟨4243264157733144422677309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22630742174576770254278981 4243264157733144422677309)
              ·
                refine ⟨1591224059149929158503991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4243264157733144422677309 1591224059149929158503991)
                ·
                  refine ⟨2386836088724893737755987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591224059149929158503991 2386836088724893737755987)
                  ·
                    refine ⟨3580254133087340606633981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2386836088724893737755987 3580254133087340606633981)
                    ·
                      refine ⟨1342595299907752727487743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580254133087340606633981 1342595299907752727487743)
                      ·
                        rfl

theorem cell23_2614695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2614695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614695 prefixEnd_2614695 := by exact prefixLift 2614695
  have htrace : WordTrace (prefixWord ++ tailWord_2614695) baseStart_2614695 baseEnd_2614695 := by
    simpa [prefixWord, tailWord_2614695, baseEnd_2614695] using wordTrace_append hprefix tailTrace_2614695
  have hstable : (prefixWord ++ tailWord_2614695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614695).length < 2 ^ (prefixWord ++ tailWord_2614695).sum := by decide
  have hdescent : baseEnd_2614695 < baseStart_2614695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614697 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_2614697 : Nat := 118140960795 + 2614697 * 2 ^ 59
def prefixEnd_2614697 : Nat := 4983230072969 + 3 ^ 40 * 2614697 * 2
def baseEnd_2614697 : Nat := 1342596326869061719662733

theorem tailTrace_2614697 : CollatzResearch.WordTrace tailWord_2614697 prefixEnd_2614697 1342596326869061719662733 := by
  unfold tailWord_2614697
  simp only [CollatzResearch.WordTrace]
  refine ⟨95365834208406798540674345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63577222805604532360449563 95365834208406798540674345)
  ·
    refine ⟨71524375656305098905505759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95365834208406798540674345 71524375656305098905505759)
    ·
      refine ⟨107286563484457648358258639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71524375656305098905505759 107286563484457648358258639)
      ·
        refine ⟨160929845226686472537387959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107286563484457648358258639 160929845226686472537387959)
        ·
          refine ⟨241394767840029708806081939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160929845226686472537387959 241394767840029708806081939)
          ·
            refine ⟨362092151760044563209122909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241394767840029708806081939 362092151760044563209122909)
            ·
              refine ⟨135784556910016711203421091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362092151760044563209122909 135784556910016711203421091)
              ·
                refine ⟨203676835365025066805131637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135784556910016711203421091 203676835365025066805131637)
                ·
                  refine ⟨19094703315471100012981091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203676835365025066805131637 19094703315471100012981091)
                  ·
                    refine ⟨28642054973206650019471637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19094703315471100012981091 28642054973206650019471637)
                    ·
                      refine ⟨1342596326869061719662733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28642054973206650019471637 1342596326869061719662733)
                      ·
                        rfl

theorem cell23_2614697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_2614697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614697 prefixEnd_2614697 := by exact prefixLift 2614697
  have htrace : WordTrace (prefixWord ++ tailWord_2614697) baseStart_2614697 baseEnd_2614697 := by
    simpa [prefixWord, tailWord_2614697, baseEnd_2614697] using wordTrace_append hprefix tailTrace_2614697
  have hstable : (prefixWord ++ tailWord_2614697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614697).length < 2 ^ (prefixWord ++ tailWord_2614697).sum := by decide
  have hdescent : baseEnd_2614697 < baseStart_2614697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614704 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3]
def baseStart_2614704 : Nat := 118140960795 + 2614704 * 2 ^ 59
def prefixEnd_2614704 : Nat := 4983230072969 + 3 ^ 40 * 2614704 * 2
def baseEnd_2614704 : Nat := 1342599921233643192275201

theorem tailTrace_2614704 : CollatzResearch.WordTrace tailWord_2614704 prefixEnd_2614704 1342599921233643192275201 := by
  unfold tailWord_2614704
  simp only [CollatzResearch.WordTrace]
  refine ⟨47683044759690719368089583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63577393012920959157452777 47683044759690719368089583)
  ·
    refine ⟨71524567139536079052134375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47683044759690719368089583 71524567139536079052134375)
    ·
      refine ⟨107286850709304118578201563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71524567139536079052134375 107286850709304118578201563)
      ·
        refine ⟨160930276063956177867302345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107286850709304118578201563 160930276063956177867302345)
        ·
          refine ⟨120697707047967133400476759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160930276063956177867302345 120697707047967133400476759)
          ·
            refine ⟨181046560571950700100715139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120697707047967133400476759 181046560571950700100715139)
            ·
              refine ⟨271569840857926050151072709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181046560571950700100715139 271569840857926050151072709)
              ·
                refine ⟨50919345160861134403326133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271569840857926050151072709 50919345160861134403326133)
                ·
                  refine ⟨4773688608830731350311825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50919345160861134403326133 4773688608830731350311825)
                  ·
                    refine ⟨3580266456623048512733869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4773688608830731350311825 3580266456623048512733869)
                    ·
                      refine ⟨1342599921233643192275201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580266456623048512733869 1342599921233643192275201)
                      ·
                        rfl

theorem cell23_2614704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_2614704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614704 prefixEnd_2614704 := by exact prefixLift 2614704
  have htrace : WordTrace (prefixWord ++ tailWord_2614704) baseStart_2614704 baseEnd_2614704 := by
    simpa [prefixWord, tailWord_2614704, baseEnd_2614704] using wordTrace_append hprefix tailTrace_2614704
  have hstable : (prefixWord ++ tailWord_2614704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614704).length < 2 ^ (prefixWord ++ tailWord_2614704).sum := by decide
  have hdescent : baseEnd_2614704 < baseStart_2614704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614728 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 2, 4]
def baseStart_2614728 : Nat := 118140960795 + 2614728 * 2 ^ 59
def prefixEnd_2614728 : Nat := 4983230072969 + 3 ^ 40 * 2614728 * 2
def baseEnd_2614728 : Nat := 447537414923117032791697

theorem tailTrace_2614728 : CollatzResearch.WordTrace tailWord_2614728 prefixEnd_2614728 447537414923117032791697 := by
  unfold tailWord_2614728
  simp only [CollatzResearch.WordTrace]
  refine ⟨47683482435647245417526419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63577976580862993890035225 47683482435647245417526419)
  ·
    refine ⟨71525223653470868126289629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47683482435647245417526419 71525223653470868126289629)
    ·
      refine ⟨26821958870051575547358611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71525223653470868126289629 26821958870051575547358611)
      ·
        refine ⟨40232938305077363321037917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26821958870051575547358611 40232938305077363321037917)
        ·
          refine ⟨15087351864404011245389219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40232938305077363321037917 15087351864404011245389219)
          ·
            refine ⟨22631027796606016868083829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15087351864404011245389219 22631027796606016868083829)
            ·
              refine ⟨2121658855931814081382859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22631027796606016868083829 2121658855931814081382859)
              ·
                refine ⟨3182488283897721122074289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121658855931814081382859 3182488283897721122074289)
                ·
                  refine ⟨2386866212923290841555717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3182488283897721122074289 2386866212923290841555717)
                  ·
                    refine ⟨447537414923117032791697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2386866212923290841555717 447537414923117032791697)
                    ·
                      rfl

theorem cell23_2614728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_2614728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614728 prefixEnd_2614728 := by exact prefixLift 2614728
  have htrace : WordTrace (prefixWord ++ tailWord_2614728) baseStart_2614728 baseEnd_2614728 := by
    simpa [prefixWord, tailWord_2614728, baseEnd_2614728] using wordTrace_append hprefix tailTrace_2614728
  have hstable : (prefixWord ++ tailWord_2614728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614728).length < 2 ^ (prefixWord ++ tailWord_2614728).sum := by decide
  have hdescent : baseEnd_2614728 < baseStart_2614728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614751 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 3]
def baseStart_2614751 : Nat := 118140960795 + 2614751 * 2 ^ 59
def prefixEnd_2614751 : Nat := 4983230072969 + 3 ^ 40 * 2614751 * 2
def baseEnd_2614751 : Nat := 1342624054824404508387485

theorem tailTrace_2614751 : CollatzResearch.WordTrace tailWord_2614751 prefixEnd_2614751 1342624054824404508387485 := by
  unfold tailWord_2614751
  simp only [CollatzResearch.WordTrace]
  refine ⟨95367803750211165763140107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63578535833474110508760071 95367803750211165763140107)
  ·
    refine ⟨143051705625316748644710161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95367803750211165763140107 143051705625316748644710161)
    ·
      refine ⟨107288779218987561483532621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143051705625316748644710161 107288779218987561483532621)
      ·
        refine ⟨40233292207120335556324733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107288779218987561483532621 40233292207120335556324733)
        ·
          refine ⟨15087484577670125833621775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40233292207120335556324733 15087484577670125833621775)
          ·
            refine ⟨22631226866505188750432663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15087484577670125833621775 22631226866505188750432663)
            ·
              refine ⟨33946840299757783125648995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22631226866505188750432663 33946840299757783125648995)
              ·
                refine ⟨50920260449636674688473493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33946840299757783125648995 50920260449636674688473493)
                ·
                  refine ⟨2386887208576719126022195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50920260449636674688473493 2386887208576719126022195)
                  ·
                    refine ⟨3580330812865078689033293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2386887208576719126022195 3580330812865078689033293)
                    ·
                      refine ⟨1342624054824404508387485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580330812865078689033293 1342624054824404508387485)
                      ·
                        rfl

theorem cell23_2614751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_2614751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614751 prefixEnd_2614751 := by exact prefixLift 2614751
  have htrace : WordTrace (prefixWord ++ tailWord_2614751) baseStart_2614751 baseEnd_2614751 := by
    simpa [prefixWord, tailWord_2614751, baseEnd_2614751] using wordTrace_append hprefix tailTrace_2614751
  have hstable : (prefixWord ++ tailWord_2614751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614751).length < 2 ^ (prefixWord ++ tailWord_2614751).sum := by decide
  have hdescent : baseEnd_2614751 < baseStart_2614751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614785 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_2614785 : Nat := 118140960795 + 2614785 * 2 ^ 59
def prefixEnd_2614785 : Nat := 4983230072969 + 3 ^ 40 * 2614785 * 2
def baseEnd_2614785 : Nat := 1342641513166657375362329

theorem tailTrace_2614785 : CollatzResearch.WordTrace tailWord_2614785 prefixEnd_2614785 1342641513166657375362329 := by
  unfold tailWord_2614785
  simp only [CollatzResearch.WordTrace]
  refine ⟨95369043832087989569877809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63579362554725326379918539 95369043832087989569877809)
  ·
    refine ⟨71526782874065992177408357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95369043832087989569877809 71526782874065992177408357)
    ·
      refine ⟨13411271788887373533264067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71526782874065992177408357 13411271788887373533264067)
      ·
        refine ⟨20116907683331060299896101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13411271788887373533264067 20116907683331060299896101)
        ·
          refine ⟨3771920190624573806230519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20116907683331060299896101 3771920190624573806230519)
          ·
            refine ⟨5657880285936860709345779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771920190624573806230519 5657880285936860709345779)
            ·
              refine ⟨8486820428905291064018669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5657880285936860709345779 8486820428905291064018669)
              ·
                refine ⟨3182557660839484149007001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8486820428905291064018669 3182557660839484149007001)
                ·
                  refine ⟨2386918245629613111755251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3182557660839484149007001 2386918245629613111755251)
                  ·
                    refine ⟨3580377368444419667632877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2386918245629613111755251 3580377368444419667632877)
                    ·
                      refine ⟨1342641513166657375362329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580377368444419667632877 1342641513166657375362329)
                      ·
                        rfl

theorem cell23_2614785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_2614785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614785 prefixEnd_2614785 := by exact prefixLift 2614785
  have htrace : WordTrace (prefixWord ++ tailWord_2614785) baseStart_2614785 baseEnd_2614785 := by
    simpa [prefixWord, tailWord_2614785, baseEnd_2614785] using wordTrace_append hprefix tailTrace_2614785
  have hstable : (prefixWord ++ tailWord_2614785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614785).length < 2 ^ (prefixWord ++ tailWord_2614785).sum := by decide
  have hdescent : baseEnd_2614785 < baseStart_2614785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614834 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2614834 : Nat := 118140960795 + 2614834 * 2 ^ 59
def prefixEnd_2614834 : Nat := 4983230072969 + 3 ^ 40 * 2614834 * 2
def baseEnd_2614834 : Nat := 1342666673718727683649603

theorem tailTrace_2614834 : CollatzResearch.WordTrace tailWord_2614834 prefixEnd_2614834 1342666673718727683649603 := by
  unfold tailWord_2614834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23842707752227617734602889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63580554005940313958941037 23842707752227617734602889)
  ·
    refine ⟨17882030814170713300952167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23842707752227617734602889 17882030814170713300952167)
    ·
      refine ⟨26823046221256069951428251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17882030814170713300952167 26823046221256069951428251)
      ·
        refine ⟨40234569331884104927142377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26823046221256069951428251 40234569331884104927142377)
        ·
          refine ⟨30175926998913078695356783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40234569331884104927142377 30175926998913078695356783)
          ·
            refine ⟨45263890498369618043035175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30175926998913078695356783 45263890498369618043035175)
            ·
              refine ⟨67895835747554427064552763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45263890498369618043035175 67895835747554427064552763)
              ·
                refine ⟨101843753621331640596829145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67895835747554427064552763 101843753621331640596829145)
                ·
                  refine ⟨76382815215998730447621859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101843753621331640596829145 76382815215998730447621859)
                  ·
                    refine ⟨114574222823998095671432789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76382815215998730447621859 114574222823998095671432789)
                    ·
                      refine ⟨1342666673718727683649603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114574222823998095671432789 1342666673718727683649603)
                      ·
                        rfl

theorem cell23_2614834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2614834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614834 prefixEnd_2614834 := by exact prefixLift 2614834
  have htrace : WordTrace (prefixWord ++ tailWord_2614834) baseStart_2614834 baseEnd_2614834 := by
    simpa [prefixWord, tailWord_2614834, baseEnd_2614834] using wordTrace_append hprefix tailTrace_2614834
  have hstable : (prefixWord ++ tailWord_2614834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614834).length < 2 ^ (prefixWord ++ tailWord_2614834).sum := by decide
  have hdescent : baseEnd_2614834 < baseStart_2614834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614841 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2614841 : Nat := 118140960795 + 2614841 * 2 ^ 59
def prefixEnd_2614841 : Nat := 4983230072969 + 3 ^ 40 * 2614841 * 2
def baseEnd_2614841 : Nat := 1342670268083309156262071

theorem tailTrace_2614841 : CollatzResearch.WordTrace tailWord_2614841 prefixEnd_2614841 1342670268083309156262071 := by
  unfold tailWord_2614841
  simp only [CollatzResearch.WordTrace]
  refine ⟨95371086319885111133916377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63580724213256740755944251 95371086319885111133916377)
  ·
    refine ⟨71528314739913833350437283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95371086319885111133916377 71528314739913833350437283)
    ·
      refine ⟨107292472109870750025655925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71528314739913833350437283 107292472109870750025655925)
      ·
        refine ⟨10058669260300382814905243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107292472109870750025655925 10058669260300382814905243)
        ·
          refine ⟨15088003890450574222357865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10058669260300382814905243 15088003890450574222357865)
          ·
            refine ⟨11316002917837930666768399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15088003890450574222357865 11316002917837930666768399)
            ·
              refine ⟨16974004376756896000152599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11316002917837930666768399 16974004376756896000152599)
              ·
                refine ⟨25461006565135344000228899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16974004376756896000152599 25461006565135344000228899)
                ·
                  refine ⟨38191509847703016000343349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25461006565135344000228899 38191509847703016000343349)
                  ·
                    refine ⟨3580454048222157750032189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38191509847703016000343349 3580454048222157750032189)
                    ·
                      refine ⟨1342670268083309156262071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580454048222157750032189 1342670268083309156262071)
                      ·
                        rfl

theorem cell23_2614841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2614841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614841 prefixEnd_2614841 := by exact prefixLift 2614841
  have htrace : WordTrace (prefixWord ++ tailWord_2614841) baseStart_2614841 baseEnd_2614841 := by
    simpa [prefixWord, tailWord_2614841, baseEnd_2614841] using wordTrace_append hprefix tailTrace_2614841
  have hstable : (prefixWord ++ tailWord_2614841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614841).length < 2 ^ (prefixWord ++ tailWord_2614841).sum := by decide
  have hdescent : baseEnd_2614841 < baseStart_2614841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614874 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_2614874 : Nat := 118140960795 + 2614874 * 2 ^ 59
def prefixEnd_2614874 : Nat := 4983230072969 + 3 ^ 40 * 2614874 * 2
def baseEnd_2614874 : Nat := 447562404314969175716473

theorem tailTrace_2614874 : CollatzResearch.WordTrace tailWord_2614874 prefixEnd_2614874 447562404314969175716473 := by
  unfold tailWord_2614874
  simp only [CollatzResearch.WordTrace]
  refine ⟨23843072482191389442466919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63581526619177038513245117 23843072482191389442466919)
  ·
    refine ⟨35764608723287084163700379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23843072482191389442466919 35764608723287084163700379)
    ·
      refine ⟨53646913084930626245550569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35764608723287084163700379 53646913084930626245550569)
      ·
        refine ⟨40235184813697969684162927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53646913084930626245550569 40235184813697969684162927)
        ·
          refine ⟨60352777220546954526244391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40235184813697969684162927 60352777220546954526244391)
          ·
            refine ⟨90529165830820431789366587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60352777220546954526244391 90529165830820431789366587)
            ·
              refine ⟨135793748746230647684049881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90529165830820431789366587 135793748746230647684049881)
              ·
                refine ⟨101845311559672985763037411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135793748746230647684049881 101845311559672985763037411)
                ·
                  refine ⟨152767967339509478644556117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101845311559672985763037411 152767967339509478644556117)
                  ·
                    refine ⟨447562404314969175716473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 152767967339509478644556117 447562404314969175716473)
                    ·
                      rfl

theorem cell23_2614874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_2614874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614874 prefixEnd_2614874 := by exact prefixLift 2614874
  have htrace : WordTrace (prefixWord ++ tailWord_2614874) baseStart_2614874 baseEnd_2614874 := by
    simpa [prefixWord, tailWord_2614874, baseEnd_2614874] using wordTrace_append hprefix tailTrace_2614874
  have hstable : (prefixWord ++ tailWord_2614874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614874).length < 2 ^ (prefixWord ++ tailWord_2614874).sum := by decide
  have hdescent : baseEnd_2614874 < baseStart_2614874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614881 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2614881 : Nat := 118140960795 + 2614881 * 2 ^ 59
def prefixEnd_2614881 : Nat := 4983230072969 + 3 ^ 40 * 2614881 * 2
def baseEnd_2614881 : Nat := 1342690807309488999761887

theorem tailTrace_2614881 : CollatzResearch.WordTrace tailWord_2614881 prefixEnd_2614881 1342690807309488999761887 := by
  unfold tailWord_2614881
  simp only [CollatzResearch.WordTrace]
  refine ⟨95372545239740197965372497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63581696826493465310248331 95372545239740197965372497)
  ·
    refine ⟨71529408929805148474029373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95372545239740197965372497 71529408929805148474029373)
    ·
      refine ⟨26823528348676930677761015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71529408929805148474029373 26823528348676930677761015)
      ·
        refine ⟨40235292523015396016641523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26823528348676930677761015 40235292523015396016641523)
        ·
          refine ⟨60352938784523094024962285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40235292523015396016641523 60352938784523094024962285)
          ·
            refine ⟨22632352044196160259360857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60352938784523094024962285 22632352044196160259360857)
            ·
              refine ⟨16974264033147120194520643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22632352044196160259360857 16974264033147120194520643)
              ·
                refine ⟨25461396049720680291780965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16974264033147120194520643 25461396049720680291780965)
                ·
                  refine ⟨4774011759322627554708931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25461396049720680291780965 4774011759322627554708931)
                  ·
                    refine ⟨7161017638983941332063397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4774011759322627554708931 7161017638983941332063397)
                    ·
                      refine ⟨1342690807309488999761887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7161017638983941332063397 1342690807309488999761887)
                      ·
                        rfl

theorem cell23_2614881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2614881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614881 prefixEnd_2614881 := by exact prefixLift 2614881
  have htrace : WordTrace (prefixWord ++ tailWord_2614881) baseStart_2614881 baseEnd_2614881 := by
    simpa [prefixWord, tailWord_2614881, baseEnd_2614881] using wordTrace_append hprefix tailTrace_2614881
  have hstable : (prefixWord ++ tailWord_2614881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614881).length < 2 ^ (prefixWord ++ tailWord_2614881).sum := by decide
  have hdescent : baseEnd_2614881 < baseStart_2614881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614904 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 12]
def baseStart_2614904 : Nat := 118140960795 + 2614904 * 2 ^ 59
def prefixEnd_2614904 : Nat := 4983230072969 + 3 ^ 40 * 2614904 * 2
def baseEnd_2614904 : Nat := 149189179707171378863809

theorem tailTrace_2614904 : CollatzResearch.WordTrace tailWord_2614904 prefixEnd_2614904 149189179707171378863809 := by
  unfold tailWord_2614904
  simp only [CollatzResearch.WordTrace]
  refine ⟨47686692059328436446729883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63582256079104581928973177 47686692059328436446729883)
  ·
    refine ⟨71530038088992654670094825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47686692059328436446729883 71530038088992654670094825)
    ·
      refine ⟨53647528566744491002571119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71530038088992654670094825 53647528566744491002571119)
      ·
        refine ⟨80471292850116736503856679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53647528566744491002571119 80471292850116736503856679)
        ·
          refine ⟨120706939275175104755785019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80471292850116736503856679 120706939275175104755785019)
          ·
            refine ⟨181060408912762657133677529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120706939275175104755785019 181060408912762657133677529)
            ·
              refine ⟨135795306684571992850258147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181060408912762657133677529 135795306684571992850258147)
              ·
                refine ⟨203692960026857989275387221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135795306684571992850258147 203692960026857989275387221)
                ·
                  refine ⟨149189179707171378863809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 203692960026857989275387221 149189179707171378863809)
                  ·
                    rfl

theorem cell23_2614904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 12].length) (baseStart_2614904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614904 prefixEnd_2614904 := by exact prefixLift 2614904
  have htrace : WordTrace (prefixWord ++ tailWord_2614904) baseStart_2614904 baseEnd_2614904 := by
    simpa [prefixWord, tailWord_2614904, baseEnd_2614904] using wordTrace_append hprefix tailTrace_2614904
  have hstable : (prefixWord ++ tailWord_2614904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614904).length < 2 ^ (prefixWord ++ tailWord_2614904).sum := by decide
  have hdescent : baseEnd_2614904 < baseStart_2614904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614942 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2614942 : Nat := 118140960795 + 2614942 * 2 ^ 59
def prefixEnd_2614942 : Nat := 4983230072969 + 3 ^ 40 * 2614942 * 2
def baseEnd_2614942 : Nat := 447574043209804420366369

theorem tailTrace_2614942 : CollatzResearch.WordTrace tailWord_2614942 prefixEnd_2614942 447574043209804420366369 := by
  unfold tailWord_2614942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11921846261564900672917885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63583180061679470255562053 11921846261564900672917885)
  ·
    refine ⟨4470692348086837752344207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11921846261564900672917885 4470692348086837752344207)
    ·
      refine ⟨6706038522130256628516311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4470692348086837752344207 6706038522130256628516311)
      ·
        refine ⟨10059057783195384942774467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6706038522130256628516311 10059057783195384942774467)
        ·
          refine ⟨15088586674793077414161701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10059057783195384942774467 15088586674793077414161701)
          ·
            refine ⟨2829110001523702015155319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15088586674793077414161701 2829110001523702015155319)
            ·
              refine ⟨4243665002285553022732979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829110001523702015155319 4243665002285553022732979)
              ·
                refine ⟨6365497503428329534099469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4243665002285553022732979 6365497503428329534099469)
                ·
                  refine ⟨2387061563785623575287301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6365497503428329534099469 2387061563785623575287301)
                  ·
                    refine ⟨447574043209804420366369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2387061563785623575287301 447574043209804420366369)
                    ·
                      rfl

theorem cell23_2614942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2614942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614942 prefixEnd_2614942 := by exact prefixLift 2614942
  have htrace : WordTrace (prefixWord ++ tailWord_2614942) baseStart_2614942 baseEnd_2614942 := by
    simpa [prefixWord, tailWord_2614942, baseEnd_2614942] using wordTrace_append hprefix tailTrace_2614942
  have hstable : (prefixWord ++ tailWord_2614942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614942).length < 2 ^ (prefixWord ++ tailWord_2614942).sum := by decide
  have hdescent : baseEnd_2614942 < baseStart_2614942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614975 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 2, 3, 2]
def baseStart_2614975 : Nat := 118140960795 + 2614975 * 2 ^ 59
def prefixEnd_2614975 : Nat := 4983230072969 + 3 ^ 40 * 2614975 * 2
def baseEnd_2614975 : Nat := 1342739074491011631986455

theorem tailTrace_2614975 : CollatzResearch.WordTrace tailWord_2614975 prefixEnd_2614975 1342739074491011631986455 := by
  unfold tailWord_2614975
  simp only [CollatzResearch.WordTrace]
  refine ⟨95375973701399652019294379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63583982467599768012862919 95375973701399652019294379)
  ·
    refine ⟨143063960552099478028941569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95375973701399652019294379 143063960552099478028941569)
    ·
      refine ⟨107297970414074608521706177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143063960552099478028941569 107297970414074608521706177)
      ·
        refine ⟨80473477810555956391279633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107297970414074608521706177 80473477810555956391279633)
        ·
          refine ⟨60355108357916967293459725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80473477810555956391279633 60355108357916967293459725)
          ·
            refine ⟨22633165634218862735047397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60355108357916967293459725 22633165634218862735047397)
            ·
              refine ⟨4243718556416036762821387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22633165634218862735047397 4243718556416036762821387)
              ·
                refine ⟨6365577834624055144232081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4243718556416036762821387 6365577834624055144232081)
                ·
                  refine ⟨4774183375968041358174061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6365577834624055144232081 4774183375968041358174061)
                  ·
                    refine ⟨1790318765988015509315273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4774183375968041358174061 1790318765988015509315273)
                    ·
                      refine ⟨1342739074491011631986455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790318765988015509315273 1342739074491011631986455)
                      ·
                        rfl

theorem cell23_2614975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_2614975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614975 prefixEnd_2614975 := by exact prefixLift 2614975
  have htrace : WordTrace (prefixWord ++ tailWord_2614975) baseStart_2614975 baseEnd_2614975 := by
    simpa [prefixWord, tailWord_2614975, baseEnd_2614975] using wordTrace_append hprefix tailTrace_2614975
  have hstable : (prefixWord ++ tailWord_2614975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614975).length < 2 ^ (prefixWord ++ tailWord_2614975).sum := by decide
  have hdescent : baseEnd_2614975 < baseStart_2614975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2614981 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_2614981 : Nat := 118140960795 + 2614981 * 2 ^ 59
def prefixEnd_2614981 : Nat := 4983230072969 + 3 ^ 40 * 2614981 * 2
def baseEnd_2614981 : Nat := 447580718458312869503809

theorem tailTrace_2614981 : CollatzResearch.WordTrace tailWord_2614981 prefixEnd_2614981 447580718458312869503809 := by
  unfold tailWord_2614981
  simp only [CollatzResearch.WordTrace]
  refine ⟨95376192539377915044012797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63584128359585276696008531 95376192539377915044012797)
  ·
    refine ⟨35766072202266718141504799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95376192539377915044012797 35766072202266718141504799)
    ·
      refine ⟨53649108303400077212257199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35766072202266718141504799 53649108303400077212257199)
      ·
        refine ⟨80473662455100115818385799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53649108303400077212257199 80473662455100115818385799)
        ·
          refine ⟨120710493682650173727578699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80473662455100115818385799 120710493682650173727578699)
          ·
            refine ⟨181065740523975260591368049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120710493682650173727578699 181065740523975260591368049)
            ·
              refine ⟨135799305392981445443526037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181065740523975260591368049 135799305392981445443526037)
              ·
                refine ⟨6365592440296005255165283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135799305392981445443526037 6365592440296005255165283)
                ·
                  refine ⟨9548388660444007882747925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6365592440296005255165283 9548388660444007882747925)
                  ·
                    refine ⟨447580718458312869503809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9548388660444007882747925 447580718458312869503809)
                    ·
                      rfl

theorem cell23_2614981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_2614981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2614981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2614981 prefixEnd_2614981 := by exact prefixLift 2614981
  have htrace : WordTrace (prefixWord ++ tailWord_2614981) baseStart_2614981 baseEnd_2614981 := by
    simpa [prefixWord, tailWord_2614981, baseEnd_2614981] using wordTrace_append hprefix tailTrace_2614981
  have hstable : (prefixWord ++ tailWord_2614981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2614981).length < 2 ^ (prefixWord ++ tailWord_2614981).sum := by decide
  have hdescent : baseEnd_2614981 < baseStart_2614981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2614981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615008 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3]
def baseStart_2615008 : Nat := 118140960795 + 2615008 * 2 ^ 59
def prefixEnd_2615008 : Nat := 4983230072969 + 3 ^ 40 * 2615008 * 2
def baseEnd_2615008 : Nat := 1342756019352610002873803

theorem tailTrace_2615008 : CollatzResearch.WordTrace tailWord_2615008 prefixEnd_2615008 1342756019352610002873803 := by
  unfold tailWord_2615008
  simp only [CollatzResearch.WordTrace]
  refine ⟨47688588655140049327622839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63584784873520065770163785 47688588655140049327622839)
  ·
    refine ⟨71532882982710073991434259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47688588655140049327622839 71532882982710073991434259)
    ·
      refine ⟨107299324474065110987151389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71532882982710073991434259 107299324474065110987151389)
      ·
        refine ⟨40237246677774416620181771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107299324474065110987151389 40237246677774416620181771)
        ·
          refine ⟨60355870016661624930272657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40237246677774416620181771 60355870016661624930272657)
          ·
            refine ⟨45266902512496218697704493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60355870016661624930272657 45266902512496218697704493)
            ·
              refine ⟨16975088442186082011639185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45266902512496218697704493 16975088442186082011639185)
              ·
                refine ⟨12731316331639561508729389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16975088442186082011639185 12731316331639561508729389)
                ·
                  refine ⟨4774243624364835565773521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12731316331639561508729389 4774243624364835565773521)
                  ·
                    refine ⟨3580682718273626674330141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4774243624364835565773521 3580682718273626674330141)
                    ·
                      refine ⟨1342756019352610002873803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580682718273626674330141 1342756019352610002873803)
                      ·
                        rfl

theorem cell23_2615008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_2615008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615008 prefixEnd_2615008 := by exact prefixLift 2615008
  have htrace : WordTrace (prefixWord ++ tailWord_2615008) baseStart_2615008 baseEnd_2615008 := by
    simpa [prefixWord, tailWord_2615008, baseEnd_2615008] using wordTrace_append hprefix tailTrace_2615008
  have hstable : (prefixWord ++ tailWord_2615008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615008).length < 2 ^ (prefixWord ++ tailWord_2615008).sum := by decide
  have hdescent : baseEnd_2615008 < baseStart_2615008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615018 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2615018 : Nat := 118140960795 + 2615018 * 2 ^ 59
def prefixEnd_2615018 : Nat := 4983230072969 + 3 ^ 40 * 2615018 * 2
def baseEnd_2615018 : Nat := 1342761154159154963748757

theorem tailTrace_2615018 : CollatzResearch.WordTrace tailWord_2615018 prefixEnd_2615018 1342761154159154963748757 := by
  unfold tailWord_2615018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23844385510060967590777427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63585028026829246908739805 23844385510060967590777427)
  ·
    refine ⟨35766578265091451386166141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23844385510060967590777427 35766578265091451386166141)
    ·
      refine ⟨13412466849409294269812303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35766578265091451386166141 13412466849409294269812303)
      ·
        refine ⟨20118700274113941404718455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13412466849409294269812303 20118700274113941404718455)
        ·
          refine ⟨30178050411170912107077683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20118700274113941404718455 30178050411170912107077683)
          ·
            refine ⟨45267075616756368160616525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30178050411170912107077683 45267075616756368160616525)
            ·
              refine ⟨16975153356283638060231197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45267075616756368160616525 16975153356283638060231197)
              ·
                refine ⟨6365682508606364272586699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16975153356283638060231197 6365682508606364272586699)
                ·
                  refine ⟨9548523762909546408880049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6365682508606364272586699 9548523762909546408880049)
                  ·
                    refine ⟨7161392822182159806660037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9548523762909546408880049 7161392822182159806660037)
                    ·
                      refine ⟨1342761154159154963748757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7161392822182159806660037 1342761154159154963748757)
                      ·
                        rfl

theorem cell23_2615018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2615018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615018 prefixEnd_2615018 := by exact prefixLift 2615018
  have htrace : WordTrace (prefixWord ++ tailWord_2615018) baseStart_2615018 baseEnd_2615018 := by
    simpa [prefixWord, tailWord_2615018, baseEnd_2615018] using wordTrace_append hprefix tailTrace_2615018
  have hstable : (prefixWord ++ tailWord_2615018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615018).length < 2 ^ (prefixWord ++ tailWord_2615018).sum := by decide
  have hdescent : baseEnd_2615018 < baseStart_2615018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615022 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_2615022 : Nat := 118140960795 + 2615022 * 2 ^ 59
def prefixEnd_2615022 : Nat := 4983230072969 + 3 ^ 40 * 2615022 * 2
def baseEnd_2615022 : Nat := 1342763208081772948098739

theorem tailTrace_2615022 : CollatzResearch.WordTrace tailWord_2615022 prefixEnd_2615022 1342763208081772948098739 := by
  unfold tailWord_2615022
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922210991528672380781915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63585125288152919364170213 11922210991528672380781915)
  ·
    refine ⟨17883316487293008571172873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11922210991528672380781915 17883316487293008571172873)
    ·
      refine ⟨13412487365469756428379655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17883316487293008571172873 13412487365469756428379655)
      ·
        refine ⟨20118731048204634642569483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13412487365469756428379655 20118731048204634642569483)
        ·
          refine ⟨30178096572306951963854225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20118731048204634642569483 30178096572306951963854225)
          ·
            refine ⟨22633572429230213972890669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30178096572306951963854225 22633572429230213972890669)
            ·
              refine ⟨8487589660961330239834001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22633572429230213972890669 8487589660961330239834001)
              ·
                refine ⟨6365692245720997679875501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8487589660961330239834001 6365692245720997679875501)
                ·
                  refine ⟨2387134592145374129953313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6365692245720997679875501 2387134592145374129953313)
                  ·
                    refine ⟨1790350944109030597464985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2387134592145374129953313 1790350944109030597464985)
                    ·
                      refine ⟨1342763208081772948098739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790350944109030597464985 1342763208081772948098739)
                      ·
                        rfl

theorem cell23_2615022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_2615022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615022 prefixEnd_2615022 := by exact prefixLift 2615022
  have htrace : WordTrace (prefixWord ++ tailWord_2615022) baseStart_2615022 baseEnd_2615022 := by
    simpa [prefixWord, tailWord_2615022, baseEnd_2615022] using wordTrace_append hprefix tailTrace_2615022
  have hstable : (prefixWord ++ tailWord_2615022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615022).length < 2 ^ (prefixWord ++ tailWord_2615022).sum := by decide
  have hdescent : baseEnd_2615022 < baseStart_2615022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615042 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2615042 : Nat := 118140960795 + 2615042 * 2 ^ 59
def prefixEnd_2615042 : Nat := 4983230072969 + 3 ^ 40 * 2615042 * 2
def baseEnd_2615042 : Nat := 1342773477694862869848647

theorem tailTrace_2615042 : CollatzResearch.WordTrace tailWord_2615042 prefixEnd_2615042 1342773477694862869848647 := by
  unfold tailWord_2615042
  simp only [CollatzResearch.WordTrace]
  refine ⟨23844604348039230615495845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63585611594771281641322253 23844604348039230615495845)
  ·
    refine ⟨4470863315257355740405471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23844604348039230615495845 4470863315257355740405471)
    ·
      refine ⟨6706294972886033610608207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4470863315257355740405471 6706294972886033610608207)
      ·
        refine ⟨10059442459329050415912311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6706294972886033610608207 10059442459329050415912311)
        ·
          refine ⟨15089163688993575623868467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10059442459329050415912311 15089163688993575623868467)
          ·
            refine ⟨22633745533490363435802701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15089163688993575623868467 22633745533490363435802701)
            ·
              refine ⟨8487654575058886288426013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22633745533490363435802701 8487654575058886288426013)
              ·
                refine ⟨3182870465647082358159755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8487654575058886288426013 3182870465647082358159755)
                ·
                  refine ⟨4774305698470623537239633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3182870465647082358159755 4774305698470623537239633)
                  ·
                    refine ⟨3580729273852967652929725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4774305698470623537239633 3580729273852967652929725)
                    ·
                      refine ⟨1342773477694862869848647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580729273852967652929725 1342773477694862869848647)
                      ·
                        rfl

theorem cell23_2615042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2615042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615042 prefixEnd_2615042 := by exact prefixLift 2615042
  have htrace : WordTrace (prefixWord ++ tailWord_2615042) baseStart_2615042 baseEnd_2615042 := by
    simpa [prefixWord, tailWord_2615042, baseEnd_2615042] using wordTrace_append hprefix tailTrace_2615042
  have hstable : (prefixWord ++ tailWord_2615042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615042).length < 2 ^ (prefixWord ++ tailWord_2615042).sum := by decide
  have hdescent : baseEnd_2615042 < baseStart_2615042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615055 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 3]
def baseStart_2615055 : Nat := 118140960795 + 2615055 * 2 ^ 59
def prefixEnd_2615055 : Nat := 4983230072969 + 3 ^ 40 * 2615055 * 2
def baseEnd_2615055 : Nat := 1342780152943371318986087

theorem tailTrace_2615055 : CollatzResearch.WordTrace tailWord_2615055 prefixEnd_2615055 1342780152943371318986087 := by
  unfold tailWord_2615055
  simp only [CollatzResearch.WordTrace]
  refine ⟨95378891541109825682206619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63585927694073217121471079 95378891541109825682206619)
  ·
    refine ⟨143068337311664738523309929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95378891541109825682206619 143068337311664738523309929)
    ·
      refine ⟨107301252983748553892482447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143068337311664738523309929 107301252983748553892482447)
      ·
        refine ⟨160951879475622830838723671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107301252983748553892482447 160951879475622830838723671)
        ·
          refine ⟨241427819213434246258085507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160951879475622830838723671 241427819213434246258085507)
          ·
            refine ⟨362141728820151369387128261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241427819213434246258085507 362141728820151369387128261)
            ·
              refine ⟨67901574153778381760086549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 362141728820151369387128261 67901574153778381760086549)
              ·
                refine ⟨3182886288458361645004057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67901574153778381760086549 3182886288458361645004057)
                ·
                  refine ⟨2387164716343771233753043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3182886288458361645004057 2387164716343771233753043)
                  ·
                    refine ⟨3580747074515656850629565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2387164716343771233753043 3580747074515656850629565)
                    ·
                      refine ⟨1342780152943371318986087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3580747074515656850629565 1342780152943371318986087)
                      ·
                        rfl

theorem cell23_2615055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 3].length) (baseStart_2615055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615055 prefixEnd_2615055 := by exact prefixLift 2615055
  have htrace : WordTrace (prefixWord ++ tailWord_2615055) baseStart_2615055 baseEnd_2615055 := by
    simpa [prefixWord, tailWord_2615055, baseEnd_2615055] using wordTrace_append hprefix tailTrace_2615055
  have hstable : (prefixWord ++ tailWord_2615055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615055).length < 2 ^ (prefixWord ++ tailWord_2615055).sum := by decide
  have hdescent : baseEnd_2615055 < baseStart_2615055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615098 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_2615098 : Nat := 118140960795 + 2615098 * 2 ^ 59
def prefixEnd_2615098 : Nat := 4983230072969 + 3 ^ 40 * 2615098 * 2
def baseEnd_2615098 : Nat := 1342802232611514650748389

theorem tailTrace_2615098 : CollatzResearch.WordTrace tailWord_2615098 prefixEnd_2615098 1342802232611514650748389 := by
  unfold tailWord_2615098
  simp only [CollatzResearch.WordTrace]
  refine ⟨23845114969988511006505487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63586973253302696017347965 23845114969988511006505487)
  ·
    refine ⟨35767672454982766509758231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23845114969988511006505487 35767672454982766509758231)
    ·
      refine ⟨53651508682474149764637347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35767672454982766509758231 53651508682474149764637347)
      ·
        refine ⟨80477263023711224646956021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53651508682474149764637347 80477263023711224646956021)
        ·
          refine ⟨7544743408472927310652127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80477263023711224646956021 7544743408472927310652127)
          ·
            refine ⟨11317115112709390965978191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7544743408472927310652127 11317115112709390965978191)
            ·
              refine ⟨16975672669064086448967287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11317115112709390965978191 16975672669064086448967287)
              ·
                refine ⟨25463509003596129673450931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16975672669064086448967287 25463509003596129673450931)
                ·
                  refine ⟨38195263505394194510176397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25463509003596129673450931 38195263505394194510176397)
                  ·
                    refine ⟨14323223814522822941316149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38195263505394194510176397 14323223814522822941316149)
                    ·
                      refine ⟨1342802232611514650748389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14323223814522822941316149 1342802232611514650748389)
                      ·
                        rfl

theorem cell23_2615098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_2615098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615098 prefixEnd_2615098 := by exact prefixLift 2615098
  have htrace : WordTrace (prefixWord ++ tailWord_2615098) baseStart_2615098 baseEnd_2615098 := by
    simpa [prefixWord, tailWord_2615098, baseEnd_2615098] using wordTrace_append hprefix tailTrace_2615098
  have hstable : (prefixWord ++ tailWord_2615098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615098).length < 2 ^ (prefixWord ++ tailWord_2615098).sum := by decide
  have hdescent : baseEnd_2615098 < baseStart_2615098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615112 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_2615112 : Nat := 118140960795 + 2615112 * 2 ^ 59
def prefixEnd_2615112 : Nat := 4983230072969 + 3 ^ 40 * 2615112 * 2
def baseEnd_2615112 : Nat := 1342809421340677595973325

theorem tailTrace_2615112 : CollatzResearch.WordTrace tailWord_2615112 prefixEnd_2615112 1342809421340677595973325 := by
  unfold tailWord_2615112
  simp only [CollatzResearch.WordTrace]
  refine ⟨47690485250951662208515795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63587313667935549611354393 47690485250951662208515795)
  ·
    refine ⟨71535727876427493312773693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47690485250951662208515795 71535727876427493312773693)
    ·
      refine ⟨26825897953660309992290135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71535727876427493312773693 26825897953660309992290135)
      ·
        refine ⟨40238846930490464988435203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26825897953660309992290135 40238846930490464988435203)
        ·
          refine ⟨60358270395735697482652805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40238846930490464988435203 60358270395735697482652805)
          ·
            refine ⟨11317175699200443277997401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60358270395735697482652805 11317175699200443277997401)
            ·
              refine ⟨8487881774400332458498051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11317175699200443277997401 8487881774400332458498051)
              ·
                refine ⟨12731822661600498687747077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8487881774400332458498051 12731822661600498687747077)
                ·
                  refine ⟨2387216749050093503952577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12731822661600498687747077 2387216749050093503952577)
                  ·
                    refine ⟨1790412561787570127964433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2387216749050093503952577 1790412561787570127964433)
                    ·
                      refine ⟨1342809421340677595973325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790412561787570127964433 1342809421340677595973325)
                      ·
                        rfl

theorem cell23_2615112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_2615112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615112 prefixEnd_2615112 := by exact prefixLift 2615112
  have htrace : WordTrace (prefixWord ++ tailWord_2615112) baseStart_2615112 baseEnd_2615112 := by
    simpa [prefixWord, tailWord_2615112, baseEnd_2615112] using wordTrace_append hprefix tailTrace_2615112
  have hstable : (prefixWord ++ tailWord_2615112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615112).length < 2 ^ (prefixWord ++ tailWord_2615112).sum := by decide
  have hdescent : baseEnd_2615112 < baseStart_2615112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615169 : List Nat := [1, 2, 4, 4, 1, 1, 1, 4, 5]
def baseStart_2615169 : Nat := 118140960795 + 2615169 * 2 ^ 59
def prefixEnd_2615169 : Nat := 4983230072969 + 3 ^ 40 * 2615169 * 2
def baseEnd_2615169 : Nat := 149204298859775985884507

theorem tailTrace_2615169 : CollatzResearch.WordTrace tailWord_2615169 prefixEnd_2615169 149204298859775985884507 := by
  unfold tailWord_2615169
  simp only [CollatzResearch.WordTrace]
  refine ⟨95383049462696823151856561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63588699641797882101237707 95383049462696823151856561)
  ·
    refine ⟨71537287097022617363892421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95383049462696823151856561 71537287097022617363892421)
    ·
      refine ⟨13413241330691740755729829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71537287097022617363892421 13413241330691740755729829)
      ·
        refine ⟨2514982749504701391699343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13413241330691740755729829 2514982749504701391699343)
        ·
          refine ⟨3772474124257052087549015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514982749504701391699343 3772474124257052087549015)
          ·
            refine ⟨5658711186385578131323523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772474124257052087549015 5658711186385578131323523)
            ·
              refine ⟨8488066779578367196985285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658711186385578131323523 8488066779578367196985285)
              ·
                refine ⟨1591512521170943849434741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8488066779578367196985285 1591512521170943849434741)
                ·
                  refine ⟨149204298859775985884507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1591512521170943849434741 149204298859775985884507)
                  ·
                    rfl

theorem cell23_2615169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 5].length) (baseStart_2615169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615169 prefixEnd_2615169 := by exact prefixLift 2615169
  have htrace : WordTrace (prefixWord ++ tailWord_2615169) baseStart_2615169 baseEnd_2615169 := by
    simpa [prefixWord, tailWord_2615169, baseEnd_2615169] using wordTrace_append hprefix tailTrace_2615169
  have hstable : (prefixWord ++ tailWord_2615169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615169).length < 2 ^ (prefixWord ++ tailWord_2615169).sum := by decide
  have hdescent : baseEnd_2615169 < baseStart_2615169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615185 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 1, 6, 2]
def baseStart_2615185 : Nat := 118140960795 + 2615185 * 2 ^ 59
def prefixEnd_2615185 : Nat := 4983230072969 + 3 ^ 40 * 2615185 * 2
def baseEnd_2615185 : Nat := 1342846905428455810360489

theorem tailTrace_2615185 : CollatzResearch.WordTrace tailWord_2615185 prefixEnd_2615185 1342846905428455810360489 := by
  unfold tailWord_2615185
  simp only [CollatzResearch.WordTrace]
  refine ⟨95383633030638857884439009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63589088687092571922959339 95383633030638857884439009)
  ·
    refine ⟨71537724772979143413329257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95383633030638857884439009 71537724772979143413329257)
    ·
      refine ⟨53653293579734357559996943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71537724772979143413329257 53653293579734357559996943)
      ·
        refine ⟨80479940369601536339995415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53653293579734357559996943 80479940369601536339995415)
        ·
          refine ⟨120719910554402304509993123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80479940369601536339995415 120719910554402304509993123)
          ·
            refine ⟨181079865831603456764989685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120719910554402304509993123 181079865831603456764989685)
            ·
              refine ⟨16976237421712824071717783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181079865831603456764989685 16976237421712824071717783)
              ·
                refine ⟨25464356132569236107576675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16976237421712824071717783 25464356132569236107576675)
                ·
                  refine ⟨38196534198853854161365013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25464356132569236107576675 38196534198853854161365013)
                  ·
                    refine ⟨1790462540571274413813985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38196534198853854161365013 1790462540571274413813985)
                    ·
                      refine ⟨1342846905428455810360489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790462540571274413813985 1342846905428455810360489)
                      ·
                        rfl

theorem cell23_2615185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_2615185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615185 prefixEnd_2615185 := by exact prefixLift 2615185
  have htrace : WordTrace (prefixWord ++ tailWord_2615185) baseStart_2615185 baseEnd_2615185 := by
    simpa [prefixWord, tailWord_2615185, baseEnd_2615185] using wordTrace_append hprefix tailTrace_2615185
  have hstable : (prefixWord ++ tailWord_2615185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615185).length < 2 ^ (prefixWord ++ tailWord_2615185).sum := by decide
  have hdescent : baseEnd_2615185 < baseStart_2615185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615199 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 2, 5]
def baseStart_2615199 : Nat := 118140960795 + 2615199 * 2 ^ 59
def prefixEnd_2615199 : Nat := 4983230072969 + 3 ^ 40 * 2615199 * 2
def baseEnd_2615199 : Nat := 447618031385872918528475

theorem tailTrace_2615199 : CollatzResearch.WordTrace tailWord_2615199 prefixEnd_2615199 447618031385872918528475 := by
  unfold tailWord_2615199
  simp only [CollatzResearch.WordTrace]
  refine ⟨95384143652588138275448651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63589429101725425516965767 95384143652588138275448651)
  ·
    refine ⟨143076215478882207413172977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95384143652588138275448651 143076215478882207413172977)
    ·
      refine ⟨107307161609161655559879733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143076215478882207413172977 107307161609161655559879733)
      ·
        refine ⟨10060046400858905208738725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107307161609161655559879733 10060046400858905208738725)
        ·
          refine ⟨1886258700161044726638511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10060046400858905208738725 1886258700161044726638511)
          ·
            refine ⟨2829388050241567089957767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886258700161044726638511 2829388050241567089957767)
            ·
              refine ⟨4244082075362350634936651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829388050241567089957767 4244082075362350634936651)
              ·
                refine ⟨6366123113043525952404977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244082075362350634936651 6366123113043525952404977)
                ·
                  refine ⟨4774592334782644464303733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6366123113043525952404977 4774592334782644464303733)
                  ·
                    refine ⟨447618031385872918528475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4774592334782644464303733 447618031385872918528475)
                    ·
                      rfl

theorem cell23_2615199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 2, 5].length) (baseStart_2615199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615199 prefixEnd_2615199 := by exact prefixLift 2615199
  have htrace : WordTrace (prefixWord ++ tailWord_2615199) baseStart_2615199 baseEnd_2615199 := by
    simpa [prefixWord, tailWord_2615199, baseEnd_2615199] using wordTrace_append hprefix tailTrace_2615199
  have hstable : (prefixWord ++ tailWord_2615199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615199).length < 2 ^ (prefixWord ++ tailWord_2615199).sum := by decide
  have hdescent : baseEnd_2615199 < baseStart_2615199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615202 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2615202 : Nat := 118140960795 + 2615202 * 2 ^ 59
def prefixEnd_2615202 : Nat := 4983230072969 + 3 ^ 40 * 2615202 * 2
def baseEnd_2615202 : Nat := 1342855634599582243847911

theorem tailTrace_2615202 : CollatzResearch.WordTrace tailWord_2615202 prefixEnd_2615202 1342855634599582243847911 := by
  unfold tailWord_2615202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846063267894317446951965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63589502047718179858538573 23846063267894317446951965)
  ·
    refine ⟨8942273725460369042606987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23846063267894317446951965 8942273725460369042606987)
    ·
      refine ⟨13413410588190553563910481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8942273725460369042606987 13413410588190553563910481)
      ·
        refine ⟨10060057941142915172932861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13413410588190553563910481 10060057941142915172932861)
        ·
          refine ⟨3772521727928593189849823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10060057941142915172932861 3772521727928593189849823)
          ·
            refine ⟨5658782591892889784774735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772521727928593189849823 5658782591892889784774735)
            ·
              refine ⟨8488173887839334677162103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658782591892889784774735 8488173887839334677162103)
              ·
                refine ⟨12732260831759002015743155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8488173887839334677162103 12732260831759002015743155)
                ·
                  refine ⟨19098391247638503023614733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12732260831759002015743155 19098391247638503023614733)
                  ·
                    refine ⟨7161896717864438633855525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19098391247638503023614733 7161896717864438633855525)
                    ·
                      refine ⟨1342855634599582243847911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7161896717864438633855525 1342855634599582243847911)
                      ·
                        rfl

theorem cell23_2615202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2615202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615202 prefixEnd_2615202 := by exact prefixLift 2615202
  have htrace : WordTrace (prefixWord ++ tailWord_2615202) baseStart_2615202 baseEnd_2615202 := by
    simpa [prefixWord, tailWord_2615202, baseEnd_2615202] using wordTrace_append hprefix tailTrace_2615202
  have hstable : (prefixWord ++ tailWord_2615202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615202).length < 2 ^ (prefixWord ++ tailWord_2615202).sum := by decide
  have hdescent : baseEnd_2615202 < baseStart_2615202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615229 : List Nat := [1, 4, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_2615229 : Nat := 118140960795 + 2615229 * 2 ^ 59
def prefixEnd_2615229 : Nat := 4983230072969 + 3 ^ 40 * 2615229 * 2
def baseEnd_2615229 : Nat := 447623166192417879403429

theorem tailTrace_2615229 : CollatzResearch.WordTrace tailWord_2615229 prefixEnd_2615229 447623166192417879403429 := by
  unfold tailWord_2615229
  simp only [CollatzResearch.WordTrace]
  refine ⟨95385237842479453399040741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63590158561652968932693827 95385237842479453399040741)
  ·
    refine ⟨17884732095464897512320139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95385237842479453399040741 17884732095464897512320139)
    ·
      refine ⟨26827098143197346268480209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17884732095464897512320139 26827098143197346268480209)
      ·
        refine ⟨20120323607398009701360157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26827098143197346268480209 20120323607398009701360157)
        ·
          refine ⟨7545121352774253638010059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20120323607398009701360157 7545121352774253638010059)
          ·
            refine ⟨11317682029161380457015089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7545121352774253638010059 11317682029161380457015089)
            ·
              refine ⟨8488261521871035342761317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11317682029161380457015089 8488261521871035342761317)
              ·
                refine ⟨1591549035350819126767747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8488261521871035342761317 1591549035350819126767747)
                ·
                  refine ⟨2387323553026228690151621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591549035350819126767747 2387323553026228690151621)
                  ·
                    refine ⟨447623166192417879403429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2387323553026228690151621 447623166192417879403429)
                    ·
                      rfl

theorem cell23_2615229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_2615229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615229 prefixEnd_2615229 := by exact prefixLift 2615229
  have htrace : WordTrace (prefixWord ++ tailWord_2615229) baseStart_2615229 baseEnd_2615229 := by
    simpa [prefixWord, tailWord_2615229, baseEnd_2615229] using wordTrace_append hprefix tailTrace_2615229
  have hstable : (prefixWord ++ tailWord_2615229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615229).length < 2 ^ (prefixWord ++ tailWord_2615229).sum := by decide
  have hdescent : baseEnd_2615229 < baseStart_2615229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615248 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_2615248 : Nat := 118140960795 + 2615248 * 2 ^ 59
def prefixEnd_2615248 : Nat := 4983230072969 + 3 ^ 40 * 2615248 * 2
def baseEnd_2615248 : Nat := 1342879254709689063872699

theorem tailTrace_2615248 : CollatzResearch.WordTrace tailWord_2615248 prefixEnd_2615248 1342879254709689063872699 := by
  unfold tailWord_2615248
  simp only [CollatzResearch.WordTrace]
  refine ⟨47692965414705309821991199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63590620552940413095988265 47692965414705309821991199)
  ·
    refine ⟨71539448122057964732986799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47692965414705309821991199 71539448122057964732986799)
    ·
      refine ⟨107309172183086947099480199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71539448122057964732986799 107309172183086947099480199)
      ·
        refine ⟨160963758274630420649220299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107309172183086947099480199 160963758274630420649220299)
        ·
          refine ⟨241445637411945630973830449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160963758274630420649220299 241445637411945630973830449)
          ·
            refine ⟨181084228058959223230372837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241445637411945630973830449 181084228058959223230372837)
            ·
              refine ⟨33953292761054854355694907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181084228058959223230372837 33953292761054854355694907)
              ·
                refine ⟨50929939141582281533542361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33953292761054854355694907 50929939141582281533542361)
                ·
                  refine ⟨38197454356186711150156771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50929939141582281533542361 38197454356186711150156771)
                  ·
                    refine ⟨57296181534280066725235157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38197454356186711150156771 57296181534280066725235157)
                    ·
                      refine ⟨1342879254709689063872699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57296181534280066725235157 1342879254709689063872699)
                      ·
                        rfl

theorem cell23_2615248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_2615248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615248 prefixEnd_2615248 := by exact prefixLift 2615248
  have htrace : WordTrace (prefixWord ++ tailWord_2615248) baseStart_2615248 baseEnd_2615248 := by
    simpa [prefixWord, tailWord_2615248, baseEnd_2615248] using wordTrace_append hprefix tailTrace_2615248
  have hstable : (prefixWord ++ tailWord_2615248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615248).length < 2 ^ (prefixWord ++ tailWord_2615248).sum := by decide
  have hdescent : baseEnd_2615248 < baseStart_2615248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615306 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_2615306 : Nat := 118140960795 + 2615306 * 2 ^ 59
def prefixEnd_2615306 : Nat := 4983230072969 + 3 ^ 40 * 2615306 * 2
def baseEnd_2615306 : Nat := 447636345529216612315811

theorem tailTrace_2615306 : CollatzResearch.WordTrace tailWord_2615306 prefixEnd_2615306 447636345529216612315811 := by
  unfold tailWord_2615306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23847011565800123887398443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63592030842133663699729181 23847011565800123887398443)
  ·
    refine ⟨35770517348700185831097665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23847011565800123887398443 35770517348700185831097665)
    ·
      refine ⟨26827888011525139373323249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35770517348700185831097665 26827888011525139373323249)
      ·
        refine ⟨20120916008643854529992437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26827888011525139373323249 20120916008643854529992437)
        ·
          refine ⟨1886335875810361362186791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20120916008643854529992437 1886335875810361362186791)
          ·
            refine ⟨2829503813715542043280187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886335875810361362186791 2829503813715542043280187)
            ·
              refine ⟨4244255720573313064920281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829503813715542043280187 4244255720573313064920281)
              ·
                refine ⟨3183191790429984798690211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4244255720573313064920281 3183191790429984798690211)
                ·
                  refine ⟨4774787685644977198035317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183191790429984798690211 4774787685644977198035317)
                  ·
                    refine ⟨447636345529216612315811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4774787685644977198035317 447636345529216612315811)
                    ·
                      rfl

theorem cell23_2615306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_2615306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615306 prefixEnd_2615306 := by exact prefixLift 2615306
  have htrace : WordTrace (prefixWord ++ tailWord_2615306) baseStart_2615306 baseEnd_2615306 := by
    simpa [prefixWord, tailWord_2615306, baseEnd_2615306] using wordTrace_append hprefix tailTrace_2615306
  have hstable : (prefixWord ++ tailWord_2615306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615306).length < 2 ^ (prefixWord ++ tailWord_2615306).sum := by decide
  have hdescent : baseEnd_2615306 < baseStart_2615306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615322 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_2615322 : Nat := 118140960795 + 2615322 * 2 ^ 59
def prefixEnd_2615322 : Nat := 4983230072969 + 3 ^ 40 * 2615322 * 2
def baseEnd_2615322 : Nat := 1342917252278121774347359

theorem tailTrace_2615322 : CollatzResearch.WordTrace tailWord_2615322 prefixEnd_2615322 1342917252278121774347359 := by
  unfold tailWord_2615322
  simp only [CollatzResearch.WordTrace]
  refine ⟨23847157457785632570544055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63592419887428353521450813 23847157457785632570544055)
  ·
    refine ⟨35770736186678448855816083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23847157457785632570544055 35770736186678448855816083)
    ·
      refine ⟨53656104280017673283724125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35770736186678448855816083 53656104280017673283724125)
      ·
        refine ⟨20121039105006627481396547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53656104280017673283724125 20121039105006627481396547)
        ·
          refine ⟨30181558657509941222094821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20121039105006627481396547 30181558657509941222094821)
          ·
            refine ⟨5659042248283113979142779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30181558657509941222094821 5659042248283113979142779)
            ·
              refine ⟨8488563372424670968714169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659042248283113979142779 8488563372424670968714169)
              ·
                refine ⟨6366422529318503226535627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8488563372424670968714169 6366422529318503226535627)
                ·
                  refine ⟨9549633793977754839803441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6366422529318503226535627 9549633793977754839803441)
                  ·
                    refine ⟨7162225345483316129852581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9549633793977754839803441 7162225345483316129852581)
                    ·
                      refine ⟨1342917252278121774347359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7162225345483316129852581 1342917252278121774347359)
                      ·
                        rfl

theorem cell23_2615322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_2615322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615322 prefixEnd_2615322 := by exact prefixLift 2615322
  have htrace : WordTrace (prefixWord ++ tailWord_2615322) baseStart_2615322 baseEnd_2615322 := by
    simpa [prefixWord, tailWord_2615322, baseEnd_2615322] using wordTrace_append hprefix tailTrace_2615322
  have hstable : (prefixWord ++ tailWord_2615322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615322).length < 2 ^ (prefixWord ++ tailWord_2615322).sum := by decide
  have hdescent : baseEnd_2615322 < baseStart_2615322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615329 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2615329 : Nat := 118140960795 + 2615329 * 2 ^ 59
def prefixEnd_2615329 : Nat := 4983230072969 + 3 ^ 40 * 2615329 * 2
def baseEnd_2615329 : Nat := 1342920846642703246959827

theorem tailTrace_2615329 : CollatzResearch.WordTrace tailWord_2615329 prefixEnd_2615329 1342920846642703246959827 := by
  unfold tailWord_2615329
  simp only [CollatzResearch.WordTrace]
  refine ⟨95388885142117170477681041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63592590094744780318454027 95388885142117170477681041)
  ·
    refine ⟨71541663856587877858260781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95388885142117170477681041 71541663856587877858260781)
    ·
      refine ⟨26828123946220454196847793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71541663856587877858260781 26828123946220454196847793)
      ·
        refine ⟨20121092959665340647635845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26828123946220454196847793 20121092959665340647635845)
        ·
          refine ⟨3772704929937251371431721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20121092959665340647635845 3772704929937251371431721)
          ·
            refine ⟨2829528697452938528573791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3772704929937251371431721 2829528697452938528573791)
            ·
              refine ⟨4244293046179407792860687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829528697452938528573791 4244293046179407792860687)
              ·
                refine ⟨6366439569269111689291031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244293046179407792860687 6366439569269111689291031)
                ·
                  refine ⟨9549659353903667533936547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6366439569269111689291031 9549659353903667533936547)
                  ·
                    refine ⟨14324489030855501300904821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9549659353903667533936547 14324489030855501300904821)
                    ·
                      refine ⟨1342920846642703246959827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14324489030855501300904821 1342920846642703246959827)
                      ·
                        rfl

theorem cell23_2615329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2615329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615329 prefixEnd_2615329 := by exact prefixLift 2615329
  have htrace : WordTrace (prefixWord ++ tailWord_2615329) baseStart_2615329 baseEnd_2615329 := by
    simpa [prefixWord, tailWord_2615329, baseEnd_2615329] using wordTrace_append hprefix tailTrace_2615329
  have hstable : (prefixWord ++ tailWord_2615329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615329).length < 2 ^ (prefixWord ++ tailWord_2615329).sum := by decide
  have hdescent : baseEnd_2615329 < baseStart_2615329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615332 : List Nat := [2, 3, 1, 4, 3, 10]
def baseStart_2615332 : Nat := 118140960795 + 2615332 * 2 ^ 59
def prefixEnd_2615332 : Nat := 4983230072969 + 3 ^ 40 * 2615332 * 2
def baseEnd_2615332 : Nat := 5526429576480110021491

theorem tailTrace_2615332 : CollatzResearch.WordTrace tailWord_2615332 prefixEnd_2615332 5526429576480110021491 := by
  unfold tailWord_2615332
  simp only [CollatzResearch.WordTrace]
  refine ⟨47694497280553150995020125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63592663040737534660026833 47694497280553150995020125)
  ·
    refine ⟨17885436480207431623132547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47694497280553150995020125 17885436480207431623132547)
    ·
      refine ⟨26828154720311147434698821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17885436480207431623132547 26828154720311147434698821)
      ·
        refine ⟨5030279010058340144006029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26828154720311147434698821 5030279010058340144006029)
        ·
          refine ⟨1886354628771877554002261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5030279010058340144006029 1886354628771877554002261)
          ·
            refine ⟨5526429576480110021491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1886354628771877554002261 5526429576480110021491)
            ·
              rfl

theorem cell23_2615332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 10].length) (baseStart_2615332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615332 prefixEnd_2615332 := by exact prefixLift 2615332
  have htrace : WordTrace (prefixWord ++ tailWord_2615332) baseStart_2615332 baseEnd_2615332 := by
    simpa [prefixWord, tailWord_2615332, baseEnd_2615332] using wordTrace_append hprefix tailTrace_2615332
  have hstable : (prefixWord ++ tailWord_2615332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615332).length < 2 ^ (prefixWord ++ tailWord_2615332).sum := by decide
  have hdescent : baseEnd_2615332 < baseStart_2615332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615345 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 2, 7]
def baseStart_2615345 : Nat := 118140960795 + 2615345 * 2 ^ 59
def prefixEnd_2615345 : Nat := 4983230072969 + 3 ^ 40 * 2615345 * 2
def baseEnd_2615345 : Nat := 447643020777725061453251

theorem tailTrace_2615345 : CollatzResearch.WordTrace tailWord_2615345 prefixEnd_2615345 447643020777725061453251 := by
  unfold tailWord_2615345
  simp only [CollatzResearch.WordTrace]
  refine ⟨95389468710059205210263489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63592979140039470140175659 95389468710059205210263489)
  ·
    refine ⟨71542101532544403907697617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95389468710059205210263489 71542101532544403907697617)
    ·
      refine ⟨53656576149408302930773213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71542101532544403907697617 53656576149408302930773213)
      ·
        refine ⟨20121216056028113599039955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53656576149408302930773213 20121216056028113599039955)
        ·
          refine ⟨30181824084042170398559933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20121216056028113599039955 30181824084042170398559933)
          ·
            refine ⟨11318184031515813899459975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30181824084042170398559933 11318184031515813899459975)
            ·
              refine ⟨16977276047273720849189963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11318184031515813899459975 16977276047273720849189963)
              ·
                refine ⟨25465914070910581273784945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16977276047273720849189963 25465914070910581273784945)
                ·
                  refine ⟨19099435553182935955338709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25465914070910581273784945 19099435553182935955338709)
                  ·
                    refine ⟨447643020777725061453251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19099435553182935955338709 447643020777725061453251)
                    ·
                      rfl

theorem cell23_2615345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_2615345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615345 prefixEnd_2615345 := by exact prefixLift 2615345
  have htrace : WordTrace (prefixWord ++ tailWord_2615345) baseStart_2615345 baseEnd_2615345 := by
    simpa [prefixWord, tailWord_2615345, baseEnd_2615345] using wordTrace_append hprefix tailTrace_2615345
  have hstable : (prefixWord ++ tailWord_2615345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615345).length < 2 ^ (prefixWord ++ tailWord_2615345).sum := by decide
  have hdescent : baseEnd_2615345 < baseStart_2615345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615359 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 3]
def baseStart_2615359 : Nat := 118140960795 + 2615359 * 2 ^ 59
def prefixEnd_2615359 : Nat := 4983230072969 + 3 ^ 40 * 2615359 * 2
def baseEnd_2615359 : Nat := 1342936251062338129584689

theorem tailTrace_2615359 : CollatzResearch.WordTrace tailWord_2615359 prefixEnd_2615359 1342936251062338129584689 := by
  unfold tailWord_2615359
  simp only [CollatzResearch.WordTrace]
  refine ⟨95389979332008485601273131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63593319554672323734182087 95389979332008485601273131)
  ·
    refine ⟨143084968998012728401909697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95389979332008485601273131 143084968998012728401909697)
    ·
      refine ⟨107313726748509546301432273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143084968998012728401909697 107313726748509546301432273)
      ·
        refine ⟨80485295061382159726074205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107313726748509546301432273 80485295061382159726074205)
        ·
          refine ⟨30181985648018309897277827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80485295061382159726074205 30181985648018309897277827)
          ·
            refine ⟨45272978472027464845916741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30181985648018309897277827 45272978472027464845916741)
            ·
              refine ⟨8488683463505149658609389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45272978472027464845916741 8488683463505149658609389)
              ·
                refine ⟨3183256298814431121978521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8488683463505149658609389 3183256298814431121978521)
                ·
                  refine ⟨2387442224110823341483891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3183256298814431121978521 2387442224110823341483891)
                  ·
                    refine ⟨3581163336166235012225837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2387442224110823341483891 3581163336166235012225837)
                    ·
                      refine ⟨1342936251062338129584689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3581163336166235012225837 1342936251062338129584689)
                      ·
                        rfl

theorem cell23_2615359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_2615359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615359 prefixEnd_2615359 := by exact prefixLift 2615359
  have htrace : WordTrace (prefixWord ++ tailWord_2615359) baseStart_2615359 baseEnd_2615359 := by
    simpa [prefixWord, tailWord_2615359, baseEnd_2615359] using wordTrace_append hprefix tailTrace_2615359
  have hstable : (prefixWord ++ tailWord_2615359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615359).length < 2 ^ (prefixWord ++ tailWord_2615359).sum := by decide
  have hdescent : baseEnd_2615359 < baseStart_2615359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615365 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_2615365 : Nat := 118140960795 + 2615365 * 2 ^ 59
def prefixEnd_2615365 : Nat := 4983230072969 + 3 ^ 40 * 2615365 * 2
def baseEnd_2615365 : Nat := 1342939331946265106109661

theorem tailTrace_2615365 : CollatzResearch.WordTrace tailWord_2615365 prefixEnd_2615365 1342939331946265106109661 := by
  unfold tailWord_2615365
  simp only [CollatzResearch.WordTrace]
  refine ⟨95390198169986748625991549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63593465446657832417327699 95390198169986748625991549)
  ·
    refine ⟨35771324313745030734746831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95390198169986748625991549 35771324313745030734746831)
    ·
      refine ⟨53656986470617546102120247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35771324313745030734746831 53656986470617546102120247)
      ·
        refine ⟨80485479705926319153180371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53656986470617546102120247 80485479705926319153180371)
        ·
          refine ⟨120728219558889478729770557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80485479705926319153180371 120728219558889478729770557)
          ·
            refine ⟨45273082334583554523663959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120728219558889478729770557 45273082334583554523663959)
            ·
              refine ⟨67909623501875331785495939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45273082334583554523663959 67909623501875331785495939)
              ·
                refine ⟨101864435252812997678243909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67909623501875331785495939 101864435252812997678243909)
                ·
                  refine ⟨19099581609902437064670733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101864435252812997678243909 19099581609902437064670733)
                  ·
                    refine ⟨7162343103713413899251525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19099581609902437064670733 7162343103713413899251525)
                    ·
                      refine ⟨1342939331946265106109661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7162343103713413899251525 1342939331946265106109661)
                      ·
                        rfl

theorem cell23_2615365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_2615365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615365 prefixEnd_2615365 := by exact prefixLift 2615365
  have htrace : WordTrace (prefixWord ++ tailWord_2615365) baseStart_2615365 baseEnd_2615365 := by
    simpa [prefixWord, tailWord_2615365, baseEnd_2615365] using wordTrace_append hprefix tailTrace_2615365
  have hstable : (prefixWord ++ tailWord_2615365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615365).length < 2 ^ (prefixWord ++ tailWord_2615365).sum := by decide
  have hdescent : baseEnd_2615365 < baseStart_2615365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615369 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 1, 3, 2]
def baseStart_2615369 : Nat := 118140960795 + 2615369 * 2 ^ 59
def prefixEnd_2615369 : Nat := 4983230072969 + 3 ^ 40 * 2615369 * 2
def baseEnd_2615369 : Nat := 1342941385868883090459643

theorem tailTrace_2615369 : CollatzResearch.WordTrace tailWord_2615369 prefixEnd_2615369 1342941385868883090459643 := by
  unfold tailWord_2615369
  simp only [CollatzResearch.WordTrace]
  refine ⟨95390344061972257309137161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63593562707981504872758107 95390344061972257309137161)
  ·
    refine ⟨71542758046479192981852871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95390344061972257309137161 71542758046479192981852871)
    ·
      refine ⟨107314137069718789472779307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71542758046479192981852871 107314137069718789472779307)
      ·
        refine ⟨160971205604578184209168961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107314137069718789472779307 160971205604578184209168961)
        ·
          refine ⟨120728404203433638156876721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160971205604578184209168961 120728404203433638156876721)
          ·
            refine ⟨90546303152575228617657541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120728404203433638156876721 90546303152575228617657541)
            ·
              refine ⟨16977431841107855365810789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90546303152575228617657541 16977431841107855365810789)
              ·
                refine ⟨3183268470207722881089523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16977431841107855365810789 3183268470207722881089523)
                ·
                  refine ⟨4774902705311584321634285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183268470207722881089523 4774902705311584321634285)
                  ·
                    refine ⟨1790588514491844120612857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4774902705311584321634285 1790588514491844120612857)
                    ·
                      refine ⟨1342941385868883090459643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790588514491844120612857 1342941385868883090459643)
                      ·
                        rfl

theorem cell23_2615369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 3, 2].length) (baseStart_2615369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615369 prefixEnd_2615369 := by exact prefixLift 2615369
  have htrace : WordTrace (prefixWord ++ tailWord_2615369) baseStart_2615369 baseEnd_2615369 := by
    simpa [prefixWord, tailWord_2615369, baseEnd_2615369] using wordTrace_append hprefix tailTrace_2615369
  have hstable : (prefixWord ++ tailWord_2615369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615369).length < 2 ^ (prefixWord ++ tailWord_2615369).sum := by decide
  have hdescent : baseEnd_2615369 < baseStart_2615369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615385 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_2615385 : Nat := 118140960795 + 2615385 * 2 ^ 59
def prefixEnd_2615385 : Nat := 4983230072969 + 3 ^ 40 * 2615385 * 2
def baseEnd_2615385 : Nat := 1342949601559355027859569

theorem tailTrace_2615385 : CollatzResearch.WordTrace tailWord_2615385 prefixEnd_2615385 1342949601559355027859569 := by
  unfold tailWord_2615385
  simp only [CollatzResearch.WordTrace]
  refine ⟨95390927629914292041719609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63593951753276194694479739 95390927629914292041719609)
  ·
    refine ⟨71543195722435719031289707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95390927629914292041719609 71543195722435719031289707)
    ·
      refine ⟨107314793583653578546934561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71543195722435719031289707 107314793583653578546934561)
      ·
        refine ⟨80486095187740183910200921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107314793583653578546934561 80486095187740183910200921)
        ·
          refine ⟨60364571390805137932650691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80486095187740183910200921 60364571390805137932650691)
          ·
            refine ⟨90546857086207706898976037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60364571390805137932650691 90546857086207706898976037)
            ·
              refine ⟨16977535703663945043558007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90546857086207706898976037 16977535703663945043558007)
              ·
                refine ⟨25466303555495917565337011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16977535703663945043558007 25466303555495917565337011)
                ·
                  refine ⟨38199455333243876348005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25466303555495917565337011 38199455333243876348005517)
                  ·
                    refine ⟨14324795749966453630502069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38199455333243876348005517 14324795749966453630502069)
                    ·
                      refine ⟨1342949601559355027859569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14324795749966453630502069 1342949601559355027859569)
                      ·
                        rfl

theorem cell23_2615385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_2615385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615385 prefixEnd_2615385 := by exact prefixLift 2615385
  have htrace : WordTrace (prefixWord ++ tailWord_2615385) baseStart_2615385 baseEnd_2615385 := by
    simpa [prefixWord, tailWord_2615385, baseEnd_2615385] using wordTrace_append hprefix tailTrace_2615385
  have hstable : (prefixWord ++ tailWord_2615385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615385).length < 2 ^ (prefixWord ++ tailWord_2615385).sum := by decide
  have hdescent : baseEnd_2615385 < baseStart_2615385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615456 : List Nat := [2, 1, 1, 4, 2, 3, 3, 2, 5]
def baseStart_2615456 : Nat := 118140960795 + 2615456 * 2 ^ 59
def prefixEnd_2615456 : Nat := 4983230072969 + 3 ^ 40 * 2615456 * 2
def baseEnd_2615456 : Nat := 149220673187313805563527

theorem tailTrace_2615456 : CollatzResearch.WordTrace tailWord_2615456 prefixEnd_2615456 149220673187313805563527 := by
  unfold tailWord_2615456
  simp only [CollatzResearch.WordTrace]
  refine ⟨47696758606328535583777111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63595678141771380778369481 47696758606328535583777111)
  ·
    refine ⟨71545137909492803375665667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47696758606328535583777111 71545137909492803375665667)
    ·
      refine ⟨107317706864239205063498501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71545137909492803375665667 107317706864239205063498501)
      ·
        refine ⟨20122070037044850949405969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107317706864239205063498501 20122070037044850949405969)
        ·
          refine ⟨15091552527783638212054477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20122070037044850949405969 15091552527783638212054477)
          ·
            refine ⟨5659332197918864329520429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15091552527783638212054477 5659332197918864329520429)
            ·
              refine ⟨2122249574219574123570161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5659332197918864329520429 2122249574219574123570161)
              ·
                refine ⟨1591687180664680592677621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122249574219574123570161 1591687180664680592677621)
                ·
                  refine ⟨149220673187313805563527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1591687180664680592677621 149220673187313805563527)
                  ·
                    rfl

theorem cell23_2615456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 5].length) (baseStart_2615456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615456 prefixEnd_2615456 := by exact prefixLift 2615456
  have htrace : WordTrace (prefixWord ++ tailWord_2615456) baseStart_2615456 baseEnd_2615456 := by
    simpa [prefixWord, tailWord_2615456, baseEnd_2615456] using wordTrace_append hprefix tailTrace_2615456
  have hstable : (prefixWord ++ tailWord_2615456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615456).length < 2 ^ (prefixWord ++ tailWord_2615456).sum := by decide
  have hdescent : baseEnd_2615456 < baseStart_2615456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615486 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2615486 : Nat := 118140960795 + 2615486 * 2 ^ 59
def prefixEnd_2615486 : Nat := 4983230072969 + 3 ^ 40 * 2615486 * 2
def baseEnd_2615486 : Nat := 447667154368486377565535

theorem tailTrace_2615486 : CollatzResearch.WordTrace tailWord_2615486 prefixEnd_2615486 447667154368486377565535 := by
  unfold tailWord_2615486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11924326425318548286393289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63596407601698924194097541 11924326425318548286393289)
  ·
    refine ⟨8943244818988911214794967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11924326425318548286393289 8943244818988911214794967)
    ·
      refine ⟨13414867228483366822192451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8943244818988911214794967 13414867228483366822192451)
      ·
        refine ⟨20122300842725050233288677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13414867228483366822192451 20122300842725050233288677)
        ·
          refine ⟨3772931408010946918741627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20122300842725050233288677 3772931408010946918741627)
          ·
            refine ⟨5659397112016420378112441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772931408010946918741627 5659397112016420378112441)
            ·
              refine ⟨4244547834012315283584331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5659397112016420378112441 4244547834012315283584331)
              ·
                refine ⟨6366821751018472925376497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244547834012315283584331 6366821751018472925376497)
                ·
                  refine ⟨4775116313263854694032373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6366821751018472925376497 4775116313263854694032373)
                  ·
                    refine ⟨447667154368486377565535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4775116313263854694032373 447667154368486377565535)
                    ·
                      rfl

theorem cell23_2615486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2615486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615486 prefixEnd_2615486 := by exact prefixLift 2615486
  have htrace : WordTrace (prefixWord ++ tailWord_2615486) baseStart_2615486 baseEnd_2615486 := by
    simpa [prefixWord, tailWord_2615486, baseEnd_2615486] using wordTrace_append hprefix tailTrace_2615486
  have hstable : (prefixWord ++ tailWord_2615486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615486).length < 2 ^ (prefixWord ++ tailWord_2615486).sum := by decide
  have hdescent : baseEnd_2615486 < baseStart_2615486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615523 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2615523 : Nat := 118140960795 + 2615523 * 2 ^ 59
def prefixEnd_2615523 : Nat := 4983230072969 + 3 ^ 40 * 2615523 * 2
def baseEnd_2615523 : Nat := 1343020461889675487933935

theorem tailTrace_2615523 : CollatzResearch.WordTrace tailWord_2615523 prefixEnd_2615523 1343020461889675487933935 := by
  unfold tailWord_2615523
  simp only [CollatzResearch.WordTrace]
  refine ⟨95395960903414341610243223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63597307268942894406828815 95395960903414341610243223)
  ·
    refine ⟨143093941355121512415364835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95395960903414341610243223 143093941355121512415364835)
    ·
      refine ⟨214640912032682268623047253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143093941355121512415364835 214640912032682268623047253)
      ·
        refine ⟨2515323187882995335426335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 214640912032682268623047253 2515323187882995335426335)
        ·
          refine ⟨3772984781824493003139503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515323187882995335426335 3772984781824493003139503)
          ·
            refine ⟨5659477172736739504709255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772984781824493003139503 5659477172736739504709255)
            ·
              refine ⟨8489215759105109257063883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5659477172736739504709255 8489215759105109257063883)
              ·
                refine ⟨12733823638657663885595825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8489215759105109257063883 12733823638657663885595825)
                ·
                  refine ⟨9550367728993247914196869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12733823638657663885595825 9550367728993247914196869)
                  ·
                    refine ⟨1790693949186233983911913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9550367728993247914196869 1790693949186233983911913)
                    ·
                      refine ⟨1343020461889675487933935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790693949186233983911913 1343020461889675487933935)
                      ·
                        rfl

theorem cell23_2615523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2615523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615523 prefixEnd_2615523 := by exact prefixLift 2615523
  have htrace : WordTrace (prefixWord ++ tailWord_2615523) baseStart_2615523 baseEnd_2615523 := by
    simpa [prefixWord, tailWord_2615523, baseEnd_2615523] using wordTrace_append hprefix tailTrace_2615523
  have hstable : (prefixWord ++ tailWord_2615523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615523).length < 2 ^ (prefixWord ++ tailWord_2615523).sum := by decide
  have hdescent : baseEnd_2615523 < baseStart_2615523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615566 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_2615566 : Nat := 118140960795 + 2615566 * 2 ^ 59
def prefixEnd_2615566 : Nat := 4983230072969 + 3 ^ 40 * 2615566 * 2
def baseEnd_2615566 : Nat := 1343042541557818819696237

theorem tailTrace_2615566 : CollatzResearch.WordTrace tailWord_2615566 prefixEnd_2615566 1343042541557818819696237 := by
  unfold tailWord_2615566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11924691155282319994257319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63598352828172373302705701 11924691155282319994257319)
  ·
    refine ⟨17887036732923479991385979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11924691155282319994257319 17887036732923479991385979)
    ·
      refine ⟨26830555099385219987078969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17887036732923479991385979 26830555099385219987078969)
      ·
        refine ⟨20122916324538914990309227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26830555099385219987078969 20122916324538914990309227)
        ·
          refine ⟨30184374486808372485463841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20122916324538914990309227 30184374486808372485463841)
          ·
            refine ⟨22638280865106279364097881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30184374486808372485463841 22638280865106279364097881)
            ·
              refine ⟨16978710648829709523073411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22638280865106279364097881 16978710648829709523073411)
              ·
                refine ⟨25468065973244564284610117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16978710648829709523073411 25468065973244564284610117)
                ·
                  refine ⟨4775262369983355803364397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25468065973244564284610117 4775262369983355803364397)
                  ·
                    refine ⟨1790723388743758426261649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4775262369983355803364397 1790723388743758426261649)
                    ·
                      refine ⟨1343042541557818819696237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790723388743758426261649 1343042541557818819696237)
                      ·
                        rfl

theorem cell23_2615566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_2615566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615566 prefixEnd_2615566 := by exact prefixLift 2615566
  have htrace : WordTrace (prefixWord ++ tailWord_2615566) baseStart_2615566 baseEnd_2615566 := by
    simpa [prefixWord, tailWord_2615566, baseEnd_2615566] using wordTrace_append hprefix tailTrace_2615566
  have hstable : (prefixWord ++ tailWord_2615566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615566).length < 2 ^ (prefixWord ++ tailWord_2615566).sum := by decide
  have hdescent : baseEnd_2615566 < baseStart_2615566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615573 : List Nat := [1, 3, 2, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_2615573 : Nat := 118140960795 + 2615573 * 2 ^ 59
def prefixEnd_2615573 : Nat := 4983230072969 + 3 ^ 40 * 2615573 * 2
def baseEnd_2615573 : Nat := 1343046135922400292308705

theorem tailTrace_2615573 : CollatzResearch.WordTrace tailWord_2615573 prefixEnd_2615573 1343046135922400292308705 := by
  unfold tailWord_2615573
  simp only [CollatzResearch.WordTrace]
  refine ⟨95397784553233200149563373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63598523035488800099708915 95397784553233200149563373)
  ·
    refine ⟨35774169207462450056086265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95397784553233200149563373 35774169207462450056086265)
    ·
      refine ⟨26830626905596837542064699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35774169207462450056086265 26830626905596837542064699)
      ·
        refine ⟨40245940358395256313097049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26830626905596837542064699 40245940358395256313097049)
        ·
          refine ⟨30184455268796442234822787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40245940358395256313097049 30184455268796442234822787)
          ·
            refine ⟨45276682903194663352234181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30184455268796442234822787 45276682903194663352234181)
            ·
              refine ⟨8489378044348999378543909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45276682903194663352234181 8489378044348999378543909)
              ·
                refine ⟨1591758383315437383476983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8489378044348999378543909 1591758383315437383476983)
                ·
                  refine ⟨2387637574973156075215475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591758383315437383476983 2387637574973156075215475)
                  ·
                    refine ⟨3581456362459734112823213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2387637574973156075215475 3581456362459734112823213)
                    ·
                      refine ⟨1343046135922400292308705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3581456362459734112823213 1343046135922400292308705)
                      ·
                        rfl

theorem cell23_2615573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_2615573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615573 prefixEnd_2615573 := by exact prefixLift 2615573
  have htrace : WordTrace (prefixWord ++ tailWord_2615573) baseStart_2615573 baseEnd_2615573 := by
    simpa [prefixWord, tailWord_2615573, baseEnd_2615573] using wordTrace_append hprefix tailTrace_2615573
  have hstable : (prefixWord ++ tailWord_2615573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615573).length < 2 ^ (prefixWord ++ tailWord_2615573).sum := by decide
  have hdescent : baseEnd_2615573 < baseStart_2615573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615599 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 3]
def baseStart_2615599 : Nat := 118140960795 + 2615599 * 2 ^ 59
def prefixEnd_2615599 : Nat := 4983230072969 + 3 ^ 40 * 2615599 * 2
def baseEnd_2615599 : Nat := 1343059486419417190583585

theorem tailTrace_2615599 : CollatzResearch.WordTrace tailWord_2615599 prefixEnd_2615599 1343059486419417190583585 := by
  unfold tailWord_2615599
  simp only [CollatzResearch.WordTrace]
  refine ⟨95398732851139006590009851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63599155234092671060006567 95398732851139006590009851)
  ·
    refine ⟨143098099276708509885014777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95398732851139006590009851 143098099276708509885014777)
    ·
      refine ⟨107323574457531382413761083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143098099276708509885014777 107323574457531382413761083)
      ·
        refine ⟨160985361686297073620641625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107323574457531382413761083 160985361686297073620641625)
        ·
          refine ⟨120739021264722805215481219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160985361686297073620641625 120739021264722805215481219)
          ·
            refine ⟨181108531897084207823221829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120739021264722805215481219 181108531897084207823221829)
            ·
              refine ⟨33957849730703288966854093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181108531897084207823221829 33957849730703288966854093)
              ·
                refine ⟨12734193649013733362570285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33957849730703288966854093 12734193649013733362570285)
                ·
                  refine ⟨4775322618380150010963857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12734193649013733362570285 4775322618380150010963857)
                  ·
                    refine ⟨3581491963785112508222893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4775322618380150010963857 3581491963785112508222893)
                    ·
                      refine ⟨1343059486419417190583585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3581491963785112508222893 1343059486419417190583585)
                      ·
                        rfl

theorem cell23_2615599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_2615599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615599 prefixEnd_2615599 := by exact prefixLift 2615599
  have htrace : WordTrace (prefixWord ++ tailWord_2615599) baseStart_2615599 baseEnd_2615599 := by
    simpa [prefixWord, tailWord_2615599, baseEnd_2615599] using wordTrace_append hprefix tailTrace_2615599
  have hstable : (prefixWord ++ tailWord_2615599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615599).length < 2 ^ (prefixWord ++ tailWord_2615599).sum := by decide
  have hdescent : baseEnd_2615599 < baseStart_2615599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615650 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2615650 : Nat := 118140960795 + 2615650 * 2 ^ 59
def prefixEnd_2615650 : Nat := 4983230072969 + 3 ^ 40 * 2615650 * 2
def baseEnd_2615650 : Nat := 1343085673932796491045851

theorem tailTrace_2615650 : CollatzResearch.WordTrace tailWord_2615650 prefixEnd_2615650 1343085673932796491045851 := by
  unfold tailWord_2615650
  simp only [CollatzResearch.WordTrace]
  refine ⟨23850148243488560575029101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63600395315969494866744269 23850148243488560575029101)
  ·
    refine ⟨8943805591308210215635913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23850148243488560575029101 8943805591308210215635913)
    ·
      refine ⟨6707854193481157661726935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8943805591308210215635913 6707854193481157661726935)
      ·
        refine ⟨10061781290221736492590403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6707854193481157661726935 10061781290221736492590403)
        ·
          refine ⟨15092671935332604738885605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10061781290221736492590403 15092671935332604738885605)
          ·
            refine ⟨2829875987874863388541051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15092671935332604738885605 2829875987874863388541051)
            ·
              refine ⟨4244813981812295082811577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829875987874863388541051 4244813981812295082811577)
              ·
                refine ⟨3183610486359221312108683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4244813981812295082811577 3183610486359221312108683)
                ·
                  refine ⟨4775415729538831968163025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183610486359221312108683 4775415729538831968163025)
                  ·
                    refine ⟨3581561797154123976122269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4775415729538831968163025 3581561797154123976122269)
                    ·
                      refine ⟨1343085673932796491045851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3581561797154123976122269 1343085673932796491045851)
                      ·
                        rfl

theorem cell23_2615650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2615650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615650 prefixEnd_2615650 := by exact prefixLift 2615650
  have htrace : WordTrace (prefixWord ++ tailWord_2615650) baseStart_2615650 baseEnd_2615650 := by
    simpa [prefixWord, tailWord_2615650, baseEnd_2615650] using wordTrace_append hprefix tailTrace_2615650
  have hstable : (prefixWord ++ tailWord_2615650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615650).length < 2 ^ (prefixWord ++ tailWord_2615650).sum := by decide
  have hdescent : baseEnd_2615650 < baseStart_2615650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615720 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2615720 : Nat := 118140960795 + 2615720 * 2 ^ 59
def prefixEnd_2615720 : Nat := 4983230072969 + 3 ^ 40 * 2615720 * 2
def baseEnd_2615720 : Nat := 1343121617578611217170529

theorem tailTrace_2615720 : CollatzResearch.WordTrace tailWord_2615720 prefixEnd_2615720 1343121617578611217170529 := by
  unfold tailWord_2615720
  simp only [CollatzResearch.WordTrace]
  refine ⟨47701573041850322127582307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63602097389133762836776409 47701573041850322127582307)
  ·
    refine ⟨71552359562775483191373461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47701573041850322127582307 71552359562775483191373461)
    ·
      refine ⟨3354016854505100774595631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71552359562775483191373461 3354016854505100774595631)
      ·
        refine ⟨5031025281757651161893447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354016854505100774595631 5031025281757651161893447)
        ·
          refine ⟨7546537922636476742840171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031025281757651161893447 7546537922636476742840171)
          ·
            refine ⟨11319806883954715114260257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546537922636476742840171 11319806883954715114260257)
            ·
              refine ⟨8489855162966036335695193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11319806883954715114260257 8489855162966036335695193)
              ·
                refine ⟨6367391372224527251771395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8489855162966036335695193 6367391372224527251771395)
                ·
                  refine ⟨9551087058336790877657093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6367391372224527251771395 9551087058336790877657093)
                  ·
                    refine ⟨1790828823438148289560705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9551087058336790877657093 1790828823438148289560705)
                    ·
                      refine ⟨1343121617578611217170529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790828823438148289560705 1343121617578611217170529)
                      ·
                        rfl

theorem cell23_2615720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2615720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615720 prefixEnd_2615720 := by exact prefixLift 2615720
  have htrace : WordTrace (prefixWord ++ tailWord_2615720) baseStart_2615720 baseEnd_2615720 := by
    simpa [prefixWord, tailWord_2615720, baseEnd_2615720] using wordTrace_append hprefix tailTrace_2615720
  have hstable : (prefixWord ++ tailWord_2615720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615720).length < 2 ^ (prefixWord ++ tailWord_2615720).sum := by decide
  have hdescent : baseEnd_2615720 < baseStart_2615720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615737 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 2, 2, 2]
def baseStart_2615737 : Nat := 118140960795 + 2615737 * 2 ^ 59
def prefixEnd_2615737 : Nat := 4983230072969 + 3 ^ 40 * 2615737 * 2
def baseEnd_2615737 : Nat := 1343130346749737650657951

theorem tailTrace_2615737 : CollatzResearch.WordTrace tailWord_2615737 prefixEnd_2615737 1343130346749737650657951 := by
  unfold tailWord_2615737
  simp only [CollatzResearch.WordTrace]
  refine ⟨95403766124639056158533465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63602510749759370772355643 95403766124639056158533465)
  ·
    refine ⟨71552824593479292118900099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95403766124639056158533465 71552824593479292118900099)
    ·
      refine ⟨107329236890218938178350149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71552824593479292118900099 107329236890218938178350149)
      ·
        refine ⟨20124231916916050908440653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107329236890218938178350149 20124231916916050908440653)
        ·
          refine ⟨7546586968843519090665245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20124231916916050908440653 7546586968843519090665245)
          ·
            refine ⟨2829970113316319658999467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7546586968843519090665245 2829970113316319658999467)
            ·
              refine ⟨4244955169974479488499201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829970113316319658999467 4244955169974479488499201)
              ·
                refine ⟨3183716377480859616374401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4244955169974479488499201 3183716377480859616374401)
                ·
                  refine ⟨2387787283110644712280801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3183716377480859616374401 2387787283110644712280801)
                  ·
                    refine ⟨1790840462332983534210601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2387787283110644712280801 1790840462332983534210601)
                    ·
                      refine ⟨1343130346749737650657951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790840462332983534210601 1343130346749737650657951)
                      ·
                        rfl

theorem cell23_2615737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_2615737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615737 prefixEnd_2615737 := by exact prefixLift 2615737
  have htrace : WordTrace (prefixWord ++ tailWord_2615737) baseStart_2615737 baseEnd_2615737 := by
    simpa [prefixWord, tailWord_2615737, baseEnd_2615737] using wordTrace_append hprefix tailTrace_2615737
  have hstable : (prefixWord ++ tailWord_2615737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615737).length < 2 ^ (prefixWord ++ tailWord_2615737).sum := by decide
  have hdescent : baseEnd_2615737 < baseStart_2615737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615769 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 2, 8]
def baseStart_2615769 : Nat := 118140960795 + 2615769 * 2 ^ 59
def prefixEnd_2615769 : Nat := 4983230072969 + 3 ^ 40 * 2615769 * 2
def baseEnd_2615769 : Nat := 447715592710227175152601

theorem tailTrace_2615769 : CollatzResearch.WordTrace tailWord_2615769 prefixEnd_2615769 447715592710227175152601 := by
  unfold tailWord_2615769
  simp only [CollatzResearch.WordTrace]
  refine ⟨95404933260523125623698361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63603288840348750415798907 95404933260523125623698361)
  ·
    refine ⟨71553699945392344217773771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95404933260523125623698361 71553699945392344217773771)
    ·
      refine ⟨107330549918088516326660657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71553699945392344217773771 107330549918088516326660657)
      ·
        refine ⟨80497912438566387244995493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107330549918088516326660657 80497912438566387244995493)
        ·
          refine ⟨15093358582231197608436655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80497912438566387244995493 15093358582231197608436655)
          ·
            refine ⟨22640037873346796412654983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15093358582231197608436655 22640037873346796412654983)
            ·
              refine ⟨33960056810020194618982475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22640037873346796412654983 33960056810020194618982475)
              ·
                refine ⟨50940085215030291928473713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33960056810020194618982475 50940085215030291928473713)
                ·
                  refine ⟨38205063911272718946355285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50940085215030291928473713 38205063911272718946355285)
                  ·
                    refine ⟨447715592710227175152601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38205063911272718946355285 447715592710227175152601)
                    ·
                      rfl

theorem cell23_2615769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_2615769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615769 prefixEnd_2615769 := by exact prefixLift 2615769
  have htrace : WordTrace (prefixWord ++ tailWord_2615769) baseStart_2615769 baseEnd_2615769 := by
    simpa [prefixWord, tailWord_2615769, baseEnd_2615769] using wordTrace_append hprefix tailTrace_2615769
  have hstable : (prefixWord ++ tailWord_2615769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615769).length < 2 ^ (prefixWord ++ tailWord_2615769).sum := by decide
  have hdescent : baseEnd_2615769 < baseStart_2615769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615776 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_2615776 : Nat := 118140960795 + 2615776 * 2 ^ 59
def prefixEnd_2615776 : Nat := 4983230072969 + 3 ^ 40 * 2615776 * 2
def baseEnd_2615776 : Nat := 1343150372495262998070271

theorem tailTrace_2615776 : CollatzResearch.WordTrace tailWord_2615776 prefixEnd_2615776 1343150372495262998070271 := by
  unfold tailWord_2615776
  simp only [CollatzResearch.WordTrace]
  refine ⟨47702594285748882909601591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63603459047665177212802121 47702594285748882909601591)
  ·
    refine ⟨71553891428623324364402387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47702594285748882909601591 71553891428623324364402387)
    ·
      refine ⟨107330837142934986546603581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71553891428623324364402387 107330837142934986546603581)
      ·
        refine ⟨40249063928600619954976343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107330837142934986546603581 40249063928600619954976343)
        ·
          refine ⟨60373595892900929932464515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40249063928600619954976343 60373595892900929932464515)
          ·
            refine ⟨90560393839351394898696773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60373595892900929932464515 90560393839351394898696773)
            ·
              refine ⟨16980073844878386543505645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90560393839351394898696773 16980073844878386543505645)
              ·
                refine ⟨6367527691829394953814617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16980073844878386543505645 6367527691829394953814617)
                ·
                  refine ⟨4775645768872046215360963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6367527691829394953814617 4775645768872046215360963)
                  ·
                    refine ⟨7163468653308069323041445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4775645768872046215360963 7163468653308069323041445)
                    ·
                      refine ⟨1343150372495262998070271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7163468653308069323041445 1343150372495262998070271)
                      ·
                        rfl

theorem cell23_2615776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_2615776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615776 prefixEnd_2615776 := by exact prefixLift 2615776
  have htrace : WordTrace (prefixWord ++ tailWord_2615776) baseStart_2615776 baseEnd_2615776 := by
    simpa [prefixWord, tailWord_2615776, baseEnd_2615776] using wordTrace_append hprefix tailTrace_2615776
  have hstable : (prefixWord ++ tailWord_2615776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615776).length < 2 ^ (prefixWord ++ tailWord_2615776).sum := by decide
  have hdescent : baseEnd_2615776 < baseStart_2615776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615917 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_2615917 : Nat := 118140960795 + 2615917 * 2 ^ 59
def prefixEnd_2615917 : Nat := 4983230072969 + 3 ^ 40 * 2615917 * 2
def baseEnd_2615917 : Nat := 1343222773267546946407123

theorem tailTrace_2615917 : CollatzResearch.WordTrace tailWord_2615917 prefixEnd_2615917 1343222773267546946407123 := by
  unfold tailWord_2615917
  simp only [CollatzResearch.WordTrace]
  refine ⟨95410331263986946900086005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63606887509324631266724003 95410331263986946900086005)
  ·
    refine ⟨8944718555998776271883063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95410331263986946900086005 8944718555998776271883063)
    ·
      refine ⟨13417077833998164407824595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8944718555998776271883063 13417077833998164407824595)
      ·
        refine ⟨20125616750997246611736893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13417077833998164407824595 20125616750997246611736893)
        ·
          refine ⟨7547106281623967479401335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20125616750997246611736893 7547106281623967479401335)
          ·
            refine ⟨11320659422435951219102003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7547106281623967479401335 11320659422435951219102003)
            ·
              refine ⟨16980989133653926828653005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11320659422435951219102003 16980989133653926828653005)
              ·
                refine ⟨6367870925120222560744877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16980989133653926828653005 6367870925120222560744877)
                ·
                  refine ⟨2387951596920083460279329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6367870925120222560744877 2387951596920083460279329)
                  ·
                    refine ⟨1790963697690062595209497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2387951596920083460279329 1790963697690062595209497)
                    ·
                      refine ⟨1343222773267546946407123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1790963697690062595209497 1343222773267546946407123)
                      ·
                        rfl

theorem cell23_2615917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_2615917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615917 prefixEnd_2615917 := by exact prefixLift 2615917
  have htrace : WordTrace (prefixWord ++ tailWord_2615917) baseStart_2615917 baseEnd_2615917 := by
    simpa [prefixWord, tailWord_2615917, baseEnd_2615917] using wordTrace_append hprefix tailTrace_2615917
  have hstable : (prefixWord ++ tailWord_2615917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615917).length < 2 ^ (prefixWord ++ tailWord_2615917).sum := by decide
  have hdescent : baseEnd_2615917 < baseStart_2615917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615940 : List Nat := [2, 3, 2, 1, 3, 3, 2, 7]
def baseStart_2615940 : Nat := 118140960795 + 2615940 * 2 ^ 59
def prefixEnd_2615940 : Nat := 4983230072969 + 3 ^ 40 * 2615940 * 2
def baseEnd_2615940 : Nat := 49749429011948161348871

theorem tailTrace_2615940 : CollatzResearch.WordTrace tailWord_2615940 prefixEnd_2615940 49749429011948161348871 := by
  unfold tailWord_2615940
  simp only [CollatzResearch.WordTrace]
  refine ⟨47705585071451810914086637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63607446761935747885448849 47705585071451810914086637)
  ·
    refine ⟨17889594401794429092782489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47705585071451810914086637 17889594401794429092782489)
    ·
      refine ⟨13417195801345821819586867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17889594401794429092782489 13417195801345821819586867)
      ·
        refine ⟨20125793702018732729380301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13417195801345821819586867 20125793702018732729380301)
        ·
          refine ⟨7547172638257024773517613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20125793702018732729380301 7547172638257024773517613)
          ·
            refine ⟨2830189739346384290069105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7547172638257024773517613 2830189739346384290069105)
            ·
              refine ⟨2122642304509788217551829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830189739346384290069105 2122642304509788217551829)
              ·
                refine ⟨49749429011948161348871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2122642304509788217551829 49749429011948161348871)
                ·
                  rfl

theorem cell23_2615940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 7].length) (baseStart_2615940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615940 prefixEnd_2615940 := by exact prefixLift 2615940
  have htrace : WordTrace (prefixWord ++ tailWord_2615940) baseStart_2615940 baseEnd_2615940 := by
    simpa [prefixWord, tailWord_2615940, baseEnd_2615940] using wordTrace_append hprefix tailTrace_2615940
  have hstable : (prefixWord ++ tailWord_2615940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615940).length < 2 ^ (prefixWord ++ tailWord_2615940).sum := by decide
  have hdescent : baseEnd_2615940 < baseStart_2615940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615950 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2615950 : Nat := 118140960795 + 2615950 * 2 ^ 59
def prefixEnd_2615950 : Nat := 4983230072969 + 3 ^ 40 * 2615950 * 2
def baseEnd_2615950 : Nat := 1343239718129145317294471

theorem tailTrace_2615950 : CollatzResearch.WordTrace tailWord_2615950 prefixEnd_2615950 1343239718129145317294471 := by
  unfold tailWord_2615950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926441859108424192004663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63607689915244929024024869 11926441859108424192004663)
  ·
    refine ⟨17889662788662636288006995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11926441859108424192004663 17889662788662636288006995)
    ·
      refine ⟨26834494182993954432010493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17889662788662636288006995 26834494182993954432010493)
      ·
        refine ⟨10062935318622732912003935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26834494182993954432010493 10062935318622732912003935)
        ·
          refine ⟨15094402977934099368005903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10062935318622732912003935 15094402977934099368005903)
          ·
            refine ⟨22641604466901149052008855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15094402977934099368005903 22641604466901149052008855)
            ·
              refine ⟨33962406700351723578013283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22641604466901149052008855 33962406700351723578013283)
              ·
                refine ⟨50943610050527585367019925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33962406700351723578013283 50943610050527585367019925)
                ·
                  refine ⟨2387981721118480564079059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50943610050527585367019925 2387981721118480564079059)
                  ·
                    refine ⟨3581972581677720846118589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2387981721118480564079059 3581972581677720846118589)
                    ·
                      refine ⟨1343239718129145317294471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3581972581677720846118589 1343239718129145317294471)
                      ·
                        rfl

theorem cell23_2615950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2615950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615950 prefixEnd_2615950 := by exact prefixLift 2615950
  have htrace : WordTrace (prefixWord ++ tailWord_2615950) baseStart_2615950 baseEnd_2615950 := by
    simpa [prefixWord, tailWord_2615950, baseEnd_2615950] using wordTrace_append hprefix tailTrace_2615950
  have hstable : (prefixWord ++ tailWord_2615950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615950).length < 2 ^ (prefixWord ++ tailWord_2615950).sum := by decide
  have hdescent : baseEnd_2615950 < baseStart_2615950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2615978 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2615978 : Nat := 118140960795 + 2615978 * 2 ^ 59
def prefixEnd_2615978 : Nat := 4983230072969 + 3 ^ 40 * 2615978 * 2
def baseEnd_2615978 : Nat := 447751365195823735914781

theorem tailTrace_2615978 : CollatzResearch.WordTrace tailWord_2615978 prefixEnd_2615978 447751365195823735914781 := by
  unfold tailWord_2615978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23853139029191488579514147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63608370744510636212037725 23853139029191488579514147)
  ·
    refine ⟨35779708543787232869271221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23853139029191488579514147 35779708543787232869271221)
    ·
      refine ⟨3354347675980053081494177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35779708543787232869271221 3354347675980053081494177)
      ·
        refine ⟨2515760756985039811120633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354347675980053081494177 2515760756985039811120633)
        ·
          refine ⟨1886820567738779858340475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2515760756985039811120633 1886820567738779858340475)
          ·
            refine ⟨2830230851608169787510713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886820567738779858340475 2830230851608169787510713)
            ·
              refine ⟨2122673138706127340633035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830230851608169787510713 2122673138706127340633035)
              ·
                refine ⟨3184009708059191010949553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122673138706127340633035 3184009708059191010949553)
                ·
                  refine ⟨2388007281044393258212165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184009708059191010949553 2388007281044393258212165)
                  ·
                    refine ⟨447751365195823735914781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2388007281044393258212165 447751365195823735914781)
                    ·
                      rfl

theorem cell23_2615978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2615978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2615978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2615978 prefixEnd_2615978 := by exact prefixLift 2615978
  have htrace : WordTrace (prefixWord ++ tailWord_2615978) baseStart_2615978 baseEnd_2615978 := by
    simpa [prefixWord, tailWord_2615978, baseEnd_2615978] using wordTrace_append hprefix tailTrace_2615978
  have hstable : (prefixWord ++ tailWord_2615978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2615978).length < 2 ^ (prefixWord ++ tailWord_2615978).sum := by decide
  have hdescent : baseEnd_2615978 < baseStart_2615978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2615978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616016 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_2616016 : Nat := 118140960795 + 2616016 * 2 ^ 59
def prefixEnd_2616016 : Nat := 4983230072969 + 3 ^ 40 * 2616016 * 2
def baseEnd_2616016 : Nat := 1343273607852342059069167

theorem tailTrace_2616016 : CollatzResearch.WordTrace tailWord_2616016 prefixEnd_2616016 1343273607852342059069167 := by
  unfold tailWord_2616016
  simp only [CollatzResearch.WordTrace]
  refine ⟨47706971045314143403969951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63609294727085524538626601 47706971045314143403969951)
  ·
    refine ⟨71560456567971215105954927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47706971045314143403969951 71560456567971215105954927)
    ·
      refine ⟨107340684851956822658932391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71560456567971215105954927 107340684851956822658932391)
      ·
        refine ⟨161011027277935233988398587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107340684851956822658932391 161011027277935233988398587)
        ·
          refine ⟨241516540916902850982597881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161011027277935233988398587 241516540916902850982597881)
          ·
            refine ⟨181137405687677138236948411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241516540916902850982597881 181137405687677138236948411)
            ·
              refine ⟨271706108531515707355422617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181137405687677138236948411 271706108531515707355422617)
              ·
                refine ⟨203779581398636780516566963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271706108531515707355422617 203779581398636780516566963)
                ·
                  refine ⟨305669372097955170774850445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203779581398636780516566963 305669372097955170774850445)
                  ·
                    refine ⟨114626014536733189040568917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305669372097955170774850445 114626014536733189040568917)
                    ·
                      refine ⟨1343273607852342059069167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114626014536733189040568917 1343273607852342059069167)
                      ·
                        rfl

theorem cell23_2616016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_2616016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616016 prefixEnd_2616016 := by exact prefixLift 2616016
  have htrace : WordTrace (prefixWord ++ tailWord_2616016) baseStart_2616016 baseEnd_2616016 := by
    simpa [prefixWord, tailWord_2616016, baseEnd_2616016] using wordTrace_append hprefix tailTrace_2616016
  have hstable : (prefixWord ++ tailWord_2616016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616016).length < 2 ^ (prefixWord ++ tailWord_2616016).sum := by decide
  have hdescent : baseEnd_2616016 < baseStart_2616016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616024 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2]
def baseStart_2616024 : Nat := 118140960795 + 2616024 * 2 ^ 59
def prefixEnd_2616024 : Nat := 4983230072969 + 3 ^ 40 * 2616024 * 2
def baseEnd_2616024 : Nat := 1343277715697578027769131

theorem tailTrace_2616024 : CollatzResearch.WordTrace tailWord_2616024 prefixEnd_2616024 1343277715697578027769131 := by
  unfold tailWord_2616024
  simp only [CollatzResearch.WordTrace]
  refine ⟨47707116937299652087115563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63609489249732869449487417 47707116937299652087115563)
  ·
    refine ⟨71560675405949478130673345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47707116937299652087115563 71560675405949478130673345)
    ·
      refine ⟨53670506554462108598005009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71560675405949478130673345 53670506554462108598005009)
      ·
        refine ⟨40252879915846581448503757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53670506554462108598005009 40252879915846581448503757)
        ·
          refine ⟨15094829968442468043188909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40252879915846581448503757 15094829968442468043188909)
          ·
            refine ⟨5660561238165925516195841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15094829968442468043188909 5660561238165925516195841)
            ·
              refine ⟨4245420928624444137146881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5660561238165925516195841 4245420928624444137146881)
              ·
                refine ⟨3184065696468333102860161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4245420928624444137146881 3184065696468333102860161)
                ·
                  refine ⟨2388049272351249827145121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184065696468333102860161 2388049272351249827145121)
                  ·
                    refine ⟨1791036954263437370358841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2388049272351249827145121 1791036954263437370358841)
                    ·
                      refine ⟨1343277715697578027769131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791036954263437370358841 1343277715697578027769131)
                      ·
                        rfl

theorem cell23_2616024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_2616024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616024 prefixEnd_2616024 := by exact prefixLift 2616024
  have htrace : WordTrace (prefixWord ++ tailWord_2616024) baseStart_2616024 baseEnd_2616024 := by
    simpa [prefixWord, tailWord_2616024, baseEnd_2616024] using wordTrace_append hprefix tailTrace_2616024
  have hstable : (prefixWord ++ tailWord_2616024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616024).length < 2 ^ (prefixWord ++ tailWord_2616024).sum := by decide
  have hdescent : baseEnd_2616024 < baseStart_2616024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616060 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_2616060 : Nat := 118140960795 + 2616060 * 2 ^ 59
def prefixEnd_2616060 : Nat := 4983230072969 + 3 ^ 40 * 2616060 * 2
def baseEnd_2616060 : Nat := 447765400333713295639655

theorem tailTrace_2616060 : CollatzResearch.WordTrace tailWord_2616060 prefixEnd_2616060 447765400333713295639655 := by
  unfold tailWord_2616060
  simp only [CollatzResearch.WordTrace]
  refine ⟨47707773451234441161270817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63610364601645921548361089 47707773451234441161270817)
  ·
    refine ⟨35780830088425830870953113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47707773451234441161270817 35780830088425830870953113)
    ·
      refine ⟨26835622566319373153214835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35780830088425830870953113 26835622566319373153214835)
      ·
        refine ⟨40253433849479059729822253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26835622566319373153214835 40253433849479059729822253)
        ·
          refine ⟨15095037693554647398683345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40253433849479059729822253 15095037693554647398683345)
          ·
            refine ⟨11321278270165985549012509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15095037693554647398683345 11321278270165985549012509)
            ·
              refine ⟨4245479351312244580879691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11321278270165985549012509 4245479351312244580879691)
              ·
                refine ⟨6368219026968366871319537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245479351312244580879691 6368219026968366871319537)
                ·
                  refine ⟨4776164270226275153489653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368219026968366871319537 4776164270226275153489653)
                  ·
                    refine ⟨447765400333713295639655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4776164270226275153489653 447765400333713295639655)
                    ·
                      rfl

theorem cell23_2616060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_2616060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616060 prefixEnd_2616060 := by exact prefixLift 2616060
  have htrace : WordTrace (prefixWord ++ tailWord_2616060) baseStart_2616060 baseEnd_2616060 := by
    simpa [prefixWord, tailWord_2616060, baseEnd_2616060] using wordTrace_append hprefix tailTrace_2616060
  have hstable : (prefixWord ++ tailWord_2616060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616060).length < 2 ^ (prefixWord ++ tailWord_2616060).sum := by decide
  have hdescent : baseEnd_2616060 < baseStart_2616060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616141 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2616141 : Nat := 118140960795 + 2616141 * 2 ^ 59
def prefixEnd_2616141 : Nat := 4983230072969 + 3 ^ 40 * 2616141 * 2
def baseEnd_2616141 : Nat := 447779264311384690002031

theorem tailTrace_2616141 : CollatzResearch.WordTrace tailWord_2616141 prefixEnd_2616141 447779264311384690002031 := by
  unfold tailWord_2616141
  simp only [CollatzResearch.WordTrace]
  refine ⟨95418501215175433156240277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63612334143450288770826851 95418501215175433156240277)
  ·
    refine ⟨4472742244461348429198763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95418501215175433156240277 4472742244461348429198763)
    ·
      refine ⟨6709113366692022643798145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4472742244461348429198763 6709113366692022643798145)
      ·
        refine ⟨5031835025019016982848609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6709113366692022643798145 5031835025019016982848609)
        ·
          refine ⟨3773876268764262737136457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5031835025019016982848609 3773876268764262737136457)
          ·
            refine ⟨2830407201573197052852343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3773876268764262737136457 2830407201573197052852343)
            ·
              refine ⟨4245610802359795579278515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830407201573197052852343 4245610802359795579278515)
              ·
                refine ⟨6368416203539693368917773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245610802359795579278515 6368416203539693368917773)
                ·
                  refine ⟨2388156076327385013344165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6368416203539693368917773 2388156076327385013344165)
                  ·
                    refine ⟨447779264311384690002031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2388156076327385013344165 447779264311384690002031)
                    ·
                      rfl

theorem cell23_2616141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2616141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616141 prefixEnd_2616141 := by exact prefixLift 2616141
  have htrace : WordTrace (prefixWord ++ tailWord_2616141) baseStart_2616141 baseEnd_2616141 := by
    simpa [prefixWord, tailWord_2616141, baseEnd_2616141] using wordTrace_append hprefix tailTrace_2616141
  have hstable : (prefixWord ++ tailWord_2616141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616141).length < 2 ^ (prefixWord ++ tailWord_2616141).sum := by decide
  have hdescent : baseEnd_2616141 < baseStart_2616141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616167 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 1, 5]
def baseStart_2616167 : Nat := 118140960795 + 2616167 * 2 ^ 59
def prefixEnd_2616167 : Nat := 4983230072969 + 3 ^ 40 * 2616167 * 2
def baseEnd_2616167 : Nat := 447783714477056989426991

theorem tailTrace_2616167 : CollatzResearch.WordTrace tailWord_2616167 prefixEnd_2616167 447783714477056989426991 := by
  unfold tailWord_2616167
  simp only [CollatzResearch.WordTrace]
  refine ⟨95419449513081239596686755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63612966342054159731124503 95419449513081239596686755)
  ·
    refine ⟨143129174269621859395030133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95419449513081239596686755 143129174269621859395030133)
    ·
      refine ⟨13418360087777049318284075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143129174269621859395030133 13418360087777049318284075)
      ·
        refine ⟨20127540131665573977426113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13418360087777049318284075 20127540131665573977426113)
        ·
          refine ⟨15095655098749180483069585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20127540131665573977426113 15095655098749180483069585)
          ·
            refine ⟨11321741324061885362302189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15095655098749180483069585 11321741324061885362302189)
            ·
              refine ⟨4245652996523207010863321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11321741324061885362302189 4245652996523207010863321)
              ·
                refine ⟨3184239747392405258147491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4245652996523207010863321 3184239747392405258147491)
                ·
                  refine ⟨4776359621088607887221237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184239747392405258147491 4776359621088607887221237)
                  ·
                    refine ⟨447783714477056989426991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4776359621088607887221237 447783714477056989426991)
                    ·
                      rfl

theorem cell23_2616167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_2616167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616167 prefixEnd_2616167 := by exact prefixLift 2616167
  have htrace : WordTrace (prefixWord ++ tailWord_2616167) baseStart_2616167 baseEnd_2616167 := by
    simpa [prefixWord, tailWord_2616167, baseEnd_2616167] using wordTrace_append hprefix tailTrace_2616167
  have hstable : (prefixWord ++ tailWord_2616167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616167).length < 2 ^ (prefixWord ++ tailWord_2616167).sum := by decide
  have hdescent : baseEnd_2616167 < baseStart_2616167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616193 : List Nat := [1, 2, 4, 16]
def baseStart_2616193 : Nat := 118140960795 + 2616193 * 2 ^ 59
def prefixEnd_2616193 : Nat := 4983230072969 + 3 ^ 40 * 2616193 * 2
def baseEnd_2616193 : Nat := 614249882911837158919

theorem tailTrace_2616193 : CollatzResearch.WordTrace tailWord_2616193 prefixEnd_2616193 614249882911837158919 := by
  unfold tailWord_2616193
  simp only [CollatzResearch.WordTrace]
  refine ⟨95420397810987046037133233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63613598540658030691422155 95420397810987046037133233)
  ·
    refine ⟨71565298358240284527849925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95420397810987046037133233 71565298358240284527849925)
    ·
      refine ⟨13418493442170053348971861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71565298358240284527849925 13418493442170053348971861)
      ·
        refine ⟨614249882911837158919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 13418493442170053348971861 614249882911837158919)
        ·
          rfl

theorem cell23_2616193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 16].length) (baseStart_2616193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616193 prefixEnd_2616193 := by exact prefixLift 2616193
  have htrace : WordTrace (prefixWord ++ tailWord_2616193) baseStart_2616193 baseEnd_2616193 := by
    simpa [prefixWord, tailWord_2616193, baseEnd_2616193] using wordTrace_append hprefix tailTrace_2616193
  have hstable : (prefixWord ++ tailWord_2616193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616193).length < 2 ^ (prefixWord ++ tailWord_2616193).sum := by decide
  have hdescent : baseEnd_2616193 < baseStart_2616193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616197 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_2616197 : Nat := 118140960795 + 2616197 * 2 ^ 59
def prefixEnd_2616197 : Nat := 4983230072969 + 3 ^ 40 * 2616197 * 2
def baseEnd_2616197 : Nat := 447788849283601950301945

theorem tailTrace_2616197 : CollatzResearch.WordTrace tailWord_2616197 prefixEnd_2616197 447788849283601950301945 := by
  unfold tailWord_2616197
  simp only [CollatzResearch.WordTrace]
  refine ⟨95420543702972554720278845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63613695801981703146852563 95420543702972554720278845)
  ·
    refine ⟨35782703888614708020104567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95420543702972554720278845 35782703888614708020104567)
    ·
      refine ⟨53674055832922062030156851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35782703888614708020104567 53674055832922062030156851)
      ·
        refine ⟨80511083749383093045235277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53674055832922062030156851 80511083749383093045235277)
        ·
          refine ⟨30191656406018659891963229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80511083749383093045235277 30191656406018659891963229)
          ·
            refine ⟨11321871152256997459486211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30191656406018659891963229 11321871152256997459486211)
            ·
              refine ⟨16982806728385496189229317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11321871152256997459486211 16982806728385496189229317)
              ·
                refine ⟨3184276261572280535480497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16982806728385496189229317 3184276261572280535480497)
                ·
                  refine ⟨2388207196179210401610373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184276261572280535480497 2388207196179210401610373)
                  ·
                    refine ⟨447788849283601950301945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2388207196179210401610373 447788849283601950301945)
                    ·
                      rfl

theorem cell23_2616197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_2616197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616197 prefixEnd_2616197 := by exact prefixLift 2616197
  have htrace : WordTrace (prefixWord ++ tailWord_2616197) baseStart_2616197 baseEnd_2616197 := by
    simpa [prefixWord, tailWord_2616197, baseEnd_2616197] using wordTrace_append hprefix tailTrace_2616197
  have hstable : (prefixWord ++ tailWord_2616197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616197).length < 2 ^ (prefixWord ++ tailWord_2616197).sum := by decide
  have hdescent : baseEnd_2616197 < baseStart_2616197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616254 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2616254 : Nat := 118140960795 + 2616254 * 2 ^ 59
def prefixEnd_2616254 : Nat := 4983230072969 + 3 ^ 40 * 2616254 * 2
def baseEnd_2616254 : Nat := 1343395816248112127893073

theorem tailTrace_2616254 : CollatzResearch.WordTrace tailWord_2616254 prefixEnd_2616254 1343395816248112127893073 := by
  unfold tailWord_2616254
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927827832970756681887977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63615081775844035636735877 11927827832970756681887977)
  ·
    refine ⟨8945870874728067511415983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11927827832970756681887977 8945870874728067511415983)
    ·
      refine ⟨13418806312092101267123975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8945870874728067511415983 13418806312092101267123975)
      ·
        refine ⟨20128209468138151900685963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13418806312092101267123975 20128209468138151900685963)
        ·
          refine ⟨30192314202207227851028945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20128209468138151900685963 30192314202207227851028945)
          ·
            refine ⟨22644235651655420888271709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30192314202207227851028945 22644235651655420888271709)
            ·
              refine ⟨8491588369370782833101891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22644235651655420888271709 8491588369370782833101891)
              ·
                refine ⟨12737382554056174249652837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8491588369370782833101891 12737382554056174249652837)
                ·
                  refine ⟨2388259228885532671809907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12737382554056174249652837 2388259228885532671809907)
                  ·
                    refine ⟨3582388843328299007714861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2388259228885532671809907 3582388843328299007714861)
                    ·
                      refine ⟨1343395816248112127893073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3582388843328299007714861 1343395816248112127893073)
                      ·
                        rfl

theorem cell23_2616254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2616254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616254 prefixEnd_2616254 := by exact prefixLift 2616254
  have htrace : WordTrace (prefixWord ++ tailWord_2616254) baseStart_2616254 baseEnd_2616254 := by
    simpa [prefixWord, tailWord_2616254, baseEnd_2616254] using wordTrace_append hprefix tailTrace_2616254
  have hstable : (prefixWord ++ tailWord_2616254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616254).length < 2 ^ (prefixWord ++ tailWord_2616254).sum := by decide
  have hdescent : baseEnd_2616254 < baseStart_2616254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616271 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 2, 1, 3]
def baseStart_2616271 : Nat := 118140960795 + 2616271 * 2 ^ 59
def prefixEnd_2616271 : Nat := 4983230072969 + 3 ^ 40 * 2616271 * 2
def baseEnd_2616271 : Nat := 1343404545419238561380495

theorem tailTrace_2616271 : CollatzResearch.WordTrace tailWord_2616271 prefixEnd_2616271 1343404545419238561380495 := by
  unfold tailWord_2616271
  simp only [CollatzResearch.WordTrace]
  refine ⟨95423242704704465358472667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63615495136469643572315111 95423242704704465358472667)
  ·
    refine ⟨143134864057056698037709001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95423242704704465358472667 143134864057056698037709001)
    ·
      refine ⟨107351148042792523528281751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143134864057056698037709001 107351148042792523528281751)
      ·
        refine ⟨161026722064188785292422627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107351148042792523528281751 161026722064188785292422627)
        ·
          refine ⟨241540083096283177938633941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161026722064188785292422627 241540083096283177938633941)
          ·
            refine ⟨5661095697569136982936733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 241540083096283177938633941 5661095697569136982936733)
            ·
              refine ⟨2122910886588426368601275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5661095697569136982936733 2122910886588426368601275)
              ·
                refine ⟨3184366329882639552901913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122910886588426368601275 3184366329882639552901913)
                ·
                  refine ⟨2388274747411979664676435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184366329882639552901913 2388274747411979664676435)
                  ·
                    refine ⟨3582412121117969497014653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2388274747411979664676435 3582412121117969497014653)
                    ·
                      refine ⟨1343404545419238561380495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3582412121117969497014653 1343404545419238561380495)
                      ·
                        rfl

theorem cell23_2616271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 2, 1, 3].length) (baseStart_2616271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616271 prefixEnd_2616271 := by exact prefixLift 2616271
  have htrace : WordTrace (prefixWord ++ tailWord_2616271) baseStart_2616271 baseEnd_2616271 := by
    simpa [prefixWord, tailWord_2616271, baseEnd_2616271] using wordTrace_append hprefix tailTrace_2616271
  have hstable : (prefixWord ++ tailWord_2616271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616271).length < 2 ^ (prefixWord ++ tailWord_2616271).sum := by decide
  have hdescent : baseEnd_2616271 < baseStart_2616271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616281 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 1, 3, 2]
def baseStart_2616281 : Nat := 118140960795 + 2616281 * 2 ^ 59
def prefixEnd_2616281 : Nat := 4983230072969 + 3 ^ 40 * 2616281 * 2
def baseEnd_2616281 : Nat := 1343409680225783522255449

theorem tailTrace_2616281 : CollatzResearch.WordTrace tailWord_2616281 prefixEnd_2616281 1343409680225783522255449 := by
  unfold tailWord_2616281
  simp only [CollatzResearch.WordTrace]
  refine ⟨95423607434668237066336697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63615738289778824710891131 95423607434668237066336697)
  ·
    refine ⟨71567705576001177799752523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95423607434668237066336697 71567705576001177799752523)
    ·
      refine ⟨107351558364001766699628785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71567705576001177799752523 107351558364001766699628785)
      ·
        refine ⟨80513668773001325024721589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107351558364001766699628785 80513668773001325024721589)
        ·
          refine ⟨7548156447468874221067649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80513668773001325024721589 7548156447468874221067649)
          ·
            refine ⟨5661117335601655665800737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7548156447468874221067649 5661117335601655665800737)
            ·
              refine ⟨4245838001701241749350553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5661117335601655665800737 4245838001701241749350553)
              ·
                refine ⟨3184378501275931312012915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4245838001701241749350553 3184378501275931312012915)
                ·
                  refine ⟨4776567751913896968019373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184378501275931312012915 4776567751913896968019373)
                  ·
                    refine ⟨1791212906967711363007265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4776567751913896968019373 1791212906967711363007265)
                    ·
                      refine ⟨1343409680225783522255449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791212906967711363007265 1343409680225783522255449)
                      ·
                        rfl

theorem cell23_2616281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_2616281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616281 prefixEnd_2616281 := by exact prefixLift 2616281
  have htrace : WordTrace (prefixWord ++ tailWord_2616281) baseStart_2616281 baseEnd_2616281 := by
    simpa [prefixWord, tailWord_2616281, baseEnd_2616281] using wordTrace_append hprefix tailTrace_2616281
  have hstable : (prefixWord ++ tailWord_2616281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616281).length < 2 ^ (prefixWord ++ tailWord_2616281).sum := by decide
  have hdescent : baseEnd_2616281 < baseStart_2616281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616322 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2616322 : Nat := 118140960795 + 2616322 * 2 ^ 59
def prefixEnd_2616322 : Nat := 4983230072969 + 3 ^ 40 * 2616322 * 2
def baseEnd_2616322 : Nat := 1343430732932617861842761

theorem tailTrace_2616322 : CollatzResearch.WordTrace tailWord_2616322 prefixEnd_2616322 1343430732932617861842761 := by
  unfold tailWord_2616322
  simp only [CollatzResearch.WordTrace]
  refine ⟨23856275706879925267144805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63616735218346467379052813 23856275706879925267144805)
  ·
    refine ⟨4473051695039985987589651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23856275706879925267144805 4473051695039985987589651)
    ·
      refine ⟨6709577542559978981384477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4473051695039985987589651 6709577542559978981384477)
      ·
        refine ⟨2516091578459992118019179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6709577542559978981384477 2516091578459992118019179)
        ·
          refine ⟨3774137367689988177028769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516091578459992118019179 3774137367689988177028769)
          ·
            refine ⟨2830603025767491132771577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3774137367689988177028769 2830603025767491132771577)
            ·
              refine ⟨2122952269325618349578683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830603025767491132771577 2122952269325618349578683)
              ·
                refine ⟨3184428403988427524368025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122952269325618349578683 3184428403988427524368025)
                ·
                  refine ⟨2388321302991320643276019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184428403988427524368025 2388321302991320643276019)
                  ·
                    refine ⟨3582481954486980964914029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2388321302991320643276019 3582481954486980964914029)
                    ·
                      refine ⟨1343430732932617861842761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3582481954486980964914029 1343430732932617861842761)
                      ·
                        rfl

theorem cell23_2616322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2616322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616322 prefixEnd_2616322 := by exact prefixLift 2616322
  have htrace : WordTrace (prefixWord ++ tailWord_2616322) baseStart_2616322 baseEnd_2616322 := by
    simpa [prefixWord, tailWord_2616322, baseEnd_2616322] using wordTrace_append hprefix tailTrace_2616322
  have hstable : (prefixWord ++ tailWord_2616322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616322).length < 2 ^ (prefixWord ++ tailWord_2616322).sum := by decide
  have hdescent : baseEnd_2616322 < baseStart_2616322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616327 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2616327 : Nat := 118140960795 + 2616327 * 2 ^ 59
def prefixEnd_2616327 : Nat := 4983230072969 + 3 ^ 40 * 2616327 * 2
def baseEnd_2616327 : Nat := 1343433300335890342280237

theorem tailTrace_2616327 : CollatzResearch.WordTrace tailWord_2616327 prefixEnd_2616327 1343433300335890342280237 := by
  unfold tailWord_2616327
  simp only [CollatzResearch.WordTrace]
  refine ⟨95425285192501586922511235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63616856795001057948340823 95425285192501586922511235)
  ·
    refine ⟨143137927788752380383766853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95425285192501586922511235 143137927788752380383766853)
    ·
      refine ⟨26838361460391071321956285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143137927788752380383766853 26838361460391071321956285)
      ·
        refine ⟨10064385547646651745733607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26838361460391071321956285 10064385547646651745733607)
        ·
          refine ⟨15096578321469977618600411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10064385547646651745733607 15096578321469977618600411)
          ·
            refine ⟨22644867482204966427900617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15096578321469977618600411 22644867482204966427900617)
            ·
              refine ⟨16983650611653724820925463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22644867482204966427900617 16983650611653724820925463)
              ·
                refine ⟨25475475917480587231388195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16983650611653724820925463 25475475917480587231388195)
                ·
                  refine ⟨38213213876220880847082293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25475475917480587231388195 38213213876220880847082293)
                  ·
                    refine ⟨3582488800895707579413965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38213213876220880847082293 3582488800895707579413965)
                    ·
                      refine ⟨1343433300335890342280237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3582488800895707579413965 1343433300335890342280237)
                      ·
                        rfl

theorem cell23_2616327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2616327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616327 prefixEnd_2616327 := by exact prefixLift 2616327
  have htrace : WordTrace (prefixWord ++ tailWord_2616327) baseStart_2616327 baseEnd_2616327 := by
    simpa [prefixWord, tailWord_2616327, baseEnd_2616327] using wordTrace_append hprefix tailTrace_2616327
  have hstable : (prefixWord ++ tailWord_2616327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616327).length < 2 ^ (prefixWord ++ tailWord_2616327).sum := by decide
  have hdescent : baseEnd_2616327 < baseStart_2616327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616328 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 2, 2, 2]
def baseStart_2616328 : Nat := 118140960795 + 2616328 * 2 ^ 59
def prefixEnd_2616328 : Nat := 4983230072969 + 3 ^ 40 * 2616328 * 2
def baseEnd_2616328 : Nat := 1343433813816544838367733

theorem tailTrace_2616328 : CollatzResearch.WordTrace tailWord_2616328 prefixEnd_2616328 1343433813816544838367733 := by
  unfold tailWord_2616328
  simp only [CollatzResearch.WordTrace]
  refine ⟨47712660832748982046648819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63616881110331976062198425 47712660832748982046648819)
  ·
    refine ⟨71568991249123473069973229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47712660832748982046648819 71568991249123473069973229)
    ·
      refine ⟨26838371718421302401239961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71568991249123473069973229 26838371718421302401239961)
      ·
        refine ⟨20128778788815976800929971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26838371718421302401239961 20128778788815976800929971)
        ·
          refine ⟨30193168183223965201394957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20128778788815976800929971 30193168183223965201394957)
          ·
            refine ⟨11322438068708986950523109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30193168183223965201394957 11322438068708986950523109)
            ·
              refine ⟨2122957137882935053223083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11322438068708986950523109 2122957137882935053223083)
              ·
                refine ⟨3184435706824402579834625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122957137882935053223083 3184435706824402579834625)
                ·
                  refine ⟨2388326780118301934875969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184435706824402579834625 2388326780118301934875969)
                  ·
                    refine ⟨1791245085088726451156977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2388326780118301934875969 1791245085088726451156977)
                    ·
                      refine ⟨1343433813816544838367733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791245085088726451156977 1343433813816544838367733)
                      ·
                        rfl

theorem cell23_2616328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_2616328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616328 prefixEnd_2616328 := by exact prefixLift 2616328
  have htrace : WordTrace (prefixWord ++ tailWord_2616328) baseStart_2616328 baseEnd_2616328 := by
    simpa [prefixWord, tailWord_2616328, baseEnd_2616328] using wordTrace_append hprefix tailTrace_2616328
  have hstable : (prefixWord ++ tailWord_2616328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616328).length < 2 ^ (prefixWord ++ tailWord_2616328).sum := by decide
  have hdescent : baseEnd_2616328 < baseStart_2616328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616374 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2616374 : Nat := 118140960795 + 2616374 * 2 ^ 59
def prefixEnd_2616374 : Nat := 4983230072969 + 3 ^ 40 * 2616374 * 2
def baseEnd_2616374 : Nat := 1343457433926651658392521

theorem tailTrace_2616374 : CollatzResearch.WordTrace tailWord_2616374 prefixEnd_2616374 1343457433926651658392521 := by
  unfold tailWord_2616374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964187463958207121842011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63617999615554209299648117 5964187463958207121842011)
  ·
    refine ⟨8946281195937310682763017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5964187463958207121842011 8946281195937310682763017)
    ·
      refine ⟨6709710896952983012072263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8946281195937310682763017 6709710896952983012072263)
      ·
        refine ⟨10064566345429474518108395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709710896952983012072263 10064566345429474518108395)
        ·
          refine ⟨15096849518144211777162593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10064566345429474518108395 15096849518144211777162593)
          ·
            refine ⟨11322637138608158832871945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15096849518144211777162593 11322637138608158832871945)
            ·
              refine ⟨8491977853956119124653959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11322637138608158832871945 8491977853956119124653959)
              ·
                refine ⟨12737966780934178686980939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8491977853956119124653959 12737966780934178686980939)
                ·
                  refine ⟨19106950171401268030471409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12737966780934178686980939 19106950171401268030471409)
                  ·
                    refine ⟨14330212628550951022853557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19106950171401268030471409 14330212628550951022853557)
                    ·
                      refine ⟨1343457433926651658392521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14330212628550951022853557 1343457433926651658392521)
                      ·
                        rfl

theorem cell23_2616374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2616374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616374 prefixEnd_2616374 := by exact prefixLift 2616374
  have htrace : WordTrace (prefixWord ++ tailWord_2616374) baseStart_2616374 baseEnd_2616374 := by
    simpa [prefixWord, tailWord_2616374, baseEnd_2616374] using wordTrace_append hprefix tailTrace_2616374
  have hstable : (prefixWord ++ tailWord_2616374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616374).length < 2 ^ (prefixWord ++ tailWord_2616374).sum := by decide
  have hdescent : baseEnd_2616374 < baseStart_2616374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616384 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 2, 4, 2]
def baseStart_2616384 : Nat := 118140960795 + 2616384 * 2 ^ 59
def prefixEnd_2616384 : Nat := 4983230072969 + 3 ^ 40 * 2616384 * 2
def baseEnd_2616384 : Nat := 1343462568733196619267475

theorem tailTrace_2616384 : CollatzResearch.WordTrace tailWord_2616384 prefixEnd_2616384 1343462568733196619267475 := by
  unfold tailWord_2616384
  simp only [CollatzResearch.WordTrace]
  refine ⟨47713682076647542828668103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63618242768863390438224137 47713682076647542828668103)
  ·
    refine ⟨71570523114971314243002155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47713682076647542828668103 71570523114971314243002155)
    ·
      refine ⟨107355784672456971364503233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71570523114971314243002155 107355784672456971364503233)
      ·
        refine ⟨80516838504342728523377425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107355784672456971364503233 80516838504342728523377425)
        ·
          refine ⟨60387628878257046392533069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80516838504342728523377425 60387628878257046392533069)
          ·
            refine ⟨22645360829346392397199901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60387628878257046392533069 22645360829346392397199901)
            ·
              refine ⟨8492010311004897148949963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22645360829346392397199901 8492010311004897148949963)
              ·
                refine ⟨12738015466507345723424945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492010311004897148949963 12738015466507345723424945)
                ·
                  refine ⟨9553511599880509292568709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12738015466507345723424945 9553511599880509292568709)
                  ·
                    refine ⟨1791283424977595492356633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9553511599880509292568709 1791283424977595492356633)
                    ·
                      refine ⟨1343462568733196619267475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791283424977595492356633 1343462568733196619267475)
                      ·
                        rfl

theorem cell23_2616384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_2616384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616384 prefixEnd_2616384 := by exact prefixLift 2616384
  have htrace : WordTrace (prefixWord ++ tailWord_2616384) baseStart_2616384 baseEnd_2616384 := by
    simpa [prefixWord, tailWord_2616384, baseEnd_2616384] using wordTrace_append hprefix tailTrace_2616384
  have hstable : (prefixWord ++ tailWord_2616384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616384).length < 2 ^ (prefixWord ++ tailWord_2616384).sum := by decide
  have hdescent : baseEnd_2616384 < baseStart_2616384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616387 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 3]
def baseStart_2616387 : Nat := 118140960795 + 2616387 * 2 ^ 59
def prefixEnd_2616387 : Nat := 4983230072969 + 3 ^ 40 * 2616387 * 2
def baseEnd_2616387 : Nat := 1343464109175160107529961

theorem tailTrace_2616387 : CollatzResearch.WordTrace tailWord_2616387 prefixEnd_2616387 1343464109175160107529961 := by
  unfold tailWord_2616387
  simp only [CollatzResearch.WordTrace]
  refine ⟨95427473572284217169695415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63618315714856144779796943 95427473572284217169695415)
  ·
    refine ⟨143141210358426325754543123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95427473572284217169695415 143141210358426325754543123)
    ·
      refine ⟨214711815537639488631814685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143141210358426325754543123 214711815537639488631814685)
      ·
        refine ⟨80516930826614808236930507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214711815537639488631814685 80516930826614808236930507)
        ·
          refine ⟨120775396239922212355395761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80516930826614808236930507 120775396239922212355395761)
          ·
            refine ⟨90581547179941659266546821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120775396239922212355395761 90581547179941659266546821)
            ·
              refine ⟨16984040096239061112477529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90581547179941659266546821 16984040096239061112477529)
              ·
                refine ⟨12738030072179295834358147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16984040096239061112477529 12738030072179295834358147)
                ·
                  refine ⟨19107045108268943751537221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12738030072179295834358147 19107045108268943751537221)
                  ·
                    refine ⟨3582570957800426953413229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19107045108268943751537221 3582570957800426953413229)
                    ·
                      refine ⟨1343464109175160107529961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3582570957800426953413229 1343464109175160107529961)
                      ·
                        rfl

theorem cell23_2616387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_2616387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616387 prefixEnd_2616387 := by exact prefixLift 2616387
  have htrace : WordTrace (prefixWord ++ tailWord_2616387) baseStart_2616387 baseEnd_2616387 := by
    simpa [prefixWord, tailWord_2616387, baseEnd_2616387] using wordTrace_append hprefix tailTrace_2616387
  have hstable : (prefixWord ++ tailWord_2616387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616387).length < 2 ^ (prefixWord ++ tailWord_2616387).sum := by decide
  have hdescent : baseEnd_2616387 < baseStart_2616387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616441 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 6]
def baseStart_2616441 : Nat := 118140960795 + 2616441 * 2 ^ 59
def prefixEnd_2616441 : Nat := 4983230072969 + 3 ^ 40 * 2616441 * 2
def baseEnd_2616441 : Nat := 149276870792278099583857

theorem tailTrace_2616441 : CollatzResearch.WordTrace tailWord_2616441 prefixEnd_2616441 149276870792278099583857 := by
  unfold tailWord_2616441
  simp only [CollatzResearch.WordTrace]
  refine ⟨95429443114088584392161177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63619628742725722928107451 95429443114088584392161177)
  ·
    refine ⟨71572082335566438294120883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95429443114088584392161177 71572082335566438294120883)
    ·
      refine ⟨107358123503349657441181325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71572082335566438294120883 107358123503349657441181325)
      ·
        refine ⟨40259296313756121540442997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107358123503349657441181325 40259296313756121540442997)
        ·
          refine ⟨3774309029414636394416531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40259296313756121540442997 3774309029414636394416531)
          ·
            refine ⟨5661463544121954591624797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774309029414636394416531 5661463544121954591624797)
            ·
              refine ⟨2123048829045732971859299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5661463544121954591624797 2123048829045732971859299)
              ·
                refine ⟨3184573243568599457788949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123048829045732971859299 3184573243568599457788949)
                ·
                  refine ⟨149276870792278099583857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3184573243568599457788949 149276870792278099583857)
                  ·
                    rfl

theorem cell23_2616441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 6].length) (baseStart_2616441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616441 prefixEnd_2616441 := by exact prefixLift 2616441
  have htrace : WordTrace (prefixWord ++ tailWord_2616441) baseStart_2616441 baseEnd_2616441 := by
    simpa [prefixWord, tailWord_2616441, baseEnd_2616441] using wordTrace_append hprefix tailTrace_2616441
  have hstable : (prefixWord ++ tailWord_2616441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616441).length < 2 ^ (prefixWord ++ tailWord_2616441).sum := by decide
  have hdescent : baseEnd_2616441 < baseStart_2616441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616444 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_2616444 : Nat := 118140960795 + 2616444 * 2 ^ 59
def prefixEnd_2616444 : Nat := 4983230072969 + 3 ^ 40 * 2616444 * 2
def baseEnd_2616444 : Nat := 1343493377572466384517199

theorem tailTrace_2616444 : CollatzResearch.WordTrace tailWord_2616444 prefixEnd_2616444 1343493377572466384517199 := by
  unfold tailWord_2616444
  simp only [CollatzResearch.WordTrace]
  refine ⟨47714776266538857952260193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63619701688718477269680257 47714776266538857952260193)
  ·
    refine ⟨35786082199904143464195145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47714776266538857952260193 35786082199904143464195145)
    ·
      refine ⟨26839561649928107598146359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35786082199904143464195145 26839561649928107598146359)
      ·
        refine ⟨40259342474892161397219539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26839561649928107598146359 40259342474892161397219539)
        ·
          refine ⟨60389013712338242095829309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40259342474892161397219539 60389013712338242095829309)
          ·
            refine ⟨22645880142126840785935991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60389013712338242095829309 22645880142126840785935991)
            ·
              refine ⟨33968820213190261178903987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22645880142126840785935991 33968820213190261178903987)
              ·
                refine ⟨50953230319785391768355981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33968820213190261178903987 50953230319785391768355981)
                ·
                  refine ⟨19107461369919521913133493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50953230319785391768355981 19107461369919521913133493)
                  ·
                    refine ⟨1791324503429955179356265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19107461369919521913133493 1791324503429955179356265)
                    ·
                      refine ⟨1343493377572466384517199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791324503429955179356265 1343493377572466384517199)
                      ·
                        rfl

theorem cell23_2616444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_2616444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616444 prefixEnd_2616444 := by exact prefixLift 2616444
  have htrace : WordTrace (prefixWord ++ tailWord_2616444) baseStart_2616444 baseEnd_2616444 := by
    simpa [prefixWord, tailWord_2616444, baseEnd_2616444] using wordTrace_append hprefix tailTrace_2616444
  have hstable : (prefixWord ++ tailWord_2616444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616444).length < 2 ^ (prefixWord ++ tailWord_2616444).sum := by decide
  have hdescent : baseEnd_2616444 < baseStart_2616444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616467 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 1, 6]
def baseStart_2616467 : Nat := 118140960795 + 2616467 * 2 ^ 59
def prefixEnd_2616467 : Nat := 4983230072969 + 3 ^ 40 * 2616467 * 2
def baseEnd_2616467 : Nat := 447835062542506598176531

theorem tailTrace_2616467 : CollatzResearch.WordTrace tailWord_2616467 prefixEnd_2616467 447835062542506598176531 := by
  unfold tailWord_2616467
  simp only [CollatzResearch.WordTrace]
  refine ⟨95430391411994390832607655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63620260941329593888405103 95430391411994390832607655)
  ·
    refine ⟨143145587117991586248911483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95430391411994390832607655 143145587117991586248911483)
    ·
      refine ⟨214718380676987379373367225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143145587117991586248911483 214718380676987379373367225)
      ·
        refine ⟨161038785507740534530025419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214718380676987379373367225 161038785507740534530025419)
        ·
          refine ⟨241558178261610801795038129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161038785507740534530025419 241558178261610801795038129)
          ·
            refine ⟨181168633696208101346278597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241558178261610801795038129 181168633696208101346278597)
            ·
              refine ⟨33969118818039019002427237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181168633696208101346278597 33969118818039019002427237)
              ·
                refine ⟨6369209778382316062955107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33969118818039019002427237 6369209778382316062955107)
                ·
                  refine ⟨9553814667573474094432661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6369209778382316062955107 9553814667573474094432661)
                  ·
                    refine ⟨447835062542506598176531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9553814667573474094432661 447835062542506598176531)
                    ·
                      rfl

theorem cell23_2616467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 6].length) (baseStart_2616467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616467 prefixEnd_2616467 := by exact prefixLift 2616467
  have htrace : WordTrace (prefixWord ++ tailWord_2616467) baseStart_2616467 baseEnd_2616467 := by
    simpa [prefixWord, tailWord_2616467, baseEnd_2616467] using wordTrace_append hprefix tailTrace_2616467
  have hstable : (prefixWord ++ tailWord_2616467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616467).length < 2 ^ (prefixWord ++ tailWord_2616467).sum := by decide
  have hdescent : baseEnd_2616467 < baseStart_2616467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616478 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_2616478 : Nat := 118140960795 + 2616478 * 2 ^ 59
def prefixEnd_2616478 : Nat := 4983230072969 + 3 ^ 40 * 2616478 * 2
def baseEnd_2616478 : Nat := 1343510835914719251492043

theorem tailTrace_2616478 : CollatzResearch.WordTrace tailWord_2616478 prefixEnd_2616478 1343510835914719251492043 := by
  unfold tailWord_2616478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11928849076869317463907261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63620528409969693140838725 11928849076869317463907261)
  ·
    refine ⟨4473318403825994048965223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11928849076869317463907261 4473318403825994048965223)
    ·
      refine ⟨6709977605738991073447835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4473318403825994048965223 6709977605738991073447835)
      ·
        refine ⟨10064966408608486610171753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709977605738991073447835 10064966408608486610171753)
        ·
          refine ⟨7548724806456364957628815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10064966408608486610171753 7548724806456364957628815)
          ·
            refine ⟨11323087209684547436443223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7548724806456364957628815 11323087209684547436443223)
            ·
              refine ⟨16984630814526821154664835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11323087209684547436443223 16984630814526821154664835)
              ·
                refine ⟨25476946221790231731997253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16984630814526821154664835 25476946221790231731997253)
                ·
                  refine ⟨4776927416585668449749485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25476946221790231731997253 4776927416585668449749485)
                  ·
                    refine ⟨1791347781219625668656057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4776927416585668449749485 1791347781219625668656057)
                    ·
                      refine ⟨1343510835914719251492043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791347781219625668656057 1343510835914719251492043)
                      ·
                        rfl

theorem cell23_2616478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_2616478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616478 prefixEnd_2616478 := by exact prefixLift 2616478
  have htrace : WordTrace (prefixWord ++ tailWord_2616478) baseStart_2616478 baseEnd_2616478 := by
    simpa [prefixWord, tailWord_2616478, baseEnd_2616478] using wordTrace_append hprefix tailTrace_2616478
  have hstable : (prefixWord ++ tailWord_2616478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616478).length < 2 ^ (prefixWord ++ tailWord_2616478).sum := by decide
  have hdescent : baseEnd_2616478 < baseStart_2616478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616485 : List Nat := [1, 3, 1, 2, 1, 5, 3, 2, 1, 1, 3]
def baseStart_2616485 : Nat := 118140960795 + 2616485 * 2 ^ 59
def prefixEnd_2616485 : Nat := 4983230072969 + 3 ^ 40 * 2616485 * 2
def baseEnd_2616485 : Nat := 1343514430279300724104511

theorem tailTrace_2616485 : CollatzResearch.WordTrace tailWord_2616485 prefixEnd_2616485 1343514430279300724104511 := by
  unfold tailWord_2616485
  simp only [CollatzResearch.WordTrace]
  refine ⟨95431047925929179906762909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63620698617286119937841939 95431047925929179906762909)
  ·
    refine ⟨35786642972223442465036091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95431047925929179906762909 35786642972223442465036091)
    ·
      refine ⟨53679964458335163697554137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35786642972223442465036091 53679964458335163697554137)
      ·
        refine ⟨40259973343751372773165603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53679964458335163697554137 40259973343751372773165603)
        ·
          refine ⟨60389960015627059159748405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40259973343751372773165603 60389960015627059159748405)
          ·
            refine ⟨5661558751465036796226413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60389960015627059159748405 5661558751465036796226413)
            ·
              refine ⟨2123084531799388798584905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5661558751465036796226413 2123084531799388798584905)
              ·
                refine ⟨1592313398849541598938679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123084531799388798584905 1592313398849541598938679)
                ·
                  refine ⟨2388470098274312398408019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592313398849541598938679 2388470098274312398408019)
                  ·
                    refine ⟨3582705147411468597612029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2388470098274312398408019 3582705147411468597612029)
                    ·
                      refine ⟨1343514430279300724104511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3582705147411468597612029 1343514430279300724104511)
                      ·
                        rfl

theorem cell23_2616485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_2616485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616485 prefixEnd_2616485 := by exact prefixLift 2616485
  have htrace : WordTrace (prefixWord ++ tailWord_2616485) baseStart_2616485 baseEnd_2616485 := by
    simpa [prefixWord, tailWord_2616485, baseEnd_2616485] using wordTrace_append hprefix tailTrace_2616485
  have hstable : (prefixWord ++ tailWord_2616485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616485).length < 2 ^ (prefixWord ++ tailWord_2616485).sum := by decide
  have hdescent : baseEnd_2616485 < baseStart_2616485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616508 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2616508 : Nat := 118140960795 + 2616508 * 2 ^ 59
def prefixEnd_2616508 : Nat := 4983230072969 + 3 ^ 40 * 2616508 * 2
def baseEnd_2616508 : Nat := 1343526240334354134116905

theorem tailTrace_2616508 : CollatzResearch.WordTrace tailWord_2616508 prefixEnd_2616508 1343526240334354134116905 := by
  unfold tailWord_2616508
  simp only [CollatzResearch.WordTrace]
  refine ⟨47715943402422927417425089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63621257869897236556566785 47715943402422927417425089)
  ·
    refine ⟨35786957551817195563068817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47715943402422927417425089 35786957551817195563068817)
    ·
      refine ⟨26840218163862896672301613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35786957551817195563068817 26840218163862896672301613)
      ·
        refine ⟨10065081811448586252113105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26840218163862896672301613 10065081811448586252113105)
        ·
          refine ⟨7548811358586439689084829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10065081811448586252113105 7548811358586439689084829)
          ·
            refine ⟨2830804259469914883406811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7548811358586439689084829 2830804259469914883406811)
            ·
              refine ⟨4246206389204872325110217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830804259469914883406811 4246206389204872325110217)
              ·
                refine ⟨3184654791903654243832663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246206389204872325110217 3184654791903654243832663)
                ·
                  refine ⟨4776982187855481365748995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184654791903654243832663 4776982187855481365748995)
                  ·
                    refine ⟨7165473281783222048623493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4776982187855481365748995 7165473281783222048623493)
                    ·
                      refine ⟨1343526240334354134116905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7165473281783222048623493 1343526240334354134116905)
                      ·
                        rfl

theorem cell23_2616508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2616508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616508 prefixEnd_2616508 := by exact prefixLift 2616508
  have htrace : WordTrace (prefixWord ++ tailWord_2616508) baseStart_2616508 baseEnd_2616508 := by
    simpa [prefixWord, tailWord_2616508, baseEnd_2616508] using wordTrace_append hprefix tailTrace_2616508
  have hstable : (prefixWord ++ tailWord_2616508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616508).length < 2 ^ (prefixWord ++ tailWord_2616508).sum := by decide
  have hdescent : baseEnd_2616508 < baseStart_2616508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616511 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 3]
def baseStart_2616511 : Nat := 118140960795 + 2616511 * 2 ^ 59
def prefixEnd_2616511 : Nat := 4983230072969 + 3 ^ 40 * 2616511 * 2
def baseEnd_2616511 : Nat := 1343527780776317622379391

theorem tailTrace_2616511 : CollatzResearch.WordTrace tailWord_2616511 prefixEnd_2616511 1343527780776317622379391 := by
  unfold tailWord_2616511
  simp only [CollatzResearch.WordTrace]
  refine ⟨95431996223834986347209387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63621330815889990898139591 95431996223834986347209387)
  ·
    refine ⟨143147994335752479520814081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95431996223834986347209387 143147994335752479520814081)
    ·
      refine ⟨107360995751814359640610561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143147994335752479520814081 107360995751814359640610561)
      ·
        refine ⟨80520746813860769730457921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107360995751814359640610561 80520746813860769730457921)
        ·
          refine ⟨60390560110395577297843441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80520746813860769730457921 60390560110395577297843441)
          ·
            refine ⟨45292920082796682973382581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60390560110395577297843441 45292920082796682973382581)
            ·
              refine ⟨4246211257762189028754617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45292920082796682973382581 4246211257762189028754617)
              ·
                refine ⟨3184658443321641771565963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246211257762189028754617 3184658443321641771565963)
                ·
                  refine ⟨4776987664982462657348945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184658443321641771565963 4776987664982462657348945)
                  ·
                    refine ⟨3582740748736846993011709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776987664982462657348945 3582740748736846993011709)
                    ·
                      refine ⟨1343527780776317622379391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3582740748736846993011709 1343527780776317622379391)
                      ·
                        rfl

theorem cell23_2616511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_2616511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616511 prefixEnd_2616511 := by exact prefixLift 2616511
  have htrace : WordTrace (prefixWord ++ tailWord_2616511) baseStart_2616511 baseEnd_2616511 := by
    simpa [prefixWord, tailWord_2616511, baseEnd_2616511] using wordTrace_append hprefix tailTrace_2616511
  have hstable : (prefixWord ++ tailWord_2616511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616511).length < 2 ^ (prefixWord ++ tailWord_2616511).sum := by decide
  have hdescent : baseEnd_2616511 < baseStart_2616511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616558 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_2616558 : Nat := 118140960795 + 2616558 * 2 ^ 59
def prefixEnd_2616558 : Nat := 4983230072969 + 3 ^ 40 * 2616558 * 2
def baseEnd_2616558 : Nat := 1343551914367078938491675

theorem tailTrace_2616558 : CollatzResearch.WordTrace tailWord_2616558 prefixEnd_2616558 1343551914367078938491675 := by
  unfold tailWord_2616558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11929213806833089171771291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63622473636443142249446885 11929213806833089171771291)
  ·
    refine ⟨17893820710249633757656937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11929213806833089171771291 17893820710249633757656937)
    ·
      refine ⟨13420365532687225318242703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17893820710249633757656937 13420365532687225318242703)
      ·
        refine ⟨20130548299030837977364055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13420365532687225318242703 20130548299030837977364055)
        ·
          refine ⟨30195822448546256966046083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20130548299030837977364055 30195822448546256966046083)
          ·
            refine ⟨45293733672819385449069125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30195822448546256966046083 45293733672819385449069125)
            ·
              refine ⟨8492575063653634771700461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45293733672819385449069125 8492575063653634771700461)
              ·
                refine ⟨3184715648870113039387673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8492575063653634771700461 3184715648870113039387673)
                ·
                  refine ⟨2388536736652584779540755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3184715648870113039387673 2388536736652584779540755)
                  ·
                    refine ⟨3582805104978877169311133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2388536736652584779540755 3582805104978877169311133)
                    ·
                      refine ⟨1343551914367078938491675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3582805104978877169311133 1343551914367078938491675)
                      ·
                        rfl

theorem cell23_2616558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_2616558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616558 prefixEnd_2616558 := by exact prefixLift 2616558
  have htrace : WordTrace (prefixWord ++ tailWord_2616558) baseStart_2616558 baseEnd_2616558 := by
    simpa [prefixWord, tailWord_2616558, baseEnd_2616558] using wordTrace_append hprefix tailTrace_2616558
  have hstable : (prefixWord ++ tailWord_2616558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616558).length < 2 ^ (prefixWord ++ tailWord_2616558).sum := by decide
  have hdescent : baseEnd_2616558 < baseStart_2616558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616581 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 1, 4, 2]
def baseStart_2616581 : Nat := 118140960795 + 2616581 * 2 ^ 59
def prefixEnd_2616581 : Nat := 4983230072969 + 3 ^ 40 * 2616581 * 2
def baseEnd_2616581 : Nat := 1343563724422132348504069

theorem tailTrace_2616581 : CollatzResearch.WordTrace tailWord_2616581 prefixEnd_2616581 1343563724422132348504069 := by
  unfold tailWord_2616581
  simp only [CollatzResearch.WordTrace]
  refine ⟨95434549333581388302257597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63623032889054258868171731 95434549333581388302257597)
  ·
    refine ⟨35787956000093020613346599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95434549333581388302257597 35787956000093020613346599)
    ·
      refine ⟨53681934000139530920019899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35787956000093020613346599 53681934000139530920019899)
      ·
        refine ⟨80522901000209296380029849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53681934000139530920019899 80522901000209296380029849)
        ·
          refine ⟨60392175750156972285022387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80522901000209296380029849 60392175750156972285022387)
          ·
            refine ⟨90588263625235458427533581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60392175750156972285022387 90588263625235458427533581)
            ·
              refine ⟨33970598859463296910325093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90588263625235458427533581 33970598859463296910325093)
              ·
                refine ⟨6369487286149368170685955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33970598859463296910325093 6369487286149368170685955)
                ·
                  refine ⟨9554230929224052256028933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6369487286149368170685955 9554230929224052256028933)
                  ·
                    refine ⟨1791418299229509798005425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9554230929224052256028933 1791418299229509798005425)
                    ·
                      refine ⟨1343563724422132348504069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791418299229509798005425 1343563724422132348504069)
                      ·
                        rfl

theorem cell23_2616581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_2616581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616581 prefixEnd_2616581 := by exact prefixLift 2616581
  have htrace : WordTrace (prefixWord ++ tailWord_2616581) baseStart_2616581 baseEnd_2616581 := by
    simpa [prefixWord, tailWord_2616581, baseEnd_2616581] using wordTrace_append hprefix tailTrace_2616581
  have hstable : (prefixWord ++ tailWord_2616581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616581).length < 2 ^ (prefixWord ++ tailWord_2616581).sum := by decide
  have hdescent : baseEnd_2616581 < baseStart_2616581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616604 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 7]
def baseStart_2616604 : Nat := 118140960795 + 2616604 * 2 ^ 59
def prefixEnd_2616604 : Nat := 4983230072969 + 3 ^ 40 * 2616604 * 2
def baseEnd_2616604 : Nat := 149286170497465084279607

theorem tailTrace_2616604 : CollatzResearch.WordTrace tailWord_2616604 prefixEnd_2616604 149286170497465084279607 := by
  unfold tailWord_2616604
  simp only [CollatzResearch.WordTrace]
  refine ⟨47717694106249031615172433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63623592141665375486896577 47717694106249031615172433)
  ·
    refine ⟨35788270579686773711379325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47717694106249031615172433 35788270579686773711379325)
    ·
      refine ⟨13420601467382540141767247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35788270579686773711379325 13420601467382540141767247)
      ·
        refine ⟨20130902201073810212650871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13420601467382540141767247 20130902201073810212650871)
        ·
          refine ⟨30196353301610715318976307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20130902201073810212650871 30196353301610715318976307)
          ·
            refine ⟨45294529952416072978464461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30196353301610715318976307 45294529952416072978464461)
            ·
              refine ⟨16985448732156027366924173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45294529952416072978464461 16985448732156027366924173)
              ·
                refine ⟨6369543274558510262596565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16985448732156027366924173 6369543274558510262596565)
                ·
                  refine ⟨149286170497465084279607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6369543274558510262596565 149286170497465084279607)
                  ·
                    rfl

theorem cell23_2616604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_2616604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616604 prefixEnd_2616604 := by exact prefixLift 2616604
  have htrace : WordTrace (prefixWord ++ tailWord_2616604) baseStart_2616604 baseEnd_2616604 := by
    simpa [prefixWord, tailWord_2616604, baseEnd_2616604] using wordTrace_append hprefix tailTrace_2616604
  have hstable : (prefixWord ++ tailWord_2616604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616604).length < 2 ^ (prefixWord ++ tailWord_2616604).sum := by decide
  have hdescent : baseEnd_2616604 < baseStart_2616604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616634 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_2616634 : Nat := 118140960795 + 2616634 * 2 ^ 59
def prefixEnd_2616634 : Nat := 4983230072969 + 3 ^ 40 * 2616634 * 2
def baseEnd_2616634 : Nat := 447863646298940213713775

theorem tailTrace_2616634 : CollatzResearch.WordTrace tailWord_2616634 prefixEnd_2616634 447863646298940213713775 := by
  unfold tailWord_2616634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23859120600597344588484239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63624321601592918902624637 23859120600597344588484239)
  ·
    refine ⟨35788680900896016882726359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23859120600597344588484239 35788680900896016882726359)
    ·
      refine ⟨53683021351344025324089539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35788680900896016882726359 53683021351344025324089539)
      ·
        refine ⟨80524532027016037986134309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53683021351344025324089539 80524532027016037986134309)
        ·
          refine ⟨15098349755065507122400183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80524532027016037986134309 15098349755065507122400183)
          ·
            refine ⟨22647524632598260683600275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15098349755065507122400183 22647524632598260683600275)
            ·
              refine ⟨33971286948897391025400413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22647524632598260683600275 33971286948897391025400413)
              ·
                refine ⟨12739232605836521634525155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33971286948897391025400413 12739232605836521634525155)
                ·
                  refine ⟨19108848908754782451787733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12739232605836521634525155 19108848908754782451787733)
                  ·
                    refine ⟨447863646298940213713775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19108848908754782451787733 447863646298940213713775)
                    ·
                      rfl

theorem cell23_2616634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_2616634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616634 prefixEnd_2616634 := by exact prefixLift 2616634
  have htrace : WordTrace (prefixWord ++ tailWord_2616634) baseStart_2616634 baseEnd_2616634 := by
    simpa [prefixWord, tailWord_2616634, baseEnd_2616634] using wordTrace_append hprefix tailTrace_2616634
  have hstable : (prefixWord ++ tailWord_2616634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616634).length < 2 ^ (prefixWord ++ tailWord_2616634).sum := by decide
  have hdescent : baseEnd_2616634 < baseStart_2616634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616661 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2616661 : Nat := 118140960795 + 2616661 * 2 ^ 59
def prefixEnd_2616661 : Nat := 4983230072969 + 3 ^ 40 * 2616661 * 2
def baseEnd_2616661 : Nat := 1343604802874492035503701

theorem tailTrace_2616661 : CollatzResearch.WordTrace tailWord_2616661 prefixEnd_2616661 1343604802874492035503701 := by
  unfold tailWord_2616661
  simp only [CollatzResearch.WordTrace]
  refine ⟨95437467173291561965169837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63624978115527707976779891 95437467173291561965169837)
  ·
    refine ⟨35789050189984335736938689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95437467173291561965169837 35789050189984335736938689)
    ·
      refine ⟨26841787642488251802704017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35789050189984335736938689 26841787642488251802704017)
      ·
        refine ⟨20131340731866188852028013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26841787642488251802704017 20131340731866188852028013)
        ·
          refine ⟨7549252774449820819510505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20131340731866188852028013 7549252774449820819510505)
          ·
            refine ⟨5661939580837365614632879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7549252774449820819510505 5661939580837365614632879)
            ·
              refine ⟨8492909371256048421949319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661939580837365614632879 8492909371256048421949319)
              ·
                refine ⟨12739364056884072632923979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492909371256048421949319 12739364056884072632923979)
                ·
                  refine ⟨19109046085326108949385969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12739364056884072632923979 19109046085326108949385969)
                  ·
                    refine ⟨14331784563994581712039477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19109046085326108949385969 14331784563994581712039477)
                    ·
                      refine ⟨1343604802874492035503701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14331784563994581712039477 1343604802874492035503701)
                      ·
                        rfl

theorem cell23_2616661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2616661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616661 prefixEnd_2616661 := by exact prefixLift 2616661
  have htrace : WordTrace (prefixWord ++ tailWord_2616661) baseStart_2616661 baseEnd_2616661 := by
    simpa [prefixWord, tailWord_2616661, baseEnd_2616661] using wordTrace_append hprefix tailTrace_2616661
  have hstable : (prefixWord ++ tailWord_2616661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616661).length < 2 ^ (prefixWord ++ tailWord_2616661).sum := by decide
  have hdescent : baseEnd_2616661 < baseStart_2616661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616671 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 1, 6, 2]
def baseStart_2616671 : Nat := 118140960795 + 2616671 * 2 ^ 59
def prefixEnd_2616671 : Nat := 4983230072969 + 3 ^ 40 * 2616671 * 2
def baseEnd_2616671 : Nat := 1343609937681036996378655

theorem tailTrace_2616671 : CollatzResearch.WordTrace tailWord_2616671 prefixEnd_2616671 1343609937681036996378655 := by
  unfold tailWord_2616671
  simp only [CollatzResearch.WordTrace]
  refine ⟨95437831903255333673033867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63625221268836889115355911 95437831903255333673033867)
  ·
    refine ⟨143156747854883000509550801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95437831903255333673033867 143156747854883000509550801)
    ·
      refine ⟨107367560891162250382163101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143156747854883000509550801 107367560891162250382163101)
      ·
        refine ⟨40262835334185843893311163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107367560891162250382163101 40262835334185843893311163)
        ·
          refine ⟨60394253001278765839966745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40262835334185843893311163 60394253001278765839966745)
          ·
            refine ⟨45295689750959074379975059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60394253001278765839966745 45295689750959074379975059)
            ·
              refine ⟨67943534626438611569962589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45295689750959074379975059 67943534626438611569962589)
              ·
                refine ⟨25478825484914479338735971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67943534626438611569962589 25478825484914479338735971)
                ·
                  refine ⟨38218238227371719008103957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25478825484914479338735971 38218238227371719008103957)
                  ·
                    refine ⟨1791479916908049328504873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38218238227371719008103957 1791479916908049328504873)
                    ·
                      refine ⟨1343609937681036996378655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791479916908049328504873 1343609937681036996378655)
                      ·
                        rfl

theorem cell23_2616671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_2616671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616671 prefixEnd_2616671 := by exact prefixLift 2616671
  have htrace : WordTrace (prefixWord ++ tailWord_2616671) baseStart_2616671 baseEnd_2616671 := by
    simpa [prefixWord, tailWord_2616671, baseEnd_2616671] using wordTrace_append hprefix tailTrace_2616671
  have hstable : (prefixWord ++ tailWord_2616671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616671).length < 2 ^ (prefixWord ++ tailWord_2616671).sum := by decide
  have hdescent : baseEnd_2616671 < baseStart_2616671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616708 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2616708 : Nat := 118140960795 + 2616708 * 2 ^ 59
def prefixEnd_2616708 : Nat := 4983230072969 + 3 ^ 40 * 2616708 * 2
def baseEnd_2616708 : Nat := 1343628936465253351615985

theorem tailTrace_2616708 : CollatzResearch.WordTrace tailWord_2616708 prefixEnd_2616708 1343628936465253351615985 := by
  unfold tailWord_2616708
  simp only [CollatzResearch.WordTrace]
  refine ⟨47719590702060644496065389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63626120936080859328087185 47719590702060644496065389)
  ·
    refine ⟨17894846513272741686024521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47719590702060644496065389 17894846513272741686024521)
    ·
      refine ⟨13421134884954556264518391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17894846513272741686024521 13421134884954556264518391)
      ·
        refine ⟨20131702327431834396777587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13421134884954556264518391 20131702327431834396777587)
        ·
          refine ⟨30197553491147751595166381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20131702327431834396777587 30197553491147751595166381)
          ·
            refine ⟨11324082559180406848187393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30197553491147751595166381 11324082559180406848187393)
            ·
              refine ⟨8493061919385305136140545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11324082559180406848187393 8493061919385305136140545)
              ·
                refine ⟨6369796439538978852105409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8493061919385305136140545 6369796439538978852105409)
                ·
                  refine ⟨4777347329654234139079057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6369796439538978852105409 4777347329654234139079057)
                  ·
                    refine ⟨3583010497240675604309293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4777347329654234139079057 3583010497240675604309293)
                    ·
                      refine ⟨1343628936465253351615985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3583010497240675604309293 1343628936465253351615985)
                      ·
                        rfl

theorem cell23_2616708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2616708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616708 prefixEnd_2616708 := by exact prefixLift 2616708
  have htrace : WordTrace (prefixWord ++ tailWord_2616708) baseStart_2616708 baseEnd_2616708 := by
    simpa [prefixWord, tailWord_2616708, baseEnd_2616708] using wordTrace_append hprefix tailTrace_2616708
  have hstable : (prefixWord ++ tailWord_2616708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616708).length < 2 ^ (prefixWord ++ tailWord_2616708).sum := by decide
  have hdescent : baseEnd_2616708 < baseStart_2616708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616711 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 6]
def baseStart_2616711 : Nat := 118140960795 + 2616711 * 2 ^ 59
def prefixEnd_2616711 : Nat := 4983230072969 + 3 ^ 40 * 2616711 * 2
def baseEnd_2616711 : Nat := 149292275211912982208719

theorem tailTrace_2616711 : CollatzResearch.WordTrace tailWord_2616711 prefixEnd_2616711 149292275211912982208719 := by
  unfold tailWord_2616711
  simp only [CollatzResearch.WordTrace]
  refine ⟨95439290823110420504489987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63626193882073613669659991 95439290823110420504489987)
  ·
    refine ⟨143158936234665630756734981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95439290823110420504489987 143158936234665630756734981)
    ·
      refine ⟨26842300543999805766887809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143158936234665630756734981 26842300543999805766887809)
      ·
        refine ⟨20131725407999854325165857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26842300543999805766887809 20131725407999854325165857)
        ·
          refine ⟨15098794055999890743874393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20131725407999854325165857 15098794055999890743874393)
          ·
            refine ⟨11324095541999918057905795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15098794055999890743874393 11324095541999918057905795)
            ·
              refine ⟨16986143312999877086858693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11324095541999918057905795 16986143312999877086858693)
              ·
                refine ⟨3184901871187476953786005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16986143312999877086858693 3184901871187476953786005)
                ·
                  refine ⟨149292275211912982208719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3184901871187476953786005 149292275211912982208719)
                  ·
                    rfl

theorem cell23_2616711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 6].length) (baseStart_2616711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616711 prefixEnd_2616711 := by exact prefixLift 2616711
  have htrace : WordTrace (prefixWord ++ tailWord_2616711) baseStart_2616711 baseEnd_2616711 := by
    simpa [prefixWord, tailWord_2616711, baseEnd_2616711] using wordTrace_append hprefix tailTrace_2616711
  have hstable : (prefixWord ++ tailWord_2616711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616711).length < 2 ^ (prefixWord ++ tailWord_2616711).sum := by decide
  have hdescent : baseEnd_2616711 < baseStart_2616711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616722 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2616722 : Nat := 118140960795 + 2616722 * 2 ^ 59
def prefixEnd_2616722 : Nat := 4983230072969 + 3 ^ 40 * 2616722 * 2
def baseEnd_2616722 : Nat := 1343636125194416296840921

theorem tailTrace_2616722 : CollatzResearch.WordTrace tailWord_2616722 prefixEnd_2616722 1343636125194416296840921 := by
  unfold tailWord_2616722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23859923006517642345785105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63626461350713712922093613 23859923006517642345785105)
  ·
    refine ⟨17894942254888231759338829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23859923006517642345785105 17894942254888231759338829)
    ·
      refine ⟨6710603345583086909752061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17894942254888231759338829 6710603345583086909752061)
      ·
        refine ⟨2516476254593657591157023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6710603345583086909752061 2516476254593657591157023)
        ·
          refine ⟨3774714381890486386735535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516476254593657591157023 3774714381890486386735535)
          ·
            refine ⟨5662071572835729580103303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774714381890486386735535 5662071572835729580103303)
            ·
              refine ⟨8493107359253594370154955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662071572835729580103303 8493107359253594370154955)
              ·
                refine ⟨12739661038880391555232433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8493107359253594370154955 12739661038880391555232433)
                ·
                  refine ⟨9554745779160293666424325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12739661038880391555232433 9554745779160293666424325)
                  ·
                    refine ⟨1791514833592555062454561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9554745779160293666424325 1791514833592555062454561)
                    ·
                      refine ⟨1343636125194416296840921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791514833592555062454561 1343636125194416296840921)
                      ·
                        rfl

theorem cell23_2616722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2616722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616722 prefixEnd_2616722 := by exact prefixLift 2616722
  have htrace : WordTrace (prefixWord ++ tailWord_2616722) baseStart_2616722 baseEnd_2616722 := by
    simpa [prefixWord, tailWord_2616722, baseEnd_2616722] using wordTrace_append hprefix tailTrace_2616722
  have hstable : (prefixWord ++ tailWord_2616722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616722).length < 2 ^ (prefixWord ++ tailWord_2616722).sum := by decide
  have hdescent : baseEnd_2616722 < baseStart_2616722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616772 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2616772 : Nat := 118140960795 + 2616772 * 2 ^ 59
def prefixEnd_2616772 : Nat := 4983230072969 + 3 ^ 40 * 2616772 * 2
def baseEnd_2616772 : Nat := 1343661799227141101215691

theorem tailTrace_2616772 : CollatzResearch.WordTrace tailWord_2616772 prefixEnd_2616772 1343661799227141101215691 := by
  unfold tailWord_2616772
  simp only [CollatzResearch.WordTrace]
  refine ⟨47720757837944713961230285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63627677117259618614973713 47720757837944713961230285)
  ·
    refine ⟨17895284189229267735461357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47720757837944713961230285 17895284189229267735461357)
    ·
      refine ⟨6710731570960975400798009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17895284189229267735461357 6710731570960975400798009)
      ·
        refine ⟨5033048678220731550598507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6710731570960975400798009 5033048678220731550598507)
        ·
          refine ⟨7549573017331097325897761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033048678220731550598507 7549573017331097325897761)
          ·
            refine ⟨5662179762998322994423321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7549573017331097325897761 5662179762998322994423321)
            ·
              refine ⟨4246634822248742245817491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5662179762998322994423321 4246634822248742245817491)
              ·
                refine ⟨6369952233373113368726237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246634822248742245817491 6369952233373113368726237)
                ·
                  refine ⟨2388732087514917513272339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6369952233373113368726237 2388732087514917513272339)
                  ·
                    refine ⟨3583098131272376269908509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2388732087514917513272339 3583098131272376269908509)
                    ·
                      refine ⟨1343661799227141101215691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3583098131272376269908509 1343661799227141101215691)
                      ·
                        rfl

theorem cell23_2616772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2616772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616772 prefixEnd_2616772 := by exact prefixLift 2616772
  have htrace : WordTrace (prefixWord ++ tailWord_2616772) baseStart_2616772 baseEnd_2616772 := by
    simpa [prefixWord, tailWord_2616772, baseEnd_2616772] using wordTrace_append hprefix tailTrace_2616772
  have hstable : (prefixWord ++ tailWord_2616772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616772).length < 2 ^ (prefixWord ++ tailWord_2616772).sum := by decide
  have hdescent : baseEnd_2616772 < baseStart_2616772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616801 : List Nat := [1, 2, 3, 1, 2, 4, 1, 9]
def baseStart_2616801 : Nat := 118140960795 + 2616801 * 2 ^ 59
def prefixEnd_2616801 : Nat := 4983230072969 + 3 ^ 40 * 2616801 * 2
def baseEnd_2616801 : Nat := 49765803339485981027891

theorem tailTrace_2616801 : CollatzResearch.WordTrace tailWord_2616801 prefixEnd_2616801 49765803339485981027891 := by
  unfold tailWord_2616801
  simp only [CollatzResearch.WordTrace]
  refine ⟨95442573392784365875266257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63628382261856243916844171 95442573392784365875266257)
  ·
    refine ⟨71581930044588274406449693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95442573392784365875266257 71581930044588274406449693)
    ·
      refine ⟨26843223766720602902418635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71581930044588274406449693 26843223766720602902418635)
      ·
        refine ⟨40264835650080904353627953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26843223766720602902418635 40264835650080904353627953)
        ·
          refine ⟨30198626737560678265220965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40264835650080904353627953 30198626737560678265220965)
          ·
            refine ⟨5662242513292627174728931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30198626737560678265220965 5662242513292627174728931)
            ·
              refine ⟨8493363769938940762093397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662242513292627174728931 8493363769938940762093397)
              ·
                refine ⟨49765803339485981027891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8493363769938940762093397 49765803339485981027891)
                ·
                  rfl

theorem cell23_2616801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 9].length) (baseStart_2616801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616801 prefixEnd_2616801 := by exact prefixLift 2616801
  have htrace : WordTrace (prefixWord ++ tailWord_2616801) baseStart_2616801 baseEnd_2616801 := by
    simpa [prefixWord, tailWord_2616801, baseEnd_2616801] using wordTrace_append hprefix tailTrace_2616801
  have hstable : (prefixWord ++ tailWord_2616801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616801).length < 2 ^ (prefixWord ++ tailWord_2616801).sum := by decide
  have hdescent : baseEnd_2616801 < baseStart_2616801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616812 : List Nat := [2, 2, 1, 1, 2, 1, 2, 7, 1, 2, 2]
def baseStart_2616812 : Nat := 118140960795 + 2616812 * 2 ^ 59
def prefixEnd_2616812 : Nat := 4983230072969 + 3 ^ 40 * 2616812 * 2
def baseEnd_2616812 : Nat := 1343682338453320944715507

theorem tailTrace_2616812 : CollatzResearch.WordTrace tailWord_2616812 prefixEnd_2616812 1343682338453320944715507 := by
  unfold tailWord_2616812
  simp only [CollatzResearch.WordTrace]
  refine ⟨47721487297872257376958345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63628649730496343169277793 47721487297872257376958345)
  ·
    refine ⟨35791115473404193032718759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47721487297872257376958345 35791115473404193032718759)
    ·
      refine ⟨53686673210106289549078139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35791115473404193032718759 53686673210106289549078139)
      ·
        refine ⟨80530009815159434323617209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53686673210106289549078139 80530009815159434323617209)
        ·
          refine ⟨60397507361369575742712907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80530009815159434323617209 60397507361369575742712907)
          ·
            refine ⟨90596261042054363614069361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60397507361369575742712907 90596261042054363614069361)
            ·
              refine ⟨67947195781540772710552021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90596261042054363614069361 67947195781540772710552021)
              ·
                refine ⟨1592512401129861860403563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67947195781540772710552021 1592512401129861860403563)
                ·
                  refine ⟨2388768601694792790605345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592512401129861860403563 2388768601694792790605345)
                  ·
                    refine ⟨1791576451271094592954009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2388768601694792790605345 1791576451271094592954009)
                    ·
                      refine ⟨1343682338453320944715507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791576451271094592954009 1343682338453320944715507)
                      ·
                        rfl

theorem cell23_2616812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_2616812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616812 prefixEnd_2616812 := by exact prefixLift 2616812
  have htrace : WordTrace (prefixWord ++ tailWord_2616812) baseStart_2616812 baseEnd_2616812 := by
    simpa [prefixWord, tailWord_2616812, baseEnd_2616812] using wordTrace_append hprefix tailTrace_2616812
  have hstable : (prefixWord ++ tailWord_2616812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616812).length < 2 ^ (prefixWord ++ tailWord_2616812).sum := by decide
  have hdescent : baseEnd_2616812 < baseStart_2616812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616818 : List Nat := [3, 2, 1, 4, 1, 3, 9]
def baseStart_2616818 : Nat := 118140960795 + 2616818 * 2 ^ 59
def prefixEnd_2616818 : Nat := 4983230072969 + 3 ^ 40 * 2616818 * 2
def baseEnd_2616818 : Nat := 16588708880706764459759

theorem tailTrace_2616818 : CollatzResearch.WordTrace tailWord_2616818 prefixEnd_2616818 16588708880706764459759 := by
  unfold tailWord_2616818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23860798358430694444658777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63628795622481851852423405 23860798358430694444658777)
  ·
    refine ⟨17895598768823020833494083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23860798358430694444658777 17895598768823020833494083)
    ·
      refine ⟨26843398153234531250241125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17895598768823020833494083 26843398153234531250241125)
      ·
        refine ⟨5033137153731474609420211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26843398153234531250241125 5033137153731474609420211)
        ·
          refine ⟨7549705730597211914130317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033137153731474609420211 7549705730597211914130317)
          ·
            refine ⟨2831139648973954467798869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7549705730597211914130317 2831139648973954467798869)
            ·
              refine ⟨16588708880706764459759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2831139648973954467798869 16588708880706764459759)
              ·
                rfl

theorem cell23_2616818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 9].length) (baseStart_2616818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616818 prefixEnd_2616818 := by exact prefixLift 2616818
  have htrace : WordTrace (prefixWord ++ tailWord_2616818) baseStart_2616818 baseEnd_2616818 := by
    simpa [prefixWord, tailWord_2616818, baseEnd_2616818] using wordTrace_append hprefix tailTrace_2616818
  have hstable : (prefixWord ++ tailWord_2616818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616818).length < 2 ^ (prefixWord ++ tailWord_2616818).sum := by decide
  have hdescent : baseEnd_2616818 < baseStart_2616818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616881 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2616881 : Nat := 118140960795 + 2616881 * 2 ^ 59
def prefixEnd_2616881 : Nat := 4983230072969 + 3 ^ 40 * 2616881 * 2
def baseEnd_2616881 : Nat := 1343717768618481174752689

theorem tailTrace_2616881 : CollatzResearch.WordTrace tailWord_2616881 prefixEnd_2616881 1343717768618481174752689 := by
  unfold tailWord_2616881
  simp only [CollatzResearch.WordTrace]
  refine ⟨95445491232494539538178497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63630327488329693025452331 95445491232494539538178497)
  ·
    refine ⟨71584118424370904653633873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95445491232494539538178497 71584118424370904653633873)
    ·
      refine ⟨53688088818278178490225405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71584118424370904653633873 53688088818278178490225405)
      ·
        refine ⟨20133033306854316933834527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53688088818278178490225405 20133033306854316933834527)
        ·
          refine ⟨30199549960281475400751791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20133033306854316933834527 30199549960281475400751791)
          ·
            refine ⟨45299324940422213101127687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30199549960281475400751791 45299324940422213101127687)
            ·
              refine ⟨67948987410633319651691531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45299324940422213101127687 67948987410633319651691531)
              ·
                refine ⟨101923481115949979477537297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67948987410633319651691531 101923481115949979477537297)
                ·
                  refine ⟨76442610836962484608152973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101923481115949979477537297 76442610836962484608152973)
                  ·
                    refine ⟨28665979063860931728057365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76442610836962484608152973 28665979063860931728057365)
                    ·
                      refine ⟨1343717768618481174752689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28665979063860931728057365 1343717768618481174752689)
                      ·
                        rfl

theorem cell23_2616881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2616881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616881 prefixEnd_2616881 := by exact prefixLift 2616881
  have htrace : WordTrace (prefixWord ++ tailWord_2616881) baseStart_2616881 baseEnd_2616881 := by
    simpa [prefixWord, tailWord_2616881, baseEnd_2616881] using wordTrace_append hprefix tailTrace_2616881
  have hstable : (prefixWord ++ tailWord_2616881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616881).length < 2 ^ (prefixWord ++ tailWord_2616881).sum := by decide
  have hdescent : baseEnd_2616881 < baseStart_2616881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616888 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 2, 4, 3]
def baseStart_2616888 : Nat := 118140960795 + 2616888 * 2 ^ 59
def prefixEnd_2616888 : Nat := 4983230072969 + 3 ^ 40 * 2616888 * 2
def baseEnd_2616888 : Nat := 1343721362983062647365157

theorem tailTrace_2616888 : CollatzResearch.WordTrace tailWord_2616888 prefixEnd_2616888 1343721362983062647365157 := by
  unfold tailWord_2616888
  simp only [CollatzResearch.WordTrace]
  refine ⟨47722873271734589866841659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63630497695646119822455545 47722873271734589866841659)
  ·
    refine ⟨71584309907601884800262489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47722873271734589866841659 71584309907601884800262489)
    ·
      refine ⟨53688232430701413600196867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71584309907601884800262489 53688232430701413600196867)
      ·
        refine ⟨80532348646052120400295301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53688232430701413600196867 80532348646052120400295301)
        ·
          refine ⟨15099815371134772575055369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80532348646052120400295301 15099815371134772575055369)
          ·
            refine ⟨11324861528351079431291527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15099815371134772575055369 11324861528351079431291527)
            ·
              refine ⟨16987292292526619146937291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11324861528351079431291527 16987292292526619146937291)
              ·
                refine ⟨25480938438789928720405937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16987292292526619146937291 25480938438789928720405937)
                ·
                  refine ⟨19110703829092446540304453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25480938438789928720405937 19110703829092446540304453)
                  ·
                    refine ⟨3583256967954833726307085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19110703829092446540304453 3583256967954833726307085)
                    ·
                      refine ⟨1343721362983062647365157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3583256967954833726307085 1343721362983062647365157)
                      ·
                        rfl

theorem cell23_2616888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_2616888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616888 prefixEnd_2616888 := by exact prefixLift 2616888
  have htrace : WordTrace (prefixWord ++ tailWord_2616888) baseStart_2616888 baseEnd_2616888 := by
    simpa [prefixWord, tailWord_2616888, baseEnd_2616888] using wordTrace_append hprefix tailTrace_2616888
  have hstable : (prefixWord ++ tailWord_2616888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616888).length < 2 ^ (prefixWord ++ tailWord_2616888).sum := by decide
  have hdescent : baseEnd_2616888 < baseStart_2616888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616908 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 7]
def baseStart_2616908 : Nat := 118140960795 + 2616908 * 2 ^ 59
def prefixEnd_2616908 : Nat := 4983230072969 + 3 ^ 40 * 2616908 * 2
def baseEnd_2616908 : Nat := 149303514732905841012785

theorem tailTrace_2616908 : CollatzResearch.WordTrace tailWord_2616908 prefixEnd_2616908 149303514732905841012785 := by
  unfold tailWord_2616908
  simp only [CollatzResearch.WordTrace]
  refine ⟨47723238001698361574705689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63630984002264482099607585 47723238001698361574705689)
  ·
    refine ⟨35792428501273771181029267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47723238001698361574705689 35792428501273771181029267)
    ·
      refine ⟨53688642751910656771543901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35792428501273771181029267 53688642751910656771543901)
      ·
        refine ⟨20133241031966496289328963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53688642751910656771543901 20133241031966496289328963)
        ·
          refine ⟨30199861547949744433993445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20133241031966496289328963 30199861547949744433993445)
          ·
            refine ⟨5662474040240577081373771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30199861547949744433993445 5662474040240577081373771)
            ·
              refine ⟨8493711060360865622060657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662474040240577081373771 8493711060360865622060657)
              ·
                refine ⟨6370283295270649216545493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8493711060360865622060657 6370283295270649216545493)
                ·
                  refine ⟨149303514732905841012785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6370283295270649216545493 149303514732905841012785)
                  ·
                    rfl

theorem cell23_2616908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_2616908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616908 prefixEnd_2616908 := by exact prefixLift 2616908
  have htrace : WordTrace (prefixWord ++ tailWord_2616908) baseStart_2616908 baseEnd_2616908 := by
    simpa [prefixWord, tailWord_2616908, baseEnd_2616908] using wordTrace_append hprefix tailTrace_2616908
  have hstable : (prefixWord ++ tailWord_2616908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616908).length < 2 ^ (prefixWord ++ tailWord_2616908).sum := by decide
  have hdescent : baseEnd_2616908 < baseStart_2616908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616936 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2616936 : Nat := 118140960795 + 2616936 * 2 ^ 59
def prefixEnd_2616936 : Nat := 4983230072969 + 3 ^ 40 * 2616936 * 2
def baseEnd_2616936 : Nat := 1343746010054478459564937

theorem tailTrace_2616936 : CollatzResearch.WordTrace tailWord_2616936 prefixEnd_2616936 1343746010054478459564937 := by
  unfold tailWord_2616936
  simp only [CollatzResearch.WordTrace]
  refine ⟨47723748623647641965715331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63631664831530189287620441 47723748623647641965715331)
  ·
    refine ⟨71585622935471462948572997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47723748623647641965715331 71585622935471462948572997)
    ·
      refine ⟨13422304300400899302857437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71585622935471462948572997 13422304300400899302857437)
      ·
        refine ⟨5033364112650337238571539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13422304300400899302857437 5033364112650337238571539)
        ·
          refine ⟨7550046168975505857857309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033364112650337238571539 7550046168975505857857309)
          ·
            refine ⟨2831267313365814696696491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7550046168975505857857309 2831267313365814696696491)
            ·
              refine ⟨4246900970048722045044737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831267313365814696696491 4246900970048722045044737)
              ·
                refine ⟨3185175727536541533783553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246900970048722045044737 3185175727536541533783553)
                ·
                  refine ⟨2388881795652406150337665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185175727536541533783553 2388881795652406150337665)
                  ·
                    refine ⟨1791661346739304612753249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2388881795652406150337665 1791661346739304612753249)
                    ·
                      refine ⟨1343746010054478459564937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791661346739304612753249 1343746010054478459564937)
                      ·
                        rfl

theorem cell23_2616936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2616936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616936 prefixEnd_2616936 := by exact prefixLift 2616936
  have htrace : WordTrace (prefixWord ++ tailWord_2616936) baseStart_2616936 baseEnd_2616936 := by
    simpa [prefixWord, tailWord_2616936, baseEnd_2616936] using wordTrace_append hprefix tailTrace_2616936
  have hstable : (prefixWord ++ tailWord_2616936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616936).length < 2 ^ (prefixWord ++ tailWord_2616936).sum := by decide
  have hdescent : baseEnd_2616936 < baseStart_2616936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2616995 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 3]
def baseStart_2616995 : Nat := 118140960795 + 2616995 * 2 ^ 59
def prefixEnd_2616995 : Nat := 4983230072969 + 3 ^ 40 * 2616995 * 2
def baseEnd_2616995 : Nat := 1343776305413093728727165

theorem tailTrace_2616995 : CollatzResearch.WordTrace tailWord_2616995 prefixEnd_2616995 1343776305413093728727165 := by
  unfold tailWord_2616995
  simp only [CollatzResearch.WordTrace]
  refine ⟨95449649154081537007828439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63633099436054358005218959 95449649154081537007828439)
  ·
    refine ⟨143174473731122305511742659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95449649154081537007828439 143174473731122305511742659)
    ·
      refine ⟨214761710596683458267613989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143174473731122305511742659 214761710596683458267613989)
      ·
        refine ⟨40267820736878148425177623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214761710596683458267613989 40267820736878148425177623)
        ·
          refine ⟨60401731105317222637766435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40267820736878148425177623 60401731105317222637766435)
          ·
            refine ⟨90602596657975833956649653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60401731105317222637766435 90602596657975833956649653)
            ·
              refine ⟨8493993436685234433435905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90602596657975833956649653 8493993436685234433435905)
              ·
                refine ⟨6370495077513925825076929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8493993436685234433435905 6370495077513925825076929)
                ·
                  refine ⟨4777871308135444368807697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6370495077513925825076929 4777871308135444368807697)
                  ·
                    refine ⟨3583403481101583276605773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4777871308135444368807697 3583403481101583276605773)
                    ·
                      refine ⟨1343776305413093728727165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3583403481101583276605773 1343776305413093728727165)
                      ·
                        rfl

theorem cell23_2616995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_2616995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2616995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2616995 prefixEnd_2616995 := by exact prefixLift 2616995
  have htrace : WordTrace (prefixWord ++ tailWord_2616995) baseStart_2616995 baseEnd_2616995 := by
    simpa [prefixWord, tailWord_2616995, baseEnd_2616995] using wordTrace_append hprefix tailTrace_2616995
  have hstable : (prefixWord ++ tailWord_2616995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2616995).length < 2 ^ (prefixWord ++ tailWord_2616995).sum := by decide
  have hdescent : baseEnd_2616995 < baseStart_2616995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2616995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617015 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 6]
def baseStart_2617015 : Nat := 118140960795 + 2617015 * 2 ^ 59
def prefixEnd_2617015 : Nat := 4983230072969 + 3 ^ 40 * 2617015 * 2
def baseEnd_2617015 : Nat := 149309619447353738941897

theorem tailTrace_2617015 : CollatzResearch.WordTrace tailWord_2617015 prefixEnd_2617015 149309619447353738941897 := by
  unfold tailWord_2617015
  simp only [CollatzResearch.WordTrace]
  refine ⟨95450378614009080423556499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63633585742672720282370999 95450378614009080423556499)
  ·
    refine ⟨143175567921013620635334749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95450378614009080423556499 143175567921013620635334749)
    ·
      refine ⟨53690837970380107738250531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143175567921013620635334749 53690837970380107738250531)
      ·
        refine ⟨80536256955570161607375797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53690837970380107738250531 80536256955570161607375797)
        ·
          refine ⟨7550274089584702650691481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80536256955570161607375797 7550274089584702650691481)
          ·
            refine ⟨5662705567188526988018611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7550274089584702650691481 5662705567188526988018611)
            ·
              refine ⟨8494058350782790482027917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662705567188526988018611 8494058350782790482027917)
              ·
                refine ⟨3185271881543546430760469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8494058350782790482027917 3185271881543546430760469)
                ·
                  refine ⟨149309619447353738941897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3185271881543546430760469 149309619447353738941897)
                  ·
                    rfl

theorem cell23_2617015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 6].length) (baseStart_2617015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617015 prefixEnd_2617015 := by exact prefixLift 2617015
  have htrace : WordTrace (prefixWord ++ tailWord_2617015) baseStart_2617015 baseEnd_2617015 := by
    simpa [prefixWord, tailWord_2617015, baseEnd_2617015] using wordTrace_append hprefix tailTrace_2617015
  have hstable : (prefixWord ++ tailWord_2617015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617015).length < 2 ^ (prefixWord ++ tailWord_2617015).sum := by decide
  have hdescent : baseEnd_2617015 < baseStart_2617015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617035 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 1, 5, 2]
def baseStart_2617035 : Nat := 118140960795 + 2617035 * 2 ^ 59
def prefixEnd_2617035 : Nat := 4983230072969 + 3 ^ 40 * 2617035 * 2
def baseEnd_2617035 : Nat := 1343796844639273572226981

theorem tailTrace_2617035 : CollatzResearch.WordTrace tailWord_2617035 prefixEnd_2617035 1343796844639273572226981 := by
  unfold tailWord_2617035
  simp only [CollatzResearch.WordTrace]
  refine ⟨95451108073936623839284559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63634072049291082559523039 95451108073936623839284559)
  ·
    refine ⟨143176662110904935758926839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95451108073936623839284559 143176662110904935758926839)
    ·
      refine ⟨214764993166357403638390259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143176662110904935758926839 214764993166357403638390259)
      ·
        refine ⟨322147489749536105457585389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214764993166357403638390259 322147489749536105457585389)
        ·
          refine ⟨120805308656076039546594521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322147489749536105457585389 120805308656076039546594521)
          ·
            refine ⟨90603981492057029659945891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120805308656076039546594521 90603981492057029659945891)
            ·
              refine ⟨135905972238085544489918837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90603981492057029659945891 135905972238085544489918837)
              ·
                refine ⟨12741184897320519795929891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135905972238085544489918837 12741184897320519795929891)
                ·
                  refine ⟨19111777345980779693894837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12741184897320519795929891 19111777345980779693894837)
                  ·
                    refine ⟨1791729126185698096302641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19111777345980779693894837 1791729126185698096302641)
                    ·
                      refine ⟨1343796844639273572226981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791729126185698096302641 1343796844639273572226981)
                      ·
                        rfl

theorem cell23_2617035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5, 2].length) (baseStart_2617035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617035 prefixEnd_2617035 := by exact prefixLift 2617035
  have htrace : WordTrace (prefixWord ++ tailWord_2617035) baseStart_2617035 baseEnd_2617035 := by
    simpa [prefixWord, tailWord_2617035, baseEnd_2617035] using wordTrace_append hprefix tailTrace_2617035
  have hstable : (prefixWord ++ tailWord_2617035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617035).length < 2 ^ (prefixWord ++ tailWord_2617035).sum := by decide
  have hdescent : baseEnd_2617035 < baseStart_2617035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617065 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 2, 6, 2]
def baseStart_2617065 : Nat := 118140960795 + 2617065 * 2 ^ 59
def prefixEnd_2617065 : Nat := 4983230072969 + 3 ^ 40 * 2617065 * 2
def baseEnd_2617065 : Nat := 1343812249058908454851843

theorem tailTrace_2617065 : CollatzResearch.WordTrace tailWord_2617065 prefixEnd_2617065 1343812249058908454851843 := by
  unfold tailWord_2617065
  simp only [CollatzResearch.WordTrace]
  refine ⟨95452202263827938962876649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63634801509218625975251099 95452202263827938962876649)
  ·
    refine ⟨71589151697870954222157487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95452202263827938962876649 71589151697870954222157487)
    ·
      refine ⟨107383727546806431333236231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71589151697870954222157487 107383727546806431333236231)
      ·
        refine ⟨161075591320209646999854347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107383727546806431333236231 161075591320209646999854347)
        ·
          refine ⟨241613386980314470499781521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161075591320209646999854347 241613386980314470499781521)
          ·
            refine ⟨181210040235235852874836141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241613386980314470499781521 181210040235235852874836141)
            ·
              refine ⟨67953765088213444828063553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181210040235235852874836141 67953765088213444828063553)
              ·
                refine ⟨50965323816160083621047665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67953765088213444828063553 50965323816160083621047665)
                ·
                  refine ⟨38223992862120062715785749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50965323816160083621047665 38223992862120062715785749)
                  ·
                    refine ⟨1791749665411877939802457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38223992862120062715785749 1791749665411877939802457)
                    ·
                      refine ⟨1343812249058908454851843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791749665411877939802457 1343812249058908454851843)
                      ·
                        rfl

theorem cell23_2617065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 6, 2].length) (baseStart_2617065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617065 prefixEnd_2617065 := by exact prefixLift 2617065
  have htrace : WordTrace (prefixWord ++ tailWord_2617065) baseStart_2617065 baseEnd_2617065 := by
    simpa [prefixWord, tailWord_2617065, baseEnd_2617065] using wordTrace_append hprefix tailTrace_2617065
  have hstable : (prefixWord ++ tailWord_2617065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617065).length < 2 ^ (prefixWord ++ tailWord_2617065).sum := by decide
  have hdescent : baseEnd_2617065 < baseStart_2617065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617076 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2617076 : Nat := 118140960795 + 2617076 * 2 ^ 59
def prefixEnd_2617076 : Nat := 4983230072969 + 3 ^ 40 * 2617076 * 2
def baseEnd_2617076 : Nat := 1343817897346107911814293

theorem tailTrace_2617076 : CollatzResearch.WordTrace tailWord_2617076 prefixEnd_2617076 1343817897346107911814293 := by
  unfold tailWord_2617076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47726301733394043920763541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63635068977858725227684721 47726301733394043920763541)
  ·
    refine ⟨2237170393752845808785791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47726301733394043920763541 2237170393752845808785791)
    ·
      refine ⟨3355755590629268713178687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237170393752845808785791 3355755590629268713178687)
      ·
        refine ⟨5033633385943903069768031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355755590629268713178687 5033633385943903069768031)
        ·
          refine ⟨7550450078915854604652047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033633385943903069768031 7550450078915854604652047)
          ·
            refine ⟨11325675118373781906978071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7550450078915854604652047 11325675118373781906978071)
            ·
              refine ⟨16988512677560672860467107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11325675118373781906978071 16988512677560672860467107)
              ·
                refine ⟨25482769016341009290700661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16988512677560672860467107 25482769016341009290700661)
                ·
                  refine ⟨2389009595281969621003187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25482769016341009290700661 2389009595281969621003187)
                  ·
                    refine ⟨3583514392922954431504781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389009595281969621003187 3583514392922954431504781)
                    ·
                      refine ⟨1343817897346107911814293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3583514392922954431504781 1343817897346107911814293)
                      ·
                        rfl

theorem cell23_2617076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2617076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617076 prefixEnd_2617076 := by exact prefixLift 2617076
  have htrace : WordTrace (prefixWord ++ tailWord_2617076) baseStart_2617076 baseEnd_2617076 := by
    simpa [prefixWord, tailWord_2617076, baseEnd_2617076] using wordTrace_append hprefix tailTrace_2617076
  have hstable : (prefixWord ++ tailWord_2617076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617076).length < 2 ^ (prefixWord ++ tailWord_2617076).sum := by decide
  have hdescent : baseEnd_2617076 < baseStart_2617076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617109 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_2617109 : Nat := 118140960795 + 2617109 * 2 ^ 59
def prefixEnd_2617109 : Nat := 4983230072969 + 3 ^ 40 * 2617109 * 2
def baseEnd_2617109 : Nat := 447944947402568760900547

theorem tailTrace_2617109 : CollatzResearch.WordTrace tailWord_2617109 prefixEnd_2617109 447944947402568760900547 := by
  unfold tailWord_2617109
  simp only [CollatzResearch.WordTrace]
  refine ⟨95453807075668534477478381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63635871383779022984985587 95453807075668534477478381)
  ·
    refine ⟨35795177653375700429054393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95453807075668534477478381 35795177653375700429054393)
    ·
      refine ⟨26846383240031775321790795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35795177653375700429054393 26846383240031775321790795)
      ·
        refine ⟨40269574860047662982686193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26846383240031775321790795 40269574860047662982686193)
        ·
          refine ⟨30202181145035747237014645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40269574860047662982686193 30202181145035747237014645)
          ·
            refine ⟨2831454482347101303470123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30202181145035747237014645 2831454482347101303470123)
            ·
              refine ⟨4247181723520651955205185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831454482347101303470123 4247181723520651955205185)
              ·
                refine ⟨3185386292640488966403889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247181723520651955205185 3185386292640488966403889)
                ·
                  refine ⟨2389039719480366724802917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185386292640488966403889 2389039719480366724802917)
                  ·
                    refine ⟨447944947402568760900547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2389039719480366724802917 447944947402568760900547)
                    ·
                      rfl

theorem cell23_2617109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_2617109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617109 prefixEnd_2617109 := by exact prefixLift 2617109
  have htrace : WordTrace (prefixWord ++ tailWord_2617109) baseStart_2617109 baseEnd_2617109 := by
    simpa [prefixWord, tailWord_2617109, baseEnd_2617109] using wordTrace_append hprefix tailTrace_2617109
  have hstable : (prefixWord ++ tailWord_2617109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617109).length < 2 ^ (prefixWord ++ tailWord_2617109).sum := by decide
  have hdescent : baseEnd_2617109 < baseStart_2617109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617116 : List Nat := [2, 2, 3, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_2617116 : Nat := 118140960795 + 2617116 * 2 ^ 59
def prefixEnd_2617116 : Nat := 4983230072969 + 3 ^ 40 * 2617116 * 2
def baseEnd_2617116 : Nat := 1343838436572287755314109

theorem tailTrace_2617116 : CollatzResearch.WordTrace tailWord_2617116 prefixEnd_2617116 1343838436572287755314109 := by
  unfold tailWord_2617116
  simp only [CollatzResearch.WordTrace]
  refine ⟨47727031193321587336491601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63636041591095449781988801 47727031193321587336491601)
  ·
    refine ⟨35795273394991190502368701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47727031193321587336491601 35795273394991190502368701)
    ·
      refine ⟨13423227523121696438388263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35795273394991190502368701 13423227523121696438388263)
      ·
        refine ⟨20134841284682544657582395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13423227523121696438388263 20134841284682544657582395)
        ·
          refine ⟨30202261927023816986373593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20134841284682544657582395 30202261927023816986373593)
          ·
            refine ⟨22651696445267862739780195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30202261927023816986373593 22651696445267862739780195)
            ·
              refine ⟨33977544667901794109670293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22651696445267862739780195 33977544667901794109670293)
              ·
                refine ⟨1592697406307896598890795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33977544667901794109670293 1592697406307896598890795)
                ·
                  refine ⟨2389046109461844898336193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592697406307896598890795 2389046109461844898336193)
                  ·
                    refine ⟨1791784582096383673752145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389046109461844898336193 1791784582096383673752145)
                    ·
                      refine ⟨1343838436572287755314109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791784582096383673752145 1343838436572287755314109)
                      ·
                        rfl

theorem cell23_2617116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_2617116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617116 prefixEnd_2617116 := by exact prefixLift 2617116
  have htrace : WordTrace (prefixWord ++ tailWord_2617116) baseStart_2617116 baseEnd_2617116 := by
    simpa [prefixWord, tailWord_2617116, baseEnd_2617116] using wordTrace_append hprefix tailTrace_2617116
  have hstable : (prefixWord ++ tailWord_2617116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617116).length < 2 ^ (prefixWord ++ tailWord_2617116).sum := by decide
  have hdescent : baseEnd_2617116 < baseStart_2617116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617132 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_2617132 : Nat := 118140960795 + 2617132 * 2 ^ 59
def prefixEnd_2617132 : Nat := 4983230072969 + 3 ^ 40 * 2617132 * 2
def baseEnd_2617132 : Nat := 1343846652262759692714035

theorem tailTrace_2617132 : CollatzResearch.WordTrace tailWord_2617132 prefixEnd_2617132 1343846652262759692714035 := by
  unfold tailWord_2617132
  simp only [CollatzResearch.WordTrace]
  refine ⟨47727322977292604702782825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63636430636390139603710433 47727322977292604702782825)
  ·
    refine ⟨35795492232969453527087119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47727322977292604702782825 35795492232969453527087119)
    ·
      refine ⟨53693238349454180290630679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35795492232969453527087119 53693238349454180290630679)
      ·
        refine ⟨80539857524181270435946019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53693238349454180290630679 80539857524181270435946019)
        ·
          refine ⟨120809786286271905653919029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80539857524181270435946019 120809786286271905653919029)
          ·
            refine ⟨11325917464337991155054909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120809786286271905653919029 11325917464337991155054909)
            ·
              refine ⟨4247219049126746683145591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11325917464337991155054909 4247219049126746683145591)
              ·
                refine ⟨6370828573690120024718387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247219049126746683145591 6370828573690120024718387)
                ·
                  refine ⟨9556242860535180037077581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6370828573690120024718387 9556242860535180037077581)
                  ·
                    refine ⟨3583591072700692513904093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9556242860535180037077581 3583591072700692513904093)
                    ·
                      refine ⟨1343846652262759692714035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3583591072700692513904093 1343846652262759692714035)
                      ·
                        rfl

theorem cell23_2617132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_2617132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617132 prefixEnd_2617132 := by exact prefixLift 2617132
  have htrace : WordTrace (prefixWord ++ tailWord_2617132) baseStart_2617132 baseEnd_2617132 := by
    simpa [prefixWord, tailWord_2617132, baseEnd_2617132] using wordTrace_append hprefix tailTrace_2617132
  have hstable : (prefixWord ++ tailWord_2617132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617132).length < 2 ^ (prefixWord ++ tailWord_2617132).sum := by decide
  have hdescent : baseEnd_2617132 < baseStart_2617132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617139 : List Nat := [1, 1, 1, 2, 8, 1, 2, 7]
def baseStart_2617139 : Nat := 118140960795 + 2617139 * 2 ^ 59
def prefixEnd_2617139 : Nat := 4983230072969 + 3 ^ 40 * 2617139 * 2
def baseEnd_2617139 : Nat := 49772231356568191308389

theorem tailTrace_2617139 : CollatzResearch.WordTrace tailWord_2617139 prefixEnd_2617139 49772231356568191308389 := by
  unfold tailWord_2617139
  simp only [CollatzResearch.WordTrace]
  refine ⟨95454901265559849601070471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63636600843706566400713647 95454901265559849601070471)
  ·
    refine ⟨143182351898339774401605707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95454901265559849601070471 143182351898339774401605707)
    ·
      refine ⟨214773527847509661602408561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143182351898339774401605707 214773527847509661602408561)
      ·
        refine ⟨161080145885632246201806421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214773527847509661602408561 161080145885632246201806421)
        ·
          refine ⟨1887657959597252885177419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 161080145885632246201806421 1887657959597252885177419)
          ·
            refine ⟨2831486939395879327766129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887657959597252885177419 2831486939395879327766129)
            ·
              refine ⟨2123615204546909495824597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831486939395879327766129 2123615204546909495824597)
              ·
                refine ⟨49772231356568191308389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2123615204546909495824597 49772231356568191308389)
                ·
                  rfl

theorem cell23_2617139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 7].length) (baseStart_2617139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617139 prefixEnd_2617139 := by exact prefixLift 2617139
  have htrace : WordTrace (prefixWord ++ tailWord_2617139) baseStart_2617139 baseEnd_2617139 := by
    simpa [prefixWord, tailWord_2617139, baseEnd_2617139] using wordTrace_append hprefix tailTrace_2617139
  have hstable : (prefixWord ++ tailWord_2617139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617139).length < 2 ^ (prefixWord ++ tailWord_2617139).sum := by decide
  have hdescent : baseEnd_2617139 < baseStart_2617139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617149 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2617149 : Nat := 118140960795 + 2617149 * 2 ^ 59
def prefixEnd_2617149 : Nat := 4983230072969 + 3 ^ 40 * 2617149 * 2
def baseEnd_2617149 : Nat := 1343855381433886126201457

theorem tailTrace_2617149 : CollatzResearch.WordTrace tailWord_2617149 prefixEnd_2617149 1343855381433886126201457 := by
  unfold tailWord_2617149
  simp only [CollatzResearch.WordTrace]
  refine ⟨95455265995523621308934501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63636843997015747539289667 95455265995523621308934501)
  ·
    refine ⟨17897862374160678995425219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95455265995523621308934501 17897862374160678995425219)
    ·
      refine ⟨26846793561241018493137829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17897862374160678995425219 26846793561241018493137829)
      ·
        refine ⟨5033773792732690967463343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26846793561241018493137829 5033773792732690967463343)
        ·
          refine ⟨7550660689099036451195015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033773792732690967463343 7550660689099036451195015)
          ·
            refine ⟨11325991033648554676792523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7550660689099036451195015 11325991033648554676792523)
            ·
              refine ⟨16988986550472832015188785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11325991033648554676792523 16988986550472832015188785)
              ·
                refine ⟨12741739912854624011391589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16988986550472832015188785 12741739912854624011391589)
                ·
                  refine ⟨2389076233660242002135923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12741739912854624011391589 2389076233660242002135923)
                  ·
                    refine ⟨3583614350490363003203885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389076233660242002135923 3583614350490363003203885)
                    ·
                      refine ⟨1343855381433886126201457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3583614350490363003203885 1343855381433886126201457)
                      ·
                        rfl

theorem cell23_2617149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2617149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617149 prefixEnd_2617149 := by exact prefixLift 2617149
  have htrace : WordTrace (prefixWord ++ tailWord_2617149) baseStart_2617149 baseEnd_2617149 := by
    simpa [prefixWord, tailWord_2617149, baseEnd_2617149] using wordTrace_append hprefix tailTrace_2617149
  have hstable : (prefixWord ++ tailWord_2617149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617149).length < 2 ^ (prefixWord ++ tailWord_2617149).sum := by decide
  have hdescent : baseEnd_2617149 < baseStart_2617149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617150 : List Nat := [4, 2, 1, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_2617150 : Nat := 118140960795 + 2617150 * 2 ^ 59
def prefixEnd_2617150 : Nat := 4983230072969 + 3 ^ 40 * 2617150 * 2
def baseEnd_2617150 : Nat := 1343855894914540622288953

theorem tailTrace_2617150 : CollatzResearch.WordTrace tailWord_2617150 prefixEnd_2617150 1343855894914540622288953 := by
  unfold tailWord_2617150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11931912808564999809965113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63636868312346665653147269 11931912808564999809965113)
  ·
    refine ⟨8948934606423749857473835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11931912808564999809965113 8948934606423749857473835)
    ·
      refine ⟨13423401909635624786210753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8948934606423749857473835 13423401909635624786210753)
      ·
        refine ⟨10067551432226718589658065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13423401909635624786210753 10067551432226718589658065)
        ·
          refine ⟨7550663574170038942243549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10067551432226718589658065 7550663574170038942243549)
          ·
            refine ⟨2831498840313764603341331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7550663574170038942243549 2831498840313764603341331)
            ·
              refine ⟨4247248260470646905011997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831498840313764603341331 4247248260470646905011997)
              ·
                refine ⟨1592718097676492589379499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4247248260470646905011997 1592718097676492589379499)
                ·
                  refine ⟨2389077146514738884069249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592718097676492589379499 2389077146514738884069249)
                  ·
                    refine ⟨1791807859886054163051937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389077146514738884069249 1791807859886054163051937)
                    ·
                      refine ⟨1343855894914540622288953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791807859886054163051937 1343855894914540622288953)
                      ·
                        rfl

theorem cell23_2617150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_2617150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617150 prefixEnd_2617150 := by exact prefixLift 2617150
  have htrace : WordTrace (prefixWord ++ tailWord_2617150) baseStart_2617150 baseEnd_2617150 := by
    simpa [prefixWord, tailWord_2617150, baseEnd_2617150] using wordTrace_append hprefix tailTrace_2617150
  have hstable : (prefixWord ++ tailWord_2617150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617150).length < 2 ^ (prefixWord ++ tailWord_2617150).sum := by decide
  have hdescent : baseEnd_2617150 < baseStart_2617150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617159 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_2617159 : Nat := 118140960795 + 2617159 * 2 ^ 59
def prefixEnd_2617159 : Nat := 4983230072969 + 3 ^ 40 * 2617159 * 2
def baseEnd_2617159 : Nat := 1343860516240431087076411

theorem tailTrace_2617159 : CollatzResearch.WordTrace tailWord_2617159 prefixEnd_2617159 1343860516240431087076411 := by
  unfold tailWord_2617159
  simp only [CollatzResearch.WordTrace]
  refine ⟨95455630725487393016798531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63637087150324928677865687 95455630725487393016798531)
  ·
    refine ⟨143183446088231089525197797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95455630725487393016798531 143183446088231089525197797)
    ·
      refine ⟨26846896141543329285974587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143183446088231089525197797 26846896141543329285974587)
      ·
        refine ⟨40270344212314993928961881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26846896141543329285974587 40270344212314993928961881)
        ·
          refine ⟨30202758159236245446721411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40270344212314993928961881 30202758159236245446721411)
          ·
            refine ⟨45304137238854368170082117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30202758159236245446721411 45304137238854368170082117)
            ·
              refine ⟨8494525732285194031890397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45304137238854368170082117 8494525732285194031890397)
              ·
                refine ⟨3185447149606947761958899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8494525732285194031890397 3185447149606947761958899)
                ·
                  refine ⟨4778170724410421642938349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185447149606947761958899 4778170724410421642938349)
                  ·
                    refine ⟨1791814021653908116101881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4778170724410421642938349 1791814021653908116101881)
                    ·
                      refine ⟨1343860516240431087076411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791814021653908116101881 1343860516240431087076411)
                      ·
                        rfl

theorem cell23_2617159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_2617159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617159 prefixEnd_2617159 := by exact prefixLift 2617159
  have htrace : WordTrace (prefixWord ++ tailWord_2617159) baseStart_2617159 baseEnd_2617159 := by
    simpa [prefixWord, tailWord_2617159, baseEnd_2617159] using wordTrace_append hprefix tailTrace_2617159
  have hstable : (prefixWord ++ tailWord_2617159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617159).length < 2 ^ (prefixWord ++ tailWord_2617159).sum := by decide
  have hdescent : baseEnd_2617159 < baseStart_2617159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617185 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2617185 : Nat := 118140960795 + 2617185 * 2 ^ 59
def prefixEnd_2617185 : Nat := 4983230072969 + 3 ^ 40 * 2617185 * 2
def baseEnd_2617185 : Nat := 1343873866737447985351291

theorem tailTrace_2617185 : CollatzResearch.WordTrace tailWord_2617185 prefixEnd_2617185 1343873866737447985351291 := by
  unfold tailWord_2617185
  simp only [CollatzResearch.WordTrace]
  refine ⟨95456579023393199457245009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63637719348928799638163339 95456579023393199457245009)
  ·
    refine ⟨71592434267544899592933757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95456579023393199457245009 71592434267544899592933757)
    ·
      refine ⟨26847162850329337347350159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71592434267544899592933757 26847162850329337347350159)
      ·
        refine ⟨40270744275494006021025239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26847162850329337347350159 40270744275494006021025239)
        ·
          refine ⟨60406116413241009031537859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40270744275494006021025239 60406116413241009031537859)
          ·
            refine ⟨90609174619861513547306789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60406116413241009031537859 90609174619861513547306789)
            ·
              refine ⟨16989220241224033790120023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90609174619861513547306789 16989220241224033790120023)
              ·
                refine ⟨25483830361836050685180035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16989220241224033790120023 25483830361836050685180035)
                ·
                  refine ⟨38225745542754076027770053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25483830361836050685180035 38225745542754076027770053)
                  ·
                    refine ⟨7167327289266389255206885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38225745542754076027770053 7167327289266389255206885)
                    ·
                      refine ⟨1343873866737447985351291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7167327289266389255206885 1343873866737447985351291)
                      ·
                        rfl

theorem cell23_2617185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2617185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617185 prefixEnd_2617185 := by exact prefixLift 2617185
  have htrace : WordTrace (prefixWord ++ tailWord_2617185) baseStart_2617185 baseEnd_2617185 := by
    simpa [prefixWord, tailWord_2617185, baseEnd_2617185] using wordTrace_append hprefix tailTrace_2617185
  have hstable : (prefixWord ++ tailWord_2617185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617185).length < 2 ^ (prefixWord ++ tailWord_2617185).sum := by decide
  have hdescent : baseEnd_2617185 < baseStart_2617185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617223 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_2617223 : Nat := 118140960795 + 2617223 * 2 ^ 59
def prefixEnd_2617223 : Nat := 4983230072969 + 3 ^ 40 * 2617223 * 2
def baseEnd_2617223 : Nat := 1343893379002318836676117

theorem tailTrace_2617223 : CollatzResearch.WordTrace tailWord_2617223 prefixEnd_2617223 1343893379002318836676117 := by
  unfold tailWord_2617223
  simp only [CollatzResearch.WordTrace]
  refine ⟨95457964997255531947128323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63638643331503687964752215 95457964997255531947128323)
  ·
    refine ⟨143186947495883297920692485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95457964997255531947128323 143186947495883297920692485)
    ·
      refine ⟨26847552655478118360129841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143186947495883297920692485 26847552655478118360129841)
      ·
        refine ⟨20135664491608588770097381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26847552655478118360129841 20135664491608588770097381)
        ·
          refine ⟨3775437092176610394393259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20135664491608588770097381 3775437092176610394393259)
          ·
            refine ⟨5663155638264915591589889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775437092176610394393259 5663155638264915591589889)
            ·
              refine ⟨4247366728698686693692417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5663155638264915591589889 4247366728698686693692417)
              ·
                refine ⟨3185525046524015020269313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247366728698686693692417 3185525046524015020269313)
                ·
                  refine ⟨2389143784893011265201985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185525046524015020269313 2389143784893011265201985)
                  ·
                    refine ⟨1791857838669758448901489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389143784893011265201985 1791857838669758448901489)
                    ·
                      refine ⟨1343893379002318836676117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791857838669758448901489 1343893379002318836676117)
                      ·
                        rfl

theorem cell23_2617223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_2617223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617223 prefixEnd_2617223 := by exact prefixLift 2617223
  have htrace : WordTrace (prefixWord ++ tailWord_2617223) baseStart_2617223 baseEnd_2617223 := by
    simpa [prefixWord, tailWord_2617223, baseEnd_2617223] using wordTrace_append hprefix tailTrace_2617223
  have hstable : (prefixWord ++ tailWord_2617223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617223).length < 2 ^ (prefixWord ++ tailWord_2617223).sum := by decide
  have hdescent : baseEnd_2617223 < baseStart_2617223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617232 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 2, 5, 2]
def baseStart_2617232 : Nat := 118140960795 + 2617232 * 2 ^ 59
def prefixEnd_2617232 : Nat := 4983230072969 + 3 ^ 40 * 2617232 * 2
def baseEnd_2617232 : Nat := 1343898000328209301463575

theorem tailTrace_2617232 : CollatzResearch.WordTrace tailWord_2617232 prefixEnd_2617232 1343898000328209301463575 := by
  unfold tailWord_2617232
  simp only [CollatzResearch.WordTrace]
  refine ⟨47729146627111463242102975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63638862169481950989470633 47729146627111463242102975)
  ·
    refine ⟨71593719940667194863154463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47729146627111463242102975 71593719940667194863154463)
    ·
      refine ⟨107390579911000792294731695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71593719940667194863154463 107390579911000792294731695)
      ·
        refine ⟨161085869866501188442097543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107390579911000792294731695 161085869866501188442097543)
        ·
          refine ⟨241628804799751782663146315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161085869866501188442097543 241628804799751782663146315)
          ·
            refine ⟨362443207199627673994719473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241628804799751782663146315 362443207199627673994719473)
            ·
              refine ⟨271832405399720755496039605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362443207199627673994719473 271832405399720755496039605)
              ·
                refine ⟨25484288006223820827753713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 271832405399720755496039605 25484288006223820827753713)
                ·
                  refine ⟨19113216004667865620815285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25484288006223820827753713 19113216004667865620815285)
                  ·
                    refine ⟨1791864000437612401951433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19113216004667865620815285 1791864000437612401951433)
                    ·
                      refine ⟨1343898000328209301463575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791864000437612401951433 1343898000328209301463575)
                      ·
                        rfl

theorem cell23_2617232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 5, 2].length) (baseStart_2617232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617232 prefixEnd_2617232 := by exact prefixLift 2617232
  have htrace : WordTrace (prefixWord ++ tailWord_2617232) baseStart_2617232 baseEnd_2617232 := by
    simpa [prefixWord, tailWord_2617232, baseEnd_2617232] using wordTrace_append hprefix tailTrace_2617232
  have hstable : (prefixWord ++ tailWord_2617232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617232).length < 2 ^ (prefixWord ++ tailWord_2617232).sum := by decide
  have hdescent : baseEnd_2617232 < baseStart_2617232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617246 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2617246 : Nat := 118140960795 + 2617246 * 2 ^ 59
def prefixEnd_2617246 : Nat := 4983230072969 + 3 ^ 40 * 2617246 * 2
def baseEnd_2617246 : Nat := 149322798784152471854279

theorem tailTrace_2617246 : CollatzResearch.WordTrace tailWord_2617246 prefixEnd_2617246 149322798784152471854279 := by
  unfold tailWord_2617246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11932350484521525859401949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63639202584114804583477061 11932350484521525859401949)
  ·
    refine ⟨4474631431695572197275731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11932350484521525859401949 4474631431695572197275731)
    ·
      refine ⟨6711947147543358295913597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4474631431695572197275731 6711947147543358295913597)
      ·
        refine ⟨2516980180328759360967599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6711947147543358295913597 2516980180328759360967599)
        ·
          refine ⟨3775470270493139041451399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516980180328759360967599 3775470270493139041451399)
          ·
            refine ⟨5663205405739708562177099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775470270493139041451399 5663205405739708562177099)
            ·
              refine ⟨8494808108609562843265649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5663205405739708562177099 8494808108609562843265649)
              ·
                refine ⟨6371106081457172132449237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8494808108609562843265649 6371106081457172132449237)
                ·
                  refine ⟨149322798784152471854279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6371106081457172132449237 149322798784152471854279)
                  ·
                    rfl

theorem cell23_2617246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2617246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617246 prefixEnd_2617246 := by exact prefixLift 2617246
  have htrace : WordTrace (prefixWord ++ tailWord_2617246) baseStart_2617246 baseEnd_2617246 := by
    simpa [prefixWord, tailWord_2617246, baseEnd_2617246] using wordTrace_append hprefix tailTrace_2617246
  have hstable : (prefixWord ++ tailWord_2617246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617246).length < 2 ^ (prefixWord ++ tailWord_2617246).sum := by decide
  have hdescent : baseEnd_2617246 < baseStart_2617246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617272 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 5, 4]
def baseStart_2617272 : Nat := 118140960795 + 2617272 * 2 ^ 59
def prefixEnd_2617272 : Nat := 4983230072969 + 3 ^ 40 * 2617272 * 2
def baseEnd_2617272 : Nat := 447972846518129714987797

theorem tailTrace_2617272 : CollatzResearch.WordTrace tailWord_2617272 prefixEnd_2617272 447972846518129714987797 := by
  unfold tailWord_2617272
  simp only [CollatzResearch.WordTrace]
  refine ⟨47729876087039006657831035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63639834782718675543774713 47729876087039006657831035)
  ·
    refine ⟨71594814130558509986746553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47729876087039006657831035 71594814130558509986746553)
    ·
      refine ⟨53696110597918882490059915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71594814130558509986746553 53696110597918882490059915)
      ·
        refine ⟨80544165896878323735089873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53696110597918882490059915 80544165896878323735089873)
        ·
          refine ⟨60408124422658742801317405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80544165896878323735089873 60408124422658742801317405)
          ·
            refine ⟨22653046658497028550494027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60408124422658742801317405 22653046658497028550494027)
            ·
              refine ⟨33979569987745542825741041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22653046658497028550494027 33979569987745542825741041)
              ·
                refine ⟨25484677490809157119305781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33979569987745542825741041 25484677490809157119305781)
                ·
                  refine ⟨2389188514763358479934917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25484677490809157119305781 2389188514763358479934917)
                  ·
                    refine ⟨447972846518129714987797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2389188514763358479934917 447972846518129714987797)
                    ·
                      rfl

theorem cell23_2617272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_2617272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617272 prefixEnd_2617272 := by exact prefixLift 2617272
  have htrace : WordTrace (prefixWord ++ tailWord_2617272) baseStart_2617272 baseEnd_2617272 := by
    simpa [prefixWord, tailWord_2617272, baseEnd_2617272] using wordTrace_append hprefix tailTrace_2617272
  have hstable : (prefixWord ++ tailWord_2617272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617272).length < 2 ^ (prefixWord ++ tailWord_2617272).sum := by decide
  have hdescent : baseEnd_2617272 < baseStart_2617272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617275 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6]
def baseStart_2617275 : Nat := 118140960795 + 2617275 * 2 ^ 59
def prefixEnd_2617275 : Nat := 4983230072969 + 3 ^ 40 * 2617275 * 2
def baseEnd_2617275 : Nat := 1343920079996352633225877

theorem tailTrace_2617275 : CollatzResearch.WordTrace tailWord_2617275 prefixEnd_2617275 1343920079996352633225877 := by
  unfold tailWord_2617275
  simp only [CollatzResearch.WordTrace]
  refine ⟨95459861593067144828021279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63639907728711429885347519 95459861593067144828021279)
  ·
    refine ⟨143189792389600717242031919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95459861593067144828021279 143189792389600717242031919)
    ·
      refine ⟨214784688584401075863047879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143189792389600717242031919 214784688584401075863047879)
      ·
        refine ⟨322177032876601613794571819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214784688584401075863047879 322177032876601613794571819)
        ·
          refine ⟨483265549314902420691857729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322177032876601613794571819 483265549314902420691857729)
          ·
            refine ⟨362449161986176815518893297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483265549314902420691857729 362449161986176815518893297)
            ·
              refine ⟨271836871489632611639169973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362449161986176815518893297 271836871489632611639169973)
              ·
                refine ⟨25484706702153057341172185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 271836871489632611639169973 25484706702153057341172185)
                ·
                  refine ⟨19113530026614793005879139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25484706702153057341172185 19113530026614793005879139)
                  ·
                    refine ⟨28670295039922189508818709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19113530026614793005879139 28670295039922189508818709)
                    ·
                      refine ⟨1343920079996352633225877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28670295039922189508818709 1343920079996352633225877)
                      ·
                        rfl

theorem cell23_2617275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_2617275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617275 prefixEnd_2617275 := by exact prefixLift 2617275
  have htrace : WordTrace (prefixWord ++ tailWord_2617275) baseStart_2617275 baseEnd_2617275 := by
    simpa [prefixWord, tailWord_2617275, baseEnd_2617275] using wordTrace_append hprefix tailTrace_2617275
  have hstable : (prefixWord ++ tailWord_2617275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617275).length < 2 ^ (prefixWord ++ tailWord_2617275).sum := by decide
  have hdescent : baseEnd_2617275 < baseStart_2617275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617339 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 4, 3, 2]
def baseStart_2617339 : Nat := 118140960795 + 2617339 * 2 ^ 59
def prefixEnd_2617339 : Nat := 4983230072969 + 3 ^ 40 * 2617339 * 2
def baseEnd_2617339 : Nat := 1343952942758240382825583

theorem tailTrace_2617339 : CollatzResearch.WordTrace tailWord_2617339 prefixEnd_2617339 1343952942758240382825583 := by
  unfold tailWord_2617339
  simp only [CollatzResearch.WordTrace]
  refine ⟨95462195864835283758351071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63641463909890189172234047 95462195864835283758351071)
  ·
    refine ⟨143193293797252925637526607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95462195864835283758351071 143193293797252925637526607)
    ·
      refine ⟨214789940695879388456289911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143193293797252925637526607 214789940695879388456289911)
      ·
        refine ⟨322184911043819082684434867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214789940695879388456289911 322184911043819082684434867)
        ·
          refine ⟨483277366565728624026652301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322184911043819082684434867 483277366565728624026652301)
          ·
            refine ⟨181229012462148234009994613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 483277366565728624026652301 181229012462148234009994613)
            ·
              refine ⟨16990219918326396938436995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181229012462148234009994613 16990219918326396938436995)
              ·
                refine ⟨25485329877489595407655493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16990219918326396938436995 25485329877489595407655493)
                ·
                  refine ⟨4778499352029299138935405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25485329877489595407655493 4778499352029299138935405)
                  ·
                    refine ⟨1791937257010987177100777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4778499352029299138935405 1791937257010987177100777)
                    ·
                      refine ⟨1343952942758240382825583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791937257010987177100777 1343952942758240382825583)
                      ·
                        rfl

theorem cell23_2617339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3, 2].length) (baseStart_2617339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617339 prefixEnd_2617339 := by exact prefixLift 2617339
  have htrace : WordTrace (prefixWord ++ tailWord_2617339) baseStart_2617339 baseEnd_2617339 := by
    simpa [prefixWord, tailWord_2617339, baseEnd_2617339] using wordTrace_append hprefix tailTrace_2617339
  have hstable : (prefixWord ++ tailWord_2617339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617339).length < 2 ^ (prefixWord ++ tailWord_2617339).sum := by decide
  have hdescent : baseEnd_2617339 < baseStart_2617339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617373 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_2617373 : Nat := 118140960795 + 2617373 * 2 ^ 59
def prefixEnd_2617373 : Nat := 4983230072969 + 3 ^ 40 * 2617373 * 2
def baseEnd_2617373 : Nat := 1343970401100493249800427

theorem tailTrace_2617373 : CollatzResearch.WordTrace tailWord_2617373 prefixEnd_2617373 1343970401100493249800427 := by
  unfold tailWord_2617373
  simp only [CollatzResearch.WordTrace]
  refine ⟨95463435946712107565088773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63642290631141405043392515 95463435946712107565088773)
  ·
    refine ⟨17899394240008520168454145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95463435946712107565088773 17899394240008520168454145)
    ·
      refine ⟨13424545680006390126340609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17899394240008520168454145 13424545680006390126340609)
      ·
        refine ⟨10068409260004792594755457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13424545680006390126340609 10068409260004792594755457)
        ·
          refine ⟨7551306945003594446066593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10068409260004792594755457 7551306945003594446066593)
          ·
            refine ⟨5663480208752695834549945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7551306945003594446066593 5663480208752695834549945)
            ·
              refine ⟨4247610156564521875912459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5663480208752695834549945 4247610156564521875912459)
              ·
                refine ⟨6371415234846782813868689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247610156564521875912459 6371415234846782813868689)
                ·
                  refine ⟨4778561426135087110401517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6371415234846782813868689 4778561426135087110401517)
                  ·
                    refine ⟨1791960534800657666400569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4778561426135087110401517 1791960534800657666400569)
                    ·
                      refine ⟨1343970401100493249800427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791960534800657666400569 1343970401100493249800427)
                      ·
                        rfl

theorem cell23_2617373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_2617373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617373 prefixEnd_2617373 := by exact prefixLift 2617373
  have htrace : WordTrace (prefixWord ++ tailWord_2617373) baseStart_2617373 baseEnd_2617373 := by
    simpa [prefixWord, tailWord_2617373, baseEnd_2617373] using wordTrace_append hprefix tailTrace_2617373
  have hstable : (prefixWord ++ tailWord_2617373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617373).length < 2 ^ (prefixWord ++ tailWord_2617373).sum := by decide
  have hdescent : baseEnd_2617373 < baseStart_2617373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617403 : List Nat := [1, 1, 1, 1, 1, 2, 1, 10, 1, 2, 2]
def baseStart_2617403 : Nat := 118140960795 + 2617403 * 2 ^ 59
def prefixEnd_2617403 : Nat := 4983230072969 + 3 ^ 40 * 2617403 * 2
def baseEnd_2617403 : Nat := 1343985805520128132425289

theorem tailTrace_2617403 : CollatzResearch.WordTrace tailWord_2617403 prefixEnd_2617403 1343985805520128132425289 := by
  unfold tailWord_2617403
  simp only [CollatzResearch.WordTrace]
  refine ⟨95464530136603422688680863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63643020091068948459120575 95464530136603422688680863)
  ·
    refine ⟨143196795204905134033021295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95464530136603422688680863 143196795204905134033021295)
    ·
      refine ⟨214795192807357701049531943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143196795204905134033021295 214795192807357701049531943)
      ·
        refine ⟨322192789211036551574297915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214795192807357701049531943 322192789211036551574297915)
        ·
          refine ⟨483289183816554827361446873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322192789211036551574297915 483289183816554827361446873)
          ·
            refine ⟨362466887862416120521085155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483289183816554827361446873 362466887862416120521085155)
            ·
              refine ⟨543700331793624180781627733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362466887862416120521085155 543700331793624180781627733)
              ·
                refine ⟨1592872065801633342133675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 543700331793624180781627733 1592872065801633342133675)
                ·
                  refine ⟨2389308098702450013200513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592872065801633342133675 2389308098702450013200513)
                  ·
                    refine ⟨1791981074026837509900385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389308098702450013200513 1791981074026837509900385)
                    ·
                      refine ⟨1343985805520128132425289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1791981074026837509900385 1343985805520128132425289)
                      ·
                        rfl

theorem cell23_2617403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 2, 2].length) (baseStart_2617403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617403 prefixEnd_2617403 := by exact prefixLift 2617403
  have htrace : WordTrace (prefixWord ++ tailWord_2617403) baseStart_2617403 baseEnd_2617403 := by
    simpa [prefixWord, tailWord_2617403, baseEnd_2617403] using wordTrace_append hprefix tailTrace_2617403
  have hstable : (prefixWord ++ tailWord_2617403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617403).length < 2 ^ (prefixWord ++ tailWord_2617403).sum := by decide
  have hdescent : baseEnd_2617403 < baseStart_2617403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617409 : List Nat := [1, 2, 5, 1, 2, 1, 3, 8]
def baseStart_2617409 : Nat := 118140960795 + 2617409 * 2 ^ 59
def prefixEnd_2617409 : Nat := 4983230072969 + 3 ^ 40 * 2617409 * 2
def baseEnd_2617409 : Nat := 49777366163113152183343

theorem tailTrace_2617409 : CollatzResearch.WordTrace tailWord_2617409 prefixEnd_2617409 49777366163113152183343 := by
  unfold tailWord_2617409
  simp only [CollatzResearch.WordTrace]
  refine ⟨95464748974581685713399281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63643165983054457142266187 95464748974581685713399281)
  ·
    refine ⟨71598561730936264285049461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95464748974581685713399281 71598561730936264285049461)
    ·
      refine ⟨6712365162275274776723387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71598561730936264285049461 6712365162275274776723387)
      ·
        refine ⟨10068547743412912165085081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712365162275274776723387 10068547743412912165085081)
        ·
          refine ⟨7551410807559684123813811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10068547743412912165085081 7551410807559684123813811)
          ·
            refine ⟨11327116211339526185720717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7551410807559684123813811 11327116211339526185720717)
            ·
              refine ⟨4247668579252322319645269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11327116211339526185720717 4247668579252322319645269)
              ·
                refine ⟨49777366163113152183343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4247668579252322319645269 49777366163113152183343)
                ·
                  rfl

theorem cell23_2617409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 8].length) (baseStart_2617409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617409 prefixEnd_2617409 := by exact prefixLift 2617409
  have htrace : WordTrace (prefixWord ++ tailWord_2617409) baseStart_2617409 baseEnd_2617409 := by
    simpa [prefixWord, tailWord_2617409, baseEnd_2617409] using wordTrace_append hprefix tailTrace_2617409
  have hstable : (prefixWord ++ tailWord_2617409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617409).length < 2 ^ (prefixWord ++ tailWord_2617409).sum := by decide
  have hdescent : baseEnd_2617409 < baseStart_2617409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617426 : List Nat := [3, 2, 2, 1, 4, 1, 3, 7]
def baseStart_2617426 : Nat := 118140960795 + 2617426 * 2 ^ 59
def prefixEnd_2617426 : Nat := 4983230072969 + 3 ^ 40 * 2617426 * 2
def baseEnd_2617426 : Nat := 49777689465747464534729

theorem tailTrace_2617426 : CollatzResearch.WordTrace tailWord_2617426 prefixEnd_2617426 49777689465747464534729 := by
  unfold tailWord_2617426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23866342253880024404192033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63643579343680065077845421 23866342253880024404192033)
  ·
    refine ⟨17899756690410018303144025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23866342253880024404192033 17899756690410018303144025)
    ·
      refine ⟨13424817517807513727358019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17899756690410018303144025 13424817517807513727358019)
      ·
        refine ⟨20137226276711270591037029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13424817517807513727358019 20137226276711270591037029)
        ·
          refine ⟨3775729926883363235819443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20137226276711270591037029 3775729926883363235819443)
          ·
            refine ⟨5663594890325044853729165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775729926883363235819443 5663594890325044853729165)
            ·
              refine ⟨2123848083871891820148437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5663594890325044853729165 2123848083871891820148437)
              ·
                refine ⟨49777689465747464534729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2123848083871891820148437 49777689465747464534729)
                ·
                  rfl

theorem cell23_2617426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 7].length) (baseStart_2617426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617426 prefixEnd_2617426 := by exact prefixLift 2617426
  have htrace : WordTrace (prefixWord ++ tailWord_2617426) baseStart_2617426 baseEnd_2617426 := by
    simpa [prefixWord, tailWord_2617426, baseEnd_2617426] using wordTrace_append hprefix tailTrace_2617426
  have hstable : (prefixWord ++ tailWord_2617426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617426).length < 2 ^ (prefixWord ++ tailWord_2617426).sum := by decide
  have hdescent : baseEnd_2617426 < baseStart_2617426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617436 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2617436 : Nat := 118140960795 + 2617436 * 2 ^ 59
def prefixEnd_2617436 : Nat := 4983230072969 + 3 ^ 40 * 2617436 * 2
def baseEnd_2617436 : Nat := 1344002750381726503312637

theorem tailTrace_2617436 : CollatzResearch.WordTrace tailWord_2617436 prefixEnd_2617436 1344002750381726503312637 := by
  unfold tailWord_2617436
  simp only [CollatzResearch.WordTrace]
  refine ⟨47732866872741934662316081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63643822496989246216421441 47732866872741934662316081)
  ·
    refine ⟨35799650154556450996737061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47732866872741934662316081 35799650154556450996737061)
    ·
      refine ⟨6712434403979334561888199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35799650154556450996737061 6712434403979334561888199)
      ·
        refine ⟨10068651605969001842832299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712434403979334561888199 10068651605969001842832299)
        ·
          refine ⟨15102977408953502764248449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10068651605969001842832299 15102977408953502764248449)
          ·
            refine ⟨11327233056715127073186337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15102977408953502764248449 11327233056715127073186337)
            ·
              refine ⟨8495424792536345304889753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11327233056715127073186337 8495424792536345304889753)
              ·
                refine ⟨6371568594402258978667315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8495424792536345304889753 6371568594402258978667315)
                ·
                  refine ⟨9557352891603388468000973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6371568594402258978667315 9557352891603388468000973)
                  ·
                    refine ⟨3584007334351270675500365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9557352891603388468000973 3584007334351270675500365)
                    ·
                      refine ⟨1344002750381726503312637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584007334351270675500365 1344002750381726503312637)
                      ·
                        rfl

theorem cell23_2617436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2617436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617436 prefixEnd_2617436 := by exact prefixLift 2617436
  have htrace : WordTrace (prefixWord ++ tailWord_2617436) baseStart_2617436 baseEnd_2617436 := by
    simpa [prefixWord, tailWord_2617436, baseEnd_2617436] using wordTrace_append hprefix tailTrace_2617436
  have hstable : (prefixWord ++ tailWord_2617436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617436).length < 2 ^ (prefixWord ++ tailWord_2617436).sum := by decide
  have hdescent : baseEnd_2617436 < baseStart_2617436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617437 : List Nat := [1, 4, 4, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2617437 : Nat := 118140960795 + 2617437 * 2 ^ 59
def prefixEnd_2617437 : Nat := 4983230072969 + 3 ^ 40 * 2617437 * 2
def baseEnd_2617437 : Nat := 1344003263862380999400133

theorem tailTrace_2617437 : CollatzResearch.WordTrace tailWord_2617437 prefixEnd_2617437 1344003263862380999400133 := by
  unfold tailWord_2617437
  simp only [CollatzResearch.WordTrace]
  refine ⟨95465770218480246495418565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63643846812320164330279043 95465770218480246495418565)
  ·
    refine ⟨17899831915965046217890981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95465770218480246495418565 17899831915965046217890981)
    ·
      refine ⟨3356218484243446165854559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17899831915965046217890981 3356218484243446165854559)
      ·
        refine ⟨5034327726365169248781839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356218484243446165854559 5034327726365169248781839)
        ·
          refine ⟨7551491589547753873172759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5034327726365169248781839 7551491589547753873172759)
          ·
            refine ⟨11327237384321630809759139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7551491589547753873172759 11327237384321630809759139)
            ·
              refine ⟨16990856076482446214638709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11327237384321630809759139 16990856076482446214638709)
              ·
                refine ⟨1592892757170229332622379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16990856076482446214638709 1592892757170229332622379)
                ·
                  refine ⟨2389339135755343998933569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592892757170229332622379 2389339135755343998933569)
                  ·
                    refine ⟨1792004351816507999200177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389339135755343998933569 1792004351816507999200177)
                    ·
                      refine ⟨1344003263862380999400133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792004351816507999200177 1344003263862380999400133)
                      ·
                        rfl

theorem cell23_2617437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2617437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617437 prefixEnd_2617437 := by exact prefixLift 2617437
  have htrace : WordTrace (prefixWord ++ tailWord_2617437) baseStart_2617437 baseEnd_2617437 := by
    simpa [prefixWord, tailWord_2617437, baseEnd_2617437] using wordTrace_append hprefix tailTrace_2617437
  have hstable : (prefixWord ++ tailWord_2617437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617437).length < 2 ^ (prefixWord ++ tailWord_2617437).sum := by decide
  have hdescent : baseEnd_2617437 < baseStart_2617437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617459 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 10, 2]
def baseStart_2617459 : Nat := 118140960795 + 2617459 * 2 ^ 59
def prefixEnd_2617459 : Nat := 4983230072969 + 3 ^ 40 * 2617459 * 2
def baseEnd_2617459 : Nat := 1344014560436779913325031

theorem tailTrace_2617459 : CollatzResearch.WordTrace tailWord_2617459 prefixEnd_2617459 1344014560436779913325031 := by
  unfold tailWord_2617459
  simp only [CollatzResearch.WordTrace]
  refine ⟨95466572624400544252719431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63644381749600362835146287 95466572624400544252719431)
  ·
    refine ⟨143199858936600816379079147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95466572624400544252719431 143199858936600816379079147)
    ·
      refine ⟨214799788404901224568618721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143199858936600816379079147 214799788404901224568618721)
      ·
        refine ⟨161099841303675918426464041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214799788404901224568618721 161099841303675918426464041)
        ·
          refine ⟨120824880977756938819848031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161099841303675918426464041 120824880977756938819848031)
          ·
            refine ⟨181237321466635408229772047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120824880977756938819848031 181237321466635408229772047)
            ·
              refine ⟨271855982199953112344658071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181237321466635408229772047 271855982199953112344658071)
              ·
                refine ⟨407783973299929668516987107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271855982199953112344658071 407783973299929668516987107)
                ·
                  refine ⟨611675959949894502775480661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407783973299929668516987107 611675959949894502775480661)
                  ·
                    refine ⟨1792019413915706551100041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 611675959949894502775480661 1792019413915706551100041)
                    ·
                      refine ⟨1344014560436779913325031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792019413915706551100041 1344014560436779913325031)
                      ·
                        rfl

theorem cell23_2617459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10, 2].length) (baseStart_2617459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617459 prefixEnd_2617459 := by exact prefixLift 2617459
  have htrace : WordTrace (prefixWord ++ tailWord_2617459) baseStart_2617459 baseEnd_2617459 := by
    simpa [prefixWord, tailWord_2617459, baseEnd_2617459] using wordTrace_append hprefix tailTrace_2617459
  have hstable : (prefixWord ++ tailWord_2617459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617459).length < 2 ^ (prefixWord ++ tailWord_2617459).sum := by decide
  have hdescent : baseEnd_2617459 < baseStart_2617459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617469 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2617469 : Nat := 118140960795 + 2617469 * 2 ^ 59
def prefixEnd_2617469 : Nat := 4983230072969 + 3 ^ 40 * 2617469 * 2
def baseEnd_2617469 : Nat := 448006565081108291399995

theorem tailTrace_2617469 : CollatzResearch.WordTrace tailWord_2617469 prefixEnd_2617469 448006565081108291399995 := by
  unfold tailWord_2617469
  simp only [CollatzResearch.WordTrace]
  refine ⟨95466937354364315960583461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63644624902909543973722307 95466937354364315960583461)
  ·
    refine ⟨17900050753943309242609399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95466937354364315960583461 17900050753943309242609399)
    ·
      refine ⟨26850076130914963863914099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17900050753943309242609399 26850076130914963863914099)
      ·
        refine ⟨40275114196372445795871149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26850076130914963863914099 40275114196372445795871149)
        ·
          refine ⟨15103167823639667173451681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40275114196372445795871149 15103167823639667173451681)
          ·
            refine ⟨11327375867729750380088761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15103167823639667173451681 11327375867729750380088761)
            ·
              refine ⟨8495531900797312785066571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11327375867729750380088761 8495531900797312785066571)
              ·
                refine ⟨12743297851195969177599857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8495531900797312785066571 12743297851195969177599857)
                ·
                  refine ⟨9557473388396976883199893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12743297851195969177599857 9557473388396976883199893)
                  ·
                    refine ⟨448006565081108291399995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9557473388396976883199893 448006565081108291399995)
                    ·
                      rfl

theorem cell23_2617469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2617469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617469 prefixEnd_2617469 := by exact prefixLift 2617469
  have htrace : WordTrace (prefixWord ++ tailWord_2617469) baseStart_2617469 baseEnd_2617469 := by
    simpa [prefixWord, tailWord_2617469, baseEnd_2617469] using wordTrace_append hprefix tailTrace_2617469
  have hstable : (prefixWord ++ tailWord_2617469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617469).length < 2 ^ (prefixWord ++ tailWord_2617469).sum := by decide
  have hdescent : baseEnd_2617469 < baseStart_2617469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617479 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_2617479 : Nat := 118140960795 + 2617479 * 2 ^ 59
def prefixEnd_2617479 : Nat := 4983230072969 + 3 ^ 40 * 2617479 * 2
def baseEnd_2617479 : Nat := 1344024830049869835074939

theorem tailTrace_2617479 : CollatzResearch.WordTrace tailWord_2617479 prefixEnd_2617479 1344024830049869835074939 := by
  unfold tailWord_2617479
  simp only [CollatzResearch.WordTrace]
  refine ⟨95467302084328087668447491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63644868056218725112298327 95467302084328087668447491)
  ·
    refine ⟨143200953126492131502671237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95467302084328087668447491 143200953126492131502671237)
    ·
      refine ⟨26850178711217274656750857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143200953126492131502671237 26850178711217274656750857)
      ·
        refine ⟨20137634033412955992563143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26850178711217274656750857 20137634033412955992563143)
        ·
          refine ⟨30206451050119433988844715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20137634033412955992563143 30206451050119433988844715)
          ·
            refine ⟨45309676575179150983267073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30206451050119433988844715 45309676575179150983267073)
            ·
              refine ⟨33982257431384363237450305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45309676575179150983267073 33982257431384363237450305)
              ·
                refine ⟨25486693073538272428087729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33982257431384363237450305 25486693073538272428087729)
                ·
                  refine ⟨19115019805153704321065797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25486693073538272428087729 19115019805153704321065797)
                  ·
                    refine ⟨3584066213466319560199837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19115019805153704321065797 3584066213466319560199837)
                    ·
                      refine ⟨1344024830049869835074939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584066213466319560199837 1344024830049869835074939)
                      ·
                        rfl

theorem cell23_2617479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_2617479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617479 prefixEnd_2617479 := by exact prefixLift 2617479
  have htrace : WordTrace (prefixWord ++ tailWord_2617479) baseStart_2617479 baseEnd_2617479 := by
    simpa [prefixWord, tailWord_2617479, baseEnd_2617479] using wordTrace_append hprefix tailTrace_2617479
  have hstable : (prefixWord ++ tailWord_2617479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617479).length < 2 ^ (prefixWord ++ tailWord_2617479).sum := by decide
  have hdescent : baseEnd_2617479 < baseStart_2617479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617480 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2617480 : Nat := 118140960795 + 2617480 * 2 ^ 59
def prefixEnd_2617480 : Nat := 4983230072969 + 3 ^ 40 * 2617480 * 2
def baseEnd_2617480 : Nat := 1344025343530524331162435

theorem tailTrace_2617480 : CollatzResearch.WordTrace tailWord_2617480 prefixEnd_2617480 1344025343530524331162435 := by
  unfold tailWord_2617480
  simp only [CollatzResearch.WordTrace]
  refine ⟨47733669278662232419616947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63644892371549643226155929 47733669278662232419616947)
  ·
    refine ⟨71600503917993348629425421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47733669278662232419616947 71600503917993348629425421)
    ·
      refine ⟨26850188969247505736034533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71600503917993348629425421 26850188969247505736034533)
      ·
        refine ⟨5034410431733907325506475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26850188969247505736034533 5034410431733907325506475)
        ·
          refine ⟨7551615647600860988259713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5034410431733907325506475 7551615647600860988259713)
          ·
            refine ⟨5663711735700645741194785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7551615647600860988259713 5663711735700645741194785)
            ·
              refine ⟨4247783801775484305896089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5663711735700645741194785 4247783801775484305896089)
              ·
                refine ⟨3185837851331613229422067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247783801775484305896089 3185837851331613229422067)
                ·
                  refine ⟨4778756776997419844133101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185837851331613229422067 4778756776997419844133101)
                  ·
                    refine ⟨1792033791374032441549913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4778756776997419844133101 1792033791374032441549913)
                    ·
                      refine ⟨1344025343530524331162435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792033791374032441549913 1344025343530524331162435)
                      ·
                        rfl

theorem cell23_2617480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2617480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617480 prefixEnd_2617480 := by exact prefixLift 2617480
  have htrace : WordTrace (prefixWord ++ tailWord_2617480) baseStart_2617480 baseEnd_2617480 := by
    simpa [prefixWord, tailWord_2617480, baseEnd_2617480] using wordTrace_append hprefix tailTrace_2617480
  have hstable : (prefixWord ++ tailWord_2617480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617480).length < 2 ^ (prefixWord ++ tailWord_2617480).sum := by decide
  have hdescent : baseEnd_2617480 < baseStart_2617480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617496 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2617496 : Nat := 118140960795 + 2617496 * 2 ^ 59
def prefixEnd_2617496 : Nat := 4983230072969 + 3 ^ 40 * 2617496 * 2
def baseEnd_2617496 : Nat := 1344033559220996268562361

theorem tailTrace_2617496 : CollatzResearch.WordTrace tailWord_2617496 prefixEnd_2617496 1344033559220996268562361 := by
  unfold tailWord_2617496
  simp only [CollatzResearch.WordTrace]
  refine ⟨47733961062633249785908171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63645281416844333047877561 47733961062633249785908171)
  ·
    refine ⟨71600941593949874678862257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47733961062633249785908171 71600941593949874678862257)
    ·
      refine ⟨53700706195462406009146693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71600941593949874678862257 53700706195462406009146693)
      ·
        refine ⟨10068882411649201126715005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53700706195462406009146693 10068882411649201126715005)
        ·
          refine ⟨3775830904368450422518127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10068882411649201126715005 3775830904368450422518127)
          ·
            refine ⟨5663746356552675633777191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775830904368450422518127 5663746356552675633777191)
            ·
              refine ⟨8495619534829013450665787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5663746356552675633777191 8495619534829013450665787)
              ·
                refine ⟨12743429302243520175998681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8495619534829013450665787 12743429302243520175998681)
                ·
                  refine ⟨9557571976682640131999011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12743429302243520175998681 9557571976682640131999011)
                  ·
                    refine ⟨14336357965023960197998517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9557571976682640131999011 14336357965023960197998517)
                    ·
                      refine ⟨1344033559220996268562361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14336357965023960197998517 1344033559220996268562361)
                      ·
                        rfl

theorem cell23_2617496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2617496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617496 prefixEnd_2617496 := by exact prefixLift 2617496
  have htrace : WordTrace (prefixWord ++ tailWord_2617496) baseStart_2617496 baseEnd_2617496 := by
    simpa [prefixWord, tailWord_2617496, baseEnd_2617496] using wordTrace_append hprefix tailTrace_2617496
  have hstable : (prefixWord ++ tailWord_2617496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617496).length < 2 ^ (prefixWord ++ tailWord_2617496).sum := by decide
  have hdescent : baseEnd_2617496 < baseStart_2617496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617527 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 2, 2, 2]
def baseStart_2617527 : Nat := 118140960795 + 2617527 * 2 ^ 59
def prefixEnd_2617527 : Nat := 4983230072969 + 3 ^ 40 * 2617527 * 2
def baseEnd_2617527 : Nat := 1344049477121285647274719

theorem tailTrace_2617527 : CollatzResearch.WordTrace tailWord_2617527 prefixEnd_2617527 1344049477121285647274719 := by
  unfold tailWord_2617527
  simp only [CollatzResearch.WordTrace]
  refine ⟨95469052788154191866194835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63646035192102794577463223 95469052788154191866194835)
  ·
    refine ⟨143203579182231287799292253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95469052788154191866194835 143203579182231287799292253)
    ·
      refine ⟨53701342193336732924734595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143203579182231287799292253 53701342193336732924734595)
      ·
        refine ⟨80552013290005099387101893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53701342193336732924734595 80552013290005099387101893)
        ·
          refine ⟨15103502491875956135081605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80552013290005099387101893 15103502491875956135081605)
          ·
            refine ⟨2831906717226741775327801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15103502491875956135081605 2831906717226741775327801)
            ·
              refine ⟨2123930037920056331495851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831906717226741775327801 2123930037920056331495851)
              ·
                refine ⟨3185895056880084497243777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123930037920056331495851 3185895056880084497243777)
                ·
                  refine ⟨2389421292660063372932833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3185895056880084497243777 2389421292660063372932833)
                  ·
                    refine ⟨1792065969495047529699625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389421292660063372932833 1792065969495047529699625)
                    ·
                      refine ⟨1344049477121285647274719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792065969495047529699625 1344049477121285647274719)
                      ·
                        rfl

theorem cell23_2617527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_2617527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617527 prefixEnd_2617527 := by exact prefixLift 2617527
  have htrace : WordTrace (prefixWord ++ tailWord_2617527) baseStart_2617527 baseEnd_2617527 := by
    simpa [prefixWord, tailWord_2617527, baseEnd_2617527] using wordTrace_append hprefix tailTrace_2617527
  have hstable : (prefixWord ++ tailWord_2617527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617527).length < 2 ^ (prefixWord ++ tailWord_2617527).sum := by decide
  have hdescent : baseEnd_2617527 < baseStart_2617527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617529 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 4, 5]
def baseStart_2617529 : Nat := 118140960795 + 2617529 * 2 ^ 59
def prefixEnd_2617529 : Nat := 4983230072969 + 3 ^ 40 * 2617529 * 2
def baseEnd_2617529 : Nat := 448016834694198213149903

theorem tailTrace_2617529 : CollatzResearch.WordTrace tailWord_2617529 prefixEnd_2617529 448016834694198213149903 := by
  unfold tailWord_2617529
  simp only [CollatzResearch.WordTrace]
  refine ⟨95469125734146946207767641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63646083822764630805178427 95469125734146946207767641)
  ·
    refine ⟨71601844300610209655825731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95469125734146946207767641 71601844300610209655825731)
    ·
      refine ⟨107402766450915314483738597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71601844300610209655825731 107402766450915314483738597)
      ·
        refine ⟨20138018709546621465700987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107402766450915314483738597 20138018709546621465700987)
        ·
          refine ⟨30207028064319932198551481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20138018709546621465700987 30207028064319932198551481)
          ·
            refine ⟨22655271048239949148913611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30207028064319932198551481 22655271048239949148913611)
            ·
              refine ⟨33982906572359923723370417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22655271048239949148913611 33982906572359923723370417)
              ·
                refine ⟨25487179929269942792527813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33982906572359923723370417 25487179929269942792527813)
                ·
                  refine ⟨4778846236738114273598965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25487179929269942792527813 4778846236738114273598965)
                  ·
                    refine ⟨448016834694198213149903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4778846236738114273598965 448016834694198213149903)
                    ·
                      rfl

theorem cell23_2617529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_2617529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617529 prefixEnd_2617529 := by exact prefixLift 2617529
  have htrace : WordTrace (prefixWord ++ tailWord_2617529) baseStart_2617529 baseEnd_2617529 := by
    simpa [prefixWord, tailWord_2617529, baseEnd_2617529] using wordTrace_append hprefix tailTrace_2617529
  have hstable : (prefixWord ++ tailWord_2617529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617529).length < 2 ^ (prefixWord ++ tailWord_2617529).sum := by decide
  have hdescent : baseEnd_2617529 < baseStart_2617529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617546 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_2617546 : Nat := 118140960795 + 2617546 * 2 ^ 59
def prefixEnd_2617546 : Nat := 4983230072969 + 3 ^ 40 * 2617546 * 2
def baseEnd_2617546 : Nat := 448019744417907024312377

theorem tailTrace_2617546 : CollatzResearch.WordTrace tailWord_2617546 prefixEnd_2617546 448019744417907024312377 := by
  unfold tailWord_2617546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23867436443771339527784123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63646497183390238740757661 23867436443771339527784123)
  ·
    refine ⟨35801154665657009291676185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23867436443771339527784123 35801154665657009291676185)
    ·
      refine ⟨26850865999242756968757139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35801154665657009291676185 26850865999242756968757139)
      ·
        refine ⟨40276298998864135453135709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26850865999242756968757139 40276298998864135453135709)
        ·
          refine ⟨15103612124574050794925891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40276298998864135453135709 15103612124574050794925891)
          ·
            refine ⟨22655418186861076192388837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15103612124574050794925891 22655418186861076192388837)
            ·
              refine ⟨4247890910036451786072907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22655418186861076192388837 4247890910036451786072907)
              ·
                refine ⟨6371836365054677679109361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247890910036451786072907 6371836365054677679109361)
                ·
                  refine ⟨4778877273791008259332021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6371836365054677679109361 4778877273791008259332021)
                  ·
                    refine ⟨448019744417907024312377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4778877273791008259332021 448019744417907024312377)
                    ·
                      rfl

theorem cell23_2617546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_2617546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617546 prefixEnd_2617546 := by exact prefixLift 2617546
  have htrace : WordTrace (prefixWord ++ tailWord_2617546) baseStart_2617546 baseEnd_2617546 := by
    simpa [prefixWord, tailWord_2617546, baseEnd_2617546] using wordTrace_append hprefix tailTrace_2617546
  have hstable : (prefixWord ++ tailWord_2617546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617546).length < 2 ^ (prefixWord ++ tailWord_2617546).sum := by decide
  have hdescent : baseEnd_2617546 < baseStart_2617546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617569 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2617569 : Nat := 118140960795 + 2617569 * 2 ^ 59
def prefixEnd_2617569 : Nat := 4983230072969 + 3 ^ 40 * 2617569 * 2
def baseEnd_2617569 : Nat := 1344071043308774482949525

theorem tailTrace_2617569 : CollatzResearch.WordTrace tailWord_2617569 prefixEnd_2617569 1344071043308774482949525 := by
  unfold tailWord_2617569
  simp only [CollatzResearch.WordTrace]
  refine ⟨95470584654002033039223761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63647056436001355359482507 95470584654002033039223761)
  ·
    refine ⟨71602938490501524779417821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95470584654002033039223761 71602938490501524779417821)
    ·
      refine ⟨26851101933938071792281683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71602938490501524779417821 26851101933938071792281683)
      ·
        refine ⟨40276652900907107688422525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26851101933938071792281683 40276652900907107688422525)
        ·
          refine ⟨15103744837840165383158447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40276652900907107688422525 15103744837840165383158447)
          ·
            refine ⟨22655617256760248074737671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15103744837840165383158447 22655617256760248074737671)
            ·
              refine ⟨33983425885140372112106507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22655617256760248074737671 33983425885140372112106507)
              ·
                refine ⟨50975138827710558168159761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33983425885140372112106507 50975138827710558168159761)
                ·
                  refine ⟨38231354120782918626119821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50975138827710558168159761 38231354120782918626119821)
                  ·
                    refine ⟨14336757795293594484794933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38231354120782918626119821 14336757795293594484794933)
                    ·
                      refine ⟨1344071043308774482949525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14336757795293594484794933 1344071043308774482949525)
                      ·
                        rfl

theorem cell23_2617569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2617569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617569 prefixEnd_2617569 := by exact prefixLift 2617569
  have htrace : WordTrace (prefixWord ++ tailWord_2617569) baseStart_2617569 baseEnd_2617569 := by
    simpa [prefixWord, tailWord_2617569, baseEnd_2617569] using wordTrace_append hprefix tailTrace_2617569
  have hstable : (prefixWord ++ tailWord_2617569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617569).length < 2 ^ (prefixWord ++ tailWord_2617569).sum := by decide
  have hdescent : baseEnd_2617569 < baseStart_2617569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617583 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 2, 4, 2]
def baseStart_2617583 : Nat := 118140960795 + 2617583 * 2 ^ 59
def prefixEnd_2617583 : Nat := 4983230072969 + 3 ^ 40 * 2617583 * 2
def baseEnd_2617583 : Nat := 1344078232037937428174461

theorem tailTrace_2617583 : CollatzResearch.WordTrace tailWord_2617583 prefixEnd_2617583 1344078232037937428174461 := by
  unfold tailWord_2617583
  simp only [CollatzResearch.WordTrace]
  refine ⟨95471095275951313430233403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63647396850634208953488935 95471095275951313430233403)
  ·
    refine ⟨143206642913926970145350105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95471095275951313430233403 143206642913926970145350105)
    ·
      refine ⟨107404982185445227609012579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143206642913926970145350105 107404982185445227609012579)
      ·
        refine ⟨161107473278167841413518869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107404982185445227609012579 161107473278167841413518869)
        ·
          refine ⟨7551912809914117566258697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161107473278167841413518869 7551912809914117566258697)
          ·
            refine ⟨5663934607435588174694023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7551912809914117566258697 5663934607435588174694023)
            ·
              refine ⟨8495901911153382262041035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5663934607435588174694023 8495901911153382262041035)
              ·
                refine ⟨12743852866730073393061553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8495901911153382262041035 12743852866730073393061553)
                ·
                  refine ⟨9557889650047555044796165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12743852866730073393061553 9557889650047555044796165)
                  ·
                    refine ⟨1792104309383916570899281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9557889650047555044796165 1792104309383916570899281)
                    ·
                      refine ⟨1344078232037937428174461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792104309383916570899281 1344078232037937428174461)
                      ·
                        rfl

theorem cell23_2617583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4, 2].length) (baseStart_2617583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617583 prefixEnd_2617583 := by exact prefixLift 2617583
  have htrace : WordTrace (prefixWord ++ tailWord_2617583) baseStart_2617583 baseEnd_2617583 := by
    simpa [prefixWord, tailWord_2617583, baseEnd_2617583] using wordTrace_append hprefix tailTrace_2617583
  have hstable : (prefixWord ++ tailWord_2617583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617583).length < 2 ^ (prefixWord ++ tailWord_2617583).sum := by decide
  have hdescent : baseEnd_2617583 < baseStart_2617583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617623 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 6]
def baseStart_2617623 : Nat := 118140960795 + 2617623 * 2 ^ 59
def prefixEnd_2617623 : Nat := 4983230072969 + 3 ^ 40 * 2617623 * 2
def baseEnd_2617623 : Nat := 149344307918235252408253

theorem tailTrace_2617623 : CollatzResearch.WordTrace tailWord_2617623 prefixEnd_2617623 149344307918235252408253 := by
  unfold tailWord_2617623
  simp only [CollatzResearch.WordTrace]
  refine ⟨95472554195806400261689523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63648369463870933507793015 95472554195806400261689523)
  ·
    refine ⟨143208831293709600392534285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95472554195806400261689523 143208831293709600392534285)
    ·
      refine ⟨53703311735141100147200357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143208831293709600392534285 53703311735141100147200357)
      ·
        refine ⟨10069370950338956277600067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53703311735141100147200357 10069370950338956277600067)
        ·
          refine ⟨15104056425508434416400101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10069370950338956277600067 15104056425508434416400101)
          ·
            refine ⟨2832010579782831453075019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15104056425508434416400101 2832010579782831453075019)
            ·
              refine ⟨4248015869674247179612529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832010579782831453075019 4248015869674247179612529)
              ·
                refine ⟨3186011902255685384709397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4248015869674247179612529 3186011902255685384709397)
                ·
                  refine ⟨149344307918235252408253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3186011902255685384709397 149344307918235252408253)
                  ·
                    rfl

theorem cell23_2617623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 6].length) (baseStart_2617623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617623 prefixEnd_2617623 := by exact prefixLift 2617623
  have htrace : WordTrace (prefixWord ++ tailWord_2617623) baseStart_2617623 baseEnd_2617623 := by
    simpa [prefixWord, tailWord_2617623, baseEnd_2617623] using wordTrace_append hprefix tailTrace_2617623
  have hstable : (prefixWord ++ tailWord_2617623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617623).length < 2 ^ (prefixWord ++ tailWord_2617623).sum := by decide
  have hdescent : baseEnd_2617623 < baseStart_2617623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617633 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2617633 : Nat := 118140960795 + 2617633 * 2 ^ 59
def prefixEnd_2617633 : Nat := 4983230072969 + 3 ^ 40 * 2617633 * 2
def baseEnd_2617633 : Nat := 1344103906070662232549231

theorem tailTrace_2617633 : CollatzResearch.WordTrace tailWord_2617633 prefixEnd_2617633 1344103906070662232549231 := by
  unfold tailWord_2617633
  simp only [CollatzResearch.WordTrace]
  refine ⟨95472918925770171969553553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63648612617180114646369035 95472918925770171969553553)
  ·
    refine ⟨71604689194327628977165165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95472918925770171969553553 71604689194327628977165165)
    ·
      refine ⟨26851758447872860866436937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71604689194327628977165165 26851758447872860866436937)
      ·
        refine ⟨20138818835904645649827703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26851758447872860866436937 20138818835904645649827703)
        ·
          refine ⟨30208228253856968474741555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20138818835904645649827703 30208228253856968474741555)
          ·
            refine ⟨45312342380785452712112333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30208228253856968474741555 45312342380785452712112333)
            ·
              refine ⟨16992128392794544767042125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45312342380785452712112333 16992128392794544767042125)
              ·
                refine ⟨6372048147297954287640797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16992128392794544767042125 6372048147297954287640797)
                ·
                  refine ⟨2389518055236732857865299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6372048147297954287640797 2389518055236732857865299)
                  ·
                    refine ⟨3584277082855099286797949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389518055236732857865299 3584277082855099286797949)
                    ·
                      refine ⟨1344103906070662232549231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584277082855099286797949 1344103906070662232549231)
                      ·
                        rfl

theorem cell23_2617633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2617633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617633 prefixEnd_2617633 := by exact prefixLift 2617633
  have htrace : WordTrace (prefixWord ++ tailWord_2617633) baseStart_2617633 baseEnd_2617633 := by
    simpa [prefixWord, tailWord_2617633, baseEnd_2617633] using wordTrace_append hprefix tailTrace_2617633
  have hstable : (prefixWord ++ tailWord_2617633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617633).length < 2 ^ (prefixWord ++ tailWord_2617633).sum := by decide
  have hdescent : baseEnd_2617633 < baseStart_2617633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617640 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 6]
def baseStart_2617640 : Nat := 118140960795 + 2617640 * 2 ^ 59
def prefixEnd_2617640 : Nat := 4983230072969 + 3 ^ 40 * 2617640 * 2
def baseEnd_2617640 : Nat := 149345277826138189462411

theorem tailTrace_2617640 : CollatzResearch.WordTrace tailWord_2617640 prefixEnd_2617640 149345277826138189462411 := by
  unfold tailWord_2617640
  simp only [CollatzResearch.WordTrace]
  refine ⟨47736587118372406082529187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63648782824496541443372249 47736587118372406082529187)
  ·
    refine ⟨71604880677558609123793781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47736587118372406082529187 71604880677558609123793781)
    ·
      refine ⟨6712957563521119605355667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71604880677558609123793781 6712957563521119605355667)
      ·
        refine ⟨10069436345281679408033501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6712957563521119605355667 10069436345281679408033501)
        ·
          refine ⟨3776038629480629778012563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10069436345281679408033501 3776038629480629778012563)
          ·
            refine ⟨5664057944220944667018845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776038629480629778012563 5664057944220944667018845)
            ·
              refine ⟨2124021729082854250132067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664057944220944667018845 2124021729082854250132067)
              ·
                refine ⟨3186032593624281375198101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124021729082854250132067 3186032593624281375198101)
                ·
                  refine ⟨149345277826138189462411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3186032593624281375198101 149345277826138189462411)
                  ·
                    rfl

theorem cell23_2617640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 6].length) (baseStart_2617640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617640 prefixEnd_2617640 := by exact prefixLift 2617640
  have htrace : WordTrace (prefixWord ++ tailWord_2617640) baseStart_2617640 baseEnd_2617640 := by
    simpa [prefixWord, tailWord_2617640, baseEnd_2617640] using wordTrace_append hprefix tailTrace_2617640
  have hstable : (prefixWord ++ tailWord_2617640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617640).length < 2 ^ (prefixWord ++ tailWord_2617640).sum := by decide
  have hdescent : baseEnd_2617640 < baseStart_2617640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617653 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2617653 : Nat := 118140960795 + 2617653 * 2 ^ 59
def prefixEnd_2617653 : Nat := 4983230072969 + 3 ^ 40 * 2617653 * 2
def baseEnd_2617653 : Nat := 448038058561250718099713

theorem tailTrace_2617653 : CollatzResearch.WordTrace tailWord_2617653 prefixEnd_2617653 448038058561250718099713 := by
  unfold tailWord_2617653
  simp only [CollatzResearch.WordTrace]
  refine ⟨95473648385697715385281613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63649098923798476923521075 95473648385697715385281613)
  ·
    refine ⟨35802618144636643269480605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95473648385697715385281613 35802618144636643269480605)
    ·
      refine ⟨13425981804238741226055227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35802618144636643269480605 13425981804238741226055227)
      ·
        refine ⟨20138972706358111839082841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13425981804238741226055227 20138972706358111839082841)
        ·
          refine ⟨15104229529768583879312131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20138972706358111839082841 15104229529768583879312131)
          ·
            refine ⟨22656344294652875818968197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15104229529768583879312131 22656344294652875818968197)
            ·
              refine ⟨4248064555247414216056537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22656344294652875818968197 4248064555247414216056537)
              ·
                refine ⟨3186048416435560662042403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4248064555247414216056537 3186048416435560662042403)
                ·
                  refine ⟨4779072624653340993063605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186048416435560662042403 4779072624653340993063605)
                  ·
                    refine ⟨448038058561250718099713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4779072624653340993063605 448038058561250718099713)
                    ·
                      rfl

theorem cell23_2617653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2617653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617653 prefixEnd_2617653 := by exact prefixLift 2617653
  have htrace : WordTrace (prefixWord ++ tailWord_2617653) baseStart_2617653 baseEnd_2617653 := by
    simpa [prefixWord, tailWord_2617653, baseEnd_2617653] using wordTrace_append hprefix tailTrace_2617653
  have hstable : (prefixWord ++ tailWord_2617653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617653).length < 2 ^ (prefixWord ++ tailWord_2617653).sum := by decide
  have hdescent : baseEnd_2617653 < baseStart_2617653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617656 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_2617656 : Nat := 118140960795 + 2617656 * 2 ^ 59
def prefixEnd_2617656 : Nat := 4983230072969 + 3 ^ 40 * 2617656 * 2
def baseEnd_2617656 : Nat := 1344115716125715642561625

theorem tailTrace_2617656 : CollatzResearch.WordTrace tailWord_2617656 prefixEnd_2617656 1344115716125715642561625 := by
  unfold tailWord_2617656
  simp only [CollatzResearch.WordTrace]
  refine ⟨47736878902343423448820411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63649171869791231265093881 47736878902343423448820411)
  ·
    refine ⟨71605318353515135173230617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47736878902343423448820411 71605318353515135173230617)
    ·
      refine ⟨53703988765136351379922963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71605318353515135173230617 53703988765136351379922963)
      ·
        refine ⟨80555983147704527069884445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53703988765136351379922963 80555983147704527069884445)
        ·
          refine ⟨30208493680389197651206667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80555983147704527069884445 30208493680389197651206667)
          ·
            refine ⟨45312740520583796476810001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30208493680389197651206667 45312740520583796476810001)
            ·
              refine ⟨33984555390437847357607501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45312740520583796476810001 33984555390437847357607501)
              ·
                refine ⟨12744208271414192759102813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33984555390437847357607501 12744208271414192759102813)
                ·
                  refine ⟨4779078101780322284663555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12744208271414192759102813 4779078101780322284663555)
                  ·
                    refine ⟨7168617152670483426995333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4779078101780322284663555 7168617152670483426995333)
                    ·
                      refine ⟨1344115716125715642561625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7168617152670483426995333 1344115716125715642561625)
                      ·
                        rfl

theorem cell23_2617656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_2617656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617656 prefixEnd_2617656 := by exact prefixLift 2617656
  have htrace : WordTrace (prefixWord ++ tailWord_2617656) baseStart_2617656 baseEnd_2617656 := by
    simpa [prefixWord, tailWord_2617656, baseEnd_2617656] using wordTrace_append hprefix tailTrace_2617656
  have hstable : (prefixWord ++ tailWord_2617656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617656).length < 2 ^ (prefixWord ++ tailWord_2617656).sum := by decide
  have hdescent : baseEnd_2617656 < baseStart_2617656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617684 : List Nat := [2, 4, 1, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_2617684 : Nat := 118140960795 + 2617684 * 2 ^ 59
def prefixEnd_2617684 : Nat := 4983230072969 + 3 ^ 40 * 2617684 * 2
def baseEnd_2617684 : Nat := 1344130093584041533011497

theorem tailTrace_2617684 : CollatzResearch.WordTrace tailWord_2617684 prefixEnd_2617684 1344130093584041533011497 := by
  unfold tailWord_2617684
  simp only [CollatzResearch.WordTrace]
  refine ⟨47737389524292703839830053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63649852699056938453106737 47737389524292703839830053)
  ·
    refine ⟨8950760535804881969968135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47737389524292703839830053 8950760535804881969968135)
    ·
      refine ⟨13426140803707322954952203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8950760535804881969968135 13426140803707322954952203)
      ·
        refine ⟨20139211205560984432428305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13426140803707322954952203 20139211205560984432428305)
        ·
          refine ⟨15104408404170738324321229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20139211205560984432428305 15104408404170738324321229)
          ·
            refine ⟨5664153151564026871620461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15104408404170738324321229 5664153151564026871620461)
            ·
              refine ⟨2124057431836510076857673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664153151564026871620461 2124057431836510076857673)
              ·
                refine ⟨1593043073877382557643255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124057431836510076857673 1593043073877382557643255)
                ·
                  refine ⟨2389564610816073836464883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593043073877382557643255 2389564610816073836464883)
                  ·
                    refine ⟨3584346916224110754697325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389564610816073836464883 3584346916224110754697325)
                    ·
                      refine ⟨1344130093584041533011497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584346916224110754697325 1344130093584041533011497)
                      ·
                        rfl

theorem cell23_2617684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_2617684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617684 prefixEnd_2617684 := by exact prefixLift 2617684
  have htrace : WordTrace (prefixWord ++ tailWord_2617684) baseStart_2617684 baseEnd_2617684 := by
    simpa [prefixWord, tailWord_2617684, baseEnd_2617684] using wordTrace_append hprefix tailTrace_2617684
  have hstable : (prefixWord ++ tailWord_2617684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617684).length < 2 ^ (prefixWord ++ tailWord_2617684).sum := by decide
  have hdescent : baseEnd_2617684 < baseStart_2617684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617723 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 3]
def baseStart_2617723 : Nat := 118140960795 + 2617723 * 2 ^ 59
def prefixEnd_2617723 : Nat := 4983230072969 + 3 ^ 40 * 2617723 * 2
def baseEnd_2617723 : Nat := 1344150119329566880423817

theorem tailTrace_2617723 : CollatzResearch.WordTrace tailWord_2617723 prefixEnd_2617723 1344150119329566880423817 := by
  unfold tailWord_2617723
  simp only [CollatzResearch.WordTrace]
  refine ⟨95476201495444117340329823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63650800996962744893553215 95476201495444117340329823)
  ·
    refine ⟨143214302243166176010494735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95476201495444117340329823 143214302243166176010494735)
    ·
      refine ⟨214821453364749264015742103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143214302243166176010494735 214821453364749264015742103)
      ·
        refine ⟨322232180047123896023613155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214821453364749264015742103 322232180047123896023613155)
        ·
          refine ⟨483348270070685844035419733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322232180047123896023613155 483348270070685844035419733)
          ·
            refine ⟨5664237539890849734790075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 483348270070685844035419733 5664237539890849734790075)
            ·
              refine ⟨8496356309836274602185113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664237539890849734790075 8496356309836274602185113)
              ·
                refine ⟨6372267232377205951638835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8496356309836274602185113 6372267232377205951638835)
                ·
                  refine ⟨9558400848565808927458253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6372267232377205951638835 9558400848565808927458253)
                  ·
                    refine ⟨3584400318212178347796845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9558400848565808927458253 3584400318212178347796845)
                    ·
                      refine ⟨1344150119329566880423817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584400318212178347796845 1344150119329566880423817)
                      ·
                        rfl

theorem cell23_2617723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 3].length) (baseStart_2617723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617723 prefixEnd_2617723 := by exact prefixLift 2617723
  have htrace : WordTrace (prefixWord ++ tailWord_2617723) baseStart_2617723 baseEnd_2617723 := by
    simpa [prefixWord, tailWord_2617723, baseEnd_2617723] using wordTrace_append hprefix tailTrace_2617723
  have hstable : (prefixWord ++ tailWord_2617723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617723).length < 2 ^ (prefixWord ++ tailWord_2617723).sum := by decide
  have hdescent : baseEnd_2617723 < baseStart_2617723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617730 : List Nat := [3, 4, 2, 1, 3, 10]
def baseStart_2617730 : Nat := 118140960795 + 2617730 * 2 ^ 59
def prefixEnd_2617730 : Nat := 4983230072969 + 3 ^ 40 * 2617730 * 2
def baseEnd_2617730 : Nat := 5531496764173450012495

theorem tailTrace_2617730 : CollatzResearch.WordTrace tailWord_2617730 prefixEnd_2617730 5531496764173450012495 := by
  unfold tailWord_2617730
  simp only [CollatzResearch.WordTrace]
  refine ⟨23869114201604689383958661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63650971204279171690556429 23869114201604689383958661)
  ·
    refine ⟨4475458912800879259492249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23869114201604689383958661 4475458912800879259492249)
    ·
      refine ⟨3356594184600659444619187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4475458912800879259492249 3356594184600659444619187)
      ·
        refine ⟨5034891276900989166928781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356594184600659444619187 5034891276900989166928781)
        ·
          refine ⟨1888084228837870937598293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5034891276900989166928781 1888084228837870937598293)
          ·
            refine ⟨5531496764173450012495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1888084228837870937598293 5531496764173450012495)
            ·
              rfl

theorem cell23_2617730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 10].length) (baseStart_2617730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617730 prefixEnd_2617730 := by exact prefixLift 2617730
  have htrace : WordTrace (prefixWord ++ tailWord_2617730) baseStart_2617730 baseEnd_2617730 := by
    simpa [prefixWord, tailWord_2617730, baseEnd_2617730] using wordTrace_append hprefix tailTrace_2617730
  have hstable : (prefixWord ++ tailWord_2617730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617730).length < 2 ^ (prefixWord ++ tailWord_2617730).sum := by decide
  have hdescent : baseEnd_2617730 < baseStart_2617730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617740 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2617740 : Nat := 118140960795 + 2617740 * 2 ^ 59
def prefixEnd_2617740 : Nat := 4983230072969 + 3 ^ 40 * 2617740 * 2
def baseEnd_2617740 : Nat := 1344158848500693313911239

theorem tailTrace_2617740 : CollatzResearch.WordTrace tailWord_2617740 prefixEnd_2617740 1344158848500693313911239 := by
  unfold tailWord_2617740
  simp only [CollatzResearch.WordTrace]
  refine ⟨47738410768191264621849337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63651214357588352829132449 47738410768191264621849337)
  ·
    refine ⟨35803808076143448466387003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47738410768191264621849337 35803808076143448466387003)
    ·
      refine ⟨53705712114215172699580505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35803808076143448466387003 53705712114215172699580505)
      ·
        refine ⟨40279284085661379524685379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53705712114215172699580505 40279284085661379524685379)
        ·
          refine ⟨60418926128492069287028069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40279284085661379524685379 60418926128492069287028069)
          ·
            refine ⟨11328548649092262991317763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60418926128492069287028069 11328548649092262991317763)
            ·
              refine ⟨16992822973638394486976645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11328548649092262991317763 16992822973638394486976645)
              ·
                refine ⟨3186154307557198966308121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16992822973638394486976645 3186154307557198966308121)
                ·
                  refine ⟨2389615730667899224731091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186154307557198966308121 2389615730667899224731091)
                  ·
                    refine ⟨3584423596001848837096637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389615730667899224731091 3584423596001848837096637)
                    ·
                      refine ⟨1344158848500693313911239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584423596001848837096637 1344158848500693313911239)
                      ·
                        rfl

theorem cell23_2617740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2617740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617740 prefixEnd_2617740 := by exact prefixLift 2617740
  have htrace : WordTrace (prefixWord ++ tailWord_2617740) baseStart_2617740 baseEnd_2617740 := by
    simpa [prefixWord, tailWord_2617740, baseEnd_2617740] using wordTrace_append hprefix tailTrace_2617740
  have hstable : (prefixWord ++ tailWord_2617740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617740).length < 2 ^ (prefixWord ++ tailWord_2617740).sum := by decide
  have hdescent : baseEnd_2617740 < baseStart_2617740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617837 : List Nat := [1, 5, 1, 3, 1, 1, 3, 3, 5]
def baseStart_2617837 : Nat := 118140960795 + 2617837 * 2 ^ 59
def prefixEnd_2617837 : Nat := 4983230072969 + 3 ^ 40 * 2617837 * 2
def baseEnd_2617837 : Nat := 149356517347131048266477

theorem tailTrace_2617837 : CollatzResearch.WordTrace tailWord_2617837 prefixEnd_2617837 149356517347131048266477 := by
  unfold tailWord_2617837
  simp only [CollatzResearch.WordTrace]
  refine ⟨95480359417031114809979765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63653572944687409873319843 95480359417031114809979765)
  ·
    refine ⟨8951283695346667013435603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95480359417031114809979765 8951283695346667013435603)
    ·
      refine ⟨13426925543020000520153405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8951283695346667013435603 13426925543020000520153405)
      ·
        refine ⟨5035097078632500195057527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13426925543020000520153405 5035097078632500195057527)
        ·
          refine ⟨7552645617948750292586291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035097078632500195057527 7552645617948750292586291)
          ·
            refine ⟨11328968426923125438879437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7552645617948750292586291 11328968426923125438879437)
            ·
              refine ⟨4248363160096172039579789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11328968426923125438879437 4248363160096172039579789)
              ·
                refine ⟨1593136185036064514842421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4248363160096172039579789 1593136185036064514842421)
                ·
                  refine ⟨149356517347131048266477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593136185036064514842421 149356517347131048266477)
                  ·
                    rfl

theorem cell23_2617837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_2617837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617837 prefixEnd_2617837 := by exact prefixLift 2617837
  have htrace : WordTrace (prefixWord ++ tailWord_2617837) baseStart_2617837 baseEnd_2617837 := by
    simpa [prefixWord, tailWord_2617837, baseEnd_2617837] using wordTrace_append hprefix tailTrace_2617837
  have hstable : (prefixWord ++ tailWord_2617837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617837).length < 2 ^ (prefixWord ++ tailWord_2617837).sum := by decide
  have hdescent : baseEnd_2617837 < baseStart_2617837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617860 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2617860 : Nat := 118140960795 + 2617860 * 2 ^ 59
def prefixEnd_2617860 : Nat := 4983230072969 + 3 ^ 40 * 2617860 * 2
def baseEnd_2617860 : Nat := 1344220466179232844410687

theorem tailTrace_2617860 : CollatzResearch.WordTrace tailWord_2617860 prefixEnd_2617860 1344220466179232844410687 := by
  unfold tailWord_2617860
  simp only [CollatzResearch.WordTrace]
  refine ⟨47740599147973894869033517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63654132197298526492044689 47740599147973894869033517)
  ·
    refine ⟨17902724680490210575887569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47740599147973894869033517 17902724680490210575887569)
    ·
      refine ⟨13427043510367657931915677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17902724680490210575887569 13427043510367657931915677)
      ·
        refine ⟨5035141316387871724468379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13427043510367657931915677 5035141316387871724468379)
        ·
          refine ⟨7552711974581807586702569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035141316387871724468379 7552711974581807586702569)
          ·
            refine ⟨5664533980936355690026927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7552711974581807586702569 5664533980936355690026927)
            ·
              refine ⟨8496800971404533535040391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664533980936355690026927 8496800971404533535040391)
              ·
                refine ⟨12745201457106800302560587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8496800971404533535040391 12745201457106800302560587)
                ·
                  refine ⟨19117802185660200453840881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12745201457106800302560587 19117802185660200453840881)
                  ·
                    refine ⟨14338351639245150340380661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19117802185660200453840881 14338351639245150340380661)
                    ·
                      refine ⟨1344220466179232844410687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14338351639245150340380661 1344220466179232844410687)
                      ·
                        rfl

theorem cell23_2617860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2617860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617860 prefixEnd_2617860 := by exact prefixLift 2617860
  have htrace : WordTrace (prefixWord ++ tailWord_2617860) baseStart_2617860 baseEnd_2617860 := by
    simpa [prefixWord, tailWord_2617860, baseEnd_2617860] using wordTrace_append hprefix tailTrace_2617860
  have hstable : (prefixWord ++ tailWord_2617860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617860).length < 2 ^ (prefixWord ++ tailWord_2617860).sum := by decide
  have hdescent : baseEnd_2617860 < baseStart_2617860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617873 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_2617873 : Nat := 118140960795 + 2617873 * 2 ^ 59
def prefixEnd_2617873 : Nat := 4983230072969 + 3 ^ 40 * 2617873 * 2
def baseEnd_2617873 : Nat := 1344227141427741293548127

theorem tailTrace_2617873 : CollatzResearch.WordTrace tailWord_2617873 prefixEnd_2617873 1344227141427741293548127 := by
  unfold tailWord_2617873
  simp only [CollatzResearch.WordTrace]
  refine ⟨95481672444900692958290273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63654448296600461972193515 95481672444900692958290273)
  ·
    refine ⟨71611254333675519718717705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95481672444900692958290273 71611254333675519718717705)
    ·
      refine ⟨53708440750256639789038279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71611254333675519718717705 53708440750256639789038279)
      ·
        refine ⟨80562661125384959683557419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53708440750256639789038279 80562661125384959683557419)
        ·
          refine ⟨120843991688077439525336129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80562661125384959683557419 120843991688077439525336129)
          ·
            refine ⟨90632993766058079644002097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120843991688077439525336129 90632993766058079644002097)
            ·
              refine ⟨67974745324543559733001573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90632993766058079644002097 67974745324543559733001573)
              ·
                refine ⟨12745264748351917449937795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67974745324543559733001573 12745264748351917449937795)
                ·
                  refine ⟨19117897122527876174906693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12745264748351917449937795 19117897122527876174906693)
                  ·
                    refine ⟨3584605710473976782795005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19117897122527876174906693 3584605710473976782795005)
                    ·
                      refine ⟨1344227141427741293548127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584605710473976782795005 1344227141427741293548127)
                      ·
                        rfl

theorem cell23_2617873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_2617873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617873 prefixEnd_2617873 := by exact prefixLift 2617873
  have htrace : WordTrace (prefixWord ++ tailWord_2617873) baseStart_2617873 baseEnd_2617873 := by
    simpa [prefixWord, tailWord_2617873, baseEnd_2617873] using wordTrace_append hprefix tailTrace_2617873
  have hstable : (prefixWord ++ tailWord_2617873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617873).length < 2 ^ (prefixWord ++ tailWord_2617873).sum := by decide
  have hdescent : baseEnd_2617873 < baseStart_2617873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617913 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2617913 : Nat := 118140960795 + 2617913 * 2 ^ 59
def prefixEnd_2617913 : Nat := 4983230072969 + 3 ^ 40 * 2617913 * 2
def baseEnd_2617913 : Nat := 1344247680653921137047943

theorem tailTrace_2617913 : CollatzResearch.WordTrace tailWord_2617913 prefixEnd_2617913 1344247680653921137047943 := by
  unfold tailWord_2617913
  simp only [CollatzResearch.WordTrace]
  refine ⟨95483131364755779789746393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63655420909837186526497595 95483131364755779789746393)
  ·
    refine ⟨71612348523566834842309795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95483131364755779789746393 71612348523566834842309795)
    ·
      refine ⟨107418522785350252263464693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71612348523566834842309795 107418522785350252263464693)
      ·
        refine ⟨10070486511126586149699815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107418522785350252263464693 10070486511126586149699815)
        ·
          refine ⟨15105729766689879224549723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10070486511126586149699815 15105729766689879224549723)
          ·
            refine ⟨22658594650034818836824585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15105729766689879224549723 22658594650034818836824585)
            ·
              refine ⟨16993945987526114127618439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22658594650034818836824585 16993945987526114127618439)
              ·
                refine ⟨25490918981289171191427659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16993945987526114127618439 25490918981289171191427659)
                ·
                  refine ⟨38236378471933756787141489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25490918981289171191427659 38236378471933756787141489)
                  ·
                    refine ⟨28677283853950317590356117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38236378471933756787141489 28677283853950317590356117)
                    ·
                      refine ⟨1344247680653921137047943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28677283853950317590356117 1344247680653921137047943)
                      ·
                        rfl

theorem cell23_2617913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2617913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617913 prefixEnd_2617913 := by exact prefixLift 2617913
  have htrace : WordTrace (prefixWord ++ tailWord_2617913) baseStart_2617913 baseEnd_2617913 := by
    simpa [prefixWord, tailWord_2617913, baseEnd_2617913] using wordTrace_append hprefix tailTrace_2617913
  have hstable : (prefixWord ++ tailWord_2617913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617913).length < 2 ^ (prefixWord ++ tailWord_2617913).sum := by decide
  have hdescent : baseEnd_2617913 < baseStart_2617913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617914 : List Nat := [3, 1, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_2617914 : Nat := 118140960795 + 2617914 * 2 ^ 59
def prefixEnd_2617914 : Nat := 4983230072969 + 3 ^ 40 * 2617914 * 2
def baseEnd_2617914 : Nat := 448082731378191877711813

theorem tailTrace_2617914 : CollatzResearch.WordTrace tailWord_2617914 prefixEnd_2617914 448082731378191877711813 := by
  unfold tailWord_2617914
  simp only [CollatzResearch.WordTrace]
  refine ⟨23870791959438039240133199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63655445225168104640355197 23870791959438039240133199)
  ·
    refine ⟨35806187939157058860199799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23870791959438039240133199 35806187939157058860199799)
    ·
      refine ⟨53709281908735588290299699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35806187939157058860199799 53709281908735588290299699)
      ·
        refine ⟨80563922863103382435449549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53709281908735588290299699 80563922863103382435449549)
        ·
          refine ⟨30211471073663768413293581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80563922863103382435449549 30211471073663768413293581)
          ·
            refine ⟨11329301652623913154985093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30211471073663768413293581 11329301652623913154985093)
            ·
              refine ⟨2124244059866983716559705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11329301652623913154985093 2124244059866983716559705)
              ·
                refine ⟨1593183044900237787419779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124244059866983716559705 1593183044900237787419779)
                ·
                  refine ⟨2389774567350356681129669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593183044900237787419779 2389774567350356681129669)
                  ·
                    refine ⟨448082731378191877711813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2389774567350356681129669 448082731378191877711813)
                    ·
                      rfl

theorem cell23_2617914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_2617914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617914 prefixEnd_2617914 := by exact prefixLift 2617914
  have htrace : WordTrace (prefixWord ++ tailWord_2617914) baseStart_2617914 baseEnd_2617914 := by
    simpa [prefixWord, tailWord_2617914, baseEnd_2617914] using wordTrace_append hprefix tailTrace_2617914
  have hstable : (prefixWord ++ tailWord_2617914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617914).length < 2 ^ (prefixWord ++ tailWord_2617914).sum := by decide
  have hdescent : baseEnd_2617914 < baseStart_2617914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617937 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_2617937 : Nat := 118140960795 + 2617937 * 2 ^ 59
def prefixEnd_2617937 : Nat := 4983230072969 + 3 ^ 40 * 2617937 * 2
def baseEnd_2617937 : Nat := 1344260004189629043147833

theorem tailTrace_2617937 : CollatzResearch.WordTrace tailWord_2617937 prefixEnd_2617937 1344260004189629043147833 := by
  unfold tailWord_2617937
  simp only [CollatzResearch.WordTrace]
  refine ⟨95484006716668831888620065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63656004477779221259080043 95484006716668831888620065)
  ·
    refine ⟨71613005037501623916465049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95484006716668831888620065 71613005037501623916465049)
    ·
      refine ⟨53709753778126217937348787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71613005037501623916465049 53709753778126217937348787)
      ·
        refine ⟨80564630667189326906023181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53709753778126217937348787 80564630667189326906023181)
        ·
          refine ⟨30211736500195997589758693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80564630667189326906023181 30211736500195997589758693)
          ·
            refine ⟨5664700593786749548079755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30211736500195997589758693 5664700593786749548079755)
            ·
              refine ⟨8497050890680124322119633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664700593786749548079755 8497050890680124322119633)
              ·
                refine ⟨6372788168010093241589725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8497050890680124322119633 6372788168010093241589725)
                ·
                  refine ⟨2389795563003784965596147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6372788168010093241589725 2389795563003784965596147)
                  ·
                    refine ⟨3584693344505677448394221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389795563003784965596147 3584693344505677448394221)
                    ·
                      refine ⟨1344260004189629043147833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584693344505677448394221 1344260004189629043147833)
                      ·
                        rfl

theorem cell23_2617937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_2617937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617937 prefixEnd_2617937 := by exact prefixLift 2617937
  have htrace : WordTrace (prefixWord ++ tailWord_2617937) baseStart_2617937 baseEnd_2617937 := by
    simpa [prefixWord, tailWord_2617937, baseEnd_2617937] using wordTrace_append hprefix tailTrace_2617937
  have hstable : (prefixWord ++ tailWord_2617937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617937).length < 2 ^ (prefixWord ++ tailWord_2617937).sum := by decide
  have hdescent : baseEnd_2617937 < baseStart_2617937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617940 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_2617940 : Nat := 118140960795 + 2617940 * 2 ^ 59
def prefixEnd_2617940 : Nat := 4983230072969 + 3 ^ 40 * 2617940 * 2
def baseEnd_2617940 : Nat := 448087181543864177136773

theorem tailTrace_2617940 : CollatzResearch.WordTrace tailWord_2617940 prefixEnd_2617940 448087181543864177136773 := by
  unfold tailWord_2617940
  simp only [CollatzResearch.WordTrace]
  refine ⟨47742058067828981700489637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63656077423771975600652849 47742058067828981700489637)
  ·
    refine ⟨8951635887717934068841807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47742058067828981700489637 8951635887717934068841807)
    ·
      refine ⟨13427453831576901103262711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8951635887717934068841807 13427453831576901103262711)
      ·
        refine ⟨20141180747365351654894067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13427453831576901103262711 20141180747365351654894067)
        ·
          refine ⟨30211771121048027482341101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20141180747365351654894067 30211771121048027482341101)
          ·
            refine ⟨11329414170393010305877913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30211771121048027482341101 11329414170393010305877913)
            ·
              refine ⟨8497060627794757729408435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11329414170393010305877913 8497060627794757729408435)
              ·
                refine ⟨12745590941692136594112653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8497060627794757729408435 12745590941692136594112653)
                ·
                  refine ⟨4779596603134551222792245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12745590941692136594112653 4779596603134551222792245)
                  ·
                    refine ⟨448087181543864177136773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4779596603134551222792245 448087181543864177136773)
                    ·
                      rfl

theorem cell23_2617940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_2617940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617940 prefixEnd_2617940 := by exact prefixLift 2617940
  have htrace : WordTrace (prefixWord ++ tailWord_2617940) baseStart_2617940 baseEnd_2617940 := by
    simpa [prefixWord, tailWord_2617940, baseEnd_2617940] using wordTrace_append hprefix tailTrace_2617940
  have hstable : (prefixWord ++ tailWord_2617940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617940).length < 2 ^ (prefixWord ++ tailWord_2617940).sum := by decide
  have hdescent : baseEnd_2617940 < baseStart_2617940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617957 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_2617957 : Nat := 118140960795 + 2617957 * 2 ^ 59
def prefixEnd_2617957 : Nat := 4983230072969 + 3 ^ 40 * 2617957 * 2
def baseEnd_2617957 : Nat := 448090091267572988299247

theorem tailTrace_2617957 : CollatzResearch.WordTrace tailWord_2617957 prefixEnd_2617957 448090091267572988299247 := by
  unfold tailWord_2617957
  simp only [CollatzResearch.WordTrace]
  refine ⟨95484736176596375304348125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63656490784397583536232083 95484736176596375304348125)
  ·
    refine ⟨35806776066223640739130547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95484736176596375304348125 35806776066223640739130547)
    ·
      refine ⟨53710164099335461108695821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35806776066223640739130547 53710164099335461108695821)
      ·
        refine ⟨20141311537250797915760933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53710164099335461108695821 20141311537250797915760933)
        ·
          refine ⟨3776495913234524609205175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20141311537250797915760933 3776495913234524609205175)
          ·
            refine ⟨5664743869851786913807763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776495913234524609205175 5664743869851786913807763)
            ·
              refine ⟨8497115804777680370711645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664743869851786913807763 8497115804777680370711645)
              ·
                refine ⟨3186418426791630139016867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8497115804777680370711645 3186418426791630139016867)
                ·
                  refine ⟨4779627640187445208525301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186418426791630139016867 4779627640187445208525301)
                  ·
                    refine ⟨448090091267572988299247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4779627640187445208525301 448090091267572988299247)
                    ·
                      rfl

theorem cell23_2617957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_2617957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617957 prefixEnd_2617957 := by exact prefixLift 2617957
  have htrace : WordTrace (prefixWord ++ tailWord_2617957) baseStart_2617957 baseEnd_2617957 := by
    simpa [prefixWord, tailWord_2617957, baseEnd_2617957] using wordTrace_append hprefix tailTrace_2617957
  have hstable : (prefixWord ++ tailWord_2617957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617957).length < 2 ^ (prefixWord ++ tailWord_2617957).sum := by decide
  have hdescent : baseEnd_2617957 < baseStart_2617957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617980 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_2617980 : Nat := 118140960795 + 2617980 * 2 ^ 59
def prefixEnd_2617980 : Nat := 4983230072969 + 3 ^ 40 * 2617980 * 2
def baseEnd_2617980 : Nat := 1344282083857772374910135

theorem tailTrace_2617980 : CollatzResearch.WordTrace tailWord_2617980 prefixEnd_2617980 1344282083857772374910135 := by
  unfold tailWord_2617980
  simp only [CollatzResearch.WordTrace]
  refine ⟨47742787527756525116217697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63657050037008700154956929 47742787527756525116217697)
  ·
    refine ⟨35807090645817393837163273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47742787527756525116217697 35807090645817393837163273)
    ·
      refine ⟨26855317984363045377872455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35807090645817393837163273 26855317984363045377872455)
      ·
        refine ⟨40282976976544568066808683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26855317984363045377872455 40282976976544568066808683)
        ·
          refine ⟨60424465464816852100213025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40282976976544568066808683 60424465464816852100213025)
          ·
            refine ⟨45318349098612639075159769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60424465464816852100213025 45318349098612639075159769)
            ·
              refine ⟨33988761823959479306369827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45318349098612639075159769 33988761823959479306369827)
              ·
                refine ⟨50983142735939218959554741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33988761823959479306369827 50983142735939218959554741)
                ·
                  refine ⟨4779669631494301777458257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50983142735939218959554741 4779669631494301777458257)
                  ·
                    refine ⟨3584752223620726333093693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779669631494301777458257 3584752223620726333093693)
                    ·
                      refine ⟨1344282083857772374910135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584752223620726333093693 1344282083857772374910135)
                      ·
                        rfl

theorem cell23_2617980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_2617980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617980 prefixEnd_2617980 := by exact prefixLift 2617980
  have htrace : WordTrace (prefixWord ++ tailWord_2617980) baseStart_2617980 baseEnd_2617980 := by
    simpa [prefixWord, tailWord_2617980, baseEnd_2617980] using wordTrace_append hprefix tailTrace_2617980
  have hstable : (prefixWord ++ tailWord_2617980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617980).length < 2 ^ (prefixWord ++ tailWord_2617980).sum := by decide
  have hdescent : baseEnd_2617980 < baseStart_2617980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2617994 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2617994 : Nat := 118140960795 + 2617994 * 2 ^ 59
def prefixEnd_2617994 : Nat := 4983230072969 + 3 ^ 40 * 2617994 * 2
def baseEnd_2617994 : Nat := 1344289272586935320135071

theorem tailTrace_2617994 : CollatzResearch.WordTrace tailWord_2617994 prefixEnd_2617994 1344289272586935320135071 := by
  unfold tailWord_2617994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23871521419365582655861259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63657390451641553748963357 23871521419365582655861259)
  ·
    refine ⟨35807282129048373983791889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23871521419365582655861259 35807282129048373983791889)
    ·
      refine ⟨26855461596786280487843917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35807282129048373983791889 26855461596786280487843917)
      ·
        refine ⟨10070798098794855182941469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26855461596786280487843917 10070798098794855182941469)
        ·
          refine ⟨3776549287048070693603051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10070798098794855182941469 3776549287048070693603051)
          ·
            refine ⟨5664823930572106040404577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776549287048070693603051 5664823930572106040404577)
            ·
              refine ⟨4248617947929079530303433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5664823930572106040404577 4248617947929079530303433)
              ·
                refine ⟨3186463460946809647727575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4248617947929079530303433 3186463460946809647727575)
                ·
                  refine ⟨4779695191420214471591363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186463460946809647727575 4779695191420214471591363)
                  ·
                    refine ⟨7169542787130321707387045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4779695191420214471591363 7169542787130321707387045)
                    ·
                      refine ⟨1344289272586935320135071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7169542787130321707387045 1344289272586935320135071)
                      ·
                        rfl

theorem cell23_2617994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2617994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2617994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2617994 prefixEnd_2617994 := by exact prefixLift 2617994
  have htrace : WordTrace (prefixWord ++ tailWord_2617994) baseStart_2617994 baseEnd_2617994 := by
    simpa [prefixWord, tailWord_2617994, baseEnd_2617994] using wordTrace_append hprefix tailTrace_2617994
  have hstable : (prefixWord ++ tailWord_2617994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2617994).length < 2 ^ (prefixWord ++ tailWord_2617994).sum := by decide
  have hdescent : baseEnd_2617994 < baseStart_2617994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2617994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618014 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2618014 : Nat := 118140960795 + 2618014 * 2 ^ 59
def prefixEnd_2618014 : Nat := 4983230072969 + 3 ^ 40 * 2618014 * 2
def baseEnd_2618014 : Nat := 1344299542200025241884979

theorem tailTrace_2618014 : CollatzResearch.WordTrace tailWord_2618014 prefixEnd_2618014 1344299542200025241884979 := by
  unfold tailWord_2618014
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935851892173734254896637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63657876758259916026115397 11935851892173734254896637)
  ·
    refine ⟨4475944459565150345586239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11935851892173734254896637 4475944459565150345586239)
    ·
      refine ⟨6713916689347725518379359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475944459565150345586239 6713916689347725518379359)
      ·
        refine ⟨10070875034021588277569039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713916689347725518379359 10070875034021588277569039)
        ·
          refine ⟨15106312551032382416353559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10070875034021588277569039 15106312551032382416353559)
          ·
            refine ⟨22659468826548573624530339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15106312551032382416353559 22659468826548573624530339)
            ·
              refine ⟨33989203239822860436795509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22659468826548573624530339 33989203239822860436795509)
              ·
                refine ⟨3186487803733393165949579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33989203239822860436795509 3186487803733393165949579)
                ·
                  refine ⟨4779731705600089748924369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186487803733393165949579 4779731705600089748924369)
                  ·
                    refine ⟨3584798779200067311693277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779731705600089748924369 3584798779200067311693277)
                    ·
                      refine ⟨1344299542200025241884979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584798779200067311693277 1344299542200025241884979)
                      ·
                        rfl

theorem cell23_2618014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2618014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618014 prefixEnd_2618014 := by exact prefixLift 2618014
  have htrace : WordTrace (prefixWord ++ tailWord_2618014) baseStart_2618014 baseEnd_2618014 := by
    simpa [prefixWord, tailWord_2618014, baseEnd_2618014] using wordTrace_append hprefix tailTrace_2618014
  have hstable : (prefixWord ++ tailWord_2618014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618014).length < 2 ^ (prefixWord ++ tailWord_2618014).sum := by decide
  have hdescent : baseEnd_2618014 < baseStart_2618014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618017 : List Nat := [1, 2, 3, 3, 4, 1, 9]
def baseStart_2618017 : Nat := 118140960795 + 2618017 * 2 ^ 59
def prefixEnd_2618017 : Nat := 4983230072969 + 3 ^ 40 * 2618017 * 2
def baseEnd_2618017 : Nat := 16596309662246774446265

theorem tailTrace_2618017 : CollatzResearch.WordTrace tailWord_2618017 prefixEnd_2618017 16596309662246774446265 := by
  unfold tailWord_2618017
  simp only [CollatzResearch.WordTrace]
  refine ⟨95486924556379005551532305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63657949704252670367688203 95486924556379005551532305)
  ·
    refine ⟨71615193417284254163649229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95486924556379005551532305 71615193417284254163649229)
    ·
      refine ⟨26855697531481595311368461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71615193417284254163649229 26855697531481595311368461)
      ·
        refine ⟨10070886574305598241763173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26855697531481595311368461 10070886574305598241763173)
        ·
          refine ⟨1888291232682299670330595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10070886574305598241763173 1888291232682299670330595)
          ·
            refine ⟨2832436849023449505495893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888291232682299670330595 2832436849023449505495893)
            ·
              refine ⟨16596309662246774446265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2832436849023449505495893 16596309662246774446265)
              ·
                rfl

theorem cell23_2618017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 9].length) (baseStart_2618017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618017 prefixEnd_2618017 := by exact prefixLift 2618017
  have htrace : WordTrace (prefixWord ++ tailWord_2618017) baseStart_2618017 baseEnd_2618017 := by
    simpa [prefixWord, tailWord_2618017, baseEnd_2618017] using wordTrace_append hprefix tailTrace_2618017
  have hstable : (prefixWord ++ tailWord_2618017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618017).length < 2 ^ (prefixWord ++ tailWord_2618017).sum := by decide
  have hdescent : baseEnd_2618017 < baseStart_2618017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618044 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2618044 : Nat := 118140960795 + 2618044 * 2 ^ 59
def prefixEnd_2618044 : Nat := 4983230072969 + 3 ^ 40 * 2618044 * 2
def baseEnd_2618044 : Nat := 1344314946619660124509841

theorem tailTrace_2618044 : CollatzResearch.WordTrace tailWord_2618044 prefixEnd_2618044 1344314946619660124509841 := by
  unfold tailWord_2618044
  simp only [CollatzResearch.WordTrace]
  refine ⟨47743954663640594581382593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63658606218187459441843457 47743954663640594581382593)
  ·
    refine ⟨35807965997730445936036945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47743954663640594581382593 35807965997730445936036945)
    ·
      refine ⟨26855974498297834452027709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35807965997730445936036945 26855974498297834452027709)
      ·
        refine ⟨10070990436861687919510391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26855974498297834452027709 10070990436861687919510391)
        ·
          refine ⟨15106485655292531879265587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10070990436861687919510391 15106485655292531879265587)
          ·
            refine ⟨22659728482938797818898381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15106485655292531879265587 22659728482938797818898381)
            ·
              refine ⟨8497398181102049182086893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22659728482938797818898381 8497398181102049182086893)
              ·
                refine ⟨3186524317913268443282585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8497398181102049182086893 3186524317913268443282585)
                ·
                  refine ⟨2389893238434951332461939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186524317913268443282585 2389893238434951332461939)
                  ·
                    refine ⟨3584839857652426998692909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2389893238434951332461939 3584839857652426998692909)
                    ·
                      refine ⟨1344314946619660124509841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584839857652426998692909 1344314946619660124509841)
                      ·
                        rfl

theorem cell23_2618044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2618044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618044 prefixEnd_2618044 := by exact prefixLift 2618044
  have htrace : WordTrace (prefixWord ++ tailWord_2618044) baseStart_2618044 baseEnd_2618044 := by
    simpa [prefixWord, tailWord_2618044, baseEnd_2618044] using wordTrace_append hprefix tailTrace_2618044
  have hstable : (prefixWord ++ tailWord_2618044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618044).length < 2 ^ (prefixWord ++ tailWord_2618044).sum := by decide
  have hdescent : baseEnd_2618044 < baseStart_2618044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618061 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2618061 : Nat := 118140960795 + 2618061 * 2 ^ 59
def prefixEnd_2618061 : Nat := 4983230072969 + 3 ^ 40 * 2618061 * 2
def baseEnd_2618061 : Nat := 1344323675790786557997263

theorem tailTrace_2618061 : CollatzResearch.WordTrace tailWord_2618061 prefixEnd_2618061 1344323675790786557997263 := by
  unfold tailWord_2618061
  simp only [CollatzResearch.WordTrace]
  refine ⟨95488529368219601066134037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63659019578813067377422691 95488529368219601066134037)
  ·
    refine ⟨4476024814135293799975033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95488529368219601066134037 4476024814135293799975033)
    ·
      refine ⟨3357018610601470349981275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4476024814135293799975033 3357018610601470349981275)
      ·
        refine ⟨5035527915902205524971913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357018610601470349981275 5035527915902205524971913)
        ·
          refine ⟨3776645936926654143728935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5035527915902205524971913 3776645936926654143728935)
          ·
            refine ⟨5664968905389981215593403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776645936926654143728935 5664968905389981215593403)
            ·
              refine ⟨8497453358084971823390105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664968905389981215593403 8497453358084971823390105)
              ·
                refine ⟨6373090018563728867542579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8497453358084971823390105 6373090018563728867542579)
                ·
                  refine ⟨9559635027845593301313869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373090018563728867542579 9559635027845593301313869)
                  ·
                    refine ⟨3584863135442097487992701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9559635027845593301313869 3584863135442097487992701)
                    ·
                      refine ⟨1344323675790786557997263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3584863135442097487992701 1344323675790786557997263)
                      ·
                        rfl

theorem cell23_2618061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2618061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618061 prefixEnd_2618061 := by exact prefixLift 2618061
  have htrace : WordTrace (prefixWord ++ tailWord_2618061) baseStart_2618061 baseEnd_2618061 := by
    simpa [prefixWord, tailWord_2618061, baseEnd_2618061] using wordTrace_append hprefix tailTrace_2618061
  have hstable : (prefixWord ++ tailWord_2618061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618061).length < 2 ^ (prefixWord ++ tailWord_2618061).sum := by decide
  have hdescent : baseEnd_2618061 < baseStart_2618061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618071 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 1, 3, 2]
def baseStart_2618071 : Nat := 118140960795 + 2618071 * 2 ^ 59
def prefixEnd_2618071 : Nat := 4983230072969 + 3 ^ 40 * 2618071 * 2
def baseEnd_2618071 : Nat := 1344328810597331518872217

theorem tailTrace_2618071 : CollatzResearch.WordTrace tailWord_2618071 prefixEnd_2618071 1344328810597331518872217 := by
  unfold tailWord_2618071
  simp only [CollatzResearch.WordTrace]
  refine ⟨95488894098183372773998067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63659262732122248515998711 95488894098183372773998067)
  ·
    refine ⟨143233341147275059160997101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95488894098183372773998067 143233341147275059160997101)
    ·
      refine ⟨53712502930228147185373913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143233341147275059160997101 53712502930228147185373913)
      ·
        refine ⟨40284377197671110389030435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53712502930228147185373913 40284377197671110389030435)
        ·
          refine ⟨60426565796506665583545653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40284377197671110389030435 60426565796506665583545653)
          ·
            refine ⟨5664990543422499898457405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60426565796506665583545653 5664990543422499898457405)
            ·
              refine ⟨2124371453783437461921527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5664990543422499898457405 2124371453783437461921527)
              ·
                refine ⟨3186557180675156192882291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124371453783437461921527 3186557180675156192882291)
                ·
                  refine ⟨4779835771012734289323437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186557180675156192882291 4779835771012734289323437)
                  ·
                    refine ⟨1792438414129775358496289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4779835771012734289323437 1792438414129775358496289)
                    ·
                      refine ⟨1344328810597331518872217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792438414129775358496289 1344328810597331518872217)
                      ·
                        rfl

theorem cell23_2618071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_2618071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618071 prefixEnd_2618071 := by exact prefixLift 2618071
  have htrace : WordTrace (prefixWord ++ tailWord_2618071) baseStart_2618071 baseEnd_2618071 := by
    simpa [prefixWord, tailWord_2618071, baseEnd_2618071] using wordTrace_append hprefix tailTrace_2618071
  have hstable : (prefixWord ++ tailWord_2618071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618071).length < 2 ^ (prefixWord ++ tailWord_2618071).sum := by decide
  have hdescent : baseEnd_2618071 < baseStart_2618071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618080 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_2618080 : Nat := 118140960795 + 2618080 * 2 ^ 59
def prefixEnd_2618080 : Nat := 4983230072969 + 3 ^ 40 * 2618080 * 2
def baseEnd_2618080 : Nat := 1344333431923221983659675

theorem tailTrace_2618080 : CollatzResearch.WordTrace tailWord_2618080 prefixEnd_2618080 1344333431923221983659675 := by
  unfold tailWord_2618080
  simp only [CollatzResearch.WordTrace]
  refine ⟨47744611177575383655537847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63659481570100511540717129 47744611177575383655537847)
  ·
    refine ⟨71616916766363075483306771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47744611177575383655537847 71616916766363075483306771)
    ·
      refine ⟨107425375149544613224960157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71616916766363075483306771 107425375149544613224960157)
      ·
        refine ⟨40284515681079229959360059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107425375149544613224960157 40284515681079229959360059)
        ·
          refine ⟨60426773521618844939040089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40284515681079229959360059 60426773521618844939040089)
          ·
            refine ⟨45320080141214133704280067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60426773521618844939040089 45320080141214133704280067)
            ·
              refine ⟨67980120211821200556420101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45320080141214133704280067 67980120211821200556420101)
              ·
                refine ⟨12746272539716475104328769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67980120211821200556420101 12746272539716475104328769)
                ·
                  refine ⟨9559704404787356328246577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12746272539716475104328769 9559704404787356328246577)
                  ·
                    refine ⟨7169778303590517246184933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9559704404787356328246577 7169778303590517246184933)
                    ·
                      refine ⟨1344333431923221983659675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7169778303590517246184933 1344333431923221983659675)
                      ·
                        rfl

theorem cell23_2618080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_2618080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618080 prefixEnd_2618080 := by exact prefixLift 2618080
  have htrace : WordTrace (prefixWord ++ tailWord_2618080) baseStart_2618080 baseEnd_2618080 := by
    simpa [prefixWord, tailWord_2618080, baseEnd_2618080] using wordTrace_append hprefix tailTrace_2618080
  have hstable : (prefixWord ++ tailWord_2618080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618080).length < 2 ^ (prefixWord ++ tailWord_2618080).sum := by decide
  have hdescent : baseEnd_2618080 < baseStart_2618080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618090 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 7]
def baseStart_2618090 : Nat := 118140960795 + 2618090 * 2 ^ 59
def prefixEnd_2618090 : Nat := 4983230072969 + 3 ^ 40 * 2618090 * 2
def baseEnd_2618090 : Nat := 149370951858862993837181

theorem tailTrace_2618090 : CollatzResearch.WordTrace tailWord_2618090 prefixEnd_2618090 149370951858862993837181 := by
  unfold tailWord_2618090
  simp only [CollatzResearch.WordTrace]
  refine ⟨23872396771278634754734931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63659724723409692679293149 23872396771278634754734931)
  ·
    refine ⟨35808595156917952132102397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23872396771278634754734931 35808595156917952132102397)
    ·
      refine ⟨13428223183844232049538399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35808595156917952132102397 13428223183844232049538399)
      ·
        refine ⟨20142334775766348074307599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13428223183844232049538399 20142334775766348074307599)
        ·
          refine ⟨30213502163649522111461399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20142334775766348074307599 30213502163649522111461399)
          ·
            refine ⟨45320253245474283167192099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30213502163649522111461399 45320253245474283167192099)
            ·
              refine ⟨67980379868211424750788149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45320253245474283167192099 67980379868211424750788149)
              ·
                refine ⟨6373160612644821070386389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67980379868211424750788149 6373160612644821070386389)
                ·
                  refine ⟨149370951858862993837181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6373160612644821070386389 149370951858862993837181)
                  ·
                    rfl

theorem cell23_2618090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_2618090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618090 prefixEnd_2618090 := by exact prefixLift 2618090
  have htrace : WordTrace (prefixWord ++ tailWord_2618090) baseStart_2618090 baseEnd_2618090 := by
    simpa [prefixWord, tailWord_2618090, baseEnd_2618090] using wordTrace_append hprefix tailTrace_2618090
  have hstable : (prefixWord ++ tailWord_2618090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618090).length < 2 ^ (prefixWord ++ tailWord_2618090).sum := by decide
  have hdescent : baseEnd_2618090 < baseStart_2618090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618135 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 2, 2, 2]
def baseStart_2618135 : Nat := 118140960795 + 2618135 * 2 ^ 59
def prefixEnd_2618135 : Nat := 4983230072969 + 3 ^ 40 * 2618135 * 2
def baseEnd_2618135 : Nat := 1344361673359219268471923

theorem tailTrace_2618135 : CollatzResearch.WordTrace tailWord_2618135 prefixEnd_2618135 1344361673359219268471923 := by
  unfold tailWord_2618135
  simp only [CollatzResearch.WordTrace]
  refine ⟨95491228369951511704327859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63660818913301007802885239 95491228369951511704327859)
  ·
    refine ⟨143236842554927267556491789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95491228369951511704327859 143236842554927267556491789)
    ·
      refine ⟨53713815958097725333684421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143236842554927267556491789 53713815958097725333684421)
      ·
        refine ⟨10071340492143323500065829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53713815958097725333684421 10071340492143323500065829)
        ·
          refine ⟨1888376342276873156262343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10071340492143323500065829 1888376342276873156262343)
          ·
            refine ⟨2832564513415309734393515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888376342276873156262343 2832564513415309734393515)
            ·
              refine ⟨4248846770122964601590273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832564513415309734393515 4248846770122964601590273)
              ·
                refine ⟨3186635077592223451192705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4248846770122964601590273 3186635077592223451192705)
                ·
                  refine ⟨2389976308194167588394529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186635077592223451192705 2389976308194167588394529)
                  ·
                    refine ⟨1792482231145625691295897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2389976308194167588394529 1792482231145625691295897)
                    ·
                      refine ⟨1344361673359219268471923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792482231145625691295897 1344361673359219268471923)
                      ·
                        rfl

theorem cell23_2618135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_2618135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618135 prefixEnd_2618135 := by exact prefixLift 2618135
  have htrace : WordTrace (prefixWord ++ tailWord_2618135) baseStart_2618135 baseEnd_2618135 := by
    simpa [prefixWord, tailWord_2618135, baseEnd_2618135] using wordTrace_append hprefix tailTrace_2618135
  have hstable : (prefixWord ++ tailWord_2618135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618135).length < 2 ^ (prefixWord ++ tailWord_2618135).sum := by decide
  have hdescent : baseEnd_2618135 < baseStart_2618135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618167 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 3, 4]
def baseStart_2618167 : Nat := 118140960795 + 2618167 * 2 ^ 59
def prefixEnd_2618167 : Nat := 4983230072969 + 3 ^ 40 * 2618167 * 2
def baseEnd_2618167 : Nat := 448126034913387714423925

theorem tailTrace_2618167 : CollatzResearch.WordTrace tailWord_2618167 prefixEnd_2618167 448126034913387714423925 := by
  unfold tailWord_2618167
  simp only [CollatzResearch.WordTrace]
  refine ⟨95492395505835581169492755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63661597003890387446328503 95492395505835581169492755)
  ·
    refine ⟨143238593258753371754239133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95492395505835581169492755 143238593258753371754239133)
    ·
      refine ⟨53714472472032514407839675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143238593258753371754239133 53714472472032514407839675)
      ·
        refine ⟨80571708708048771611759513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53714472472032514407839675 80571708708048771611759513)
        ·
          refine ⟨60428781531036578708819635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80571708708048771611759513 60428781531036578708819635)
          ·
            refine ⟨90643172296554868063229453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60428781531036578708819635 90643172296554868063229453)
            ·
              refine ⟨33991189611208075523711045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90643172296554868063229453 33991189611208075523711045)
              ·
                refine ⟨6373348052101514160695821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33991189611208075523711045 6373348052101514160695821)
                ·
                  refine ⟨2390005519538067810260933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6373348052101514160695821 2390005519538067810260933)
                  ·
                    refine ⟨448126034913387714423925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390005519538067810260933 448126034913387714423925)
                    ·
                      rfl

theorem cell23_2618167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_2618167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618167 prefixEnd_2618167 := by exact prefixLift 2618167
  have htrace : WordTrace (prefixWord ++ tailWord_2618167) baseStart_2618167 baseEnd_2618167 := by
    simpa [prefixWord, tailWord_2618167, baseEnd_2618167] using wordTrace_append hprefix tailTrace_2618167
  have hstable : (prefixWord ++ tailWord_2618167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618167).length < 2 ^ (prefixWord ++ tailWord_2618167).sum := by decide
  have hdescent : baseEnd_2618167 < baseStart_2618167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618194 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2618194 : Nat := 118140960795 + 2618194 * 2 ^ 59
def prefixEnd_2618194 : Nat := 4983230072969 + 3 ^ 40 * 2618194 * 2
def baseEnd_2618194 : Nat := 1344391968717834537634151

theorem tailTrace_2618194 : CollatzResearch.WordTrace tailWord_2618194 prefixEnd_2618194 1344391968717834537634151 := by
  unfold tailWord_2618194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23873345069184441195181409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63662253517825176520483757 23873345069184441195181409)
  ·
    refine ⟨17905008801888330896386057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23873345069184441195181409 17905008801888330896386057)
    ·
      refine ⟨13428756601416248172289543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17905008801888330896386057 13428756601416248172289543)
      ·
        refine ⟨20143134902124372258434315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13428756601416248172289543 20143134902124372258434315)
        ·
          refine ⟨30214702353186558387651473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20143134902124372258434315 30214702353186558387651473)
          ·
            refine ⟨22661026764889918790738605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30214702353186558387651473 22661026764889918790738605)
            ·
              refine ⟨8497885036833719546526977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22661026764889918790738605 8497885036833719546526977)
              ·
                refine ⟨6373413777625289659895233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8497885036833719546526977 6373413777625289659895233)
                ·
                  refine ⟨4780060333218967244921425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6373413777625289659895233 4780060333218967244921425)
                  ·
                    refine ⟨3585045249914225433691069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4780060333218967244921425 3585045249914225433691069)
                    ·
                      refine ⟨1344391968717834537634151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3585045249914225433691069 1344391968717834537634151)
                      ·
                        rfl

theorem cell23_2618194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2618194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618194 prefixEnd_2618194 := by exact prefixLift 2618194
  have htrace : WordTrace (prefixWord ++ tailWord_2618194) baseStart_2618194 baseEnd_2618194 := by
    simpa [prefixWord, tailWord_2618194, baseEnd_2618194] using wordTrace_append hprefix tailTrace_2618194
  have hstable : (prefixWord ++ tailWord_2618194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618194).length < 2 ^ (prefixWord ++ tailWord_2618194).sum := by decide
  have hdescent : baseEnd_2618194 < baseStart_2618194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618197 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 6]
def baseStart_2618197 : Nat := 118140960795 + 2618197 * 2 ^ 59
def prefixEnd_2618197 : Nat := 4983230072969 + 3 ^ 40 * 2618197 * 2
def baseEnd_2618197 : Nat := 149377056573310891766293

theorem tailTrace_2618197 : CollatzResearch.WordTrace tailWord_2618197 prefixEnd_2618197 149377056573310891766293 := by
  unfold tailWord_2618197
  simp only [CollatzResearch.WordTrace]
  refine ⟨95493489695726896293084845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63662326463817930862056563 95493489695726896293084845)
  ·
    refine ⟨35810058635897586109906817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95493489695726896293084845 35810058635897586109906817)
    ·
      refine ⟨26857543976923189582430113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35810058635897586109906817 26857543976923189582430113)
      ·
        refine ⟨20143157982692392186822585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26857543976923189582430113 20143157982692392186822585)
        ·
          refine ⟨15107368487019294140116939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20143157982692392186822585 15107368487019294140116939)
          ·
            refine ⟨22661052730528941210175409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15107368487019294140116939 22661052730528941210175409)
            ·
              refine ⟨16995789547896705907631557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22661052730528941210175409 16995789547896705907631557)
              ·
                refine ⟨3186710540230632357680917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16995789547896705907631557 3186710540230632357680917)
                ·
                  refine ⟨149377056573310891766293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3186710540230632357680917 149377056573310891766293)
                  ·
                    rfl

theorem cell23_2618197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_2618197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618197 prefixEnd_2618197 := by exact prefixLift 2618197
  have htrace : WordTrace (prefixWord ++ tailWord_2618197) baseStart_2618197 baseEnd_2618197 := by
    simpa [prefixWord, tailWord_2618197, baseEnd_2618197] using wordTrace_append hprefix tailTrace_2618197
  have hstable : (prefixWord ++ tailWord_2618197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618197).length < 2 ^ (prefixWord ++ tailWord_2618197).sum := by decide
  have hdescent : baseEnd_2618197 < baseStart_2618197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618200 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2618200 : Nat := 118140960795 + 2618200 * 2 ^ 59
def prefixEnd_2618200 : Nat := 4983230072969 + 3 ^ 40 * 2618200 * 2
def baseEnd_2618200 : Nat := 1344395049601761514159123

theorem tailTrace_2618200 : CollatzResearch.WordTrace tailWord_2618200 prefixEnd_2618200 1344395049601761514159123 := by
  unfold tailWord_2618200
  simp only [CollatzResearch.WordTrace]
  refine ⟨47746799557358013902722027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63662399409810685203629369 47746799557358013902722027)
  ·
    refine ⟨71620199336037020854083041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47746799557358013902722027 71620199336037020854083041)
    ·
      refine ⟨53715149502027765640562281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71620199336037020854083041 53715149502027765640562281)
      ·
        refine ⟨40286362126520824230421711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53715149502027765640562281 40286362126520824230421711)
        ·
          refine ⟨60429543189781236345632567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40286362126520824230421711 60429543189781236345632567)
          ·
            refine ⟨90644314784671854518448851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60429543189781236345632567 90644314784671854518448851)
            ·
              refine ⟨135966472177007781777673277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90644314784671854518448851 135966472177007781777673277)
              ·
                refine ⟨50987427066377918166627479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135966472177007781777673277 50987427066377918166627479)
                ·
                  refine ⟨76481140599566877249941219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50987427066377918166627479 76481140599566877249941219)
                  ·
                    refine ⟨114721710899350315874911829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76481140599566877249941219 114721710899350315874911829)
                    ·
                      refine ⟨1344395049601761514159123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114721710899350315874911829 1344395049601761514159123)
                      ·
                        rfl

theorem cell23_2618200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2618200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618200 prefixEnd_2618200 := by exact prefixLift 2618200
  have htrace : WordTrace (prefixWord ++ tailWord_2618200) baseStart_2618200 baseEnd_2618200 := by
    simpa [prefixWord, tailWord_2618200, baseEnd_2618200] using wordTrace_append hprefix tailTrace_2618200
  have hstable : (prefixWord ++ tailWord_2618200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618200).length < 2 ^ (prefixWord ++ tailWord_2618200).sum := by decide
  have hdescent : baseEnd_2618200 < baseStart_2618200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618224 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 3, 1, 3]
def baseStart_2618224 : Nat := 118140960795 + 2618224 * 2 ^ 59
def prefixEnd_2618224 : Nat := 4983230072969 + 3 ^ 40 * 2618224 * 2
def baseEnd_2618224 : Nat := 1344407373137469420259013

theorem tailTrace_2618224 : CollatzResearch.WordTrace tailWord_2618224 prefixEnd_2618224 1344407373137469420259013 := by
  unfold tailWord_2618224
  simp only [CollatzResearch.WordTrace]
  refine ⟨47747237233314539952158863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63662982977752719936211817 47747237233314539952158863)
  ·
    refine ⟨71620855849971809928238295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47747237233314539952158863 71620855849971809928238295)
    ·
      refine ⟨107431283774957714892357443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71620855849971809928238295 107431283774957714892357443)
      ·
        refine ⟨161146925662436572338536165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107431283774957714892357443 161146925662436572338536165)
        ·
          refine ⟨30215048561706857313475531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161146925662436572338536165 30215048561706857313475531)
          ·
            refine ⟨45322572842560285970213297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30215048561706857313475531 45322572842560285970213297)
            ·
              refine ⟨33991929631920214477659973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45322572842560285970213297 33991929631920214477659973)
              ·
                refine ⟨6373486805985040214561245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33991929631920214477659973 6373486805985040214561245)
                ·
                  refine ⟨2390057552244390080460467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6373486805985040214561245 2390057552244390080460467)
                  ·
                    refine ⟨3585086328366585120690701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390057552244390080460467 3585086328366585120690701)
                    ·
                      refine ⟨1344407373137469420259013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3585086328366585120690701 1344407373137469420259013)
                      ·
                        rfl

theorem cell23_2618224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 1, 3].length) (baseStart_2618224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618224 prefixEnd_2618224 := by exact prefixLift 2618224
  have htrace : WordTrace (prefixWord ++ tailWord_2618224) baseStart_2618224 baseEnd_2618224 := by
    simpa [prefixWord, tailWord_2618224, baseEnd_2618224] using wordTrace_append hprefix tailTrace_2618224
  have hstable : (prefixWord ++ tailWord_2618224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618224).length < 2 ^ (prefixWord ++ tailWord_2618224).sum := by decide
  have hdescent : baseEnd_2618224 < baseStart_2618224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618274 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2618274 : Nat := 118140960795 + 2618274 * 2 ^ 59
def prefixEnd_2618274 : Nat := 4983230072969 + 3 ^ 40 * 2618274 * 2
def baseEnd_2618274 : Nat := 448144349056731408211261

theorem tailTrace_2618274 : CollatzResearch.WordTrace tailWord_2618274 prefixEnd_2618274 448144349056731408211261 := by
  unfold tailWord_2618274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23874074529111984610909469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63664198744298625629091917 23874074529111984610909469)
  ·
    refine ⟨8952777948416994229091051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23874074529111984610909469 8952777948416994229091051)
    ·
      refine ⟨13429166922625491343636577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8952777948416994229091051 13429166922625491343636577)
      ·
        refine ⟨10071875191969118507727433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13429166922625491343636577 10071875191969118507727433)
        ·
          refine ⟨7553906393976838880795575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10071875191969118507727433 7553906393976838880795575)
          ·
            refine ⟨11330859590965258321193363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553906393976838880795575 11330859590965258321193363)
            ·
              refine ⟨16996289386447887481790045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11330859590965258321193363 16996289386447887481790045)
              ·
                refine ⟨6373608519917957805671267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16996289386447887481790045 6373608519917957805671267)
                ·
                  refine ⟨9560412779876936708506901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373608519917957805671267 9560412779876936708506901)
                  ·
                    refine ⟨448144349056731408211261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9560412779876936708506901 448144349056731408211261)
                    ·
                      rfl

theorem cell23_2618274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2618274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618274 prefixEnd_2618274 := by exact prefixLift 2618274
  have htrace : WordTrace (prefixWord ++ tailWord_2618274) baseStart_2618274 baseEnd_2618274 := by
    simpa [prefixWord, tailWord_2618274, baseEnd_2618274] using wordTrace_append hprefix tailTrace_2618274
  have hstable : (prefixWord ++ tailWord_2618274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618274).length < 2 ^ (prefixWord ++ tailWord_2618274).sum := by decide
  have hdescent : baseEnd_2618274 < baseStart_2618274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618281 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 3, 2, 2]
def baseStart_2618281 : Nat := 118140960795 + 2618281 * 2 ^ 59
def prefixEnd_2618281 : Nat := 4983230072969 + 3 ^ 40 * 2618281 * 2
def baseEnd_2618281 : Nat := 1344436641534775697246251

theorem tailTrace_2618281 : CollatzResearch.WordTrace tailWord_2618281 prefixEnd_2618281 1344436641534775697246251 := by
  unfold tailWord_2618281
  simp only [CollatzResearch.WordTrace]
  refine ⟨95496553427422578639142697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63664368951615052426095131 95496553427422578639142697)
  ·
    refine ⟨71622415070566933979357023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95496553427422578639142697 71622415070566933979357023)
    ·
      refine ⟨107433622605850400969035535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71622415070566933979357023 107433622605850400969035535)
      ·
        refine ⟨161150433908775601453553303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107433622605850400969035535 161150433908775601453553303)
        ·
          refine ⟨241725650863163402180329955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161150433908775601453553303 241725650863163402180329955)
          ·
            refine ⟨362588476294745103270494933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241725650863163402180329955 362588476294745103270494933)
            ·
              refine ⟨8498167413158088357902225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 362588476294745103270494933 8498167413158088357902225)
              ·
                refine ⟨6373625559868566268426669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8498167413158088357902225 6373625559868566268426669)
                ·
                  refine ⟨2390109584950712350660001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6373625559868566268426669 2390109584950712350660001)
                  ·
                    refine ⟨1792582188713034262995001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2390109584950712350660001 1792582188713034262995001)
                    ·
                      refine ⟨1344436641534775697246251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792582188713034262995001 1344436641534775697246251)
                      ·
                        rfl

theorem cell23_2618281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 2, 2].length) (baseStart_2618281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618281 prefixEnd_2618281 := by exact prefixLift 2618281
  have htrace : WordTrace (prefixWord ++ tailWord_2618281) baseStart_2618281 baseEnd_2618281 := by
    simpa [prefixWord, tailWord_2618281, baseEnd_2618281] using wordTrace_append hprefix tailTrace_2618281
  have hstable : (prefixWord ++ tailWord_2618281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618281).length < 2 ^ (prefixWord ++ tailWord_2618281).sum := by decide
  have hdescent : baseEnd_2618281 < baseStart_2618281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618292 : List Nat := [2, 5, 2, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_2618292 : Nat := 118140960795 + 2618292 * 2 ^ 59
def prefixEnd_2618292 : Nat := 4983230072969 + 3 ^ 40 * 2618292 * 2
def baseEnd_2618292 : Nat := 1344442289821975154208701

theorem tailTrace_2618292 : CollatzResearch.WordTrace tailWord_2618292 prefixEnd_2618292 1344442289821975154208701 := by
  unfold tailWord_2618292
  simp only [CollatzResearch.WordTrace]
  refine ⟨47748477315191363758896565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63664636420255151678528753 47748477315191363758896565)
  ·
    refine ⟨4476419748299190352396553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47748477315191363758896565 4476419748299190352396553)
    ·
      refine ⟨3357314811224392764297415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4476419748299190352396553 3357314811224392764297415)
      ·
        refine ⟨5035972216836589146446123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357314811224392764297415 5035972216836589146446123)
        ·
          refine ⟨7553958325254883719669185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035972216836589146446123 7553958325254883719669185)
          ·
            refine ⟨5665468743941162789751889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7553958325254883719669185 5665468743941162789751889)
            ·
              refine ⟨4249101557955872092313917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5665468743941162789751889 4249101557955872092313917)
              ·
                refine ⟨1593413084233452034617719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4249101557955872092313917 1593413084233452034617719)
                ·
                  refine ⟨2390119626350178051926579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593413084233452034617719 2390119626350178051926579)
                  ·
                    refine ⟨3585179439525267077889869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390119626350178051926579 3585179439525267077889869)
                    ·
                      refine ⟨1344442289821975154208701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3585179439525267077889869 1344442289821975154208701)
                      ·
                        rfl

theorem cell23_2618292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_2618292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618292 prefixEnd_2618292 := by exact prefixLift 2618292
  have htrace : WordTrace (prefixWord ++ tailWord_2618292) baseStart_2618292 baseEnd_2618292 := by
    simpa [prefixWord, tailWord_2618292, baseEnd_2618292] using wordTrace_append hprefix tailTrace_2618292
  have hstable : (prefixWord ++ tailWord_2618292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618292).length < 2 ^ (prefixWord ++ tailWord_2618292).sum := by decide
  have hdescent : baseEnd_2618292 < baseStart_2618292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618308 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2618308 : Nat := 118140960795 + 2618308 * 2 ^ 59
def prefixEnd_2618308 : Nat := 4983230072969 + 3 ^ 40 * 2618308 * 2
def baseEnd_2618308 : Nat := 448150168504149030536209

theorem tailTrace_2618308 : CollatzResearch.WordTrace tailWord_2618308 prefixEnd_2618308 448150168504149030536209 := by
  unfold tailWord_2618308
  simp only [CollatzResearch.WordTrace]
  refine ⟨47748769099162381125187789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63665025465549841500250385 47748769099162381125187789)
  ·
    refine ⟨17905788412185892921945421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47748769099162381125187789 17905788412185892921945421)
    ·
      refine ⟨6714670654569709845729533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17905788412185892921945421 6714670654569709845729533)
      ·
        refine ⟨2518001495463641192148575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6714670654569709845729533 2518001495463641192148575)
        ·
          refine ⟨3777002243195461788222863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518001495463641192148575 3777002243195461788222863)
          ·
            refine ⟨5665503364793192682334295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3777002243195461788222863 5665503364793192682334295)
            ·
              refine ⟨8498255047189789023501443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5665503364793192682334295 8498255047189789023501443)
              ·
                refine ⟨12747382570784683535252165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8498255047189789023501443 12747382570784683535252165)
                ·
                  refine ⟨2390134232022128162859781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12747382570784683535252165 2390134232022128162859781)
                  ·
                    refine ⟨448150168504149030536209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390134232022128162859781 448150168504149030536209)
                    ·
                      rfl

theorem cell23_2618308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2618308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618308 prefixEnd_2618308 := by exact prefixLift 2618308
  have htrace : WordTrace (prefixWord ++ tailWord_2618308) baseStart_2618308 baseEnd_2618308 := by
    simpa [prefixWord, tailWord_2618308, baseEnd_2618308] using wordTrace_append hprefix tailTrace_2618308
  have hstable : (prefixWord ++ tailWord_2618308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618308).length < 2 ^ (prefixWord ++ tailWord_2618308).sum := by decide
  have hdescent : baseEnd_2618308 < baseStart_2618308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618338 : List Nat := [3, 3, 3, 1, 1, 3, 2, 7]
def baseStart_2618338 : Nat := 118140960795 + 2618338 * 2 ^ 59
def prefixEnd_2618338 : Nat := 4983230072969 + 3 ^ 40 * 2618338 * 2
def baseEnd_2618338 : Nat := 49795033701188221267907

theorem tailTrace_2618338 : CollatzResearch.WordTrace tailWord_2618338 prefixEnd_2618338 49795033701188221267907 := by
  unfold tailWord_2618338
  simp only [CollatzResearch.WordTrace]
  refine ⟨23874658097054019343491917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63665754925477384915978445 23874658097054019343491917)
  ·
    refine ⟨8952996786395257253809469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23874658097054019343491917 8952996786395257253809469)
    ·
      refine ⟨3357373794898221470178551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8952996786395257253809469 3357373794898221470178551)
      ·
        refine ⟨5036060692347332205267827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357373794898221470178551 5036060692347332205267827)
        ·
          refine ⟨7554091038520998307901741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036060692347332205267827 7554091038520998307901741)
          ·
            refine ⟨2832784139445374365463153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7554091038520998307901741 2832784139445374365463153)
            ·
              refine ⟨2124588104584030774097365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2832784139445374365463153 2124588104584030774097365)
              ·
                refine ⟨49795033701188221267907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2124588104584030774097365 49795033701188221267907)
                ·
                  rfl

theorem cell23_2618338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 7].length) (baseStart_2618338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618338 prefixEnd_2618338 := by exact prefixLift 2618338
  have htrace : WordTrace (prefixWord ++ tailWord_2618338) baseStart_2618338 baseEnd_2618338 := by
    simpa [prefixWord, tailWord_2618338, baseEnd_2618338] using wordTrace_append hprefix tailTrace_2618338
  have hstable : (prefixWord ++ tailWord_2618338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618338).length < 2 ^ (prefixWord ++ tailWord_2618338).sum := by decide
  have hdescent : baseEnd_2618338 < baseStart_2618338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618422 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_2618422 : Nat := 118140960795 + 2618422 * 2 ^ 59
def prefixEnd_2618422 : Nat := 4983230072969 + 3 ^ 40 * 2618422 * 2
def baseEnd_2618422 : Nat := 1344509042307059645583103

theorem tailTrace_2618422 : CollatzResearch.WordTrace tailWord_2618422 prefixEnd_2618422 1344509042307059645583103 := by
  unfold tailWord_2618422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968856007494484982501595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63667797413274506480017013 5968856007494484982501595)
  ·
    refine ⟨8953284011241727473752393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5968856007494484982501595 8953284011241727473752393)
    ·
      refine ⟨6714963008431295605314295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8953284011241727473752393 6714963008431295605314295)
      ·
        refine ⟨10072444512646943407971443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6714963008431295605314295 10072444512646943407971443)
        ·
          refine ⟨15108666768970415111957165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072444512646943407971443 15108666768970415111957165)
          ·
            refine ⟨5665750038363905666983937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15108666768970415111957165 5665750038363905666983937)
            ·
              refine ⟨4249312528772929250237953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5665750038363905666983937 4249312528772929250237953)
              ·
                refine ⟨3186984396579696937678465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4249312528772929250237953 3186984396579696937678465)
                ·
                  refine ⟨2390238297434772703258849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186984396579696937678465 2390238297434772703258849)
                  ·
                    refine ⟨1792678723076079527444137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2390238297434772703258849 1792678723076079527444137)
                    ·
                      refine ⟨1344509042307059645583103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792678723076079527444137 1344509042307059645583103)
                      ·
                        rfl

theorem cell23_2618422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_2618422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618422 prefixEnd_2618422 := by exact prefixLift 2618422
  have htrace : WordTrace (prefixWord ++ tailWord_2618422) baseStart_2618422 baseEnd_2618422 := by
    simpa [prefixWord, tailWord_2618422, baseEnd_2618422] using wordTrace_append hprefix tailTrace_2618422
  have hstable : (prefixWord ++ tailWord_2618422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618422).length < 2 ^ (prefixWord ++ tailWord_2618422).sum := by decide
  have hdescent : baseEnd_2618422 < baseStart_2618422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618427 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8]
def baseStart_2618427 : Nat := 118140960795 + 2618427 * 2 ^ 59
def prefixEnd_2618427 : Nat := 4983230072969 + 3 ^ 40 * 2618427 * 2
def baseEnd_2618427 : Nat := 1344511609710332126020579

theorem tailTrace_2618427 : CollatzResearch.WordTrace tailWord_2618427 prefixEnd_2618427 1344511609710332126020579 := by
  unfold tailWord_2618427
  simp only [CollatzResearch.WordTrace]
  refine ⟨95501878484893645573957535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63667918989929097049305023 95501878484893645573957535)
  ·
    refine ⟨143252817727340468360936303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95501878484893645573957535 143252817727340468360936303)
    ·
      refine ⟨214879226591010702541404455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143252817727340468360936303 214879226591010702541404455)
      ·
        refine ⟨322318839886516053812106683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214879226591010702541404455 322318839886516053812106683)
        ·
          refine ⟨483478259829774080718160025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322318839886516053812106683 483478259829774080718160025)
          ·
            refine ⟨362608694872330560538620019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483478259829774080718160025 362608694872330560538620019)
            ·
              refine ⟨543913042308495840807930029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362608694872330560538620019 543913042308495840807930029)
              ·
                refine ⟨203967390865685940302973761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 543913042308495840807930029 203967390865685940302973761)
                ·
                  refine ⟨152975543149264455227230321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203967390865685940302973761 152975543149264455227230321)
                  ·
                    refine ⟨114731657361948341420422741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152975543149264455227230321 114731657361948341420422741)
                    ·
                      refine ⟨1344511609710332126020579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114731657361948341420422741 1344511609710332126020579)
                      ·
                        rfl

theorem cell23_2618427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_2618427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618427 prefixEnd_2618427 := by exact prefixLift 2618427
  have htrace : WordTrace (prefixWord ++ tailWord_2618427) baseStart_2618427 baseEnd_2618427 := by
    simpa [prefixWord, tailWord_2618427, baseEnd_2618427] using wordTrace_append hprefix tailTrace_2618427
  have hstable : (prefixWord ++ tailWord_2618427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618427).length < 2 ^ (prefixWord ++ tailWord_2618427).sum := by decide
  have hdescent : baseEnd_2618427 < baseStart_2618427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618428 : List Nat := [2, 2, 2, 2, 2, 2, 4, 2, 5]
def baseStart_2618428 : Nat := 118140960795 + 2618428 * 2 ^ 59
def prefixEnd_2618428 : Nat := 4983230072969 + 3 ^ 40 * 2618428 * 2
def baseEnd_2618428 : Nat := 149390235910109624678675

theorem tailTrace_2618428 : CollatzResearch.WordTrace tailWord_2618428 prefixEnd_2618428 149390235910109624678675 := by
  unfold tailWord_2618428
  simp only [CollatzResearch.WordTrace]
  refine ⟨47750957478945011372371969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63667943305260015163162625 47750957478945011372371969)
  ·
    refine ⟨35813218109208758529278977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47750957478945011372371969 35813218109208758529278977)
    ·
      refine ⟨26859913581906568896959233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35813218109208758529278977 26859913581906568896959233)
      ·
        refine ⟨20144935186429926672719425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26859913581906568896959233 20144935186429926672719425)
        ·
          refine ⟨15108701389822445004539569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20144935186429926672719425 15108701389822445004539569)
          ·
            refine ⟨11331526042366833753404677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15108701389822445004539569 11331526042366833753404677)
            ·
              refine ⟨2124661132943781328763377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11331526042366833753404677 2124661132943781328763377)
              ·
                refine ⟨1593495849707835996572533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124661132943781328763377 1593495849707835996572533)
                ·
                  refine ⟨149390235910109624678675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593495849707835996572533 149390235910109624678675)
                  ·
                    rfl

theorem cell23_2618428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_2618428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618428 prefixEnd_2618428 := by exact prefixLift 2618428
  have htrace : WordTrace (prefixWord ++ tailWord_2618428) baseStart_2618428 baseEnd_2618428 := by
    simpa [prefixWord, tailWord_2618428, baseEnd_2618428] using wordTrace_append hprefix tailTrace_2618428
  have hstable : (prefixWord ++ tailWord_2618428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618428).length < 2 ^ (prefixWord ++ tailWord_2618428).sum := by decide
  have hdescent : baseEnd_2618428 < baseStart_2618428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618438 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2618438 : Nat := 118140960795 + 2618438 * 2 ^ 59
def prefixEnd_2618438 : Nat := 4983230072969 + 3 ^ 40 * 2618438 * 2
def baseEnd_2618438 : Nat := 1344517257997531582983029

theorem tailTrace_2618438 : CollatzResearch.WordTrace tailWord_2618438 prefixEnd_2618438 1344517257997531582983029 := by
  unfold tailWord_2618438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984446240245431076643999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63668186458569196301738645 2984446240245431076643999)
  ·
    refine ⟨4476669360368146614965999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2984446240245431076643999 4476669360368146614965999)
    ·
      refine ⟨6715004040552219922448999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4476669360368146614965999 6715004040552219922448999)
      ·
        refine ⟨10072506060828329883673499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6715004040552219922448999 10072506060828329883673499)
        ·
          refine ⟨15108759091242494825510249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072506060828329883673499 15108759091242494825510249)
          ·
            refine ⟨11331569318431871119132687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15108759091242494825510249 11331569318431871119132687)
            ·
              refine ⟨16997353977647806678699031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11331569318431871119132687 16997353977647806678699031)
              ·
                refine ⟨25496030966471710018048547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16997353977647806678699031 25496030966471710018048547)
                ·
                  refine ⟨38244046449707565027072821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25496030966471710018048547 38244046449707565027072821)
                  ·
                    refine ⟨3585379354660084221288077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38244046449707565027072821 3585379354660084221288077)
                    ·
                      refine ⟨1344517257997531582983029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3585379354660084221288077 1344517257997531582983029)
                      ·
                        rfl

theorem cell23_2618438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2618438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618438 prefixEnd_2618438 := by exact prefixLift 2618438
  have htrace : WordTrace (prefixWord ++ tailWord_2618438) baseStart_2618438 baseEnd_2618438 := by
    simpa [prefixWord, tailWord_2618438, baseEnd_2618438] using wordTrace_append hprefix tailTrace_2618438
  have hstable : (prefixWord ++ tailWord_2618438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618438).length < 2 ^ (prefixWord ++ tailWord_2618438).sum := by decide
  have hdescent : baseEnd_2618438 < baseStart_2618438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618444 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2618444 : Nat := 118140960795 + 2618444 * 2 ^ 59
def prefixEnd_2618444 : Nat := 4983230072969 + 3 ^ 40 * 2618444 * 2
def baseEnd_2618444 : Nat := 1344520338881458559508001

theorem tailTrace_2618444 : CollatzResearch.WordTrace tailWord_2618444 prefixEnd_2618444 1344520338881458559508001 := by
  unfold tailWord_2618444
  simp only [CollatzResearch.WordTrace]
  refine ⟨47751249262916028738663193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63668332350554704984884257 47751249262916028738663193)
  ·
    refine ⟨35813436947187021553997395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47751249262916028738663193 35813436947187021553997395)
    ·
      refine ⟨53720155420780532330996093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35813436947187021553997395 53720155420780532330996093)
      ·
        refine ⟨20145058282792699624123535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53720155420780532330996093 20145058282792699624123535)
        ·
          refine ⟨30217587424189049436185303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20145058282792699624123535 30217587424189049436185303)
          ·
            refine ⟨45326381136283574154277955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30217587424189049436185303 45326381136283574154277955)
            ·
              refine ⟨67989571704425361231416933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45326381136283574154277955 67989571704425361231416933)
              ·
                refine ⟨12748044694579755230890675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67989571704425361231416933 12748044694579755230890675)
                ·
                  refine ⟨19122067041869632846336013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12748044694579755230890675 19122067041869632846336013)
                  ·
                    refine ⟨7170775140701112317376005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19122067041869632846336013 7170775140701112317376005)
                    ·
                      refine ⟨1344520338881458559508001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7170775140701112317376005 1344520338881458559508001)
                      ·
                        rfl

theorem cell23_2618444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2618444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618444 prefixEnd_2618444 := by exact prefixLift 2618444
  have htrace : WordTrace (prefixWord ++ tailWord_2618444) baseStart_2618444 baseEnd_2618444 := by
    simpa [prefixWord, tailWord_2618444, baseEnd_2618444] using wordTrace_append hprefix tailTrace_2618444
  have hstable : (prefixWord ++ tailWord_2618444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618444).length < 2 ^ (prefixWord ++ tailWord_2618444).sum := by decide
  have hdescent : baseEnd_2618444 < baseStart_2618444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618462 : List Nat := [4, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2618462 : Nat := 118140960795 + 2618462 * 2 ^ 59
def prefixEnd_2618462 : Nat := 4983230072969 + 3 ^ 40 * 2618462 * 2
def baseEnd_2618462 : Nat := 149392175725915498786991

theorem tailTrace_2618462 : CollatzResearch.WordTrace tailWord_2618462 prefixEnd_2618462 149392175725915498786991 := by
  unfold tailWord_2618462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937894379970855818935205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63668770026511231034321093 11937894379970855818935205)
  ·
    refine ⟨2238355196244535466050351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11937894379970855818935205 2238355196244535466050351)
    ·
      refine ⟨3357532794366803199075527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238355196244535466050351 3357532794366803199075527)
      ·
        refine ⟨5036299191550204798613291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357532794366803199075527 5036299191550204798613291)
        ·
          refine ⟨7554448787325307197919937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036299191550204798613291 7554448787325307197919937)
          ·
            refine ⟨5665836590493980398439953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7554448787325307197919937 5665836590493980398439953)
            ·
              refine ⟨4249377442870485298829965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5665836590493980398439953 4249377442870485298829965)
              ·
                refine ⟨1593516541076431987061237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4249377442870485298829965 1593516541076431987061237)
                ·
                  refine ⟨149392175725915498786991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593516541076431987061237 149392175725915498786991)
                  ·
                    rfl

theorem cell23_2618462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2618462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618462 prefixEnd_2618462 := by exact prefixLift 2618462
  have htrace : WordTrace (prefixWord ++ tailWord_2618462) baseStart_2618462 baseEnd_2618462 := by
    simpa [prefixWord, tailWord_2618462, baseEnd_2618462] using wordTrace_append hprefix tailTrace_2618462
  have hstable : (prefixWord ++ tailWord_2618462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618462).length < 2 ^ (prefixWord ++ tailWord_2618462).sum := by decide
  have hdescent : baseEnd_2618462 < baseStart_2618462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618478 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_2618478 : Nat := 118140960795 + 2618478 * 2 ^ 59
def prefixEnd_2618478 : Nat := 4983230072969 + 3 ^ 40 * 2618478 * 2
def baseEnd_2618478 : Nat := 1344537797223711426482845

theorem tailTrace_2618478 : CollatzResearch.WordTrace tailWord_2618478 prefixEnd_2618478 1344537797223711426482845 := by
  unfold tailWord_2618478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937967325963610160508011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63669159071805920856042725 11937967325963610160508011)
  ·
    refine ⟨17906950988945415240762017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937967325963610160508011 17906950988945415240762017)
    ·
      refine ⟨13430213241709061430571513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17906950988945415240762017 13430213241709061430571513)
      ·
        refine ⟨10072659931281796072928635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13430213241709061430571513 10072659931281796072928635)
        ·
          refine ⟨15108989896922694109392953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072659931281796072928635 15108989896922694109392953)
          ·
            refine ⟨11331742422692020582044715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15108989896922694109392953 11331742422692020582044715)
            ·
              refine ⟨16997613634038030873067073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11331742422692020582044715 16997613634038030873067073)
              ·
                refine ⟨12748210225528523154800305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16997613634038030873067073 12748210225528523154800305)
                ·
                  refine ⟨9561157669146392366100229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12748210225528523154800305 9561157669146392366100229)
                  ·
                    refine ⟨1792717062964948568643793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9561157669146392366100229 1792717062964948568643793)
                    ·
                      refine ⟨1344537797223711426482845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1792717062964948568643793 1344537797223711426482845)
                      ·
                        rfl

theorem cell23_2618478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_2618478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618478 prefixEnd_2618478 := by exact prefixLift 2618478
  have htrace : WordTrace (prefixWord ++ tailWord_2618478) baseStart_2618478 baseEnd_2618478 := by
    simpa [prefixWord, tailWord_2618478, baseEnd_2618478] using wordTrace_append hprefix tailTrace_2618478
  have hstable : (prefixWord ++ tailWord_2618478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618478).length < 2 ^ (prefixWord ++ tailWord_2618478).sum := by decide
  have hdescent : baseEnd_2618478 < baseStart_2618478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618488 : List Nat := [2, 1, 2, 1, 1, 1, 6, 4, 1, 4]
def baseStart_2618488 : Nat := 118140960795 + 2618488 * 2 ^ 59
def prefixEnd_2618488 : Nat := 4983230072969 + 3 ^ 40 * 2618488 * 2
def baseEnd_2618488 : Nat := 448180977343418795785933

theorem tailTrace_2618488 : CollatzResearch.WordTrace tailWord_2618488 prefixEnd_2618488 448180977343418795785933 := by
  unfold tailWord_2618488
  simp only [CollatzResearch.WordTrace]
  refine ⟨47752051668836326495964059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63669402225115101994618745 47752051668836326495964059)
  ·
    refine ⟨71628077503254489743946089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47752051668836326495964059 71628077503254489743946089)
    ·
      refine ⟨53721058127440867307959567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71628077503254489743946089 53721058127440867307959567)
      ·
        refine ⟨80581587191161300961939351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53721058127440867307959567 80581587191161300961939351)
        ·
          refine ⟨120872380786741951442909027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80581587191161300961939351 120872380786741951442909027)
          ·
            refine ⟨181308571180112927164363541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120872380786741951442909027 181308571180112927164363541)
            ·
              refine ⟨8498839274067793460829541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 181308571180112927164363541 8498839274067793460829541)
              ·
                refine ⟨1593532363887711273905539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8498839274067793460829541 1593532363887711273905539)
                ·
                  refine ⟨2390298545831566910858309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593532363887711273905539 2390298545831566910858309)
                  ·
                    refine ⟨448180977343418795785933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390298545831566910858309 448180977343418795785933)
                    ·
                      rfl

theorem cell23_2618488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_2618488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618488 prefixEnd_2618488 := by exact prefixLift 2618488
  have htrace : WordTrace (prefixWord ++ tailWord_2618488) baseStart_2618488 baseEnd_2618488 := by
    simpa [prefixWord, tailWord_2618488, baseEnd_2618488] using wordTrace_append hprefix tailTrace_2618488
  have hstable : (prefixWord ++ tailWord_2618488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618488).length < 2 ^ (prefixWord ++ tailWord_2618488).sum := by decide
  have hdescent : baseEnd_2618488 < baseStart_2618488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618511 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 3]
def baseStart_2618511 : Nat := 118140960795 + 2618511 * 2 ^ 59
def prefixEnd_2618511 : Nat := 4983230072969 + 3 ^ 40 * 2618511 * 2
def baseEnd_2618511 : Nat := 1344554742085309797370193

theorem tailTrace_2618511 : CollatzResearch.WordTrace tailWord_2618511 prefixEnd_2618511 1344554742085309797370193 := by
  unfold tailWord_2618511
  simp only [CollatzResearch.WordTrace]
  refine ⟨95504942216589327920015387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63669961477726218613343591 95504942216589327920015387)
  ·
    refine ⟨143257413324883991880023081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95504942216589327920015387 143257413324883991880023081)
    ·
      refine ⟨107443059993662993910017311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143257413324883991880023081 107443059993662993910017311)
      ·
        refine ⟨161164589990494490865025967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107443059993662993910017311 161164589990494490865025967)
        ·
          refine ⟨241746884985741736297538951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161164589990494490865025967 241746884985741736297538951)
          ·
            refine ⟨362620327478612604446308427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241746884985741736297538951 362620327478612604446308427)
            ·
              refine ⟨543930491217918906669462641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362620327478612604446308427 543930491217918906669462641)
              ·
                refine ⟨407947868413439180002096981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543930491217918906669462641 407947868413439180002096981)
                ·
                  refine ⟨2390319541484995195324787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 407947868413439180002096981 2390319541484995195324787)
                  ·
                    refine ⟨3585479312227492792987181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390319541484995195324787 3585479312227492792987181)
                    ·
                      refine ⟨1344554742085309797370193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3585479312227492792987181 1344554742085309797370193)
                      ·
                        rfl

theorem cell23_2618511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 3].length) (baseStart_2618511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618511 prefixEnd_2618511 := by exact prefixLift 2618511
  have htrace : WordTrace (prefixWord ++ tailWord_2618511) baseStart_2618511 baseEnd_2618511 := by
    simpa [prefixWord, tailWord_2618511, baseEnd_2618511] using wordTrace_append hprefix tailTrace_2618511
  have hstable : (prefixWord ++ tailWord_2618511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618511).length < 2 ^ (prefixWord ++ tailWord_2618511).sum := by decide
  have hdescent : baseEnd_2618511 < baseStart_2618511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618522 : List Nat := [3, 1, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_2618522 : Nat := 118140960795 + 2618522 * 2 ^ 59
def prefixEnd_2618522 : Nat := 4983230072969 + 3 ^ 40 * 2618522 * 2
def baseEnd_2618522 : Nat := 448186796790836418110881

theorem tailTrace_2618522 : CollatzResearch.WordTrace tailWord_2618522 prefixEnd_2618522 448186796790836418110881 := by
  unfold tailWord_2618522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23876335854887369199666455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63670228946366317865777213 23876335854887369199666455)
  ·
    refine ⟨35814503782331053799499683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23876335854887369199666455 35814503782331053799499683)
    ·
      refine ⟨53721755673496580699249525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35814503782331053799499683 53721755673496580699249525)
      ·
        refine ⟨5036414594390304440554643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53721755673496580699249525 5036414594390304440554643)
        ·
          refine ⟨7554621891585456660831965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036414594390304440554643 7554621891585456660831965)
          ·
            refine ⟨2832983209344546247811987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7554621891585456660831965 2832983209344546247811987)
            ·
              refine ⟨4249474814016819371717981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832983209344546247811987 4249474814016819371717981)
              ·
                refine ⟨1593553055256307264394243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4249474814016819371717981 1593553055256307264394243)
                ·
                  refine ⟨2390329582884460896591365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593553055256307264394243 2390329582884460896591365)
                  ·
                    refine ⟨448186796790836418110881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390329582884460896591365 448186796790836418110881)
                    ·
                      rfl

theorem cell23_2618522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_2618522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618522 prefixEnd_2618522 := by exact prefixLift 2618522
  have htrace : WordTrace (prefixWord ++ tailWord_2618522) baseStart_2618522 baseEnd_2618522 := by
    simpa [prefixWord, tailWord_2618522, baseEnd_2618522] using wordTrace_append hprefix tailTrace_2618522
  have hstable : (prefixWord ++ tailWord_2618522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618522).length < 2 ^ (prefixWord ++ tailWord_2618522).sum := by decide
  have hdescent : baseEnd_2618522 < baseStart_2618522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618544 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 3, 6]
def baseStart_2618544 : Nat := 118140960795 + 2618544 * 2 ^ 59
def prefixEnd_2618544 : Nat := 4983230072969 + 3 ^ 40 * 2618544 * 2
def baseEnd_2618544 : Nat := 448190562315636056085847

theorem tailTrace_2618544 : CollatzResearch.WordTrace tailWord_2618544 prefixEnd_2618544 448190562315636056085847 := by
  unfold tailWord_2618544
  simp only [CollatzResearch.WordTrace]
  refine ⟨47753072912734887277983343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63670763883646516370644457 47753072912734887277983343)
  ·
    refine ⟨71629609369102330916975015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47753072912734887277983343 71629609369102330916975015)
    ·
      refine ⟨107444414053653496375462523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71629609369102330916975015 107444414053653496375462523)
      ·
        refine ⟨161166621080480244563193785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107444414053653496375462523 161166621080480244563193785)
        ·
          refine ⟨120874965810360183422395339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161166621080480244563193785 120874965810360183422395339)
          ·
            refine ⟨181312448715540275133593009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120874965810360183422395339 181312448715540275133593009)
            ·
              refine ⟨135984336536655206350194757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181312448715540275133593009 135984336536655206350194757)
              ·
                refine ⟨25497063100622851190661517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135984336536655206350194757 25497063100622851190661517)
                ·
                  refine ⟨9561398662733569196498069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25497063100622851190661517 9561398662733569196498069)
                  ·
                    refine ⟨448190562315636056085847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9561398662733569196498069 448190562315636056085847)
                    ·
                      rfl

theorem cell23_2618544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_2618544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618544 prefixEnd_2618544 := by exact prefixLift 2618544
  have htrace : WordTrace (prefixWord ++ tailWord_2618544) baseStart_2618544 baseEnd_2618544 := by
    simpa [prefixWord, tailWord_2618544, baseEnd_2618544] using wordTrace_append hprefix tailTrace_2618544
  have hstable : (prefixWord ++ tailWord_2618544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618544).length < 2 ^ (prefixWord ++ tailWord_2618544).sum := by decide
  have hdescent : baseEnd_2618544 < baseStart_2618544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618545 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2618545 : Nat := 118140960795 + 2618545 * 2 ^ 59
def prefixEnd_2618545 : Nat := 4983230072969 + 3 ^ 40 * 2618545 * 2
def baseEnd_2618545 : Nat := 1344572200427562664345037

theorem tailTrace_2618545 : CollatzResearch.WordTrace tailWord_2618545 prefixEnd_2618545 1344572200427562664345037 := by
  unfold tailWord_2618545
  simp only [CollatzResearch.WordTrace]
  refine ⟨95506182298466151726753089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63670788198977434484502059 95506182298466151726753089)
  ·
    refine ⟨71629636723849613795064817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95506182298466151726753089 71629636723849613795064817)
    ·
      refine ⟨53722227542887210346298613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71629636723849613795064817 53722227542887210346298613)
      ·
        refine ⟨5036458832145675969965495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53722227542887210346298613 5036458832145675969965495)
        ·
          refine ⟨7554688248218513954948243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036458832145675969965495 7554688248218513954948243)
          ·
            refine ⟨11332032372327770932422365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7554688248218513954948243 11332032372327770932422365)
            ·
              refine ⟨4249512139622914099658387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11332032372327770932422365 4249512139622914099658387)
              ·
                refine ⟨6374268209434371149487581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4249512139622914099658387 6374268209434371149487581)
                ·
                  refine ⟨2390350578537889181057843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6374268209434371149487581 2390350578537889181057843)
                  ·
                    refine ⟨3585525867806833771586765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2390350578537889181057843 3585525867806833771586765)
                    ·
                      refine ⟨1344572200427562664345037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3585525867806833771586765 1344572200427562664345037)
                      ·
                        rfl

theorem cell23_2618545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2618545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618545 prefixEnd_2618545 := by exact prefixLift 2618545
  have htrace : WordTrace (prefixWord ++ tailWord_2618545) baseStart_2618545 baseEnd_2618545 := by
    simpa [prefixWord, tailWord_2618545, baseEnd_2618545] using wordTrace_append hprefix tailTrace_2618545
  have hstable : (prefixWord ++ tailWord_2618545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618545).length < 2 ^ (prefixWord ++ tailWord_2618545).sum := by decide
  have hdescent : baseEnd_2618545 < baseStart_2618545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618551 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_2618551 : Nat := 118140960795 + 2618551 * 2 ^ 59
def prefixEnd_2618551 : Nat := 4983230072969 + 3 ^ 40 * 2618551 * 2
def baseEnd_2618551 : Nat := 1344575281311489640870009

theorem tailTrace_2618551 : CollatzResearch.WordTrace tailWord_2618551 prefixEnd_2618551 1344575281311489640870009 := by
  unfold tailWord_2618551
  simp only [CollatzResearch.WordTrace]
  refine ⟨95506401136444414751471507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63670934090962943167647671 95506401136444414751471507)
  ·
    refine ⟨143259601704666622127207261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95506401136444414751471507 143259601704666622127207261)
    ·
      refine ⟨53722350639249983297702723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143259601704666622127207261 53722350639249983297702723)
      ·
        refine ⟨80583525958874974946554085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53722350639249983297702723 80583525958874974946554085)
        ·
          refine ⟨15109411117289057802478891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80583525958874974946554085 15109411117289057802478891)
          ·
            refine ⟨22664116675933586703718337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15109411117289057802478891 22664116675933586703718337)
            ·
              refine ⟨16998087506950190027788753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22664116675933586703718337 16998087506950190027788753)
              ·
                refine ⟨12748565630212642520841565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16998087506950190027788753 12748565630212642520841565)
                ·
                  refine ⟨4780712111329740945315587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12748565630212642520841565 4780712111329740945315587)
                  ·
                    refine ⟨7171068166994611417973381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4780712111329740945315587 7171068166994611417973381)
                    ·
                      refine ⟨1344575281311489640870009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7171068166994611417973381 1344575281311489640870009)
                      ·
                        rfl

theorem cell23_2618551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_2618551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618551 prefixEnd_2618551 := by exact prefixLift 2618551
  have htrace : WordTrace (prefixWord ++ tailWord_2618551) baseStart_2618551 baseEnd_2618551 := by
    simpa [prefixWord, tailWord_2618551, baseEnd_2618551] using wordTrace_append hprefix tailTrace_2618551
  have hstable : (prefixWord ++ tailWord_2618551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618551).length < 2 ^ (prefixWord ++ tailWord_2618551).sum := by decide
  have hdescent : baseEnd_2618551 < baseStart_2618551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618568 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_2618568 : Nat := 118140960795 + 2618568 * 2 ^ 59
def prefixEnd_2618568 : Nat := 4983230072969 + 3 ^ 40 * 2618568 * 2
def baseEnd_2618568 : Nat := 1344584010482616074357431

theorem tailTrace_2618568 : CollatzResearch.WordTrace tailWord_2618568 prefixEnd_2618568 1344584010482616074357431 := by
  unfold tailWord_2618568
  simp only [CollatzResearch.WordTrace]
  refine ⟨47753510588691413327420179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63671347451588551103226905 47753510588691413327420179)
  ·
    refine ⟨71630265883037119991130269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47753510588691413327420179 71630265883037119991130269)
    ·
      refine ⟨26861349706138919996673851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71630265883037119991130269 26861349706138919996673851)
      ·
        refine ⟨40292024559208379995010777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26861349706138919996673851 40292024559208379995010777)
        ·
          refine ⟨30219018419406284996258083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40292024559208379995010777 30219018419406284996258083)
          ·
            refine ⟨45328527629109427494387125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30219018419406284996258083 45328527629109427494387125)
            ·
              refine ⟨4249549465229008827598793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45328527629109427494387125 4249549465229008827598793)
              ·
                refine ⟨3187162098921756620699095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4249549465229008827598793 3187162098921756620699095)
                ·
                  refine ⟨4780743148382634931048643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187162098921756620699095 4780743148382634931048643)
                  ·
                    refine ⟨7171114722573952396572965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4780743148382634931048643 7171114722573952396572965)
                    ·
                      refine ⟨1344584010482616074357431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7171114722573952396572965 1344584010482616074357431)
                      ·
                        rfl

theorem cell23_2618568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_2618568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618568 prefixEnd_2618568 := by exact prefixLift 2618568
  have htrace : WordTrace (prefixWord ++ tailWord_2618568) baseStart_2618568 baseEnd_2618568 := by
    simpa [prefixWord, tailWord_2618568, baseEnd_2618568] using wordTrace_append hprefix tailTrace_2618568
  have hstable : (prefixWord ++ tailWord_2618568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618568).length < 2 ^ (prefixWord ++ tailWord_2618568).sum := by decide
  have hdescent : baseEnd_2618568 < baseStart_2618568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2618618 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_2618618 : Nat := 118140960795 + 2618618 * 2 ^ 59
def prefixEnd_2618618 : Nat := 4983230072969 + 3 ^ 40 * 2618618 * 2
def baseEnd_2618618 : Nat := 1344609684515340878732201

theorem tailTrace_2618618 : CollatzResearch.WordTrace tailWord_2618618 prefixEnd_2618618 1344609684515340878732201 := by
  unfold tailWord_2618618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23877211206800421298540127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63672563218134456796107005 23877211206800421298540127)
  ·
    refine ⟨35815816810200631947810191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23877211206800421298540127 35815816810200631947810191)
    ·
      refine ⟨53723725215300947921715287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35815816810200631947810191 53723725215300947921715287)
      ·
        refine ⟨80585587822951421882572931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53723725215300947921715287 80585587822951421882572931)
        ·
          refine ⟨120878381734427132823859397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80585587822951421882572931 120878381734427132823859397)
          ·
            refine ⟨22664696575205087404473637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120878381734427132823859397 22664696575205087404473637)
            ·
              refine ⟨4249630607850953888338807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22664696575205087404473637 4249630607850953888338807)
              ·
                refine ⟨6374445911776430832508211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4249630607850953888338807 6374445911776430832508211)
                ·
                  refine ⟨9561668867664646248762317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6374445911776430832508211 9561668867664646248762317)
                  ·
                    refine ⟨3585625825374242343285869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9561668867664646248762317 3585625825374242343285869)
                    ·
                      refine ⟨1344609684515340878732201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3585625825374242343285869 1344609684515340878732201)
                      ·
                        rfl

theorem cell23_2618618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_2618618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2618618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2618618 prefixEnd_2618618 := by exact prefixLift 2618618
  have htrace : WordTrace (prefixWord ++ tailWord_2618618) baseStart_2618618 baseEnd_2618618 := by
    simpa [prefixWord, tailWord_2618618, baseEnd_2618618] using wordTrace_append hprefix tailTrace_2618618
  have hstable : (prefixWord ++ tailWord_2618618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2618618).length < 2 ^ (prefixWord ++ tailWord_2618618).sum := by decide
  have hdescent : baseEnd_2618618 < baseStart_2618618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2618618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
